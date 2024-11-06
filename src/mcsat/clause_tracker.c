/*
 * This file is part of the Yices SMT Solver.
 * Copyright (C) 2024 SRI International.
 *
 * Yices is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Yices is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with Yices.  If not, see <http://www.gnu.org/licenses/>.
 */

#include "mcsat/clause_tracker.h"

#include "utils/int_vectors.h"
#include "utils/int_hash_map.h"
#include "utils/ptr_hash_map.h"
#include "utils/int_hash_sets.h"

#include "mcsat/utils/scope_holder.h"

/**
 * Element in the list. Each element contains one clause that is c-unit in x.
 * Prev is the index of the previous element in the list.
 */
typedef struct {
  uint32_t prev;
  clause_ref_t c_ref;
  variable_t unit_variable;
} clause_tracker_list_element_t;

struct clause_tracker_s {
  /** The plugin context, including the trail. */
  const plugin_context_t *ctx;

  /** The unit info. */
  const constraint_unit_info_t *unit_info;

  /** Query function to check if a constraint is known by the plugin. */
  clause_tracker_query_t query;

  /** Pointer to be passed to query. */
  void* query_data;

  /** All clauses that are known to the tracker */
  int_hset_t clauses;

  /** For each detected clause, a map constraint -> list of clause_ref_t, where constraint is watching. */
  ptr_hmap_t watch_list;

  /** Elements of the lists */
  clause_tracker_list_element_t* memory;

  /** The currently occupied memory size */
  uint32_t memory_size;

  /** The capacity of the memory */
  uint32_t memory_capacity;

  /** The last reported unit clause */
  uint32_t memory_pos;

  /** Map from constraints to the last unit clause */
  int_hmap_t var_to_list_element;

  /** Scope for push/pop */
  scope_holder_t scope;
};

#define INITIAL_LIST_SIZE 50

static inline
const mcsat_clause_info_interface_t* get_clause_info(const clause_tracker_t* ct) {
  return ct->ctx->plugin_info->clause_info;
}

static inline
const mcsat_clause_t* clause_tracker_get_clause(const clause_tracker_t *ct, clause_ref_t c_ref) {
  assert(c_ref != clause_ref_null);
  const mcsat_clause_info_interface_t *clause_info = get_clause_info(ct);
  return clause_info->get_clause(clause_info, c_ref);
}

static inline
void clause_tracker_get_clauses(const clause_tracker_t *ct, variable_t v, ivector_t *clauses) {
  const mcsat_clause_info_interface_t *clause_info = get_clause_info(ct);
  clause_info->get_clauses_by_var(clause_info, v, clauses);
}

static inline
bool clause_tracker_query(const clause_tracker_t *ct, variable_t constraint) {
  assert(ct->query);
  return ct->query(ct->query_data, constraint);
}

// watch list handling

static
void clause_tracker_watchers_delete(clause_tracker_t *ct) {
  for (ptr_hmap_pair_t *p = ptr_hmap_first_record(&ct->watch_list);
       p != NULL;
       p = ptr_hmap_next_record(&ct->watch_list, p)) {
    delete_ivector(p->val);
    safe_free(&p->val);
  }
  ptr_hmap_reset(&ct->watch_list);
}

/** Adds c_ref to the watch list of constraint watcher. Returns true if it was added. */
static
void clause_tracker_watcher_add(clause_tracker_t *ct, variable_t watcher, clause_ref_t c_ref) {
  ptr_hmap_pair_t *p = ptr_hmap_get(&ct->watch_list, watcher);
  assert(p);
  if (p->val == NULL) {
    p->val = safe_malloc(sizeof(int_hset_t));
    init_ivector(p->val, 4);
  }
  assert(!ivector_contains(p->val, c_ref));
  ivector_push(p->val, c_ref);
}

/** Gets the watch list of a clause */
static inline
const ivector_t* clause_tracker_watcher_get(clause_tracker_t *ct, variable_t watcher) {
  ptr_hmap_pair_t *p = ptr_hmap_find(&ct->watch_list, watcher);
  if (p == NULL) return NULL;
  return p->val;
}

/** Stores the watch list of a clause in watch_list and removes the list. */
static
void clause_tracker_watcher_pop(clause_tracker_t *ct, variable_t watcher, ivector_t *watch_list) {
  ptr_hmap_pair_t *p = ptr_hmap_find(&ct->watch_list, watcher);
  if (p == NULL) return;
  assert(p->val);
  ivector_swap(p->val, watch_list);
  delete_ivector(p->val);
  safe_free(p->val);
  ptr_hmap_erase(&ct->watch_list, p);
}

// list handling

/** gets the index of the clause information for variable x */
static inline
uint32_t clause_tracker_list_get_index(const clause_tracker_t *ct, variable_t x) {
  int_hmap_pair_t *find = int_hmap_find(&ct->var_to_list_element, x);
  return (find == NULL) ? 0 : find->val;
}

/** Gets the new of the clause information for variable x and then updates it. */
static inline
uint32_t clause_tracker_list_update(clause_tracker_t *ct, variable_t x, uint32_t new) {
  int_hmap_pair_t *p = int_hmap_get(&ct->var_to_list_element, x);
  uint32_t old = p->val < 0 ? 0 : p->val;
  p->val = new;
  return old;
}

static
void clause_tracker_list_ensure_memory(clause_tracker_t *ct) {
  if (ct->memory_size >= ct->memory_capacity) {
    ct->memory_capacity = ct->memory_capacity + ct->memory_capacity / 2;
    ct->memory = safe_realloc(ct->memory, ct->memory_capacity * sizeof(clause_tracker_list_element_t));
  }
  assert(ct->memory_size < ct->memory_capacity);
}

static
void clause_tracker_list_push(clause_tracker_t *ct, clause_ref_t c_ref, variable_t x) {
  uint32_t index = ct->memory_size++;
  clause_tracker_list_ensure_memory(ct);
  clause_tracker_list_element_t *new = ct->memory + index;
  new->c_ref = c_ref;
  if (x != variable_null) {
    new->unit_variable = x;
    new->prev = clause_tracker_list_update(ct, x, index);
  } else {
    new->unit_variable = variable_null;
    new->prev = 0;
  }
}

// external functions

clause_tracker_t* clause_tracker_construct(const plugin_context_t *ctx, const constraint_unit_info_t *unit_info,
                                           clause_tracker_query_t query, void *query_data) {
  clause_tracker_t *ct = safe_malloc(sizeof(clause_tracker_t));

  // set config
  ct->ctx = ctx;
  ct->unit_info = unit_info;
  ct->query = query;
  ct->query_data = query_data;

  // allocate the rest
  init_ptr_hmap(&ct->watch_list, 0);
  init_int_hmap(&ct->var_to_list_element, 0);
  init_int_hset(&ct->clauses, 0);
  scope_holder_construct(&ct->scope);

  // init memory
  ct->memory_capacity = INITIAL_LIST_SIZE;
  ct->memory = safe_malloc(sizeof(clause_tracker_list_element_t) * INITIAL_LIST_SIZE);
  ct->memory_size = 1; // 0 is special null ref
  ct->memory_pos = 1;
  ct->memory[0].c_ref = clause_ref_null;

  return ct;
}

void clause_tracker_delete(clause_tracker_t *ct) {
  clause_tracker_watchers_delete(ct);
  delete_ptr_hmap(&ct->watch_list);
  delete_int_hmap(&ct->var_to_list_element);
  delete_int_hset(&ct->clauses);
  scope_holder_destruct(&ct->scope);

  safe_free(ct->memory);
  safe_free(ct);
}

void clause_tracker_reset(clause_tracker_t *ct) {
  scope_holder_reset(&ct->scope);
  int_hmap_reset(&ct->var_to_list_element);
  int_hset_reset(&ct->clauses);
  clause_tracker_watchers_delete(ct);
}

static inline
bool clause_tracker_is_unit(const clause_tracker_t *ct, variable_t constraint) {
  assert(variable_db_is_boolean(ct->ctx->var_db, constraint));
  bool is_unit = constraint_unit_info_get(ct->unit_info, constraint) == CONSTRAINT_UNIT;
  assert(!is_unit || clause_tracker_query(ct, constraint));
  assert(!is_unit || !trail_has_value(ct->ctx->trail, constraint));
  return is_unit;
}

static inline
bool clause_tracker_is_tracked(const clause_tracker_t *ct, variable_t constraint) {
  return clause_tracker_is_unit(ct, constraint) || trail_has_value(ct->ctx->trail, constraint);
}

/** Tries to find a new watch constraint for clause. Returns the new watcher, or variable_null if none was found. */
static
variable_t clause_watch_update(const clause_tracker_t *ct, clause_ref_t c_ref) {
  const mcsat_clause_t *c = clause_tracker_get_clause(ct, c_ref);
  variable_t new_watch = variable_null;
  for (uint32_t i = 0; i < c->size && c->literals[i]; ++i) {
    variable_t v = literal_get_variable(c->literals[i]);
    assert(v != variable_null);
    if (!clause_tracker_is_tracked(ct, v)) {
      new_watch = v;
      // if we found a theory constraint we're done
      // otherwise, continue to maybe later find one
      if (clause_tracker_query(ct, v)) {
        break;
      }
    }
  }
  return new_watch;
}

/** Return true if the clause is actually unit, i.e. not yet fulfilled. */
static
bool clause_tracker_found_unit(clause_tracker_t *ct, clause_ref_t c_ref) {
  const mcsat_clause_t *c = clause_tracker_get_clause(ct, c_ref);

#ifndef NDEBUG
  for (uint32_t i = 0; i < c->size && c->literals[i]; ++i) {
    assert(clause_tracker_is_tracked(ct, literal_get_variable(c->literals[i])));
  }
#endif

  // find the variable the clause is unit in
  variable_t unit_var = variable_null;

  for (uint32_t i = 0; i < c->size && c->literals[i]; ++i) {
    mcsat_literal_t l = c->literals[i];
    if (literal_is_true(l, ct->ctx->trail)) {
      unit_var = variable_null;
      break;
    }
    variable_t constraint = literal_get_variable(l);
    if (clause_tracker_is_unit(ct, constraint)) {
      variable_t x = constraint_unit_info_get_unit_var(ct->unit_info, constraint);
      assert(x != variable_null);
#ifndef NDEBUG
      if (unit_var == variable_null) { unit_var = x; }
      else { assert(unit_var == x); }
#else
      unit_var = x;
      break;
#endif
    }
  }

  // track the unit clause
  clause_tracker_list_push(ct, c_ref, unit_var);
  return unit_var != variable_null;
}

/** Updates all clauses watched by a constraint. */
static
uint32_t clause_tracker_update_constraint(clause_tracker_t *ct, variable_t constraint) {
  assert(clause_tracker_is_tracked(ct, constraint));
  uint32_t count = 0;

  // find all watch_list watched by the constraint
  ivector_t watch_list;
  init_ivector(&watch_list, 0);
  clause_tracker_watcher_pop(ct, constraint, &watch_list);

  for (uint32_t i = 0; i < watch_list.size; ++i) {
    clause_ref_t c_ref = watch_list.data[i];
    variable_t new_watcher = clause_watch_update(ct, c_ref);
    if (new_watcher == variable_null) {
      // we found a c-unit clause
      bool new_unit = clause_tracker_found_unit(ct, c_ref);
      if (new_unit) count++;
    } else {
      // we found another watcher
      assert(new_watcher != constraint);
      clause_tracker_watcher_add(ct, new_watcher, c_ref);
    }
  }

  delete_ivector(&watch_list);
  return count;
}

static
void clause_tracker_add_clauses_of_constraint(clause_tracker_t *ct, variable_t constraint) {
  // get all clauses where unit_constraint is bool-watching
  ivector_t clauses;
  init_ivector(&clauses, 0);
  clause_tracker_get_clauses(ct, constraint, &clauses);
  for (uint32_t i = 0; i < clauses.size; ++i) {
    clause_ref_t c_ref = clauses.data[i];
    // try to add it to the set of known clauses
    bool new = int_hset_add(&ct->clauses, c_ref);
    if (new) {
      variable_t watcher = clause_watch_update(ct, c_ref);
      assert(watcher != variable_null);
      clause_tracker_watcher_add(ct, watcher, c_ref);
    }
  }
  delete_ivector(&clauses);
}

uint32_t clause_tracker_track_unit_constraint(clause_tracker_t *ct, variable_t constraint) {
  assert(clause_tracker_is_unit(ct, constraint));
  clause_tracker_add_clauses_of_constraint(ct, constraint);
  return clause_tracker_update_constraint(ct, constraint);
}

uint32_t clause_tracker_track_decided_constraint(clause_tracker_t *ct, variable_t constraint) {
  assert(trail_has_value(ct->ctx->trail, constraint));
  return clause_tracker_update_constraint(ct, constraint);
}

uint32_t clause_tracker_count_unit_clauses(const clause_tracker_t *ct, variable_t x) {
  uint32_t cnt = 0, index = clause_tracker_list_get_index(ct, x);
  while (index) {
    cnt ++;
    index = ct->memory[index].prev;
  }
  return cnt;
}

void clause_tracker_get_var_unit_clause(const clause_tracker_t *ct, variable_t x, ivector_t *refs) {
  uint32_t index = clause_tracker_list_get_index(ct, x);
  while (index) {
    ivector_push(refs, index);
    index = ct->memory[index].prev;
  }
}

clause_tracker_ref_t clause_tracker_get_new_unit_clause(clause_tracker_t *ct) {
  assert(ct->memory_pos > 0);
  while (ct->memory_pos < ct->memory_size) {
    variable_t var = ct->memory[ct->memory_pos].unit_variable;
    ct->memory_pos ++;
    if (var != variable_null) {
      return ct->memory_pos - 1;
    }
  }
  return clause_tracker_ref_null;
}

variable_t clause_tracker_get_unit_variable(const clause_tracker_t *ct, clause_tracker_ref_t ref) {
  assert(ref > 0 && ref < ct->memory_size);
  assert(ct->memory[ref].unit_variable != variable_null);
  return ct->memory[ref].unit_variable;
}

void clause_tracker_get_constraints(const clause_tracker_t *ct, clause_tracker_ref_t ref, ivector_t *pos, ivector_t *neg) {
  assert(ref > 0 && ref < ct->memory_size);
  assert(ct->memory[ref].unit_variable != variable_null);

  const mcsat_clause_t *clause = clause_tracker_get_clause(ct, ct->memory[ref].c_ref);
  for (uint32_t i = 0; i < clause->size && clause->literals[i]; ++i) {
    mcsat_literal_t l = clause->literals[i];
    variable_t v = literal_get_variable(l);
    bool negated = literal_is_negated(l);
    assert(clause_tracker_is_tracked(ct, v));
    if (clause_tracker_is_unit(ct, v)) {
      assert(clause_tracker_query(ct, v));
      ivector_push(negated ? neg : pos, v);
    } else {
      assert(trail_has_value(ct->ctx->trail, v));
    }
  }
}

void clause_tracker_get_side_conditions(const clause_tracker_t *ct, clause_tracker_ref_t ref, ivector_t *pos, ivector_t *neg) {
  assert(ref > 0 && ref < ct->memory_size);
  assert(ct->memory[ref].unit_variable != variable_null);

  const mcsat_clause_t *clause = clause_tracker_get_clause(ct, ct->memory[ref].c_ref);
  for (uint32_t i = 0; i < clause->size && clause->literals[i]; ++i) {
    mcsat_literal_t l = clause->literals[i];
    variable_t v = literal_get_variable(l);
    bool negated = literal_is_negated(l);
    assert(clause_tracker_is_tracked(ct, v));
    if (!clause_tracker_is_unit(ct, v)) {
      assert(trail_has_value(ct->ctx->trail, v));
      ivector_push(negated ? neg : pos, v);
    } else {
      assert(clause_tracker_query(ct, v));
    }
  }
}

void clause_tracker_push(clause_tracker_t *ct) {
  scope_holder_push(&ct->scope,
                    &ct->memory_size,
                    &ct->memory_pos,
                    NULL);
}

void clause_tracker_pop(clause_tracker_t *ct) {
  uint32_t i = ct->memory_size;
  scope_holder_pop(&ct->scope,
                   &ct->memory_size,
                   &ct->memory_pos,
                   NULL);

  // Undo updates and find watchers
  assert(i >= ct->memory_size);
  while (--i >= ct->memory_size) {
    clause_tracker_list_element_t *e = ct->memory + i;
    // update watch
    variable_t new_watch = clause_watch_update(ct, e->c_ref);
    assert(new_watch != variable_null);
    clause_tracker_watcher_add(ct, new_watch, e->c_ref);
    // update unit variable handling
    if (e->unit_variable != variable_null) {
      uint32_t old = clause_tracker_list_update(ct, e->unit_variable, e->prev);
      (void)old;
      assert(old == i);
    }
  }
}
