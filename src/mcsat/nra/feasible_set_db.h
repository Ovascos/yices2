/*
 * This file is part of the Yices SMT Solver.
 * Copyright (C) 2017 SRI International.
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
 
#pragma once

#include <poly/poly.h>
#include <stdio.h>

#include "mcsat/variable_db.h"
#include "mcsat/mcsat_types.h"
#include "mcsat/value.h"

typedef struct nra_plugin_s nra_plugin_t;

/** Contains the map from variables to feasible sets that can be backtracked */
typedef struct feasible_set_db_s feasible_set_db_t;

/** Create a new database */
feasible_set_db_t* feasible_set_db_new(nra_plugin_t * ctx);

/** Delete the database */
void feasible_set_db_delete(feasible_set_db_t* db);

/**
 * Update the feasible set of the variable with a new set. The new set is kept
 * if it reduces the existing feasible set. Returns true if consistent.
 *
 * If more than one reason, it's considered a disjunctive top-level assertion (clause);
 */
bool
feasible_set_db_update(feasible_set_db_t *db, variable_t x, lp_feasibility_set_t *new_set, const variable_t *reasons,
                       uint32_t reasons_count, int32_t aux_id);

/** Checks if constraint cstr is (part of) a reason for variable x */
bool feasible_set_db_contains_reason(feasible_set_db_t* db, variable_t x, variable_t cstr);

/** Get the feasible set of a variable */
lp_feasibility_set_t* feasible_set_db_get(feasible_set_db_t* db, variable_t x);

/** Push the context */
void feasible_set_db_push(feasible_set_db_t* db);

/** Pop the context */
void feasible_set_db_pop(feasible_set_db_t* db);

/**
 * Get the reason for a conflict on x. Feasible set of x should be empty. If aux_ids_out is
 * not NULL, it is filled with all aux_ids of the updates in the minimized conflict.
 */
void
feasible_set_db_get_conflict_reasons(const feasible_set_db_t *db, variable_t x, const mcsat_value_t *x_value,
                                     ivector_t *reasons_out, ivector_t *lemma_reasons_out, ivector_t *aux_ids_out);

/** Print the feasible set database */
void feasible_set_db_print(feasible_set_db_t* db, FILE* out);

/** Print the feasible sets of given variable */
void feasible_set_db_print_var(feasible_set_db_t* db, variable_t var, FILE* out);

/** Returns an unassigned variable with a value in its feasible set, or variable_null otherwise */
variable_t feasible_set_db_get_cheap_unassigned(feasible_set_db_t* db, lp_value_t* value);

/** Marks all the top level reasons */
void feasible_set_db_gc_mark(feasible_set_db_t* db, gc_info_t* gc_vars);

/** Get an interval approximation of the value */
void feasible_set_db_approximate_value(feasible_set_db_t* db, variable_t constraint_var, lp_interval_t* result);


/**
 * The iterator for the feasible set db.
 * An iterator instance must not be used after a database modification.
 */
typedef struct {

  /** The feasible set, the iterator is iterating on */
  const feasible_set_db_t* db;

  /** The index to the element, 0 when done */
  uint32_t pos;

} feasible_set_db_iterator_t;

/** Constructs an iterator for the feasible set db */
void feasible_set_db_iterator_construct(feasible_set_db_iterator_t *it, const feasible_set_db_t *db, variable_t x);

/** Destructs the iterator */
void feasible_set_db_iterator_destruct(feasible_set_db_iterator_t *it);

/** Checks if the iterator is finished */
bool feasible_set_db_iterator_done(const feasible_set_db_iterator_t *it);

/** Proceeds to the next element */
void feasible_set_db_iterator_next(feasible_set_db_iterator_t *it);

/** Gets the current feasible set */
const lp_feasibility_set_t* feasible_set_db_iterator_get_set(const feasible_set_db_iterator_t *it);

/** Gets the current reason feasible set */
const lp_feasibility_set_t* feasible_set_db_iterator_get_reason_set(const feasible_set_db_iterator_t *it);

/** Gets the number of reasons of the current element */
uint32_t feasible_set_db_iterator_get_reason_size(const feasible_set_db_iterator_t *it);

/** Gets the current reason. Must be a single reason. */
variable_t feasible_set_db_iterator_get_reason(const feasible_set_db_iterator_t *it);

/** Adds all reasons of the current element to reasons */
void feasible_set_db_iterator_get_reasons(const feasible_set_db_iterator_t *it, ivector_t *reasons);
