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

#include "mcsat/ff/ff_plugin_internal.h"
#include <poly/polynomial.h>

#include "mcsat/tracing.h"

void ff_plugin_get_constraint_variables(ff_plugin_t* ff, term_t constraint, int_mset_t* vars_out) {

  term_table_t* terms = ff->ctx->terms;

  term_t atom = unsigned_term(constraint);
  term_kind_t atom_kind = term_kind(ff->ctx->terms, atom);

  switch (atom_kind) {
  case ARITH_FF_EQ_ATOM:
    ff_plugin_get_term_variables(ff, arith_ff_eq_arg(terms, atom), vars_out);
    break;
  case EQ_TERM:
  case ARITH_FF_BINEQ_ATOM:
    ff_plugin_get_term_variables(ff, composite_term_arg(terms, atom, 0), vars_out);
    ff_plugin_get_term_variables(ff, composite_term_arg(terms, atom, 1), vars_out);
    break;
  default:
    // We're fine, just a variable, arithmetic term to eval, or a foreign term
    ff_plugin_get_term_variables(ff, constraint, vars_out);
    int_mset_add(vars_out, variable_db_get_variable(ff->ctx->var_db, constraint));
    break;
  }
}

void ff_plugin_get_term_variables(ff_plugin_t* ff, term_t t, int_mset_t* vars_out) {

  // The term table
  term_table_t* terms = ff->ctx->terms;

  // Variable database
  variable_db_t* var_db = ff->ctx->var_db;


  if (ctx_trace_enabled(ff->ctx, "mcsat::new_term")) {
    ctx_trace_printf(ff->ctx, "ff_plugin_get_variables: ");
    ctx_trace_term(ff->ctx, t);
  }

  term_kind_t kind = term_kind(terms, t);
  switch (kind) {
  case ARITH_FF_CONSTANT:
    break;
  case ARITH_FF_POLY: {
    // The polynomial
    polynomial_t* polynomial = finitefield_poly_term_desc(terms, t);
    // Go through the polynomial and get the variables
    uint32_t i, j, deg;
    variable_t var;
    for (i = 0; i < polynomial->nterms; ++i) {
      term_t product = polynomial->mono[i].var;
      if (product == const_idx) {
        // Just the constant
        continue;
      } else if (term_kind(terms, product) == POWER_PRODUCT) {
        pprod_t* pprod = pprod_for_term(terms, product);
        for (j = 0; j < pprod->len; ++j) {
          var = variable_db_get_variable(var_db, pprod->prod[j].var);
          for (deg = 0; deg < pprod->prod[j].exp; ++ deg) {
            int_mset_add(vars_out, var);
          }
        }
      } else {
        // Variable, or foreign term
        var = variable_db_get_variable(var_db, product);
        int_mset_add(vars_out, var);
      }
    }
    break;
  }
  case POWER_PRODUCT: {
    pprod_t* pprod = pprod_term_desc(terms, t);
    uint32_t i, deg;
    for (i = 0; i < pprod->len; ++ i) {
      variable_t var = variable_db_get_variable(var_db, pprod->prod[i].var);
      for (deg = 0; deg < pprod->prod[i].exp; ++ deg) {
        int_mset_add(vars_out, var);
      }
    }
    break;
  }
  default:
    // A variable or a foreign term
    int_mset_add(vars_out, variable_db_get_variable(var_db, t));
  }
}

static
ff_plugin_field_t* ff_plugin_field_data_new(ff_plugin_t *ff, type_t tau) {
  mpz_t order;
  mpz_init(order);
  const rational_t *order_q = ff_type_size(ff->ctx->types, tau);
  q_get_mpz(order_q, order);

  ff_plugin_field_t *new = safe_malloc(sizeof(ff_plugin_field_t));
  new->lp_data = lp_data_new(order, ff->ctx);
  new->feasible_set_db = ff_feasible_set_db_new(ff);

  mpz_clear(order);
  return new;
}

static
void ff_plugin_field_data_delete(ff_plugin_field_t *fff) {
  assert(fff);
  assert(fff->lp_data);
  assert(fff->feasible_set_db);
  lp_data_delete(fff->lp_data);
  ff_feasible_set_db_delete(fff->feasible_set_db);
}

static
void ff_plugin_field_data_push(ff_plugin_field_t *ff_f) {
  assert(ff_f);
  assert(ff_f->lp_data);
  assert(ff_f->feasible_set_db);

  lp_data_variable_order_push(ff_f->lp_data);
  ff_feasible_set_db_push(ff_f->feasible_set_db);
}

static
void ff_plugin_field_data_pop(ff_plugin_field_t *ff_f) {
  assert(ff_f);
  assert(ff_f->lp_data);
  assert(ff_f->feasible_set_db);

  ff_feasible_set_db_pop(ff_f->feasible_set_db);
  lp_data_variable_order_pop(ff_f->lp_data);
}

static
void ff_plugin_field_data_gc_mark(ff_plugin_field_t *ff_f, gc_info_t* gc_vars) {
  assert(ff_f);
  assert(ff_f->feasible_set_db);

  ff_feasible_set_db_gc_mark(ff_f->feasible_set_db, gc_vars);
}

static
void ff_plugin_field_data_gc_sweep(ff_plugin_field_t *fff, const gc_info_t* gc_vars) {
  assert(fff);
  assert(fff->lp_data);
  assert(fff->feasible_set_db);

  lp_data_gc_sweep(fff->lp_data, gc_vars);
}

ff_plugin_field_t* ff_plugin_create_or_get_lp_data_by_type(ff_plugin_t *ff, type_t tau) {
  assert(is_ff_type(ff->ctx->types, tau));

  ptr_hmap_pair_t *found = ptr_hmap_get(&ff->lp_datas, tau);

  if (found->val == NULL) {
    found->val = ff_plugin_field_data_new(ff, tau);
    // otherwise push/pop are imbalanced
    assert(trail_is_at_base_level(ff->ctx->trail));
    // TODO push n times if trail is at level n
  }

  return found->val;
}

ff_plugin_field_t* ff_plugin_create_or_get_lp_data_by_term(ff_plugin_t *ff, term_t t) {
  type_t tau = term_type(ff->ctx->terms, t);
  return ff_plugin_create_or_get_lp_data_by_type(ff, tau);
}

ff_plugin_field_t* ff_plugin_get_lp_data_by_type(ff_plugin_t *ff, type_t tau) {
  assert(is_ff_type(ff->ctx->types, tau));
  ptr_hmap_pair_t *found = ptr_hmap_find(&ff->lp_datas, tau);
  assert(found);
  return found->val;
}

ff_plugin_field_t* ff_plugin_get_lp_data_by_var(ff_plugin_t *ff, variable_t x) {
  type_t tau = variable_db_get_type(ff->ctx->var_db, x);
  return ff_plugin_get_lp_data_by_type(ff, tau);
}

ff_plugin_field_t* ff_plugin_get_lp_data_by_term(ff_plugin_t *ff, term_t t) {
  type_t tau = term_type(ff->ctx->terms, t);
  return ff_plugin_get_lp_data_by_type(ff, tau);
}

ff_plugin_field_t* ff_plugin_get_lp_data_by_lp_polynomial(ff_plugin_t *ff, const lp_polynomial_t *p) {
  const lp_int_ring_t *ring = lp_polynomial_get_context(p)->K;
  assert(ring != lp_Z);
  type_t tau = ff_type(ff->ctx->types, &ring->M);
  return ff_plugin_get_lp_data_by_type(ff, tau);
}

void ff_plugin_lp_data_init(ff_plugin_t *ff) {
  init_ptr_hmap(&ff->lp_datas, 0);
}

void ff_plugin_lp_data_pop(ff_plugin_t *ff) {
  for (ptr_hmap_pair_t *p = ptr_hmap_first_record(&ff->lp_datas);
       p != NULL;
       p = ptr_hmap_next_record(&ff->lp_datas, p)) {
    ff_plugin_field_data_pop(p->val);
  }
}

void ff_plugin_lp_data_push(ff_plugin_t *ff) {
  for (ptr_hmap_pair_t *p = ptr_hmap_first_record(&ff->lp_datas);
       p != NULL;
       p = ptr_hmap_next_record(&ff->lp_datas, p)) {
    ff_plugin_field_data_push(p->val);
  }
}

void ff_plugin_lp_data_gc_mark(ff_plugin_t *ff, gc_info_t* gc_vars) {
  for (ptr_hmap_pair_t *p = ptr_hmap_first_record(&ff->lp_datas);
       p != NULL;
       p = ptr_hmap_next_record(&ff->lp_datas, p)) {
    ff_plugin_field_data_gc_mark(p->val, gc_vars);
  }
}

void ff_plugin_lp_data_gc_sweep(ff_plugin_t *ff, const gc_info_t* gc_vars) {
  for (ptr_hmap_pair_t *p = ptr_hmap_first_record(&ff->lp_datas);
       p != NULL;
       p = ptr_hmap_next_record(&ff->lp_datas, p)) {
    ff_plugin_field_data_gc_sweep(p->val, gc_vars);
  }
}
void ff_plugin_lp_data_delete(ff_plugin_t *ff) {
  for (ptr_hmap_pair_t *p = ptr_hmap_first_record(&ff->lp_datas);
  p != NULL;
  p = ptr_hmap_next_record(&ff->lp_datas, p)) {
    ff_plugin_field_data_delete(p->val);
    safe_free(p->val);
  }
  delete_ptr_hmap(&ff->lp_datas);
}
