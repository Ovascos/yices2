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

#ifndef MCSAT_LP_MANAGER_H
#define MCSAT_LP_MANAGER_H

#include <stdbool.h>
#include <poly/poly.h>

#include "mcsat/mcsat_types.h"
#include "mcsat/variable_db.h"
#include "mcsat/utils/scope_holder.h"

#include "utils/int_hash_map.h"

/**
 * To be used by plugins that utilize libPoly.
 * TODO remove interval_assignment from here and add to nra_plugin_t
 */
typedef struct lp_data_s {
  /** Libpoly variable database */
  lp_variable_db_t* lp_var_db;
  /** Libpoly Variable order */
  lp_variable_order_t* lp_var_order;
  /** Size of the variable order (for backtracking) */
  uint32_t lp_var_order_size;
  /** Push/Pop scope for lp_var_order_size */
  scope_holder_t scope;
  /** Libpoly polynomial context */
  lp_polynomial_context_t* lp_ctx;
  /** Libpoly model */
  lp_assignment_t* lp_assignment;
  /** Interval assignment for bound inference */
  lp_interval_assignment_t* lp_interval_assignment;

  /** Map from libpoly variables to mcsat variables */
  int_hmap_t lp_to_mcsat_var_map;
  /** Map from mcsat variables to libpoly variables */
  int_hmap_t mcsat_to_lp_var_map;
} lp_data_t;


void lp_data_init(lp_data_t *lp_data);

void lp_data_destruct(lp_data_t *lp_data);

/** Add a variable corresponding to the mcsat variable or term
 * Important: use either one or the other for each instance of lp_data, otherwise collisions might occur */
 // TODO maybe make this for term_id only
lp_variable_t lp_data_add_lp_variable(lp_data_t *lp_data, plugin_context_t *ctx, variable_t mcsat_var);
lp_variable_t lp_data_add_lp_variable_term(lp_data_t *lp_data, term_t t, term_table_t *terms);

void lp_data_variable_order_push(lp_data_t *lp_data);

void lp_data_variable_order_pop(lp_data_t *lp_data);

void lp_data_add_to_model_and_context(lp_data_t *lp_data, lp_variable_t lp_var, const lp_value_t *lp_value);

void lp_data_variable_order_print(lp_data_t *lp_data, FILE *file);

void lp_data_gc_sweep(lp_data_t *lp_data, const gc_info_t *gc_vars);

/** Creates a new lp_variable with a given name. */
lp_variable_t lp_data_new_variable(lp_data_t *lp_data, const char* var_name);

/** Crates a new lp_polynomial with the current context */
lp_polynomial_t* lp_data_new_polynomial(lp_data_t *lp_data);

/** Check if the mcsat variable has an lp variable */
static inline bool lp_data_variable_has_lp_variable(lp_data_t* lp_data, variable_t mcsat_var) {
  return int_hmap_find(&lp_data->mcsat_to_lp_var_map, mcsat_var) != NULL;
}

/** Get the libpoly variable corresponding to term t (should have been added first) */
static inline lp_variable_t lp_data_get_lp_variable(lp_data_t *lp_data, variable_t mcsat_var) {
  int_hmap_pair_t* find = int_hmap_find(&lp_data->mcsat_to_lp_var_map, mcsat_var);
  assert(find != NULL);
  return find->val;
}

/** Get the mcsat variable from the libpoly variable */
static inline variable_t lp_data_get_variable_from_lp_variable(lp_data_t *lp_data, lp_variable_t lp_var) {
  int_hmap_pair_t* find = int_hmap_find(&lp_data->lp_to_mcsat_var_map, lp_var);
  assert(find != NULL);
  return find->val;
}

#endif /* MCSAT_LP_MANAGER_H */
