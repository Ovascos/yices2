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

#include "lp_data.h"

#include <poly/polynomial.h>
#include <poly/polynomial_context.h>
#include <poly/variable_db.h>
#include <poly/feasibility_set.h>
#include <poly/variable_order.h>
#include <poly/variable_list.h>

#include "mcsat/mcsat_types.h"
#include "mcsat/plugin.h"
#include "mcsat/tracing.h"
#include "mcsat/gc.h"
#include "terms/terms.h"

void lp_data_init(lp_data_t *lp_data) {
  init_int_hmap(&lp_data->mcsat_to_lp_var_map, 0);
  init_int_hmap(&lp_data->lp_to_mcsat_var_map, 0);

  lp_data->lp_var_db = lp_variable_db_new();
  lp_data->lp_var_order = lp_variable_order_new();
  lp_data->lp_var_order_size = 0;
  lp_data->lp_ctx = lp_polynomial_context_new(lp_Z, lp_data->lp_var_db, lp_data->lp_var_order);
  lp_data->lp_assignment = lp_assignment_new(lp_data->lp_var_db);
  lp_data->lp_interval_assignment = lp_interval_assignment_new(lp_data->lp_var_db);

  scope_holder_construct(&lp_data->scope);

  // Tracing in libpoly
  if (false) {
    lp_trace_enable("coefficient");
    lp_trace_enable("coefficient::sgn");
    lp_trace_enable("coefficient::interval");
    lp_trace_enable("polynomial::expensive");
  }
}

void lp_data_destruct(lp_data_t *lp_data) {
  delete_int_hmap(&lp_data->mcsat_to_lp_var_map);
  delete_int_hmap(&lp_data->lp_to_mcsat_var_map);

  lp_polynomial_context_detach(lp_data->lp_ctx);
  lp_variable_order_detach(lp_data->lp_var_order);
  lp_variable_db_detach(lp_data->lp_var_db);
  lp_assignment_delete(lp_data->lp_assignment);
  lp_interval_assignment_delete(lp_data->lp_interval_assignment);

  scope_holder_destruct(&lp_data->scope);
}

void lp_data_add_lp_variable(lp_data_t *lp_data, plugin_context_t *ctx, variable_t mcsat_var) {
  term_t t = variable_db_get_term(ctx->var_db, mcsat_var);

  // Name of the term
  char buffer[100];
  char* var_name = term_name(ctx->terms, t);
  if (var_name == NULL) {
    var_name = buffer;
    sprintf(var_name, "#%d", t);
    if (ctx_trace_enabled(ctx, "nra::vars")) {
      ctx_trace_printf(ctx, "%s -> ", var_name);
      variable_db_print_variable(ctx->var_db, mcsat_var, ctx_trace_out(ctx));
      ctx_trace_printf(ctx, "\n");
    }
  }

  // Make the variable
  lp_variable_t lp_var = lp_variable_db_new_variable(lp_data->lp_var_db, var_name);

  assert(int_hmap_find(&lp_data->lp_to_mcsat_var_map, lp_var) == NULL);
  assert(int_hmap_find(&lp_data->mcsat_to_lp_var_map, mcsat_var) == NULL);

  int_hmap_add(&lp_data->lp_to_mcsat_var_map, lp_var, mcsat_var);
  int_hmap_add(&lp_data->mcsat_to_lp_var_map, mcsat_var, lp_var);
}

void lp_data_variable_order_push(lp_data_t *lp_data) {
  scope_holder_push(&lp_data->scope,
                    &lp_data->lp_var_order_size,
                    NULL);
}

void lp_data_variable_order_pop(lp_data_t *lp_data) {
  scope_holder_pop(&lp_data->scope,
                   &lp_data->lp_var_order_size,
                   NULL);

  lp_variable_order_t* order = lp_data->lp_var_order;
  lp_assignment_t* assignment = lp_data->lp_assignment;
  while (lp_variable_order_size(order) > lp_data->lp_var_order_size) {
    lp_variable_t lp_var = lp_variable_order_top(order);
    lp_variable_order_pop(order);
    lp_assignment_set_value(assignment, lp_var, 0);
  }
}

void lp_data_add_to_model_and_context(lp_data_t *lp_data, lp_variable_t lp_var, const lp_value_t *lp_value) {
  lp_assignment_set_value(lp_data->lp_assignment, lp_var, lp_value);
  lp_variable_order_push(lp_data->lp_var_order, lp_var);
  lp_data->lp_var_order_size ++;
}

void lp_data_variable_order_print(lp_data_t *lp_data, FILE *file) {
  lp_variable_order_print(lp_data->lp_var_order, lp_data->lp_var_db, file);
}

void lp_data_gc_sweep(lp_data_t *lp_data, const gc_info_t *gc_vars) {
  // - lpdata.lp_to_mcsat_var_map (values)
  // - lpdata.mcsat_to_lp_var_map (keys)
  gc_info_sweep_int_hmap_values(gc_vars, &lp_data->lp_to_mcsat_var_map);
  gc_info_sweep_int_hmap_keys(gc_vars, &lp_data->mcsat_to_lp_var_map);
}
