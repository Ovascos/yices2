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

#ifndef FF_PLUGIN_INTERNAL_H
#define FF_PLUGIN_INTERNAL_H

#include <poly/poly.h>

#include "mcsat/ff/ff_plugin_internal.h"
#include "mcsat/ff/ff_feasible_set_db.h"

#include "mcsat/plugin.h"
#include "mcsat/unit_info.h"
#include "mcsat/watch_list_manager.h"
#include "mcsat/utils/scope_holder.h"
#include "mcsat/utils/lp_data.h"
#include "mcsat/utils/lp_utils.h"
#include "mcsat/utils/lp_constraint_db.h"
#include "mcsat/utils/int_mset.h"

#include "terms/term_manager.h"
#include "utils/ptr_hash_map.h"

typedef struct ff_plugin_s ff_plugin_t;
typedef struct ff_plugin_field_s ff_plugin_field_t;

struct ff_plugin_s {

  /** The plugin interface */
  plugin_t plugin_interface;

  /** The plugin context */
  plugin_context_t* ctx;

  /** The watch list manager */
  watch_list_manager_t wlm;

  /** The unit info */
  constraint_unit_info_t unit_info;

  /** The data for each finite field type */
  ptr_hmap_t lp_datas;

  /** Last variable that was decided, but yet unprocessed */
  variable_t last_decided_and_unprocessed;

  /** Next index of the trail to process */
  uint32_t trail_i;

  /** The conflict variable (one with empty feasible set) */
  variable_t conflict_variable;

#if 0
  /** The conflict variable (assumption not in feasible set) */
  variable_t conflict_variable_assumption;

  /** The value that got the assumptions variable in trouble */
  lp_value_t conflict_variable_value;

  /** Bound variable term */
  term_t global_bound_term;

#endif

  /** Variables processed in propagation */
  ivector_t processed_variables;

  /** Size of processed (for backtracking) */
  uint32_t processed_variables_size;

  /** Scope holder for the int variables */
  scope_holder_t scope;

  struct {
    statistic_int_t* propagations;
    statistic_int_t* conflicts;
    statistic_int_t* conflicts_assumption;
    statistic_int_t* constraints_attached;
    statistic_int_t* evaluations;
    statistic_int_t* constraint;
    statistic_int_t* variable_hints;
  } stats;

#if 0
  /** Buffer for evaluation */
  int_hmap_t evaluation_value_cache;
  int_hmap_t evaluation_timestamp_cache;

  /** Buffer for feasible set computation (for true/false */
  int_hmap_t feasible_set_cache_top_var[2];   // Top var when cached
  int_hmap_t feasible_set_cache_timestamp[2]; // Top timestamp of other variables when cached
  ptr_hmap_t feasible_set_cache[2];           // The cache
#endif

  /** Arithmetic buffer for computation */
  rba_buffer_t buffer;

  /** Exception handler */
  jmp_buf* exception;

};

// TODO either put WLM here or move constraint_db up?
struct ff_plugin_field_s {
  /** Data related to libpoly */
  lp_data_t *lp_data;

  /** Database of polynomial constraints */
  poly_constraint_db_t *constraint_db;

  /** Map from variables to their feasible sets */
  ff_feasible_set_db_t *feasible_set_db;
};

void ff_plugin_get_constraint_variables(ff_plugin_t* ff, term_t constraint, int_mset_t* vars_out);

void ff_plugin_get_term_variables(ff_plugin_t* ff, term_t t, int_mset_t* vars_out);

void ff_plugin_lp_data_init(ff_plugin_t *ff);

void ff_plugin_lp_data_delete(ff_plugin_t *ff);

void ff_plugin_lp_data_push(ff_plugin_t *ff);

void ff_plugin_lp_data_pop(ff_plugin_t *ff);

void ff_plugin_lp_data_gc_mark(ff_plugin_t *ff, gc_info_t* gc_vars);

void ff_plugin_lp_data_gc_sweep(ff_plugin_t *ff, const gc_info_t* gc_vars);

ff_plugin_field_t* ff_plugin_get_lp_data_by_term(ff_plugin_t *ff, term_t t);

ff_plugin_field_t* ff_plugin_get_lp_data_by_type(ff_plugin_t *ff, type_t tau);

ff_plugin_field_t* ff_plugin_get_lp_data_by_var(ff_plugin_t *ff, variable_t x);

#endif /* FF_PLUGIN_INTERNAL_H */
