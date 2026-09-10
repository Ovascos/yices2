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
 
#ifndef CNF_H_
#define CNF_H_

#include <stdbool.h>

#include "mcsat/plugin.h"
#include "mcsat/variable.h"
#include "mcsat/bool/clause_db.h"
#include "mcsat/utils/int_lset.h"
#include "mcsat/utils/int_mset.h"

typedef struct clause_adder_interface_s clause_adder_interface_t;

/**
 * Object that takes the clauses produced by the CNF conversion.
 */
struct clause_adder_interface_s {

  /**
   * Add the clause given by the literals and return its reference. The adder
   * may decline the clause, in which case it returns clause_ref_null and the
   * clause is not recorded as part of a variable definition.
   */
  clause_ref_t (*clause_add) (clause_adder_interface_t* self, const mcsat_literal_t* lits, uint32_t lits_size, mcsat_clause_tag_t tag);
};

/**
 * The CNF manager keeps the definitional CNF transformation. It converts
 * the given Boolean term recursively by creating a variable for the (positive)
 * sub-term and defining it by clausifying var_t <=> t.
 */
typedef struct {

  /** Where the produced clauses go */
  clause_adder_interface_t* clause_adder;

  /** The mcsat context */
  plugin_context_t* ctx;

  /** Map from converted variables to the list of their clauses */
  int_lset_t converted;

  /** Current variable being converted */
  variable_t variable;

  /**
   * Per-instance progress index for cnf_gc_mark across iterations of one
   * mcsat_gc cycle. Reset to 0 when the cycle starts (gc_vars->level == 0)
   * and otherwise advances across the for-each-plugin marking rounds.
   *
   * Was previously a function-local `static uint32_t` in cnf_gc_mark, which
   * meant the index was shared across all live cnf_t instances. With one
   * cnf_t per bool_plugin per context, that made the marking indices race
   * across contexts under thread-safe builds and could in principle skip
   * variables when two contexts' GC cycles interleaved (issue #616).
   */
  uint32_t gc_mark_index;

} cnf_t;


/** Construct the CNF manager */
void cnf_construct(cnf_t* cnf, plugin_context_t* ctx, clause_adder_interface_t* clause_adder);

/** Destruct the CNF manager */
void cnf_destruct(cnf_t* cnf);

/**
 * Add clauses for the given term through the clause adder. Clauses are added
 * as definitions for the internal (positive) nodes, and all the necessary
 * variables are added to the variable database.
 */
mcsat_literal_t cnf_convert(cnf_t* cnf, term_t t);

/**
 * Add the clause for the given lemma through the clause adder.
 */
void cnf_convert_lemma(cnf_t* cnf, const ivector_t* lemma);

/**
 * Gets all converted clauses of a given variable if the variable was converted.
 * If the variable was converted, clauses contains all clause_refs and true is returned.
 */
bool cnf_get_clauses(cnf_t* cnf, variable_t var, ivector_t* clauses);

/**
 * Mark all the clauses that are definitions for the variables in gc_vars.
 */
void cnf_gc_mark(cnf_t* cnf, gc_info_t* gc_clauses, const gc_info_t* gc_vars);

/**
 * Collect all the clauses that are definitions and marked in gc_clauses.
 */
void cnf_gc_sweep(cnf_t* cnf, const gc_info_t* gc_clauses, int_mset_t* vars_undefined);

#endif /* CNF_H_ */
