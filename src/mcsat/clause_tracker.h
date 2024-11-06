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

#ifndef CLAUSE_TRACKER_H
#define CLAUSE_TRACKER_H

#include "mcsat/clause.h"
#include "mcsat/unit_info.h"

#include <stdbool.h>

/**
 * Manager to keep track of clause status with regard to the unit-ness of its constraints.
 * A clause c is constraint-unit (c-unit) in variable x if for every literal l of c, l is either
 * a unit constraint in x (i.e. all variables but x are assigned) or l is set to be false.
 */

typedef struct clause_tracker_s clause_tracker_t;

typedef uint32_t clause_tracker_ref_t;

#define clause_tracker_ref_null 0

/** Returns true if constraint is handled by the plugin, i.e. query plugin's data structures. */
typedef bool (*clause_tracker_query_t)(void *query_data, variable_t constraint);

/**
 * Initializes the clause tracker.
 * Invariant: for every constraint c in unit_info, query(c) must return true.
 */
clause_tracker_t *clause_tracker_construct(const plugin_context_t *ctx, const constraint_unit_info_t *unit_info,
                                           clause_tracker_query_t query, void *query_data);

/** Deletes the clause tracker. */
void clause_tracker_delete(clause_tracker_t *ct);

/** Tracks the fact that a constraint became unit. Returns the number of clauses that became unit. */
uint32_t clause_tracker_track_unit_constraint(clause_tracker_t *ct, variable_t constraint);

/** Tracks the fact that a constraint appeared on the trail.
 * Returns the number of clauses that became unit because of this. */
uint32_t clause_tracker_track_decided_constraint(clause_tracker_t *ct, variable_t constraint);

/** Returns the number of c-unit clauses in x. */
uint32_t clause_tracker_count_unit_clauses(const clause_tracker_t *ct, variable_t x);

/** Fills refs with clause tracker references of unit clauses in x. */
void clause_tracker_get_var_unit_clause(const clause_tracker_t *ct, variable_t x, ivector_t *refs);

/** Gets one new and unprocessed unit clause, or clause_tracker_ref_null if none exists. */
clause_tracker_ref_t clause_tracker_get_new_unit_clause(clause_tracker_t *ct);

/** Gets the unit variable of a unit clause. */
variable_t clause_tracker_get_unit_variable(const clause_tracker_t *ct, clause_tracker_ref_t ref);

/** Gets the c-unit constraints of a unit clause. */
void clause_tracker_get_constraints(const clause_tracker_t *ct, clause_tracker_ref_t ref, ivector_t *pos, ivector_t *neg);

/** Gets the side-conditions of a unit clause, i.e. clause literals that are non-c-unit and on the trail. */
void clause_tracker_get_side_conditions(const clause_tracker_t *ct, clause_tracker_ref_t ref, ivector_t *pos, ivector_t *neg);

/** Pushes the clause level information. */
void clause_tracker_push(clause_tracker_t *ct);

/** Pops all clause tracking information since last push.
 * Associated constraint_unit_info_t must be popped first. */
void clause_tracker_pop(clause_tracker_t *ct);

/** Resets all internal structures and forgets all clauses. Useful after restarts with clause deletion. */
void clause_tracker_reset(clause_tracker_t *ct);

// TODO add GC and clause deletion support

#endif // CLAUSE_TRACKER_H
