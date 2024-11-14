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

#ifndef MCSAT_CLAUSE_H_
#define MCSAT_CLAUSE_H_

#include "mcsat/literal.h"
#include "mcsat/variable_db.h"

/**
 * A clause is just a sequence of literals. We keep the literals null
 * terminated. So that we can make the clauses smaller while keeping track of
 * the original size.
 */
typedef struct {
  /** Size of the clause (not real size of the vector, see above) */
  uint32_t size;
  /** The literals */
  mcsat_literal_t literals[];
} mcsat_clause_t;

/** Type of clause references */
typedef int32_t clause_ref_t;

/** Null clause */
#define clause_ref_null 0


/**
 * While the boolean plugin is responsible for clause handling, other plugins can use this interface
 * to get read-only information about clauses.
 */
typedef struct mcsat_clause_info_interface_s mcsat_clause_info_interface_t;

struct mcsat_clause_info_interface_s {

  /**
   * Gets watched clauses of variable var. The clauses are returned in the clauses. Returns the number of clauses found.
   * Returns a negative number if there was an error.
   */
  uint32_t (*get_clauses_by_var) (const mcsat_clause_info_interface_t* self, variable_t v, ivector_t* clauses);

  /**
   * Gets watched clauses of literal lit. The clauses are returned in the clauses. Returns the number of clauses found.
   * Returns a negative number if there was an error.
   */
  uint32_t (*get_clauses_by_literal) (const mcsat_clause_info_interface_t* self, mcsat_literal_t l, ivector_t* clauses);

  /**
   * Gets the clause with the given reference.
   */
  const mcsat_clause_t* (*get_clause) (const mcsat_clause_info_interface_t* self, clause_ref_t ref);

};

// Some helper functions

static inline
bool clause_is_sat(const mcsat_clause_t *C, const mcsat_trail_t *trail) {
  for (uint32_t i = 0; i < C->size; ++i) {
    if (literal_is_true(C->literals[i], trail)) return true;
  }
  return false;
}

static inline
bool clause_is_unsat(const mcsat_clause_t *C, const mcsat_trail_t *trail) {
  for (uint32_t i = 0; i < C->size; ++i) {
    if (!literal_is_false(C->literals[i], trail)) return false;
  }
  return true;
}

static inline
bool clause_is_unknown(const mcsat_clause_t *C, const mcsat_trail_t *trail) {
  return !clause_is_sat(C, trail) && !clause_is_unsat(C, trail);
}

static inline
void clause_print(const mcsat_clause_t* C, const variable_db_t* var_db, FILE* out) {
  literals_print(C->literals, C->size, var_db, out);
}

#endif /* MCSAT_CLAUSE_H_ */
