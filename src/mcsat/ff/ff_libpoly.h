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

#ifndef FF_LIBPOLY_H_
#define FF_LIBPOLY_H_

#include "mcsat/mcsat_types.h"
#include "mcsat/utils/lp_constraint_db.h"

#include <poly/poly.h>

typedef struct ff_plugin_s ff_plugin_t;

/**
 * Create a libpoly polynomial from a yices term. Returns the polynomial
 * lp_p and a positive integer constant c, such that lp_p = p * c. If c is
 * NULL it is ignored.
 */
lp_polynomial_t* lp_polynomial_from_term_ff(ff_plugin_t* ff, term_t t, lp_integer_t* c);

/**
 * Get yices term from polynomial (FF plugin wrapper).
 */
term_t lp_polynomial_to_yices_term_ff(ff_plugin_t *ff, const lp_polynomial_t *lp_p, type_t tau);

/** Add a new constraint */
void ff_poly_constraint_add(ff_plugin_t *ff, variable_t constraint_var);

/** Create a new constraint */
poly_constraint_t* ff_poly_constraint_create(ff_plugin_t *ff, variable_t constraint_var);

#endif /* FF_LIBPOLY_H_ */
