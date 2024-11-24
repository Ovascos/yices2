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

/*
 * STRING TO IDENTIFIER TRANSLATIONS
 * USED IN FRONTENDS AND COMMAND LINE PARAMETERS
 */

#ifndef __FRONTEND_COMMON_STRING_OPTIONS_H
#define __FRONTEND_COMMON_STRING_OPTIONS_H

#include "solvers/quant/ef_parameters.h"
#include "api/search_parameters.h"

/*
 * Names of each branching mode (in lexicographic order)
 */
#define NUM_BRANCHING_MODES 6
extern const char * const branching_modes[NUM_BRANCHING_MODES];
extern const branch_t branching_code[NUM_BRANCHING_MODES];

/*
 * Names of the generalization modes for the EF solver
 */
#define NUM_EF_GEN_MODES 4
extern const char * const ef_gen_modes[NUM_EF_GEN_MODES];
extern const ef_gen_option_t ef_gen_code[NUM_EF_GEN_MODES];

/*
 * Names of the ematch modes for the quant solver
 */
#define NUM_EMATCH_MODES 3
extern const char * const ematch_modes[NUM_EMATCH_MODES];
extern const iterate_kind_t ematch_mode_code[NUM_EMATCH_MODES];

#endif /* __FRONTEND_COMMON_STRING_OPTIONS_H */
