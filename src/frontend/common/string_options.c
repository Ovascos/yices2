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
 * ALL STRING ARRAYS MUST BE IN LEXICOGRAPHICAL ORDER
 */

#include "frontend/common/string_options.h"

/*
 * Names of each branching mode
 */

const char * const branching_modes[NUM_BRANCHING_MODES] = {
    "default",
    "negative",
    "positive",
    "th-neg",
    "th-pos",
    "theory",
};

const branch_t branching_code[NUM_BRANCHING_MODES] = {
    BRANCHING_DEFAULT,
    BRANCHING_NEGATIVE,
    BRANCHING_POSITIVE,
    BRANCHING_TH_NEG,
    BRANCHING_TH_POS,
    BRANCHING_THEORY,
};



/*
 * Names of the generalization modes for the EF solver
 */

const char * const ef_gen_modes[NUM_EF_GEN_MODES] = {
    "auto",
    "none",
    "projection",
    "substitution",
};

const ef_gen_option_t ef_gen_code[NUM_EF_GEN_MODES] = {
    EF_GEN_AUTO_OPTION,
    EF_NOGEN_OPTION,
    EF_GEN_BY_PROJ_OPTION,
    EF_GEN_BY_SUBST_OPTION,
};



/*
 * Names of the ematch modes for the quant solver
 */

const char * const ematch_modes[NUM_EMATCH_MODES] = {
    "all",
    "epsilongreedy",
    "random",
};

const iterate_kind_t ematch_mode_code[NUM_EMATCH_MODES] = {
    ITERATE_ALL,
    ITERATE_EPSILONGREEDY,
    ITERATE_RANDOM,
};



/*
 * Names of the clause level reasoning modes for the mcsat solver
 */

const char * const mcsat_clause_level_modes[NUM_MCSAT_CLAUSE_LEVEL_MODES] = {
    "disabled",
    "many",
    "many-trail",
    "single",
    "single-trail",
};

const clause_level_options_t mcsat_clause_level_mode_code[NUM_MCSAT_CLAUSE_LEVEL_MODES] = {
    CLAUSE_LEVEL_DISABLED,
    CLAUSE_LEVEL_MULTIPLE,
    CLAUSE_LEVEL_MULTIPLE_TRAIL,
    CLAUSE_LEVEL_SINGLE,
    CLAUSE_LEVEL_SINGLE_TRAIL,
};
