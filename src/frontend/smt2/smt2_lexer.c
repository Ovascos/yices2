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

/*
 * Lexer for the SMT-LIB language (version 2) 
 * (WITH HACKS TO PARSE SOME 2.5 STUFF).
 */

#include <assert.h>
#include <ctype.h>

// perfect hash functions generated by gperf
#include "frontend/smt2/smt2_hash_tokens.h"
#include "frontend/smt2/smt2_hash_keywords.h"
#include "frontend/smt2/smt2_hash_symbols.h"

#include "frontend/smt2/smt2_lexer.h"


/*
 * Tables for conversion from token to string
 */
static const char * const smt2_token_string[NUM_SMT2_TOKENS] = {
  "(",                     // SMT2_TK_LP
  ")",                     // SMT2_TK_RP
  "<end-of-stream>",       // SMT2_TK_EOS
  "<numeral>",             // SMT2_TK_NUMERAL
  "<decimal>",             // SMT2_TK_DECIMAL
  "<hexadecimal>",         // SMT2_TK_HEXADECIMAL
  "<binary>",              // SMT2_TK_BINARY
  "<string>",              // SMT2_TK_STRING
  "<symbol>",              // SMT2_TK_SYMBOL
  "<symbol>",              // SMT2_TK_QSYMBOL
  "<keyword>",             // SMT2_TK_KEYWORD
  "par",                   // SMT2_TK_PAR
  "NUMERAL",               // SMT2_TK_NUM
  "DECIMAL",               // SMT2_TK_DEC
  "STRING",                // SMT2_TK_STR
  "_",                     // SMT2_TK_UNDERSCORE
  "!",                     // SMT2_TK_BANG
  "as",                    // SMT2_TK_AS
  "let",                   // SMT2_TK_LET
  "exists",                // SMT2_TK_EXISTS
  "forall",                // SMT2_TK_FORALL

  "assert",                // SMT2_TK_ASSERT
  "check-sat",             // SMT2_TK_CHECK_SAT
  "check-sat-assuming",    // SMT2_TK_CHECK_SAT_ASSUMING
  "check-sat-assuming-model", // SMT2_TK_CHECK_SAT_ASSUMING_MODEL
  "declare-sort",          // SMT2_TK_DECLARE_SORT
  "declare-const",         // SMT2_TK_DECLARE_CONST
  "declare-fun",           // SMT2_TK_DECLARE_FUN
  "define-sort",           // SMT2_TK_DEFINE_SORT
  "define-const",          // SMT2_TK_DEFINE_CONST
  "define-fun",            // SMT2_TK_DEFINE_FUN
  "echo",                  // SMT2_TK_ECHO
  "exit",                  // SMT2_TK_EXIT
  "get-assertions",        // SMT2_TK_GET_ASSERTIONS
  "get-assignment",        // SMT2_TK_GET_ASSIGNMENT
  "get-info",              // SMT2_TK_GET_INFO
  "get-model",             // SMT2_TK_GET_MODEL
  "get-option",            // SMT2_TK_GET_OPTION
  "get-proof",             // SMT2_TK_GET_PROOF
  "get-unsat-assumptions", // SMT2_TK_GET_UNSAT_ASSUMPTIONS
  "get-unsat-core",        // SMT2_TK_GET_UNSAT_CORE
  "get-unsat-model-interpolant", // SMT2_TK_GET_UNSAT_MODEL_INTERPOLANT
  "get-value",             // SMT2_TK_GET_VALUE
  "pop",                   // SMT2_TK_POP
  "push",                  // SMT2_TK_PUSH
  "set-logic",             // SMT2_TK_SET_LOGIC
  "set-info",              // SMT2_TK_SET_INFO
  "set-option",            // SMT2_TK_SET_OPTION
  "reset",                 // SMT2_TK_RESET
  "reset-assertions",      // SMT2_TK_RESET_ASSERTIONS

  "<bad-string>",          // SMT2_TK_INVALID_STRING
  "<invalid-numeral>",     // SMT2_TK_INVALID_NUMERAL
  "<invalid-decimal>",     // SMT2_TK_INVALID_DECIMAL
  "<invalid-hexadecimal>", // SMT2_TK_INVALID_HEXADECIMAL
  "<invalid-binary>",      // SMT2_TK_INVALID_BINARY
  "<invalid-symbol>",      // SMT2_TK_INVALID_SYMBOL
  "<invalid-keyword>",     // SMT2_TK_INVALID_KEYWORD
  "<error>",               // SMT2_TK_ERROR
};

static const char * const smt2_keyword_string[NUM_SMT2_KEYWORDS] = {
  ":diagnostic-output-channel",  // SMT2_KW_DIAGNOSTIC_OUTPUT
  ":expand-definitions",      // SMT2_KW_EXPAND_DEFINITIONS
  ":global-declarations",     // SMT2_KW_GLOBAL_DECLARATIONS
  ":interactive-mode",        // SMT2_KW_INTERACTIVE_MODE
  ":print-success",           // SMT2_KW_PRINT_SUCCESS
  ":produce-assertions",      // SMT2_KW_PRODUCE_ASSERTIONS
  ":produce-assignments",     // SMT2_KW_PRODUCE_ASSIGNMENTS
  ":produce-models",          // SMT2_KW_PRODUCE_MODELS
  ":produce-proofs",          // SMT2_KW_PRODUCE_PROOFS
  ":produce-unsat-assumptions",   // SMT2_KW_PRODUCE_UNSAT_ASSUMPTIONS
  ":produce-unsat-cores",     // SMT2_KW_PRODUCE_UNSAT_CORES
  ":produce-unsat-model-interpolants", // SMT2_KW_PRODUCE_UNSAT_MODEL_INTERPOLANS
  ":random-seed",             // SMT2_KW_RANDOM_SEED
  ":regular-output-channel",  // SMT2_KW_REGULAR_OUTPUT
  ":reproducible-resource-limit",  // SMT2_KW_REPRODUCIBLE_RESOURCE_LIMIT
  ":verbosity",               // SMT2_KW_VERBOSITY
  ":dump-models",             // SMT2_KW_DUMP_MODELS
  ":timeout",                 // SMT2_KW_TIMEOUT

  ":all-statistics",          // SMT2_KW_ALL_STATISTICS
  ":assertion-stack-levesl",  // SMT2_KM_ASSERTIONS_STACK_LEVELS
  ":authors",                 // SMT2_KW_AUTHORS
  ":error-behavior",          // SMT2_KW_ERROR_BEHAVIOR
  ":name",                    // SMT2_KW_NAME
  ":reason-unknown",          // SMT2_KW_REASON_UNKNOWN
  ":version",                 // SMT2_KW_VERSION

  ":named",                   // SMT2_KW_NAMED
  ":pattern",                 // SMT2_KW_PATTERN

  ":status",                  // SMT2_KW_STATUS
  ":source",                  // SMT2_KW_SOURCE
  ":smt-lib-version",         // SMT2_KW_SMT_LIB_VERSION
  ":category",                // SMT2_KW_CATEGORY
  ":difficulty",              // SMT2_KW_DIFFICULTY
  ":notes",                   // SMT2_KW_NOTES

  "<unknown-keyword>",        // SMT2_KW_UNKNOWN
};

static const char * const smt2_symbol_string[NUM_SMT2_SYMBOLS] = {
  "Bool",                    // SMT2_SYM_BOOL
  "true",                    // SMT2_SYM_TRUE
  "false",                   // SMT2_SYM_FALSE
  "not",                     // SMT2_SYM_NOT
  "=>",                      // SMT2_SYM_IMPLIES
  "and",                     // SMT2_SYM_AND
  "or",                      // SMT2_SYM_OR
  "xor",                     // SMT2_SYM_XOR
  "=",                       // SMT2_SYM_EQ
  "distinct",                // SMT2_SYM_DISTINCT
  "ite",                     // SMT2_SYM_ITE
  "Array",                   // SMT2_SYM_ARRAY
  "select",                  // SMT2_SYM_SELECT
  "store",                   // SMT2_SYM_STORE
  "Int",                     // SMT2_SYM_INT
  "Real",                    // SMT2_SYM_REAL
  "-",                       // SMT2_SYM_MINUS
  "+",                       // SMT2_SYM_PLUS
  "*",                       // SMT2_SYM_TIMES
  "/",                       // SMT2_SYM_DIVIDES
  "<=",                      // SMT2_SYM_LE
  "<",                       // SMT2_SYM_LT
  ">=",                      // SMT2_SYM_GE
  ">",                       // SMT2_SYM_GT
  "div",                     // SMT2_SYM_DIV
  "mod",                     // SMT2_SYM_MOD
  "abs",                     // SMT2_SYM_ABS
  "to_real",                 // SMT2_SYM_TO_REAL
  "to_int",                  // SMT2_SYM_TO_INT
  "is_int",                  // SMT2_SYM_IS_INT
  "divisible",               // SMT2_SYM_DIVISIBLE
  "<bv-constant>",           // SMT2_SYM_BV_CONSTANT,
  "BitVec",                  // SMT2_SYM_BITVEC
  "concat",                  // SMT2_SYM_CONCAT
  "extract",                 // SMT2_SYM_EXTRACT
  "repeat",                  // SMT2_SYM_REPEAT
  "bvcomp",                  // SMT2_SYM_BVCOMP
  "bvredor",                 // SMT2_SYM_BVREDOR
  "bvredand",                // SMT2_SYM_BVREDAND
  "bvnot",                   // SMT2_SYM_BVNOT
  "bvand",                   // SMT2_SYM_BVAND
  "bvor",                    // SMT2_SYM_BVOR
  "bvnand",                  // SMT2_SYM_BVNAND
  "bvnor",                   // SMT2_SYM_BVNOR
  "bvxor",                   // SMT2_SYM_BVXOR
  "bvxnor",                  // SMT2_SYM_BVXNOR
  "bvneg",                   // SMT2_SYM_BVNEG
  "bvadd",                   // SMT2_SYM_BVADD
  "bvsub",                   // SMT2_SYM_BVSUB
  "bvmul",                   // SMT2_SYM_BVMUL
  "bvudiv",                  // SMT2_SYM_BVUDIV
  "bvurem",                  // SMT2_SYM_BVUREM
  "bvsdiv",                  // SMT2_SYM_BVSDIV
  "bvsrem",                  // SMT2_SYM_BVSREM
  "bvsmod",                  // SMT2_SYM_BVSMOD
  "bvshl",                   // SMT2_SYM_BVSHL
  "bvlshr",                  // SMT2_SYM_BVLSHR
  "bvashr",                  // SMT2_SYM_BVASHR
  "zero_extend",             // SMT2_SYM_ZERO_EXTEND
  "sign_extend",             // SMT2_SYM_SIGN_EXTEND
  "rotate_left",             // SMT2_SYM_ROTATE_LEFT
  "rotate_right",            // SMT2_SYM_ROTATE_RIGHT
  "bvult",                   // SMT2_SYM_BVULT
  "bvule",                   // SMT2_SYM_BVULE
  "bvugt",                   // SMT2_SYM_BVUGT
  "bvuge",                   // SMT2_SYM_BVUGE
  "bvslt",                   // SMT2_SYM_BVSLT
  "bvsle",                   // SMT2_SYM_BVSLE
  "bvsgt",                   // SMT2_SYM_BVSGT
  "bvsge",                   // SMT2_SYM_BVSGE
  "FiniteField",             // SMT2_SYM_FINITEFIELD
  "ff.add",                  // SMT2_SYM_FFADD
  "ff.mul",                  // SMT2_SYM_FFMUL

  // errors
  "<invalid-bv-constant>",   // SMT2_SYM_INVALID_BV_CONSTANT,
  "<unknown-symbol>",        // SMT2_SYM_UNKNOWN,
};




/*
 * ACTIVE/INACTIVE SYMBOLS
 */

/*
 * Depending on the logic, some symbols are interpreted as built-in
 * operators. If they are inactive, they are just interpreted as
 * ordinary symbols. We control which symbols are active using array
 * active_symbol.
 *
 * As of 2011, the following logics/theories/type names are used:
 *
 *   AUFLIA         Int_ArraysEx                      Int Array
 *   AUFLIRA        Int_Int_Real_Array_ArraysEx       Int Real Array1 Array2
 *   AUFNIRA        Int_Int_Real_Array_ArraysEx       Int Real Array1 Array2
 *   LRA            Reals
 *   QF_AUFBV       BitVector_ArraysEx                Array BitVec
 *   QF_AUFLIA      Int_ArraysEx                      Int Array
 *   QF_AX          ArraysEx                          Array Index Element
 *   QF_BV          Fixed_Size_BitVectors             BitVec
 *   QF_IDL         Ints
 *   QF_LIA         Ints
 *   QF_LRA         Reals
 *   QF_NIA         Ints
 *   QF_NRA         Reals    (added July 2011)
 *   QF_RDL         Reals
 *   QF_UF          Empty
 *   QF_UFIDL       Ints
 *   QF_UFBV        Fixed_Size_BitVectors             BitVec
 *   QF_UFLIA       Ints
 *   QF_UFLRA       Reals
 *   QF_UFNRA       Reals
 *   UFLRA          Reals    (added July 2011)
 *   UFNIA          Ints
 */

static uint8_t active_symbol[NUM_SMT2_SYMBOLS];

/*
 * FLAG TO SELECT 2.5 SYNTAX
 */
static bool two_dot_five_variant = false;


/*
 * Activate all default symbols:
 * - all symbols in the core theory
 */
static void smt2_activate_default(void) {
  uint32_t i;

  for (i=0; i<NUM_SMT2_SYMBOLS; i++) {
    active_symbol[i] = false;
  }
  active_symbol[SMT2_SYM_BOOL] = true;
  active_symbol[SMT2_SYM_TRUE] = true;
  active_symbol[SMT2_SYM_FALSE] = true;
  active_symbol[SMT2_SYM_NOT] = true;
  active_symbol[SMT2_SYM_IMPLIES] = true;
  active_symbol[SMT2_SYM_AND] = true;
  active_symbol[SMT2_SYM_OR] = true;
  active_symbol[SMT2_SYM_XOR] = true;
  active_symbol[SMT2_SYM_EQ] = true;
  active_symbol[SMT2_SYM_DISTINCT] = true;
  active_symbol[SMT2_SYM_ITE] = true;
}


/*
 * Arrays (theory ArraysEx)
 */
static void smt2_activate_arrays(void) {
  active_symbol[SMT2_SYM_ARRAY] = true;
  active_symbol[SMT2_SYM_SELECT] = true;
  active_symbol[SMT2_SYM_STORE] = true;
}


/*
 * Integer difference logic
 */
static void smt2_activate_idl(void) {
  active_symbol[SMT2_SYM_INT] = true;
  active_symbol[SMT2_SYM_MINUS] = true;
  active_symbol[SMT2_SYM_PLUS] = true;
  active_symbol[SMT2_SYM_TIMES] = true;
  active_symbol[SMT2_SYM_LE] = true;
  active_symbol[SMT2_SYM_LT] = true;
  active_symbol[SMT2_SYM_GE] = true;
  active_symbol[SMT2_SYM_GT] = true;
}


/*
 * Integer arithmetic (theory Ints)
 */
static void smt2_activate_ints(void) {
  smt2_activate_idl();
  active_symbol[SMT2_SYM_DIV] = true;
  active_symbol[SMT2_SYM_MOD] = true;
  active_symbol[SMT2_SYM_ABS] = true;
  active_symbol[SMT2_SYM_DIVISIBLE] = true;
}


/*
 * Real arithmetic (theory Reals)
 */
static void smt2_activate_reals(void) {
  active_symbol[SMT2_SYM_REAL] = true;
  active_symbol[SMT2_SYM_MINUS] = true;
  active_symbol[SMT2_SYM_PLUS] = true;
  active_symbol[SMT2_SYM_TIMES] = true;
  active_symbol[SMT2_SYM_DIVIDES] = true;
  active_symbol[SMT2_SYM_LE] = true;
  active_symbol[SMT2_SYM_LT] = true;
  active_symbol[SMT2_SYM_GE] = true;
  active_symbol[SMT2_SYM_GT] = true;
}


/*
 * All symbols in Reals_Ints
 */
static void smt2_activate_mixed_arith(void) {
  smt2_activate_ints();
  smt2_activate_reals();
  active_symbol[SMT2_SYM_TO_REAL] = true;
  active_symbol[SMT2_SYM_TO_INT] = true;
  active_symbol[SMT2_SYM_IS_INT] = true;
}


/*
 * All bitvector symbols + the bv-constant token
 * - we don't activate bvredor and bvredand since they are not officially
 *   in SMT-LIB 2.0
 */
static void smt2_activate_bv(void) {
  active_symbol[SMT2_SYM_BV_CONSTANT] = true;
  active_symbol[SMT2_SYM_BITVEC] = true;
  active_symbol[SMT2_SYM_CONCAT] = true;
  active_symbol[SMT2_SYM_EXTRACT] = true;
  active_symbol[SMT2_SYM_REPEAT] = true;
  active_symbol[SMT2_SYM_BVCOMP] = true;
  active_symbol[SMT2_SYM_BVNOT] = true;
  active_symbol[SMT2_SYM_BVAND] = true;
  active_symbol[SMT2_SYM_BVOR] = true;
  active_symbol[SMT2_SYM_BVNAND] = true;
  active_symbol[SMT2_SYM_BVNOR] = true;
  active_symbol[SMT2_SYM_BVXOR] = true;
  active_symbol[SMT2_SYM_BVXNOR] = true;
  active_symbol[SMT2_SYM_BVNEG] = true;
  active_symbol[SMT2_SYM_BVADD] = true;
  active_symbol[SMT2_SYM_BVSUB] = true;
  active_symbol[SMT2_SYM_BVMUL] = true;
  active_symbol[SMT2_SYM_BVUDIV] = true;
  active_symbol[SMT2_SYM_BVUREM] = true;
  active_symbol[SMT2_SYM_BVSDIV] = true;
  active_symbol[SMT2_SYM_BVSREM] = true;
  active_symbol[SMT2_SYM_BVSMOD] = true;
  active_symbol[SMT2_SYM_BVSHL] = true;
  active_symbol[SMT2_SYM_BVLSHR] = true;
  active_symbol[SMT2_SYM_BVASHR] = true;
  active_symbol[SMT2_SYM_ZERO_EXTEND] = true;
  active_symbol[SMT2_SYM_SIGN_EXTEND] = true;
  active_symbol[SMT2_SYM_ROTATE_LEFT] = true;
  active_symbol[SMT2_SYM_ROTATE_RIGHT] = true;
  active_symbol[SMT2_SYM_BVULT] = true;
  active_symbol[SMT2_SYM_BVULE] = true;
  active_symbol[SMT2_SYM_BVUGT] = true;
  active_symbol[SMT2_SYM_BVUGE] = true;
  active_symbol[SMT2_SYM_BVSLT] = true;
  active_symbol[SMT2_SYM_BVSLE] = true;
  active_symbol[SMT2_SYM_BVSGT] = true;
  active_symbol[SMT2_SYM_BVSGE] = true;
}

static void smt2_activate_ff(void) {
  active_symbol[SMT2_SYM_FINITEFIELD] = true;
  active_symbol[SMT2_SYM_FF_CONSTANT] = true;
  active_symbol[SMT2_SYM_FFADD] = true;
  active_symbol[SMT2_SYM_FFMUL] = true;
}

/*
 * Select the built-in symbols for a given logic
 */
void smt2_lexer_activate_logic(smt_logic_t logic) {
  if (logic_has_arrays(logic)) {
    smt2_activate_arrays();
  }
  if (logic_has_bv(logic)) {
    smt2_activate_bv();
  }
  switch (arith_fragment(logic)) {
  case ARITH_IDL:
    smt2_activate_idl();
    break;

  case ARITH_LIA:
  case ARITH_NIA:
    smt2_activate_ints();
    break;

  case ARITH_LRA:
  case ARITH_NRA:
  case ARITH_RDL:
    smt2_activate_reals();
    break;

  case ARITH_LIRA:
  case ARITH_NIRA:
    smt2_activate_mixed_arith();
    break;

  case ARITH_FFA:
    smt2_activate_ff();
    break;

  case ARITH_NONE:
    break;
  }
}


/*
 * Reset to the defaults: all logic-specific symbols are disactivated
 */
void smt2_lexer_reset_logic(void) {
  smt2_activate_default();
}


/*
 * Switch to version 2.5
 */
void smt2_lexer_activate_two_dot_five(void) {
  two_dot_five_variant = true;
}


/*
 * Lexer initialization
 */
int32_t init_smt2_file_lexer(lexer_t *lex, const char *filename) {
  smt2_activate_default();
  return init_file_lexer(lex, filename);
}

void init_smt2_stream_lexer(lexer_t *lex, FILE *f, const char *name) {
  smt2_activate_default();
  init_stream_lexer(lex, f, name);
}

void init_smt2_string_lexer(lexer_t *lex, char *data, const char *name) {
  smt2_activate_default();
  init_string_lexer(lex, data, name);
}


#if 0

/*
 * HACK/EXPERIMENT: use UTF-8 encoded strings
 */
int32_t init_smt2_wide_file_lexer(lexer_t *lex, const char *filename) {
  smt2_activate_default();
  return init_wide_file_lexer(lex, filename);
}

void init_smt2_wide_stream_lexer(lexer_t *lex, FILE *f, const char *name) {
  smt2_activate_default();
  init_wide_stream_lexer(lex, f, name);
}

#endif

/*
 * Get string for tokens/symbols/keywords
 */
const char *smt2_token_to_string(smt2_token_t tk) {
  assert(0 <= tk && tk < NUM_SMT2_TOKENS);
  return smt2_token_string[tk];
}

const char *smt2_symbol_to_string(smt2_symbol_t sym) {
  assert(0 <= sym && sym < NUM_SMT2_SYMBOLS);
  return smt2_symbol_string[sym];
}

const char *smt2_keyword_to_string(smt2_keyword_t kw) {
  assert(0 <= kw && kw < NUM_SMT2_KEYWORDS);
  return smt2_keyword_string[kw];
}


/*
 * Read a string literal
 * - current char is "
 * - read all characters until the closing " or any non-printable
 *   character
 * - replace escape sequences \" by " and \\ by \
 *
 * Result: the lexer's buffer contains the string literal
 * without the delimiting quotes.
 * - return code:
 *   SMT2_TK_STRING if the string is valid
 *   SMT2_TK_INVALID_STRING if the string is terminated by
 *   a non-printable character
 *
 * NOTE: this is not strictly compliant with the SMT-LIB 2.0
 * standard as we may include non-ascii printable characters
 * in the string.
 *
 * NOTE2: the SMT-LIB2 standard says 'a string is any sequence of
 * printable ASCII characters delimited by double quotes ...' But it
 * does not define 'printable ASCII character'. Several benchmarks in
 * SMT-LIB include line breaks inside a string (which are not
 * printable characters), so I've changed the loop below to allow both
 * printable characters and spaces.
 */
static smt2_token_t smt2_read_string(lexer_t *lex) {
  reader_t *rd;
  string_buffer_t *buffer;
  int c;
  smt2_token_t tk;

  rd = &lex->reader;
  buffer = lex->buffer;
  assert(reader_current_char(rd) == '"');

  for (;;) {
    c = reader_next_char(rd);
    if (c == '"') {
      // consume the closing quote
      reader_next_char(rd);
      tk = SMT2_TK_STRING;
      break;
    }

    if (!isprint(c) && !isspace(c)) {
      // error
      tk = SMT2_TK_INVALID_STRING;
      break;
    }

    if (c == '\\') {
      c = reader_next_char(rd);
      if (c != '"' && c != '\\') {
        // keep the backslash
        string_buffer_append_char(buffer, '\\');
      }
    }
    string_buffer_append_char(buffer, c);
  }

  string_buffer_close(buffer);

  return tk;
}


/*
 * String literal for SMT-LIB 2.5
 *
 * Gratuitous change to the escape sequence:
 * - replace "" inside the string by "
 */
static smt2_token_t smt2_read_string_var(lexer_t *lex) {
  reader_t *rd;
  string_buffer_t *buffer;
  int c;
  smt2_token_t tk;

  rd = &lex->reader;
  buffer = lex->buffer;
  assert(reader_current_char(rd) == '"');

  for (;;) {
    c = reader_next_char(rd);
    if (c == '"') {
      c = reader_next_char(rd);
      if (c != '"') {
	tk = SMT2_TK_STRING;
	break;
      }
    }
    if (c < 32 && !isspace(c)) {
      // error
      tk = SMT2_TK_INVALID_STRING;
      break;
    }
    string_buffer_append_char(buffer, c);
  }

  string_buffer_close(buffer);

  return tk;
}



/*
 * Read a binary literal
 * - the buffer must contain '#'
 * - current char must be 'b'
 * - add 'b' and the sequence of '0' and '1' that follows
 *   to the buffer
 * - stop on the first character that's not '0' or '1'
 *
 * The resulting token is stored in buffer
 * - return code:
 *   SMT2_TK_BINARY if the sequence is non-empty
 *   SMT2_TK_INVALID_BINARY if the sequence is empty
 */
static smt2_token_t smt2_read_binary(lexer_t *lex) {
  reader_t *rd;
  string_buffer_t *buffer;
  int c;
  smt2_token_t tk;

  rd = &lex->reader;
  buffer = lex->buffer;
  c = reader_current_char(rd);

  assert(string_buffer_length(buffer) == 1 &&
         buffer->data[0] == '#' && c == 'b');

  do {
    string_buffer_append_char(buffer, c);
    c = reader_next_char(rd);
  } while (c == '0' || c == '1');
  string_buffer_close(buffer);

  tk = SMT2_TK_BINARY;
  if (string_buffer_length(buffer) <= 2) {
    tk = SMT2_TK_INVALID_BINARY;
  }

  return tk;
}


/*
 * Read an hexadecimal literal
 * - the buffer must contain '#'
 * - current_char must be 'x'
 * - add 'x' and the sequence of hexadecimal digits that
 *   follows to the buffer
 * - stop on the first character that's not hexadecimal
 *
 * The resulting token is stored in buffer
 * - return code:
 *   SMT2_TK_HEXADECIMAL if the sequence is non-empty
 *   SMT2_TK_INVALID_HEXADECIMAL if the sequence is empty
 */
static smt2_token_t smt2_read_hexa(lexer_t *lex) {
  reader_t *rd;
  string_buffer_t *buffer;
  int c;
  smt2_token_t tk;

  rd = &lex->reader;
  buffer = lex->buffer;
  c = reader_current_char(rd);

  assert(string_buffer_length(buffer) == 1 &&
         buffer->data[0] == '#' && c == 'x');

  do {
    string_buffer_append_char(buffer, c);
    c = reader_next_char(rd);
  } while (isxdigit(c));
  string_buffer_close(buffer);

  tk = SMT2_TK_HEXADECIMAL;
  if (string_buffer_length(buffer) <= 2) {
    tk = SMT2_TK_INVALID_HEXADECIMAL;
  }

  return tk;
}


/*
 * Numbers that don't start with '0'
 * - the buffer must be empty
 * - current char must be a digit '1' to '9'
 * - read the sequence of digits that follows and add it to the buffer
 * - if the character after this sequence is '.' then read as a DECIMAL
 *   otherwise the token is a NUMERAL.
 *
 * Return code:
 * - SMT2_INVALID_DECIMAL if the '.' is not followed by a digit
 */
static smt2_token_t smt2_read_number(lexer_t *lex) {
  reader_t *rd;
  string_buffer_t *buffer;
  int c;
  smt2_token_t tk;
  uint32_t i;

  rd = &lex->reader;
  buffer = lex->buffer;
  c = reader_current_char(rd);

  assert(string_buffer_length(buffer) == 0 && isdigit(c) && c != '0');

  // first sequence of digits
  do {
    string_buffer_append_char(buffer, c);
    c = reader_next_char(rd);
  } while (isdigit(c));

  tk = SMT2_TK_NUMERAL;
  if (c == '.') {
    i = string_buffer_length(buffer);

    // attempt to parse a DECIMAL
    do {
      string_buffer_append_char(buffer, c);
      c = reader_next_char(rd);
    } while (isdigit(c));

    tk = SMT2_TK_DECIMAL;
    if (string_buffer_length(buffer) <= i+1) {
      tk = SMT2_TK_INVALID_DECIMAL;
    }
  }

  string_buffer_close(buffer);

  return tk;
}


/*
 * Numbers that start with '0'
 * - the buffer must be empty
 * - current char must be '0'
 */
static smt2_token_t smt2_read_number0(lexer_t *lex) {
  reader_t *rd;
  string_buffer_t *buffer;
  int c;
  smt2_token_t tk;

  rd = &lex->reader;
  buffer = lex->buffer;
  c = reader_current_char(rd);

  assert(string_buffer_length(buffer) == 0 && c == '0');

  // add '0'
  string_buffer_append_char(buffer, c);

  c = reader_next_char(rd);
  tk = SMT2_TK_NUMERAL;

  if (c == '.') {
    // parse a decimal '0.<digits>'
    do {
      string_buffer_append_char(buffer, c);
      c = reader_next_char(rd);
    } while (isdigit(c));

    tk = SMT2_TK_DECIMAL;
    if (string_buffer_length(buffer) <= 2) {
      tk = SMT2_TK_INVALID_DECIMAL; // '0.' but not digit after that
    }

  } else if (isdigit(c)) {
    /*
     * invalid numeral such as '00..' or '05...'
     * put all the digits that follow '0' in the buffer
     * to give a nicer error message
     */
    do {
      string_buffer_append_char(buffer, c);
      c = reader_next_char(rd);
    } while (isdigit(c));

    tk = SMT2_TK_INVALID_NUMERAL;
  }

  string_buffer_close(buffer);

  return tk;
}


/*
 * Characters that may appear in keywords and simple symbols:
 * - digits + letters + ~ ! @ $ % ^ & * _ - + = < > . ? /
 *
 * NOTE: again, we don't really follow the standard (we can
 * accept non-ASCII characters, depending on the locale and
 * how isalnum(c) decides).
 */
static bool issimple(int c) {
  if (isalnum(c)) {
    return true;
  }

  switch (c) {
  case '~':
  case '!':
  case '@':
  case '$':
  case '%':
  case '^':
  case '&':
  case '*':
  case '_':
  case '-':
  case '+':
  case '=':
  case '<':
  case '>':
  case '.':
  case '?':
  case '/':
    return true;

  default:
    return false;
  }
}


/*
 * Read a keyword:
 * - the buffer must be empty
 * - current_char must be ':'
 * - add ':' + the sequence of simple_chars that follows to the buffer
 *
 * If ':' is not followed by a simple char, return SMT2_TK_INVALID_KEYWORD
 * Otherwise return SMT2_TK_KEYWORD.
 */
static smt2_token_t smt2_read_keyword(lexer_t *lex) {
  reader_t *rd;
  string_buffer_t *buffer;
  int c;
  smt2_token_t tk;

  rd = &lex->reader;
  buffer = lex->buffer;
  c = reader_current_char(rd);

  assert(string_buffer_length(buffer) == 0 && c == ':');

  do {
    string_buffer_append_char(buffer, c);
    c = reader_next_char(rd);
  } while (issimple(c));
  string_buffer_close(buffer);

  tk = SMT2_TK_KEYWORD;
  if (string_buffer_length(buffer) <= 1) {
    tk = SMT2_TK_INVALID_KEYWORD;
  }

  return tk;
}



/*
 * Read a simple symbol
 * - the buffer must be empty
 * - current_char must be simple
 * - read the sequence of simple chars and add it to the buffer
 *
 * If the symbol is a reserved word, return the corresponding
 * token id. Otherwise, return SMT2_TK_SYMBOL.
 */
static smt2_token_t smt2_read_symbol(lexer_t *lex) {
  reader_t *rd;
  string_buffer_t *buffer;
  const keyword_t *kw;
  int c;
  smt2_token_t tk;

  rd = &lex->reader;
  buffer = lex->buffer;
  c = reader_current_char(rd);

  assert(string_buffer_length(buffer) == 0 && issimple(c));

  do {
    string_buffer_append_char(buffer, c);
    c = reader_next_char(rd);
  } while (issimple(c));
  string_buffer_close(buffer);

  tk = SMT2_TK_SYMBOL;
  kw = in_smt2_tk(buffer->data, buffer->index);
  if (kw != NULL) {
    tk = kw->tk;
  }

  return tk;
}


/*
 * Hack to tolerate non-ASCII characters in some SMT-LIB benchmarks.
 * This is a hack as we don't check whether the byte sequences
 * are valid UTF-8 encodings. We also may report incorrect error
 * locations (the column count maintained in the reader is not correct).
 */
static inline bool ok_char(int c) {
  return isspace(c) || c>=32;
}

/*
 * Read a quoted symbol: any sequence of characters delimited by '|'
 * - exceptions: no '\' allowed in the symbol
 * - all characters between '|' must be printable
 * - the delimiting '|' are not part of the symbol
 *
 * - the buffer must be empty
 * - current char must be '|'
 *
 * Return SMT2_TK_INVALID_SYMBOL if a non-printable character
 * or '\' is found before the closing '|'. Return SMT2_TK_QSYMBOL
 * otherwise.
 */
static smt2_token_t smt2_read_quoted_symbol(lexer_t *lex) {
  reader_t *rd;
  string_buffer_t *buffer;
  int c;
  smt2_token_t tk;

  rd = &lex->reader;
  buffer = lex->buffer;
  assert(string_buffer_length(buffer) == 0 &&
         reader_current_char(rd) == '|');

  for (;;) {
    c = reader_next_char(rd);
    if (c == '|' || c == '\\' || !ok_char(c)) { 
      //    (!isprint(c) && !isspace(c))) { // HACK TO PARSE BENCHMARKS
      // either the terminator '|' or a character not allowed in quoted symbols
      break;
    }
    string_buffer_append_char(buffer, c);
  }
  string_buffer_close(buffer);

  tk = SMT2_TK_INVALID_SYMBOL;
  if (c == '|') {
    // consume the closing '|'
    reader_next_char(rd);
    tk = SMT2_TK_QSYMBOL;
  }

  return tk;
}


/*
 * Read the next token and return its code tk
 * - set lex->token to tk
 * - set lex->tk_pos
 * - if the token is not '(' or ')', then its value is in lex->buffer
 *   as a string
 */
smt2_token_t next_smt2_token(lexer_t *lex) {
  reader_t *rd;
  string_buffer_t *buffer;
  int c;
  smt2_token_t tk;

  rd = &lex->reader;
  c = reader_current_char(rd);
  buffer = lex->buffer;
  string_buffer_reset(buffer);

  // skip spaces and comments
  for (;;) {
    while (isspace(c)) c = reader_next_char(rd);
    if (c != ';') break;
    // comments: read everything until the end of the line or EOF
    do {
      c = reader_next_char(rd);
    } while (c != '\n' && c != EOF);
  }

  // record start of token
  lex->tk_pos = rd->pos;
  lex->tk_line = rd->line;
  lex->tk_column = rd->column;

  switch (c) {
  case '(':
    tk = SMT2_TK_LP;
    goto next_then_return;

  case ')':
    tk = SMT2_TK_RP;
    goto next_then_return;

  case EOF:
    tk = SMT2_TK_EOS;
    goto done;

  case '"':
    if (two_dot_five_variant) {
      tk = smt2_read_string_var(lex);
    } else {
      tk = smt2_read_string(lex);
    }
    goto done;

  case '#':
    string_buffer_append_char(buffer, c);
    c = reader_next_char(rd);
    if (c == 'b') {
      tk = smt2_read_binary(lex);
    } else if (c == 'x') {
      tk = smt2_read_hexa(lex);
    } else {
      tk = SMT2_TK_ERROR;
      string_buffer_close(buffer);
    }
    goto done;

  case '0':
    tk = smt2_read_number0(lex);
    goto done;

  case '1':
  case '2':
  case '3':
  case '4':
  case '5':
  case '6':
  case '7':
  case '8':
  case '9':
    tk = smt2_read_number(lex);
    goto done;

  case ':':
    tk = smt2_read_keyword(lex);
    goto done;

  case '|':
    tk = smt2_read_quoted_symbol(lex);
    goto done;

  default:
    if (issimple(c)) {
      tk = smt2_read_symbol(lex);
      goto done;
    } else {
      tk = SMT2_TK_ERROR;
      /*
       * copy the bad character in buffer for
       * better error reporting
       */
      string_buffer_append_char(buffer, c);
      string_buffer_close(buffer);
      goto next_then_return;
    }
  }

 next_then_return:
  reader_next_char(rd);

 done:
  lex->token = tk;

  return tk;
}


/*
 * Convert string to a built-in keyword index
 * - s = string, n = length of the string
 * - return SMT2_KW_UNKNOWN if s is not in the built-in keyword table.
 */
smt2_keyword_t smt2_string_to_keyword(const char *s, uint32_t n) {
  const keyword_t *kw;
  smt2_keyword_t k;

  k = SMT2_KW_UNKNOWN;
  kw = in_smt2_kw(s, n);
  if (kw != NULL) {
    k = kw->tk;
  }

  return k;
}


/*
 * Check whether sym is an active symbol
 */
bool smt2_symbol_is_active(smt2_symbol_t sym) {
  assert(0 <= sym && sym < NUM_SMT2_SYMBOLS);
  return active_symbol[sym];
}



/*
 * Check whether s is of the form 'bv<digits>'
 * - n = length of s
 * - return code:
 *   SMT2_SYM_BV_CONSTANT if s is of the form 'bv<numeral>'
 *   SMT2_SYM_INVALID_BV_CONSTANT if s is of the from 'bv0<digits>'
 *   SMT2_SYM_UNKNOWN otherwise (not a bvconstant)
 */
static smt2_symbol_t string_to_bv_constant(const char *s, uint32_t n) {
  uint32_t i;
  smt2_symbol_t sym;

  sym = SMT2_SYM_UNKNOWN;
  if (n >= 3 && s[0] == 'b' && s[1] == 'v') {
    for (i=2; i<n; i++) {
      if (!isdigit((int) s[i])) {
        goto done; // not of the form bv<digits>
      }
    }

    sym = SMT2_SYM_BV_CONSTANT;
    if (s[2] == '0' && n > 3) {
      sym = SMT2_SYM_INVALID_BV_CONSTANT;
    }
  }

 done:
  return sym;
}

/*
 * Check whether s is of the form 'ff<digits>'
 * - n = length of s
 * - return code:
 *   SMT2_SYM_FF_CONSTANT if s is of the form 'ff<numeral>'
 *   SMT2_SYM_UNKNOWN otherwise (not a ffconstant)
 */
static smt2_symbol_t string_to_ff_constant(const char *s, uint32_t n) {
  uint32_t i;
  smt2_symbol_t sym;

  sym = SMT2_SYM_UNKNOWN;
  if (n >= 3 && s[0] == 'f' && s[1] == 'f') {
    // could be a negative number
    i = (n >= 4 && s[2] == '-') ? 3 : 2;
    while (i<n) {
      if (!isdigit((int) s[i++])) {
        goto done; // not of the form ff<digits>
      }
    }
    sym = SMT2_SYM_FF_CONSTANT;
  }

  done:
  return sym;
}


/**
 * Convert a string s to a symbol code
 * - n = length of s
 * - return SMT2_SYM_UNKNOWN if s is not a predefined symbol,
 *   or if it's not active.
 *
 * Special treatment for bitvector constants, when the bit-vector
 * theory is active:
 * - if the string is of the form 'bv<numeral>' then the
 *   returned id is SMT2_SYM_BV_CONSTANT
 * - if the string starts with 'bv' but the rest is not <numeral>, then
 *   the returned if is SMT2_SYM_INVALID_BV_CONSTANT
 *
 * Special treatment for finite field constants, when the finite field
 * theory is active:
 * - if the string is of the form 'ff<numeral>' then the
 *   returned id is SMT2_SYM_FF_CONSTANT
 * - if the string starts with 'ff' but the rest is not <numeral>, then
 *   the returned if is SMT2_SYM_INVALID_FF_CONSTANT
 */
smt2_symbol_t smt2_string_to_symbol(const char *s, uint32_t n) {
  const keyword_t *kw;
  smt2_symbol_t sym;

  sym = SMT2_SYM_UNKNOWN;
  kw = in_smt2_sym(s, n);
  if (kw == NULL) {
    if (active_symbol[SMT2_SYM_BV_CONSTANT] && sym == SMT2_SYM_UNKNOWN) {
      sym = string_to_bv_constant(s, n);
    }
    if (active_symbol[SMT2_SYM_FF_CONSTANT] && sym == SMT2_SYM_UNKNOWN) {
      sym = string_to_ff_constant(s, n);
    }
  } else if (active_symbol[kw->tk]) {
    sym = kw->tk;
  }

  return sym;
}


/*
 * Check whether a symbol should be printed with quotes | .. |
 * - return false if s is a simple symbol (as defined in the SMT-LIB standard)
 * - return true if s contains spaces or other character:
 *
 * A simple symbol is a sequence of the following characters:
 * - digits (in ASCII): '0' to '9
 * - letters in ASCII: 'a' to 'z' and 'A' to 'Z'
 * - other characters:  ~ ! @ $ % ^ & * _ - + < > . ? /
 */
bool symbol_needs_quotes(const char *s) {
  int c;

  c = *s++;
  if (c == '\0') {
    return true; // empty symbol
  }

  do {
    if (!issimple(c)) {
      return true;
    }
    c = *s ++;
  } while (c != '\0');

  return false;
}

