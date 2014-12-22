Basic API Usage
===============

.. highlight:: c

The Yices distribution includes a few example source files that
illustrate basic use of the Yices library. The code fragments in this
section are from file :file:`examples/example1.c`. This file shows how
to initialize Yices, construct and print terms, create a context and
assert formulas, and build and query a model when a context is
satisfiable.

Global Initialization
---------------------

Before doing anything with Yices, make sure to initializa all internal
data structures by calling function :c:func:`yices_init`. To avoid
memory leaks, you should also call :c:func:`yices_exit` at the end of
your code to free all the memory that Yices has allocated internally.

Here is the corresponding code from :file:`examples/example1.c`::

  int main(void) {
     yices_init();    // Always call this first
     simple_test();
     yices_exit();    // Cleanup 
     return 0;
  }


Type and Term Construction
--------------------------

The following code fragment builds two uninterpreted terms ``x`` and ``y`` or type ``int``::

   type_t int_type = yices_int_type();
   term_t x = yices_new_uninterpreted_term(int_type);
   term_t y = yices_new_uninterpreted_term(int_type);

In Yices, the type and term constructors return objects of type
:c:type:`type_t` and :c:type:`term_t`, respectively. A global variable
is constructed using function
:c:func:`yices_new_uninterpreted_term`.

It is possible to assign a name to any term by calling
:c:func:`yices_set_term_name`.  Since we want to print terms, it
makes sense to give a name to both the terms ``x`` and ``y``::

   yices_set_term_name(x, "x");
   yices_set_term_name(y, "y");

This has two effects:

  1. The pretty printer will use the names ``"x"`` and ``"y"`` when
     printing these two terms. Otherwise, it would use construct names
     such ``"t!3"`` and ``"t!4"``.

  2. The symbol table will map the strings ``"x"`` and ``"y"`` to the
     terms ``x`` and ``y``, respectively.

We can now build more complex term by using constructors such as 
:c:func:`yices_arith_geq0_atom` and :c:func:`yices_and3`::

   term_t f = yices_and3(yices_arith_geq0_atom(x),
                         yices_arith_geq0_atom(y),
                         yices_arith_eq_atom(yices_add(x, y), yices_int32(100)));

The resulting term ``f`` is the formula ``(x>=0 and y>=0 and x+y=10)``. An alternative 
approach is to parse a string::

   term_t f_var = yices_parse_term("(and (>= x 0) (>= y 0) (= (+ x y) 100))");

The input to :c:func:`yices_parse_term` must be an expression in the
Yices syntax (see :ref:`yices_language`). Because we have assigned
names to the terms ``x`` and ``y``, the parser interprets the two
symbols ``"x"`` and ``"y"`` by relying on the symbol table.


Pretty Printing
---------------

Here is a simple function for printing a term on standard output::

  static void print_term(term_t term) {
    int32_t code;

    code = yices_pp_term(stdout, term, 80, 20, 0);
     if (code < 0) {
       // An error occurred
       fprintf(stderr, "Error in print_term: ");
       yices_print_error(stderr);
       exit(1);
    }
  }

This uses the pretty-printing function :c:func:`yices_pp_term`. The
first argument to this function is the output file (here we use
``stdout``).  The second argument is the term to print. The other
three parameters define the pretty-printing area (in this example, a
rectangle of 80 columns and 70 lines).

The example also illustrates the use of the error-reporting functions.
Most functions in the API return a negative number, or another special
value, to report an error. An internal data structure stores an error
code and other diagnostic information about the most recent
error. Function :c:func:`yices_print_error` reads this data and
prints an error message.


Building a Context and Checking Satisfiability
----------------------------------------------

To check whether formula ``f`` is satisfiable, we create a fresh
context, assert ``f`` in this context, then call function :c:func:`yices_check_context`::

  context_t *ctx = yices_new_context(NULL);
  code = yices_assert_formula(ctx, f);
  if (code < 0) {
    fprintf(stderr, "Assert failed: code = %"PRId32", error = %"PRId32"\n",
            code, yices_error_code());
    yices_print_error(stderr);
  }

  switch (yices_check_context(ctx, NULL)) {
  case STATUS_SAT:
    printf("The formula is satisfiable\n");
    ...
    break;

  case STATUS_UNSAT:
    printf("The formula is not satisfiable\n");
    break;

  case STATUS_UNKNOWN:
    printf("The status is unknown\n");
    break;

  case STATUS_IDLE:
  case STATUS_SEARCHING:
  case STATUS_INTERRUPTED:
  case STATUS_ERROR:
    fprintf(stderr, "Error in check_context\n");
    yices_print_error(stderr);
    break;
  }
  yices_free_context(ctx);

Function :c:func:`yices_new_context` creates a new context and
function :c:func:`yices_assert_formula` asserts a formula in the
context. Function :c:func:`yices_check_context` returns a code of type
:c:type:`smt_status_t`:
 
   - :c:data:`STATUS_SAT` means that the context is satisfiable.

     One can then construct and examine a model from the context.

   - :c:data:`STATUS_UNSAT` means that the context is not satisfiable.

   - :c:data:`STATUS_UNKNOWN` means that the context's status could
     not be determined.

Other codes are error conditions.

Once the context ``ctx`` is no longer needed, we delete it using :c:func:`yices_free_context`.



Building and Querying a Model
-----------------------------

If :c:func:`yices_check_context` returns :c:data:`STATUS_SAT` (or
:c:data:`STATUS_UNKNOWN`), we can construct a model of the
asserted formulas and print it::

  model_t* model = yices_get_model(ctx, true);
  if (model == NULL) {
    fprintf(stderr, "Error in get_model\n");
    yices_print_error(stderr);
  } else {
    printf("Model\n");
    code = yices_pp_model(stdout, model, 80, 4, 0);

Then, we can query the model to get the value of the two terms ``x`` and ``y``::

    int32_t v;
    // get the value of x
    code = yices_get_int32_value(model, x, &v);
    if (code < 0) {
      printf(stderr, "Error in get_int32_value for 'x'\n");
      yices_print_error(stderr);
    } else {
      printf("Value of x = %"PRId32"\n", v);
    }

    // get the value of y
    code = yices_get_int32_value(model, y, &v);
    if (code < 0) {
      fprintf(stderr, "Error in get_int32_value for 'y'\n");
      yices_print_error(stderr);
    } else {
      printf("Value of y = %"PRId32"\n", v);
    }

    yices_free_model(model);

In this case, the values of ``x`` and ``y`` are small integers that
fit in the 32bit integer variable ``v``, so we use function
:c:func:`yices_get_int32_value`. Other functions are available to
extract large integer values (either using 64bit integers or GMP
numbers).

Once we are done with the model, we delete it by calling
:c:func:`yices_free_model`.


Running this Example
--------------------

The source file for this example can be downloaded :download:`here <_static/example1.c>`.
It can be compiled as follows::

  gcc example1.c -o example1 -lyices

Then running this example should produce something like this::

  Formula f
  (and (>= x 0) (>= y 0) (= (+ -100 x y) 0))
  Formula f_var
  (and (>= x 0) (>= y 0) (= (+ -100 x y) 0))
  The formula is satisfiable
  Model
  (= x 0)
  (= y 100)
  Value of x = 0
  Value of y = 100




