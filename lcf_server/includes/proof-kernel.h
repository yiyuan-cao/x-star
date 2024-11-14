#ifndef PROOF_KERNEL_H
#define PROOF_KERNEL_H

#include <stdarg.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>

typedef struct Gc_Conversion Gc_Conversion;

typedef struct Gc_Term Gc_Term;

typedef struct Gc_Theorem Gc_Theorem;

typedef struct Gc_Type Gc_Type;

/**
 * Inductive type.
 */
typedef struct IndType {
  /**
   * The inductive theorem.
   */
  const struct Gc_Theorem *ind;
  /**
   * The recursion theorem.
   */
  const struct Gc_Theorem *rec;
} IndType;

/**
 * Inductive relation.
 */
typedef struct IndDef {
  /**
   * definition.
   */
  const struct Gc_Theorem *def;
  /**
   * inductive rule.
   */
  const struct Gc_Theorem *ind;
  /**
   * cases rule.
   */
  const struct Gc_Theorem *cases;
} IndDef;

/**
 * Initialize the proof kernel.
 *
 * # Returns
 * `0` on success, `-1` on failure.
 */
int cst_init(void);

/**
 * Parse a term from a string.
 *
 * # Parameters
 * - `s`: The string to parse.
 *
 * # Returns
 * A pointer to the parsed term on success, `NULL` on failure.
 */
const struct Gc_Term *parse_term(const char *s);

/**
 * Parse a type from a string.
 *
 * # Parameters
 * - `s`: The string to parse.
 *
 * # Returns
 * A pointer to the parsed type on success, `NULL` on failure.
 */
const struct Gc_Type *parse_type(const char *s);

/**
 * Parse a type from a conversion.
 *
 * # Parameters
 * - `s`: The string to parse.
 *
 * # Returns
 * A pointer to the parsed type on success, `NULL` on failure.
 */
const struct Gc_Conversion *get_conversion(const char *s);

/**
 * Convert a term to a string.
 *
 * # Parameters
 * - `term`: The term to convert.
 *
 * # Returns
 * A pointer to the string on success, `NULL` on failure.
 */
const char *string_of_term(const struct Gc_Term *term);

/**
 * Convert a theorem to a string.
 *
 * # Parameters
 * - `thm`: The theorem to convert.
 *
 * # Returns
 * A pointer to the string on success, `NULL` on failure.
 */
const char *string_of_thm(const struct Gc_Theorem *thm);

/**
 * Equality test on terms.
 *
 * # Parameters
 * - `t1`: The first term.
 * - `t2`: The second term.
 *
 * # Returns
 * `true` on it is equal, `false` on it is not (or failure).
 */
bool equals_term(const struct Gc_Term *t1, const struct Gc_Term *t2);

/**
 * Equality test on theorems.
 *
 * # Parameters
 * - `th1`: The first theorem.
 * - `th2`: The second theorem.
 *
 * # Returns
 * `true` on it is equal, `false` on it is not (or failure).
 */
bool equals_thm(const struct Gc_Theorem *th1, const struct Gc_Theorem *th2);

/**
 * Dump a Coq axiom.
 *
 * # Parameters
 * - `name`: The name of the axiom.
 * - `th`: The theorem to dump.
 *
 * # Returns
 * A pointer to the string on success, `NULL` on failure.
 */
const char *dump_coq_axiom(const char *name, const struct Gc_Theorem *th);

/**
 * Theorem: A |- A
 *
 * # Parameters
 * - `term`: The term to assume.
 *
 * # Returns
 * A pointer to the theorem on success, `NULL` on failure.
 */
const struct Gc_Theorem *assume(const struct Gc_Term *term);

/**
 * Transitivity of the theorem.
 *
 * ```text
 * A1 |- a = b  A2 |- b = c
 * -------------------------
 * A1, A2 |- a = c
 * ```
 *
 * # Parameters
 * - `th1`: The first theorem.
 * - `th2`: The second theorem.
 *
 * # Returns
 * A pointer to the theorem on success, `NULL` on failure.
 */
const struct Gc_Theorem *trans(const struct Gc_Theorem *th1, const struct Gc_Theorem *th2);

/**
 * Reflexivity.
 *
 * ```text
 * ----------
 * A |- a = a
 * ```
 *
 * # Parameters
 * - `tm`: The term.
 *
 * # Returns
 * A pointer to the theorem on success, `NULL` on failure.
 */
const struct Gc_Theorem *refl(const struct Gc_Term *tm);

/**
 * Discharge an assumption.
 *
 * ```text
 *      A |- t
 * ------------------
 * A - {u} |- u ==> t
 * ```
 *
 * # Parameters
 * - `th`: The theorem to discharge.
 * - `tm`: The term to discharge.
 *
 * # Returns
 * A pointer to the theorem on success, `NULL` on failure.
 */
const struct Gc_Theorem *disch(const struct Gc_Theorem *th, const struct Gc_Term *tm);

/**
 * Undischarges the antecedent of an implicative theorem.
 *
 * ```text
 * A |- t1 ==> t2
 * --------------
 *   A, t1 |- t2
 * ```
 * # Parameters
 * - `th`: The theorem to undischarge.
 *
 * # Returns
 * A pointer to the theorem on success, `NULL` on failure.
 */
const struct Gc_Theorem *undisch(const struct Gc_Theorem *th);

/**
 * Generalize a free term in a theorem.
 *
 * ```text
 * A |- t
 * -------     (x not free in A)
 * A |- !x. t
 * ```
 *
 * # Parameters
 * - `tm`: The term to generalize.
 * - `th`: The theorem to generalize.
 *
 * # Returns
 * A pointer to the theorem on success, `NULL` on failure.
 */
const struct Gc_Theorem *gen(const struct Gc_Term *tm, const struct Gc_Theorem *th);

/**
 * Specializes the conclusion of a theorem with its own quantified variables.
 *
 * ```text
 * A |- !x1...xn. t
 * -------------------------
 * A |- t[x1'/x1]...[xn'/xn]
 * ```
 *
 * # Parameters
 * - `th`: The theorem to specialize.
 *
 * # Returns
 * A pointer to the theorem on success, `NULL` on failure.
 */
const struct Gc_Theorem *spec_all(const struct Gc_Theorem *th);

/**
 * Specializes the conclusion of a theorem.
 *
 * ```text
 * A |- !x. t
 * ----------- SPEC `u`
 * A |- t[u/x]
 * ```
 *
 * # Parameters
 * - `tm`: The variable to be specialized.
 * - `th`: The theorem to specialize.
 *
 * # Returns
 * A pointer to the theorem on success, `NULL` on failure.
 */
const struct Gc_Theorem *spec(const struct Gc_Term *tm, const struct Gc_Theorem *th);

/**
 * Modus ponens.
 *
 * ```text
 * A1 |- t1 ==> t2   A2 |- t1
 * --------------------------
 * A1, A2 |- t2
 * ```
 *
 * # Parameters
 * - `th1`: The first theorem.
 * - `th2`: The second theorem.
 *
 * # Returns
 * A pointer to the theorem on success, `NULL` on failure.
 */
const struct Gc_Theorem *mp(const struct Gc_Theorem *th1, const struct Gc_Theorem *th2);

/**
 * Equality version of the Modus Ponens rule.
 *
 * ```text
 * A1 |- t1 <=> t2   A2 |- t1'
 * ---------------------------
 *       A1 u A2 |- t2
 * ```
 *
 * # Parameters
 * - `th1`: The first theorem.
 * - `th2`: The second theorem.
 *
 * # Returns
 * A pointer to the theorem on success, `NULL` on failure.
 */
const struct Gc_Theorem *eq_mp(const struct Gc_Theorem *th1, const struct Gc_Theorem *th2);

/**
 * Conjunction.
 *
 * ```text
 * A1 |- t1  A2 |- t2
 * ------------------
 * A1, A2 |- t1 /\ t2
 * ```
 *
 * # Parameters
 * - `th1`: The first theorem.
 * - `th2`: The second theorem.
 *
 * # Returns
 * A pointer to the theorem on success, `NULL` on failure.
 */
const struct Gc_Theorem *conjunct(const struct Gc_Theorem *th1, const struct Gc_Theorem *th2);

/**
 * Extracts left conjunct of theorem.
 *
 * ```text
 * A |- t1 /\ t2
 * -------------
 *    A |- t1
 * ```
 *
 * # Parameters
 * - `th`: The theorem.
 *
 * # Returns
 * A pointer to the theorem on success, `NULL` on failure.
 */
const struct Gc_Theorem *conjunct1(const struct Gc_Theorem *th);

/**
 * Extracts right conjunct of theorem.
 *
 * ```text
 * A |- t1 /\ t2
 * -------------
 *    A |- t2
 * ```
 *
 * # Parameters
 * - `th`: The theorem.
 *
 * # Returns
 * A pointer to the theorem on success, `NULL` on failure.
 */
const struct Gc_Theorem *conjunct2(const struct Gc_Theorem *th);

/**
 * Symmetry.
 *
 * ```text
 * A |- t1 = t2
 * ------------
 * A |- t2 = t1
 * ```
 *
 * # Parameters
 * - `th`: The equation theorem.
 *
 * # Returns
 * A pointer to the theorem on success, `NULL` on failure.
 */
const struct Gc_Theorem *symm(const struct Gc_Theorem *th);

/**
 * Eliminates disjunction by cases.
 *
 * ```text
 * A |- t1 \/ t2   A1 |- t   A2 |- t
 * ----------------------------------
 * A u (A1 - {t1}) u (A2 - {t2}) |- t
 * ```
 *
 * # Parameters
 * - `th1`: The first theorem.
 * - `th2`: The second theorem.
 * - `th3`: The third theorem.
 *
 * # Returns
 * A pointer to the theorem on success, `NULL` on failure.
 */
const struct Gc_Theorem *disj_cases(const struct Gc_Theorem *th1,
                                    const struct Gc_Theorem *th2,
                                    const struct Gc_Theorem *th3);

/**
 * Deduces logical equivalence from deduction in both directions.
 *
 * ```text
 *      A |- p        B |- q
 * --------------------------------
 * (A - {q}) u (B - {p}) |- p <=> q
 * ```
 *
 * # Parameters
 * - `th1`: The first theorem
 * - `th2`: The second theorem
 *
 * # Returns
 * A pointer to the theorem on success, `NULL` on failure.
 */
const struct Gc_Theorem *deduct_antisym(const struct Gc_Theorem *th1, const struct Gc_Theorem *th2);

/**
 * Existentially quantifies a hypothesis of a theorem.
 *
 * ```text
 * A |- t   `x` is not free in `A |- t`
 * ------------------------------------ CHOOSE `x` th
 *            A |- ?x. t
 * ```
 * # Parameters
 * - `tm`: The term
 * - `th`: The theorem
 *
 * # Returns
 * A pointer to the theorem on success, `NULL` on failure.
 */
const struct Gc_Theorem *choose(const struct Gc_Term *tm, const struct Gc_Theorem *th);

/**
 * Proves equality of alpha-equivalent terms.
 */
const struct Gc_Theorem *alpha(const struct Gc_Term *t1, const struct Gc_Term *t2);

/**
 * Performs a simple beta-conversion.
 */
const struct Gc_Theorem *beta_conv(const struct Gc_Term *tm);

/**
 * Beta-reduces all the beta-redexes in the conclusion of a theorem.
 */
const struct Gc_Theorem *beta_rule(const struct Gc_Theorem *th);

/**
 * Define an inductive type.
 *
 * # Parameters
 * - `name`: The name of the inductive type.
 * - `variants`: The variants of the inductive type.
 *
 * # Returns
 * Two theorems on success, `NULL` on failure.
 *
 */
const struct IndType *define_type(const char *tm);

/**
 * Define a new constant or function.
 *
 * # Parameters
 * - `tm`: The term to define.
 *
 * # Returns
 * A theorem on success, `NULL` on failure.
 */
const struct Gc_Theorem *define(const struct Gc_Term *tm);

/**
 * Produce cases theorem for an inductive type.
 */
const struct Gc_Theorem *cases(const char *s);

/**
 * Produce distinctness theorem for an inductive type.
 */
const struct Gc_Theorem *distinctness(const char *s);

/**
 * Uses an instance of a given equation to rewrite a term.
 *
 * # Parameters
 * - `th`: The theorem to use for rewriting.
 * - `tm`: The term to rewrite.
 *
 * # Returns
 * A theorem on success, `NULL` on failure.
 */
const struct Gc_Theorem *rewrite(const struct Gc_Theorem *th, const struct Gc_Term *tm);

/**
 * Uses an instance of a given equation to rewrite a term.
 *
 * # Parameters
 * - `th`: The theorem to use for rewriting.
 * - `tm`: The term to rewrite.
 *
 * # Returns
 * A theorem on success, `NULL` on failure.
 */
const struct Gc_Theorem *pure_rewrite(const struct Gc_Theorem *th, const struct Gc_Term *tm);

/**
 * Uses an instance of a given equation to rewrite a theorem.
 *
 * # Parameter
 * - `th`: The theorem to use for rewriting.
 * - `t`: The theorem to rewrite.
 *
 * # Returns
 * A theorem on success, `NULL` on failure.
 */
const struct Gc_Theorem *rewrite_rule(const struct Gc_Theorem *th, const struct Gc_Theorem *t);

/**
 * Uses an instance of a given equation to rewrite a theorem.
 *
 * # Parameter
 * - `th`: The theorem to use for rewriting.
 * - `t`: The theorem to rewrite.
 *
 * # Returns
 * A theorem on success, `NULL` on failure.
 */
const struct Gc_Theorem *pure_rewrite_rule(const struct Gc_Theorem *th, const struct Gc_Theorem *t);

/**
 * Uses an instance of a given equation to rewrite a term only once.
 *
 * # Parameters
 * - `th`: The theorem to use for rewriting.
 * - `tm`: The term to rewrite.
 *
 * # Returns
 * A theorem on success, `NULL` on failure.
 */
const struct Gc_Theorem *once_rewrite(const struct Gc_Theorem *th, const struct Gc_Term *tm);

/**
 * Uses an instance of a given equation to rewrite a theorem only once.
 *
 * # Parameter
 * - `th`: The theorem to use for rewriting.
 * - `t`: The theorem to rewrite.
 *
 * # Returns
 * A theorem on success, `NULL` on failure.
 */
const struct Gc_Theorem *once_rewrite_rule(const struct Gc_Theorem *th, const struct Gc_Theorem *t);

/**
 * Uses an instance of a given equation to rewrite a term only once.
 *
 * # Parameters
 * - `th`: The theorem to use for rewriting.
 * - `tm`: The term to rewrite.
 *
 * # Returns
 * A theorem on success, `NULL` on failure.
 */
const struct Gc_Theorem *pure_once_rewrite(const struct Gc_Theorem *th, const struct Gc_Term *tm);

/**
 * Uses an instance of a given equation to rewrite a theorem only once.
 *
 * # Parameter
 * - `th`: The theorem to use for rewriting.
 * - `t`: The theorem to rewrite.
 *
 * # Returns
 * A theorem on success, `NULL` on failure.
 */
const struct Gc_Theorem *pure_once_rewrite_rule(const struct Gc_Theorem *th,
                                                const struct Gc_Theorem *t);

/**
 * Instantiation of induction principle.
 *
 * # Parameters
 * - `th`: The induction principle theorem.
 * - `tm1`: The first term.
 * - `tm2`: The second term.
 *
 * # Returns
 * A theorem on success, `NULL` on failure.
 */
const struct Gc_Theorem *induction_aux(const struct Gc_Theorem *th,
                                       const struct Gc_Term *tm1,
                                       const struct Gc_Term *tm2);

/**
 * Substitute terms for other terms inside a term.
 *
 * # Parameters
 * - `tm1`: first term
 * - `tm2`: second term
 * - `tm`: term to be substituted
 *
 * # Returns
 *   a term replacing free instances of each term `tm2` inside `tm` with the corresponding `tm1`.
 */
const struct Gc_Term *subst(const struct Gc_Term *tm1,
                            const struct Gc_Term *tm2,
                            const struct Gc_Term *tm);

/**
 * Tests whether a variable (or constant) occurs free in a term.
 */
bool free_in(const struct Gc_Term *v, const struct Gc_Term *tm);

/**
 * Check if a term is an application.
 *
 * # Parameters
 * - `tm`: The term to check.
 *
 * # Returns
 * `true` on it is an application, `false` on it is not (or failure).
 */
bool is_comb(const struct Gc_Term *tm);

/**
 * Check if a term is an application of the given binary operator.
 *
 * # Parameters
 * - `op`: The binary operator.
 * - `tm`: The term to check.
 *
 * # Returns
 * `true` on it is an application of binary operator `op`, `false` on it is not (or failure).
 */
bool is_binop(const struct Gc_Term *op, const struct Gc_Term *tm);

/**
 * Check if a term is a binder construct with named constant.
 *
 * # Parameters
 * - `s`: The name of binder.
 * - `tm`: The term to check.
 *
 * # Returns
 * `true` on it is a binder construct with name `s`, `false` on it is not (or failure).
 */
bool is_binder(const char *s, const struct Gc_Term *tm);

/**
 * First element of the destruct of an application.
 *
 * # Parameters
 * - `tm`: The term to destruct
 *
 * # Returns
 * A term on success, `NULL` on failure.
 */
const struct Gc_Term *fst_comb(const struct Gc_Term *tm);

/**
 * Second element of the destruct of an application.
 *
 * # Parameters
 * - `tm`: The term to destruct
 *
 * # Returns
 * A term on success, `NULL` on failure.
 */
const struct Gc_Term *snd_comb(const struct Gc_Term *tm);

/**
 * First element of the destruct of an equation.
 *
 * # Parameters
 * - `tm`: The term to destruct
 *
 * # Returns
 * A term on success, `NULL` on failure.
 */
const struct Gc_Term *antecedent(const struct Gc_Term *tm);

/**
 * Second element of the destruct of an equation.
 *
 * # Parameters
 * - `tm`: The term to destruct
 *
 * # Returns
 * A term on success, `NULL` on failure.
 */
const struct Gc_Term *consequent(const struct Gc_Term *tm);

/**
 * First element of the destruct of an application of the given binary operator.
 *
 * # Parameters
 * - `op`: The given binary operator
 * - `tm`: The term to destruct
 *
 * # Returns
 * A term on success, `NULL` on failure.
 */
const struct Gc_Term *fst_binop(const struct Gc_Term *op, const struct Gc_Term *tm);

/**
 * Second element of the destruct of an application of the given binary operator.
 *
 * # Parameters
 * - `op`: The given binary operator
 * - `tm`: The term to destruct
 *
 * # Returns
 * A term on success, `NULL` on failure.
 */
const struct Gc_Term *snd_binop(const struct Gc_Term *op, const struct Gc_Term *tm);

/**
 * Variable of the destruct of a binder construct.
 *
 * # Parameters
 * - `s`: The name of binder
 * - `tm`: The term to destruct
 *
 * # Returns
 * A term on success, `NULL` on failure.
 */
const struct Gc_Term *binder_var(const char *s, const struct Gc_Term *tm);

/**
 * Body of the destruct of a binder construct.
 *
 * # Parameters
 * - `s`: The name of binder
 * - `tm`: The term to destruct
 *
 * # Returns
 * A term on success, `NULL` on failure.
 */
const struct Gc_Term *binder_body(const char *s, const struct Gc_Term *tm);

/**
 * Construct a abstraction.
 *
 * # Parametes
 * - `tm1`: The first term
 * - `tm2`: The second term
 *
 * # Returns
 * A term on success, `NULL` on failure.
 */
const struct Gc_Term *mk_abs(const struct Gc_Term *tm1, const struct Gc_Term *tm2);

/**
 * Construct a combination.
 *
 * # Parametes
 * - `tm1`: The first term
 * - `tm2`: The second term
 *
 * # Returns
 * A term on success, `NULL` on failure.
 */
const struct Gc_Term *mk_comb(const struct Gc_Term *tm1, const struct Gc_Term *tm2);

/**
 * Conclusion of a theorem.
 *
 * # Parameters
 * - `th`: The theorem
 *
 * # Returns
 * A term on success, `NULL` on failure.
 */
const struct Gc_Term *conclusion(const struct Gc_Theorem *th);

/**
 * Return one hypothesis of a theorem.
 *
 * # Parameters
 * - `th`: The theorem
 *
 * # Returns
 * A term on success, `NULL` on failure.
 */
const struct Gc_Term *hypth(const struct Gc_Theorem *th);

/**
 * Create a new type.
 *
 * # Parameters
 * - `name`: The name of the type.
 *
 * # Returns
 * `0` on success, `-1` on failure.
 */
int new_type(const char *name, uint32_t arity);

/**
 * Declare a new constant.
 *
 * # Parameters
 * - `name`: The name of the constant.
 * - `ty`: The type of the constant.
 *
 * # Returns
 * `0` on success, `-1` on failure.
 */
int new_constant(const char *name, const struct Gc_Type *ty);

/**
 * Set up a new axiom.
 *
 * # Parameters
 * - `tm`: The term of the axiom.
 *
 * # Returns
 * A theorem on success, `NULL` on failure.
 */
const struct Gc_Theorem *new_axiom(const struct Gc_Term *tm);

/**
 * Define a relation or family of relations inductively.
 */
const struct IndDef *new_inductive_definition(const struct Gc_Term *tm);

/**
 * Proves a propositional tautology.
 */
const struct Gc_Theorem *taut(const struct Gc_Term *tm);

/**
 * Automatically proves natural number arithmetic theorems.
 */
const struct Gc_Theorem *arith_rule(const struct Gc_Term *tm);

/**
 * Proves integer theorems needing basic rearrangement and linear inequality reasoning only.
 */
const struct Gc_Theorem *int_arith(const struct Gc_Term *tm);

/**
 * Get a theorem from the search database.
 */
const struct Gc_Theorem *get_theorem(const char *name);

/**
 * Applies a conversion to the operand of an application.
 */
const struct Gc_Conversion *rand_conv(const struct Gc_Conversion *conv);

/**
 * Applies a conversion.
 */
const struct Gc_Theorem *apply_conv(const struct Gc_Conversion *conv, const struct Gc_Term *tm);

/**
 * Get the last error message.
 *
 * If no error has been set, this function returns `NULL`.
 *
 * The returned string is GC-managed and should not be freed.
 */
const char *cst_last_error(void);

#endif  /* PROOF_KERNEL_H */
