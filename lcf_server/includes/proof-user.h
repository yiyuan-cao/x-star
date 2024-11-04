#ifndef PROOF_USER_H
#define PROOF_USER_H

#include "proof-kernel.h"
#include <gc.h>

typedef const struct Gc_Term *term;
typedef const struct Gc_Theorem *thm;
typedef const struct Gc_Conversion *conv;
typedef const struct IndType *indtype;
typedef const struct IndDef *inddef;

#define CHECK_ERROR()                                                          \
  do {                                                                         \
    if (cst_last_error() != NULL) {                                            \
      printf("failed: %s (%s:%d)", cst_last_error(), __FILE__, __LINE__);    \
      return 1;                                                                \
    }                                                                          \
  } while (0)

#define GRAY "\e[1;30m"
#define END "\e[0m"

typedef struct rewrites_item {
  term tm;
  thm th;
} rewrites_item;

static indtype slval;
static thm himpl_refl_axiom;
static thm himpl_trans_axiom;
static thm himpl_antisym_axiom;
static thm star_assoc_axiom;
static thm star_comm_axiom;
static thm star_monotone_axiom;
static thm star_neutral_l_axiom;
static thm star_exists_axiom;
static thm star_forall_axiom;
static thm frame_rule_l_axiom;
static thm single_not_null_axiom;
static thm single_conflict_axiom;
static thm field_not_null_axiom;
static thm field_conflict_axiom;
static thm undefpointsto_def_axiom;
static thm pure_l_axiom;
static thm pure_r_axiom;
static thm pure_distri_axiom;
static thm exists_l_axiom;
static thm exists_r_axiom;
static thm exists_monotone_axiom;
static thm forall_l_axiom;
static thm forall_r_axiom;
static thm forall_monotone_axiom;
static thm false_explosion_axiom;
static thm false_elim_l_axiom;
static thm false_def_axiom;
static thm himpl_sym_l_axiom;
static thm pure_contradiction_axiom;

// Added temporarily
static thm disj_split_axiom;
static thm int_le_axiom;

/** Term destructor/constructor. */

bool is_bin_op(term);
term dest_bin_fst_comb(term);
term dest_bin_snd_comb(term);
term dest_bin_op(term);
bool is_un_op(term);
term dest_un_comb(term);
term dest_un_op(term);

/** Additional User Interface for Pure Proof. */

thm rewrite_thm(thm, thm);
thm rewrite_refl(thm, term, term);
thm rewrites(rewrites_item[], int);
thm gens(term[], int, thm);
thm induction_with_goal(indtype, thm, thm, term);
thm induction(indtype, thm, thm);

/** Separation Logic Property as Axiom. */
void sl_init();

// Entailment defines an order on the set of heap predicates
thm himpl_refl(term);
thm himpl_trans(thm, thm);
thm himpl_antisym(thm, thm);

thm himpl_sym_l(thm);
thm himpl_sym_r(thm);

// Fundamental properties of the [sepconj]
thm star_assoc(term, term, term);
thm star_comm(term, term);
thm star_monotone(thm, thm);
thm star_neutral_l(term);
thm star_neutral_r(term);
thm star_exists(term, term);
thm star_forall(term, term);
thm frame_rule_l(thm, term);
thm frame_rule_r(thm, term);

// Properties of [pure]
thm pure_l(thm);
thm pure_r(thm, thm);
thm pure_distri(term, term);

// Properties of [hexists]
thm exists_l(thm);
thm exists_r(thm, term, term);
thm exists_r_aux (thm, term, term, term);
thm exists_monotone(thm);

// Properties of [hforall]
thm forall_l(thm, term, term);
thm forall_r(thm);
thm forall_monotone(thm);

// Properties of the singleton heap predicate
thm single_not_null(term, term);
thm single_conflict(term, term, term);
thm undefpointsto_def(term);

// Properties of field heap predicate
thm field_not_null(term, term, term);
thm field_conflict(term, term, term, term);

// Properties of [hfalse]
thm hfalse_explosion(term);
thm hfalse_elim_l(term);
thm hfalse_elim_r(term);
thm hfalse_def(void);

/** Additional Pure Fact Currently as Axiom. */
thm pure_contradiction(term);

/** Additional User Interface for Separation Logic Entailment Proof.*/
thm entails(rewrites_item[], int);
thm hfalse_contradiction(thm, term);
thm hfalse_antisym(thm th);
thm fieldpointer_invalid(term, term);

/*  Logic Properties  */
thm conj_comm_prop();
thm conj_comm(term, term);
thm conj_assoc_prop();
thm conj_assoc(term, term, term);
thm eq_conj_l_prop();
thm eq_conj_l(term, term, term);
thm eq_conj_r_prop();
thm eq_conj_r(term, term, term);
thm impl_conj_l_prop();
thm impl_conj_l(term, term, term);
thm impl_conj_r_prop();
thm impl_conj_r(term, term, term);
thm impl_trans_prop();
thm impl_trans(thm, thm);
thm conjunctn(thm, int);
/*  Added temporarily  */
thm disj_split(term);
thm int_le(term, term);

#endif