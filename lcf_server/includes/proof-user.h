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

#endif