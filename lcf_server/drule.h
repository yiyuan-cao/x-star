#ifndef PROOF_DRULE_H
#define PROOF_DRULE_H

#include "proof-user.h"
#include "proof-conv.h"
#include "def.h"
#include <stdio.h>
#include <string.h>

extern thm disconj1;
extern thm impl_conj_mono_thm;
extern thm impl_disj_mono_thm;
extern thm impl_if_mono_thm;
extern thm hfact_true;
extern thm sepand_t;
extern thm sepand_f;
extern thm sepconj_f;
void load_axioms();

thm give_up_fact();
thm sepeq2sepent();

/* pure logic */
thm impl_conj_mono(thm, thm);
thm impl_disj_mono(thm, thm);
thm impl_if_mono(term, thm, thm);
thm merge_disj_cases(term, thm, thm);
thm abs_term(term, term);

/* separation logic */
thm eq2ent(thm);
thm htrans(thm, thm);
thm htrans_list(thm[]);

/* rewrite related */
thm simp(thm);
term rewrite_term(term, term);
thm rewrite_after(thm, thm);
thm rewrite_after_list(thm[], thm);
thm rewrite_after_term_list(thm[], term);
thm rewrite_after_ent(thm, thm);

/* state handler */
thm create_trans_auto(term[], term[], thm[], thm[]);
thm hexists_intro_auto(thm, term);
thm give_up_facts(term[], thm);

/* other helpers */
void show_induct_goal(term, term, thm);
bool compare_hprop(term, term);

#endif