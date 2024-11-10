#ifndef PROOF_LEMMA_H
#define PROOF_LEMMA_H

#include "proof-user.h"
#include "def.h"
#include <stdio.h>

extern thm disconj1;
extern thm impl_conj_mono_thm;
extern thm impl_disj_mono_thm;
extern thm impl_if_mono_thm;
extern thm hfact_true;
extern thm sepand_t;
extern thm sepand_f;
extern thm sepconj_f;

extern thm data_at_pg_pre_order_axiom;
extern thm data_at_buddy_v_order_axiom;
extern thm data_at_pg_v_order_axiom;
extern thm data_at_pool_pre_max_order_axiom;
extern thm merge_head_body_axiom;

void load_axioms();

thm impl_conj_mono(thm, thm);
thm impl_disj_mono(thm, thm);
thm impl_if_mono(term, thm, thm);
thm merge_disj_cases(term, thm, thm);

thm sepeq2sepent();
thm htrans(thm, thm);
thm htrans_list(int, thm[]);

thm simp(thm);
term rewrite_term(term, term);
thm rewrite_after(thm, thm);
thm rewrite_after_list(int, thm[], thm);
thm rewrite_after_term_list(int, thm[], term);

void show_induct_goal(term, term, thm);

thm abs_term(term, term);
thm hprop_sepconj(int, term[], int, term[], int, thm[], int, thm[]);

thm break_list_sepconj();
thm breaknth_list_sepconj();
thm break_array_sepconj();
thm modified_nth();
thm modified_mth();
thm modified_taken_restn_lemma();
thm modified_taken();
thm modified_restn();
thm modified_len();
thm filter_inv();
thm far_inv();
thm dn_inv_lemma();
thm dn_inv();
thm dh_inv();
thm far_lemma();
thm far_split();
thm far_merge();
thm store_array_addr();
thm sza_merge_lemma();
thm sza_merge_lemma2();
thm sza_merge();
thm i2id2i();
thm data_at_pg_pre_order(thm);
thm data_at_buddy_v_order(thm);
thm data_at_pg_v_order(thm);
thm data_at_pool_pre_max_order();
thm break_spa_at_i(term, thm, thm, thm);

#endif