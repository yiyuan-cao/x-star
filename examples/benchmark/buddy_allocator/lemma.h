#ifndef PROOF_LEMMA_H
#define PROOF_LEMMA_H

#include "cstar.h"
#include "def.h"

extern thm pg2order_axiom;
extern thm buddy2order_axiom;
extern thm pool2max_order_axiom;
void point_to_axioms();
thm point_to_handler(thm ent, thm axiom, term p, term pv);

thm rest_nth();
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
thm merge_head_body_axiom();
thm break_spa_at_i(term spa, thm i_l_len, thm len, thm st_ed);

#endif