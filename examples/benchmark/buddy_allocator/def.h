#ifndef PROOF_DEF_H
#define PROOF_DEF_H

#include "cstar.h"

extern thm LENGTH;
extern thm num_CASES;
extern thm num_INDUCTION;
extern thm list_INDUCT;

extern thm hentail_refl;
extern thm hentail_trans;
extern thm hentail_antisym;
extern thm hsep_assoc;
extern thm hsep_comm;
extern thm hsep_hemp_left;
extern thm hsep_hemp_right;
extern thm hwand_hsep_adjoint;
extern thm hsep_cancel_left;
extern thm hsep_cancel_right;
extern thm hsep_monotone;
extern thm htrue_def;
extern thm hfalse_def;
extern thm htrue_intro;
extern thm hfalse_elim;
extern thm htrue_elim_left;
extern thm hfalse_absorb_left;
extern thm himpl_hand_adjoint;
extern thm hexists_intro;
extern thm hpure_intro;
extern thm hpure_elim;
extern thm hand_assoc;
extern thm hand_comm;
extern thm hsep_hpure_left;
extern thm hsep_hpure_right;
extern thm hfact_def;
extern thm hfact_hpure;
extern thm hfact_intro;
extern thm hfact_elim;
extern thm hsep_hfact_left;
extern thm hsep_hfact_right;
extern thm hexists_monotone;
extern thm hentail_sym_left;

extern thm PTR_SIZE_DEF;
extern thm LIST_HEAD_SIZE_DEF;
extern thm PAGE_SIZE_DEF;
extern thm MAX_ORDER_DEF;
extern thm NO_ORDER_DEF;
extern thm RANGE_LIM_DEF;
extern thm REF_LIM_DEF;
extern thm PTR_LIM_DEF;
extern thm START_DEF;
extern thm END_DEF;
extern thm LEN_DEF;
extern thm MAX_ORDER__DEF;
extern thm OFF_SET_DEF;

extern thm PH2VI_DEF;
extern thm VI2PH_DEF;
extern thm PH2ID_DEF;
extern thm VI2ID_DEF;
extern thm ID2PH_DEF;
extern thm ID2VI_DEF;
extern thm ID2I_DEF;
extern thm VI2I_DEF;
extern thm I2ID_DEF;
extern thm I2VI_DEF;
extern thm REF_DEF;
extern thm ORD_DEF;
extern thm NXT_DEF;
extern thm PRV_DEF;
extern thm STORE_UNDEF_ARRAY_DEF;
extern thm STORE_ZERO_ARRAY_DEF;
extern thm STORE_PAGEINFO_ARRAY_DEF;
extern thm PURE_CONST_DEF;
extern thm POOL_CONST_DEF;
extern thm DLIST_HEAD_REPR_DEF;
extern thm NTH_DEF;
extern thm MODIFIED_DEF;
extern thm TAKE_DEF;
extern thm REST_DEF;
extern thm FREE_1ST_DEF;
extern thm IS_FREE_1ST_DEF;
extern thm FREE_AREA_REPR_DEF;
extern thm FREE_AREA_HEAD_REPR_DEF;
extern thm DLIST_NODE_ONE_DEF;
extern thm DLIST_NODE_DEF;
extern thm DLIST_HEAD_HALF_DEF;
extern thm DLIST_HEAD_ONE_DEF;
extern thm DLIST_HEAD_DEF;
extern thm TOTAL_REPR_DEF;

void get_theorems();
void definitions();

#endif