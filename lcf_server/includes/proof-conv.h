#include <proof-user.h>

thm simp(thm th);
thm trans_list(thm thl[]);
thm once_rewrite_list(thm thl[], term tm);
thm rewrite_list(thm thl[], term tm);
thm rewrite_rhs(thm th1, thm th2);
thm rewrite_list_rhs(thm thl[], thm th);
term rewrite_term(term th, term tm);
thm eq2ent(thm th);
thm rewrite_after_ent(thm th1, thm th2);
thm once_rewrite_rule_list(thm thl[], thm th);
thm rewrite_rule_list(thm thl[], thm th);
thm hent_trans(thm, thm);
thm hentail_trans_list(thm thl[]);
thm hentail_trans_auto(thm th1, thm th2);
thm hentail_trans_auto_list(thm thl[]);
thm abs_term(term, term);

term normalize(term septerm);
thm sep_normalize(term septerm);
thm sep_normalize_rule(thm entail);
thm sep_lift(term lft, term septerm);
thm sep_reorder(term lft, term septerm);
thm create_trans_auto(term[], term[], thm[], thm[]);
thm which_implies(term state, thm trans);
thm hfact_auto(term pres[], term posts[], thm helpers[]);
thm hexists_intro_auto(thm, term);
bool compare_hprop(term, term);
thm unfold(term, thm);
thm fold(term, thm);
thm use_fact_rewrite(term, term);
thm use_fact_symm_rewrite(term, term);