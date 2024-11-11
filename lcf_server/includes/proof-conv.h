#include <proof-user.h>

thm trans_list(thm thl[]);
thm rewrite_list(thm thl[], term tm);
thm rewrite_rule_list(thm thl[], thm th);
thm hentail_trans_list(thm thl[]);
thm hentail_trans_auto(thm th1, thm th2);
thm hentail_trans_auto_list(thm thl[]);

term normalize(term septerm);
thm sep_normalize(term septerm);
thm sep_normalize_rule(thm entail);
thm sep_lift(term lft, term septerm);
thm sep_reorder(term lft, term septerm);
thm which_implies(term state, thm trans);
thm hfact_auto(term pres[], term posts[], thm helpers[]);