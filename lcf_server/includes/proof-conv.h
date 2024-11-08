#include <proof-user.h>

thm trans_list(thm thl[]);
thm rewrite_list(thm thl[], term tm);
thm rewrite_rule_list(thm thl[], thm th);
thm hentail_trans_list(thm thl[]);

term normalize(term septerm);
thm sep_normalize(term septerm);
thm sep_normalize_rule(thm entail);
thm sep_lift(term lft, term septerm);
thm sep_cancel(term lft, term septerm);
thm which_implies(term state, thm trans);