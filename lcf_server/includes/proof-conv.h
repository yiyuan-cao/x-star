#include <proof-user.h>

thm sep_normalize(term septerm);
thm sep_lift(term lft, term septerm);
thm sep_cancel(term lft, term septerm);
thm which_implies(term state, thm trans);