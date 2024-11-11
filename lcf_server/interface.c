#include "proof-user.h"
#include "def.h"
#include "drule.h"
#include "lemma.h"
#include <stdio.h>

thm unfold(term hp, thm def)
{
    thm th = rewrite(def, hp);
    return eq2ent(th);
}
thm fold(term hp, thm def)
{
    thm th = rewrite(def, hp);
    return eq2ent(symm(th));
}

thm use_fact_rewrite(term fact, term target)
{
    thm th = assume(fact);
    th = rewrite(th, target);
    th = eq2ent(th);
    return th;
}
thm use_fact_symm_rewrite(term fact, term target)
{
    thm th = symm(assume(fact));
    th = rewrite(th, target);
    th = eq2ent(th);
    return th;
}

// spa : spa addr start end l
// i_l_len : i < len
// len : len = LENGTH l
// st_ed : start < end
thm break_spa_at_i(term spa, thm i_l_len, thm len, thm st_ed)
{
    thm tmpth;
    thm ar3 = rewrite_rule(symm(LEN_DEF), arith_rule(parse_term("end - start <= end")));
    tmpth = mp(breaknth_list_sepconj(), STORE_PAGEINFO_ARRAY_DEF);
    tmpth = mp(mp(mp(tmpth, i_l_len), ar3), len);
    thm ar4 = rewrite_rule(symm(LEN_DEF), arith_rule(parse_term("start < end ==> end - (end - start) = start")));
    thm ar5 = arith_rule(parse_term("! a : num. 0 + a = a"));
    tmpth = rewrite_rule(ar5, rewrite_rule(mp(ar4, st_ed), tmpth));
    tmpth = rewrite(tmpth, spa);
    thm ar6 = arith_rule(parse_term("! i. start + (SUC i) = SUC (start + i)"));
    thm thl6[] = {tmpth, ar6, symm(I2ID_DEF), i2id2i(), hsep_assoc, NULL};
    tmpth = rewrite_after_term_list(thl6, spa);
    return tmpth;
}