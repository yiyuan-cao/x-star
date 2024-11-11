#ifndef PROOF_INTERFACE_H
#define PROOF_INTERFACE_H

#include "proof-user.h"
#include "def.h"
#include "drule.h"
#include "lemma.h"
#include "interface.h"
#include <stdio.h>

thm unfold(term hp, thm def);
thm fold(term hp, thm def);
thm use_fact_rewrite(term fact, term target);
thm use_fact_symm_rewrite(term fact, term target);
thm break_spa_at_i(term, thm, thm, thm);

#endif