#ifndef CSTAR_HEADER
#define CSTAR_HEADER
#pragma GCC diagnostic ignored "-Wunknown-attributes"
#include <stddef.h>
#include <stdio.h>
#include <proof-kernel.h>
#include <proof-user.h>
#include <proof-conv.h>

#define N 100

// Global variables for temporary terms, goals, and theorems
term tmp_term, tmp_term1, tmp_term2, tmp_term3, tmp_term4;
term tmp_goal;
thm tmp_thm;
term __state, __transform; 

/* Symbolic execution. */
term get_symbolic_state() { return __state; }
void set_symbolic_state(thm th) { 
  __state = snd_binop(parse_term("hentail"), conclusion(th));
  printf("%s\n\n", string_of_term(__state));
}

#endif