#ifndef HOL_HOST_H
#define HOL_HOST_H

typedef struct term {
  void *inner;
} term;

void hol_init();

term parse_term(const char *s);
char *string_of_term(term t);

#endif
