#include "host.h"
#include <stdio.h>

int main(int argc, char **argv) {
  hol_init();

  term t = parse_term("1+1");
  char *s = string_of_term(t);
  printf("%s\n", s);

  return 0;
}
