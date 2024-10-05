#ifndef HOL_HOST_H
#define HOL_HOST_H

typedef struct term {
  void *inner;
} term;

typedef struct hol_type {
  void *inner;
} hol_type;

typedef struct thm {
  void *inner;
} thm;

typedef struct indtype {
  thm induct;
  thm recursion;
} indtype;

void hol_init();

term parse_term(const char *s);
hol_type parse_type(const char *s);
char *string_of_term(term t);
char *string_of_thm(thm th);
char *string_of_type(hol_type ty);
void override_interface(const char* op1, term op2);

void parse_as_infix(const char* op, int prec, const char* assoc);
void parse_as_binder(const char* op);

void new_type(const char *s, int n);
void new_constant(const char *s, hol_type ty);
thm new_axiom(term t);

term concl(thm th);
term dest_comb_fst(term t);
term dest_comb_snd(term t);

indtype define_type(const char *s);

// 10 Primitive Rules
thm REFL(term t);
thm ASSUME(term t);
thm TRANS(thm th1, thm th2);
thm EQ_MP(thm th1, thm th2);

// Derived Rules
thm GEN(term t, thm th);
thm DISCH(term t, thm th);
thm CONJ(thm th1, thm th2);
thm MATCH_MP(thm th1, thm th2);
thm ISPEC(term t, thm th);

// Conversions
thm ONCE_REWRITE_CONV0(term t);
thm ONCE_REWRITE_CONV1(thm th, term t);
thm ONCE_REWRITE_CONV2(thm th1, thm th2, term t);
thm CONDS_ELIM_CONV(term t);

#endif
