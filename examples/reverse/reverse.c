#include <datatype99.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <assert.h>
#include "cstar.h"

datatype(
  List,
  (Nil),
  (Cons, int, List *)
);

#define LIST(list)  ((List *)(List[]){list})
#define CONS(h, t)  LIST(Cons(h, t))
#define NIL()       LIST(Nil())

void printList(const List *l) {
  match (*l) {
    of(Nil) printf("Nil");
    of(Cons, h, t) {
      printf("Cons{%d,", *h);
      printList(*t);
      printf("}");
    }
  }
}

List *app(const List *l, const List *m) {
  match (*l) {
    of(Nil) return (List *)m;
    of(Cons, h, t) {
      List *n = (List *)malloc(sizeof(List));
      *n = *app(*t, m);
      return CONS(*h, n);
    }
  }
}

List *rev(const List *l) {
  match (*l) {
    of(Nil) return (List *)NIL();
    of(Cons, h, t) {
      List *m = (List *)malloc(sizeof(List));
      *m = *rev(*t);
      List *n = (List *)malloc(sizeof(List));
      *n = *app(m, CONS(*h, NIL()));
      return n;
    }
  }
}

struct ListNode {
	int head;
	struct ListNode * tail;
};

hprop list_repr(struct ListNode * ln, const List * l) {
	match (*l) {
    of(Nil) return pure(ln == NULL);
    of(Cons, x, xs) {
      struct ListNode * y = ln->tail;
      return (ln->head == *x) * (ln->tail == y) * list_repr(y, *xs);
      //return (*ln == (struct ListNode){*x, y}) * list_repr(y, *xs);
    }
  }
}

struct ListNode * reverse(struct ListNode * ln, const List * l) {
	require(list_repr(ln, l));
	List *l_acc = (List *)NIL();
	struct ListNode * prev = NULL;
	while(ln != NULL) {
		struct ListNode * next = ln -> tail;
		ln -> tail = prev;
		l_acc = CONS(ln -> head, l_acc);
		prev = ln;
		ln = next;
		assert(list_repr(prev, l_acc));
	}
	ensure(list_repr(prev, rev(l)));
	return prev;
}

int main() {
  struct List * ln1 = 
    app(CONS(1, CONS(2, NIL())), CONS(3, CONS(4, NIL())));
  printList(rev(ln1));
  struct ListNode * ln2 = 
    reverse(
      &(struct ListNode){1, &(struct ListNode){2, NULL}}, 
      CONS(1, CONS(2, NIL()))
    );
  return 0;
}