#include <datatype99.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <assert.h>
#include <string.h>
#include "cstar.h"

datatype(
  List,
  (Nil),
  (Cons, int, List *)
);

#define LIST(list)  ((List *)(List[]){list})
#define CONS(h, t)  LIST(Cons(h, t))
#define NIL()       LIST(Nil())

List *alloc_list(List list) {
    List *res = malloc(sizeof(*res));
    assert(res);
    memcpy((void *)res, (const void *)&list, sizeof(list));
    return res;
}


[[ghosttest]]
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

[[ghostfunction]]
List *app(const List *l, const List *m) {
  match (*l) {
    of(Nil) return m;
    of(Cons, h, t) {
      List *n = alloc_list(Cons(*h, app(*t, m)));
      return n;
    }
  }
}

[[ghostfunction]]
List *rev(const List *l) {
  match (*l) {
    of(Nil) return alloc_list(Nil());
    of(Cons, h, t) {
      List *m = rev(*t);
      List *n = alloc_list(*app(m, alloc_list(Cons(*h, alloc_list(Nil())))));
      return n;
    }
  }
}

struct ListNode {
	int head;
	struct ListNode * tail;
};

[[ghostrepresentation]]
hprop list_repr(struct ListNode * ln, const List * l) {
	match (*l) {
    of(Nil) return pure(ln == NULL);
    of(Cons, x, xs) {
      struct ListNode * y = ln->tail;
      // hexist y, (ln->tail ~> y sep Top) sepand (ln->tail ~> y sep Q)
      return (ln->head == *x) SEP (ln->tail == y) SEP list_repr(y, *xs);
      //return (*ln == (struct ListNode){*x, y}) * list_repr(y, *xs);
    }
  }
}

struct ListNode * reverse(struct ListNode * ln, [[ghostparam]] const List * l) /*@ With l : lst*/
  // [[ghostrequire(list_repr(ln, l))]]
  [[ghostensure(list_repr(__result, rev(l)))]]
{
  assert(list_repr(ln, l));
  [[ghostlocalvar]] List *l_acc = (List *)NIL();
	struct ListNode * prev = NULL;
  // [[ghost: logic("forall p. is_prime(p)")]]
	while(ln != NULL)
  {
		struct ListNode * next = ln -> tail;
		ln -> tail = prev;
		[[ghostcommand]] l_acc = alloc_list(Cons(ln -> head, l_acc));
		prev = ln;
		ln = next;
    [[ghostcommand]] assert(list_repr(prev, l_acc));
	}
  ensure(list_repr(prev, rev(l)));
	return prev;
}

int main() {
  struct List * ln1 = 
    app(CONS(1, CONS(2, NIL())), CONS(3, CONS(4, NIL())));
  // printList(rev(ln1));
  // puts("");
  struct ListNode * ln2 = 
    reverse(
      &(struct ListNode){1, &(struct ListNode){2, NULL}}, 
      CONS(1, CONS(2, NIL()))
    );
  return 0;
}