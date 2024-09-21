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

#define LIST(list)  alloc_list(list)
#define CONS(h, t)  LIST(Cons(h, t))
#define NIL         LIST(Nil())

List *alloc_list(List list) {
    List *res = malloc(sizeof(*res));
    assert(res);
    memcpy((void *)res, (const void *)&list, sizeof(list));
    return res;
}


[[ghost::test]]
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

[[ghost::function]]
List *app(const List *l, const List *m) {
  match (*l) {
    of(Nil) return m;
    of(Cons, h, t) {
      List *n = CONS(*h, app(*t, m));
      return n;
    }
  }
}

[[ghost::function]]
List *rev(const List *l) {
  match (*l) {
    of(Nil) return NIL;
    of(Cons, h, t) {
      List *m = rev(*t);
      List *n = LIST(*app(m, CONS(*h, NIL)));
      return n;
    }
  }
}

struct ListNode {
	int head;
	struct ListNode * tail;
};

[[ghost::representation]]
hprop list_repr(struct ListNode * ln, const List * l) {
	match (*l) {
    of(Nil) return pure(ln == NULL);
    of(Cons, x, xs) {
      // hexist y, (ln->tail ~> y sep Top) sepand (ln->tail ~> y sep Q)
      struct ListNode * y = ln->tail;
      return (ln->head == *x) SEP (ln->tail == y) SEP list_repr(y, *xs);
      // return (*ln == (struct ListNode){*x, y}) * list_repr(y, *xs);
    }
  }
}

List * listHead (const List * l) {
  match (*l) {
    of(Nil) assert(0);
    of(Cons, x, xs) return *x;
  }
}

List * listTail (const List * l) {
  match (*l) {
    of(Nil) assert(0);
    of(Cons, x, xs) return *xs;
  }
}

bool eqList(const List * l1, const List * l2) {
  match (*l1) {
    of(Nil) {
      match (*l2) {
        of(Nil) return true;
        otherwise return false;
      }
    }
    of(Cons, x, xs) {
      match (*l2) {
        of(Nil) return false;
        of(Cons, y, ys) return *x == *y && eqList(*xs, *ys);
      }
    }
  }
}

struct ListNode * reverse(struct ListNode * ln, [[ghost::param]] const List * l) /*@ With l : lst*/
  [[ghost::requires(list_repr(ln, l))]]
  [[ghost::ensures(list_repr(__result, rev(l)))]]
{
  require(list_repr(ln, l));
  [[ghost::localvar]] List *l1 = (List *)NIL, *l2 = l;
	struct ListNode * prev = NULL;
	while (ln != NULL)
  {
		struct ListNode * next = ln -> tail;
		ln -> tail = prev;
		[[ghost::command]] l1 = CONS(ln -> head, l1);
		prev = ln;
		ln = next;
    [[ghost::command]] l2 = listTail(l2);
    [[ghost::command]] assert(pure(eqList(app(rev(l1), l2), l)) SEP list_repr(prev, l1) SEP list_repr(next, l2));
	}
  ensure(list_repr(prev, rev(l)));
	return prev;
}

int main() {
  struct ListNode * ln = 
    reverse(
      &(struct ListNode){1, &(struct ListNode){2, &(struct ListNode){4, NULL}}}, 
      CONS(1, CONS(2, CONS(4, NIL)))
    );
  puts("Correct");
  return 0;
}