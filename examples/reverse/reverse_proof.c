// linked with LCF lib, extracted from reverse.c.
#include <stdio.h>
typedef thm;
extern void define_type(string);
extern thm define(string);

struct ListNode {
	int head;
	struct ListNode * tail;
};

// extracted from reverse.c
thm app, rev, list_repr;
void ghost_def() {
  define_type("List = Nil | Cons int List");
  app = define(
    "app Nil l = l", 
    "app (Cons h t) l = Cons h (app t l)"
  );
  rev = define(
    "rev Nil = Nil", 
    "rev (Cons h t) = app (rev t) (Cons h Nil)"
  );

  list_repr = define(
    "list_repr ln Nil = pure(ln = NULL)", 
    "list_repr ln (Cons x xs) = hexists(\\y. (store_list_cell ln x y) * (list_repr y xs))"
  );
}

// VST-IDE annotated C syntax.
struct ListNode * reverse(struct ListNode * ln) 
	/*@ require(list_repr(ln, l)) @*/
  /*@ ensure(list_repr(\result, rev(l))) @*/
{
	/*@ ghost(List *l_acc = (List *)Nil) @*/
	struct ListNode * prev = NULL;
	while(ln != NULL) {
		struct ListNode * next = ln -> tail;
		ln -> tail = prev;
		/*@ ghost(l_acc = (List *)(Cons, ln -> head, l_acc)) @*/
		prev = ln;
		ln = next;
		/*@ assert(list_repr(prev, l_acc)) @*/
	}
	return prev;
}

// written in reverse_proof.c
void app_nil_r() {
  // ...
}

int main() {
  ghost_def();
  return 0;
}

// prove which-implies #1
thm p1() {
  // 
}