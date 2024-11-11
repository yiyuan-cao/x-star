// https://github.com/verifast/verifast/blob/b351656ae5b89afe0539be4c3c2703af8dc94c90/examples/swap.c

#include "vst_ide.h"

void swap(int *a, int *b)
/*@
With
  (a_v b_v : Z)
Require
  data_at(a, int, a_v) *
  data_at(b, int, b_v)
Ensure
  data_at(a@pre, int, b_v) *
  data_at(b@pre, int, a_v)
*/
{
    /*@ Assert
      data_at(a@pre, int, a_v) *
      data_at(b@pre, int, b_v) *
      data_at(&a, int*, a@pre) *
      data_at(&b, int*, b@pre)
    */
    int tmp = *a;
    /*@ Assert
      data_at(a@pre, int, a_v) *
      data_at(b@pre, int, b_v) *
      data_at(&a, int*, a@pre) *
      data_at(&b, int*, b@pre) *
      data_at(&tmp, int, a_v)
    */
    *a = *b;
    /*@ Assert
      data_at(a@pre, int, b_v) *
      data_at(b@pre, int, b_v) *
      data_at(&a, int*, a@pre) *
      data_at(&b, int*, b@pre) *
      data_at(&tmp, int, a_v)
    */
    *b = tmp;
    /*@ Assert
      data_at(a@pre, int, b_v) *
      data_at(b@pre, int, a_v) *
      data_at(&a, int*, a@pre) *
      data_at(&b, int*, b@pre) *
      data_at(&tmp, int, a_v)
    */
}

struct point {
    int x;
    int y;
};

void point_mirror(struct point *p)
/*@
With
  (x y : Z)
Require
  data_at(&p->x, int, x) *
  data_at(&p->y, int, y)
Ensure
  data_at(&p->x, int, y) *
  data_at(&p->y, int, x)
*/
{
    /*@ Assert
      data_at(&p@pre->x, int, x) *
      data_at(&p@pre->y, int, y) *
      data_at(&p, struct point*, p@pre)
    */
    swap(&p->x, &p->y) /*@ where a_v = x, b_v = y */;
    /*@ Assert
      data_at(&p@pre->x, int, y) *
      data_at(&p@pre->y, int, x) *
      data_at(&p, struct point*, p@pre)
    */
}
