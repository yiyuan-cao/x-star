#include "vst_ide.h"

int naive_and(int x, int y)
/*@
Require
  0 <= x && x <= 1 &&
  0 <= y && y <= 1 &&
  emp
Ensure
  __return == (x@pre & y@pre)
*/
{
  /*@ Assert
    0 <= x@pre && x@pre <= 1 &&
    0 <= y@pre && y@pre <= 1 &&
    data_at(&x, int, x@pre) *
    data_at(&y, int, y@pre)
  */
  int ret;
  /*@ Assert
    0 <= x@pre && x@pre <= 1 &&
    0 <= y@pre && y@pre <= 1 &&
    data_at(&x, int, x@pre) *
    data_at(&y, int, y@pre) *
    undef_data_at(&ret, int)
  */
  if (x == 0) {
    /*@ Assert
      x@pre == 0 &&
      0 <= x@pre && x@pre <= 1 &&
      0 <= y@pre && y@pre <= 1 &&
      data_at(&x, int, x@pre) *
      data_at(&y, int, y@pre) *
      undef_data_at(&ret, int)
    */
    ret = 0;
    /*@ Assert
      x@pre == 0 &&
      0 <= x@pre && x@pre <= 1 &&
      0 <= y@pre && y@pre <= 1 &&
      data_at(&x, int, x@pre) *
      data_at(&y, int, y@pre) *
      data_at(&ret, int, 0)
    */
    // naive_and_entail_wit_5
    /*@ Assert
      data_at(&x, int, x@pre) *
      data_at(&y, int, y@pre) *
      data_at(&ret, int, x@pre & y@pre)
    */
  } else {
    /*@ Assert
      x@pre != 0 &&
      0 <= x@pre && x@pre <= 1 &&
      0 <= y@pre && y@pre <= 1 &&
      data_at(&x, int, x@pre) *
      data_at(&y, int, y@pre) *
      undef_data_at(&ret, int)
    */
    ret = y;
    /*@ Assert
      x@pre != 0 &&
      0 <= x@pre && x@pre <= 1 &&
      0 <= y@pre && y@pre <= 1 &&
      data_at(&x, int, x@pre) *
      data_at(&y, int, y@pre) *
      data_at(&ret, int, y@pre)
    */
    // naive_and_entail_wit_8
    /*@ Assert
      data_at(&x, int, x@pre) *
      data_at(&y, int, y@pre) *
      data_at(&ret, int, x@pre & y@pre)
    */
  }
  /*@ Assert
    data_at(&x, int, x@pre) *
    data_at(&y, int, y@pre) *
    data_at(&ret, int, x@pre & y@pre)
  */
  return ret;
}

int sum10_while()
/*@
Require
  emp
Ensure
  __return == 55
*/
{
  /*@ Assert
    emp
  */
  int ret = 0;
  /*@ Assert
    data_at(&ret, int, 0)
  */
  int i = 1;
  /*@ Assert
    data_at(&ret, int, 0) *
    data_at(&i, int, 1)
  */
  // sum10_while_entail_wit_4
  /*@ Assert
    1 <= 1 && 1 <= 11 &&
    data_at(&ret, int, sum(1 - 1)) *
    data_at(&i, int, 1)
  */
  /*@ Assert Inv
    exists i_v,
    1 <= i_v && i_v <= 11 &&
    data_at(&ret, int, sum(i_v - 1)) *
    data_at(&i, int, i_v)
  */
  while (i <= 10) {
    /*@ Assert
      exists i_v,
      i_v <= 10 &&
      1 <= i_v && i_v <= 11 &&
      data_at(&ret, int, sum(i_v - 1)) *
      data_at(&i, int, i_v)
    */
    ret += i;
    /*@ Assert
      exists i_v,
      i_v <= 10 &&
      1 <= i_v && i_v <= 11 &&
      data_at(&ret, int, sum(i_v - 1) + i_v) *
      data_at(&i, int, i_v)
    */
    i += 1;
    /*@ Assert
      exists i_v,
      i_v <= 10 &&
      1 <= i_v && i_v <= 11 &&
      data_at(&ret, int, sum(i_v - 1) + i_v) *
      data_at(&i, int, i_v + 1)
    */
    // sum10_while_entail_wit_9
    /*@ Assert
      exists i_v,
      1 <= i_v && i_v <= 11 &&
      data_at(&ret, int, sum(i_v - 1)) *
      data_at(&i, int, i_v)
    */
  }
  /*@ Assert
    exists i_v,
    i_v > 10 &&
    1 <= i_v && i_v <= 11 &&
    data_at(&ret, int, sum(i_v - 1)) *
    data_at(&i, int, i_v)
  */
  // sum10_while_entail_wit_12
  /*@ Assert
    data_at(&ret, int, 55) *
    data_at(&i, int, 11)
  */
  return ret;
}

int sum10_for()
/*@
Require
  emp
Ensure
  __return == 55
*/
{
  /*@ Assert
    emp
  */
  int ret = 0;
  /*@ Assert
    data_at(&ret, int, 0)
  */
  int i = 1;
  /*@ Assert
    data_at(&ret, int, 0) *
    data_at(&i, int, 1)
  */
  // sum10_for_entail_wit_4
  /*@ Assert
    1 <= 1 && 1 <= 11 &&
    data_at(&ret, int, sum(1 - 1)) *
    data_at(&i, int, 1)
  */
  /*@ Assert Inv
    exists i_v,
    1 <= i_v && i_v <= 11 &&
    data_at(&ret, int, sum(i_v - 1)) *
    data_at(&i, int, i_v)
  */
  for (; i <= 10; i += 1) {
    /*@ Assert
      exists i_v,
      i_v <= 10 &&
      1 <= i_v && i_v <= 11 &&
      data_at(&ret, int, sum(i_v - 1)) *
      data_at(&i, int, i_v)
    */
    ret += i;
    /*@ Assert
      exists i_v,
      i_v <= 10 &&
      1 <= i_v && i_v <= 11 &&
      data_at(&ret, int, sum(i_v - 1) + i_v) *
      data_at(&i, int, i_v)
    */
    // sum10_for_entail_wit_8
    /*@ Assert
      exists i_v,
      1 <= i_v + 1 && i_v + 1 <= 11 &&
      data_at(&ret, int, sum((i_v + 1) - 1)) *
      data_at(&i, int, i_v)
    */
  }
  /*@ Assert
    exists i_v,
    i_v > 10 &&
    1 <= i_v && i_v <= 11 &&
    data_at(&ret, int, sum(i_v - 1)) *
    data_at(&i, int, i_v)
  */
  // sum10_for_entail_wit_11
  /*@ Assert
    data_at(&ret, int, 55) *
    data_at(&i, int, 11)
  */
  return ret;
}

int sum10_while_break()
/*@
Require
  emp
Ensure
  __return == 55
*/
{
  /*@ Assert
    emp
  */
  int ret = 0;
  /*@ Assert
    data_at(&ret, int, 0)
  */
  int i = 0;
  /*@ Assert
    data_at(&ret, int, 0) *
    data_at(&i, int, 0)
  */
  // sum10_while_entail_wit_4
  /*@ Assert
    0 <= 0 && 0 <= 10 &&
    data_at(&ret, int, sum(0)) *
    data_at(&i, int, 0)
  */
  /*@ Assert Inv
    exists i_v,
    0 <= i_v && i_v <= 10 &&
    data_at(&ret, int, sum(i_v)) *
    data_at(&i, int, i_v)
  */
  while (1) {
    /*@ Assert
      exists i_v,
      0 <= i_v && i_v <= 10 &&
      data_at(&ret, int, sum(i_v)) *
      data_at(&i, int, i_v)
    */
    i += 1;
    /*@ Assert
      exists i_v,
      0 <= i_v && i_v <= 10 &&
      data_at(&ret, int, sum(i_v)) *
      data_at(&i, int, i_v + 1)
    */
    ret += i;
    /*@ Assert
      exists i_v,
      0 <= i_v && i_v <= 10 &&
      data_at(&ret, int, sum(i_v) + (i_v + 1)) *
      data_at(&i, int, i_v + 1)
    */
    // sum10_while_break_entail_wit_9
    /*@ Assert
      exists i_v,
      0 <= i_v && i_v <= 10 &&
      data_at(&ret, int, sum(i_v + 1)) *
      data_at(&i, int, i_v + 1)
    */
    if (i >= 10) {
      /*@ Assert
        exists i_v,
        i_v + 1 >= 10 &&
        0 <= i_v && i_v <= 10 &&
        data_at(&ret, int, sum(i_v + 1)) *
        data_at(&i, int, i_v + 1)
      */
      break;
    }
    /*@ Assert
      exists i_v,
      i_v + 1 < 10 &&
      0 <= i_v && i_v <= 10 &&
      data_at(&ret, int, sum(i_v + 1)) *
      data_at(&i, int, i_v + 1)
    */
    // sum10_while_break_entail_wit_12
    /*@ Assert
      exists i_v,
      0 <= i_v && i_v <= 10 &&
      data_at(&ret, int, sum(i_v)) *
      data_at(&i, int, i_v)
    */
  }
  /*@ Assert
    exists i_v,
    i_v + 1 >= 10 &&
    0 <= i_v && i_v <= 10 &&
    data_at(&ret, int, sum(i_v + 1)) *
    data_at(&i, int, i_v + 1)
  */
  // sum10_while_break_entail_wit_15
  /*@ Assert
    data_at(&ret, int, 55) *
    data_at(&i, int, 10)
  */
  return ret;
}
