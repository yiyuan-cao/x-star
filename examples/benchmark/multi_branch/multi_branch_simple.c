#include "vst_ide.h"

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
