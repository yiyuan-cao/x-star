#include "vst_ide.h"

int next_multiple_of_3(int x)
/*@
Require
  0 <= x && x + 2 <= INT_MAX
Ensure
  __return % 3 == 0 &&
  x@pre <= __return && __return < x@pre + 3
*/
{
  /*@ Assert
    0 <= x@pre && x@pre + 2 <= INT_MAX &&
    data_at(&x, int, x@pre)
  */
  // next_multiple_of_3_entail_wit_2
  /*@ Assert
    x@pre <= x@pre &&
    (forall x_, x_ < x@pre || x_ >= x@pre || x_ % 3 != 0) &&
    0 <= x@pre && x@pre + 2 <= INT_MAX &&
    data_at(&x, int, x@pre)
  */
  /*@ Assert Inv
    exists x_v,
    x@pre <= x_v &&
    (forall x_, x_ < x@pre || x_ >= x_v || x_ % 3 != 0) &&
    0 <= x@pre && x@pre + 2 <= INT_MAX &&
    data_at(&x, int, x_v)
  */
  while (x % 3 != 0) {
    /*@ Assert
      exists x_v,
      x_v % 3 != 0 &&
      x@pre <= x_v &&
      (forall x_, x_ < x@pre || x_ >= x_v || x_ % 3 != 0) &&
      0 <= x@pre && x@pre + 2 <= INT_MAX &&
      data_at(&x, int, x_v)
    */
    x += 1;
    /*@ Assert
      exists x_v,
      x_v % 3 != 0 &&
      x@pre <= x_v &&
      (forall x_, x_ < x@pre || x_ >= x_v || x_ % 3 != 0) &&
      0 <= x@pre && x@pre + 2 <= INT_MAX &&
      data_at(&x, int, x_v + 1)
    */
    if (x % 3 == 0) {
      /*@ Assert
        exists x_v,
        (x_v + 1) % 3 == 0 &&
        x_v % 3 != 0 &&
        x@pre <= x_v &&
        (forall x_, x_ < x@pre || x_ >= x_v || x_ % 3 != 0) &&
        0 <= x@pre && x@pre + 2 <= INT_MAX &&
        data_at(&x, int, x_v + 1)
      */
      // next_multiple_of_3_entail_wit_7
      /*@ Assert
        exists x_v,
        x_v % 3 == 0 &&
        x@pre <= x_v &&
        (forall x_, x_ < x@pre || x_ >= x_v || x_ % 3 != 0) &&
        0 <= x@pre && x@pre + 2 <= INT_MAX &&
        data_at(&x, int, x_v)
      */
      break;
    }
    /*@ Assert
      exists x_v,
      (x_v + 1) % 3 != 0 &&
      x_v % 3 != 0 &&
      x@pre <= x_v &&
      (forall x_, x_ < x@pre || x_ >= x_v || x_ % 3 != 0) &&
      0 <= x@pre && x@pre + 2 <= INT_MAX &&
      data_at(&x, int, x_v + 1)
    */
    x += 1;
    /*@ Assert
      exists x_v,
      (x_v + 1) % 3 != 0 &&
      x_v % 3 != 0 &&
      x@pre <= x_v &&
      (forall x_, x_ < x@pre || x_ >= x_v || x_ % 3 != 0) &&
      0 <= x@pre && x@pre + 2 <= INT_MAX &&
      data_at(&x, int, x_v + 1 + 1)
    */
    // next_multiple_of_3_entail_wit_10
    /*@ Assert
      exists x_v,
      x@pre <= x_v &&
      (forall x_, x_ < x@pre || x_ >= x_v || x_ % 3 != 0) &&
      0 <= x@pre && x@pre + 2 <= INT_MAX &&
      data_at(&x, int, x_v)
    */
  }
  /*@ Assert
    exists x_v,
    x_v % 3 == 0 &&
    x@pre <= x_v &&
    (forall x_, x_ < x@pre || x_ >= x_v || x_ % 3 != 0) &&
    0 <= x@pre && x@pre + 2 <= INT_MAX &&
    data_at(&x, int, x_v)
  */
  // next_multiple_of_3_entail_wit_13
  /*@ Assert
    exists x_v,
    x_v % 3 == 0 &&
    x@pre <= x_v && x_v < x@pre + 3 &&
    0 <= x@pre && x@pre + 2 <= INT_MAX &&
    data_at(&x, int, x_v)
  */
  return x;
}
