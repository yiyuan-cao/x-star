@@ -0,0 +1,123 @@
// https://github.com/verifast/verifast/blob/b351656ae5b89afe0539be4c3c2703af8dc94c90/examples/globals.c

#include "vst_ide.h"

static int x;

struct counter {
    int f;
};

static struct counter *c;

void m(struct counter *cnt)
/*@
Require
  exists v,
  undef_data_at(&x, int) *
  data_at(&cnt->f, int, v)
Ensure
  data_at(&x, int, 0) *
  undef_data_at(&cnt@pre->f, int)
*/
{
  /*@ Assert
    exists v,
    undef_data_at(&x, int) *
    data_at(&cnt@pre->f, int, v) *
    data_at(&cnt, struct counter*, cnt@pre)
  */
  x = cnt->f ^ cnt->f;
  /*@ Assert
    exists v,
    data_at(&x, int, v ^ v) *
    data_at(&cnt@pre->f, int, v) *
    data_at(&cnt, struct counter*, cnt@pre)
  */

  // m_which_implies_wit_1
  /*@
    exists v,
    data_at(&x, int, v ^ v) *
    data_at(&cnt@pre->f, int, v)
    which implies
    data_at(&x, int, 0) *
    undef_data_at(&cnt@pre->f, int)
  */

  /*@ Assert
    data_at(&x, int, 0) *
    undef_data_at(&cnt@pre->f, int) *
    data_at(&cnt, struct counter*, cnt@pre)
  */
}

int main()
/*@
Require
  undef_data_at(&x, int) *
  undef_data_at(&c, struct counter*)
Ensure
  __return == 0 &&
  data_at(&x, int, 0) *
  undef_data_at(&c, struct counter*)
*/
{
  /*@ Assert
    undef_data_at(&x, int) *
    undef_data_at(&c, struct counter*)
  */
  struct counter cnt;
  /*@ Assert
    undef_data_at(&x, int) *
    undef_data_at(&c, struct counter*) *
    undef_data_at(&cnt.f, int)
  */
  c = &cnt;
  /*@ Assert
    undef_data_at(&x, int) *
    data_at(&c, struct counter*, &cnt) *
    undef_data_at(&cnt.f, int)
  */
  c->f = (int)&x;
  /*@ Assert
    undef_data_at(&x, int) *
    data_at(&c, struct counter*, &cnt) *
    data_at(&cnt.f, int, signed_last_nbits(&x, 32))
  */

  // main_which_implies_wit_1
  /*@
    data_at(&cnt.f, int, signed_last_nbits(&x, 32))
    which implies
    exists v,
    data_at(&cnt.f, int, v)
  */

  /*@ Assert
    exists v,
    undef_data_at(&x, int) *
    data_at(&c, struct counter*, &cnt) *
    data_at(&cnt.f, int, v)
  */
  m(c);
  /*@ Assert
    data_at(&x, int, 0) *
    data_at(&c, struct counter*, &cnt) *
    undef_data_at(&cnt.f, int)
  */

  // main_which_implies_wit_2
  /*@
    data_at(&c, struct counter*, &cnt)
    which implies
    undef_data_at(&c, struct counter*)
  */

  /*@ Assert
    data_at(&x, int, 0) *
    undef_data_at(&c, struct counter*) *
    undef_data_at(&cnt.f, int)
  */
  return x;
}