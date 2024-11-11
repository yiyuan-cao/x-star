// https://github.com/verifast/verifast/blob/b351656ae5b89afe0539be4c3c2703af8dc94c90/examples/noreturn.c

#include "vst_ide.h"

void external_func()
/*@
Require
  emp
Ensure
  False &&
  emp
*/
;

static void static_proxy_func()
/*@
Require
  emp
Ensure
  False &&
  emp
*/
{
  /*@ Assert
    emp
  */
	external_func();
  /*@ Assert
    False &&
    emp
  */
}

void do_something()
/*@
Require
  emp
Ensure
  emp
*/
;

void endless_while()
/*@
Require
  emp
Ensure
  False &&
  emp
*/
{
  /*@ Assert
    emp
  */
  /*@ Assert Inv
    emp
  */
  while(1) {
    /*@ Assert
      emp
    */
    do_something();
    /*@ Assert
      emp
    */
  }
  /*@ Assert
    1 != 1 &&
    emp
  */
  // endless_while_entail_wit_6
  /*@ Assert
    False &&
    emp
  */
}