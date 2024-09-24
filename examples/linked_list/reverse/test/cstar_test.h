// Generated from cstar_std.config

#ifndef CSTAR_TEST_H
#define CSTAR_TEST_H

#include <assert.h>
#include <stdbool.h>
#include <stddef.h> // for size_t
#include <stdint.h> // for int64_t

// Run-time correspondence of logical layer entities to C entities
#define VAL(e) ((Z)(e)) // get the program value of a program expression
#define Z int64_t
#define Ptr size_t
#define Bool bool
#define HProp bool
#define PURE(p) (p) // embed a pure logical assertion as a separation logic assertion with no constraints on heaps
#define EMP (true)  // requires an empty heap
#define BOT (assert(false), false) // always false (denote unreachable case)

#define EQ ==       // equality on primitive program values
#define SEP &&      // separating conjunction (the heap must satisfy two conjuncts, separately)
#define SEPAND &&   // separation logic and (the heap must satisfy both conjuncts)

#define True true
#define False false

#define LET_SEP(addr, val_binder)                                                                                    \
    val_binder = VAL(*(addr)); // add an hexists-quantified data_at separating conjunct for addr (in proof mode) when defining
                           // a representation predicate
#define DATA_AT_ANY(addr) (assert(addr), true) // for signifying a addressable stack or heap location

#define require assert
#define ensure assert

// proposal: delete these macros and overload `if`, `?:`, `&&`, `||`, and `!` to work on `Bool`
#define AND &&
#define OR ||
#define NOT !

#endif // CSTAR_TEST_H