// Generated from cstar_config.json

#ifndef CSTAR_TEST_H
#define CSTAR_TEST_H

#include <assert.h>
#include <stdbool.h>
#include <stddef.h> // for size_t
#include <stdint.h> // for int64_t, uint64_t, etc.

// Run-time correspondence of C* syntax to C
#define hprop bool
#define i32 int32_t
#define ptr size_t

#define SEP &&    // separating conjunction (the heap must satisfy two conjuncts, separately)
#define SEPAND && // separation logic and and (the heap must satisfy two conjuncts, separately)

#define EMP (true)                 // requires an empty heap
#define PURE(p) (p)                // embed a pure logical assertion with no requirements on heaps
#define FACT(p) ((p) SEPAND EMP)   // embed a pure logical assertion as a separation logic assertion with an empty heap
#define BOT (assert(false), false) // always false (denote unreachable case)

#define LET_DATA_AT(addr, val_binder)                                                                                  \
    val_binder = *(addr); // add an hexists-quantified data_at separating conjunct for addr (in proof mode) when
                          // defining a representation predicate
#define DATA_AT_ANY(addr) (assert(addr), true) // for signifying a addressable stack or heap location

#define require assert
#define ensure assert

#endif // CSTAR_TEST_H