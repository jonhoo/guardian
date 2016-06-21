# guardian

[![Build Status](https://travis-ci.org/jonhoo/guardian.svg?branch=master)](https://travis-ci.org/jonhoo/guardian)

[Documentation](https://jon.tsp.io/crates/guardian)

Guardian provides owned mutex guards for refcounted mutexes.

Normally, lock guards (be it for `Mutex` or `RwLock`) are bound to the lifetime of the borrow
of the underlying lock. Specifically, the function signatures all resemble:
`fn lock<'a>(&'a self) -> Guard<'a>`.

If the mutex is refcounted using an `Rc` or an `Arc`, it is not necessary for the guard to be
scoped in this way -- it could instead carry with it a ref to the mutex in question, which
allows the guard to be held for as long as is necessary. This is particularly useful for
writing iterators where it is advantageous to hold a read lock for the duration of the
iteration.

## Poisoning

When taking a lock using a guardian, similarly to when taking an `RwLock` or `Mutex`, the
result may be poisoned on panics. The poison is propagated from that of the underlying `lock()`
method, so for `RwLock`s, the same rule applies for when a lock may be poisioned.
