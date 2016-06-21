//! Guardian provides owned mutex guards for refcounted mutexes.
//!
//! Normally, lock guards (be it for `Mutex` or `RwLock`) are bound to the lifetime of the borrow
//! of the underlying lock. Specifically, the function signatures all resemble:
//! `fn lock<'a>(&'a self) -> Guard<'a>`.
//!
//! If the mutex is refcounted using an `Rc` or an `Arc`, it is not necessary for the guard to be
//! scoped in this way -- it could instead carry with it a ref to the mutex in question, which
//! allows the guard to be held for as long as is necessary. This is particularly useful for
//! writing iterators where it is advantageous to hold a read lock for the duration of the
//! iteration.
//!
//! # Poisoning
//!
//! When taking a lock using a guardian, similarly to when taking an `RwLock` or `Mutex`, the
//! result may be poisoned on panics. The poison is propagated from that of the underlying `lock()`
//! method, so for `RwLock`s, the same rule applies for when a lock may be poisioned.

use std::sync;
use std::ops::Deref;

/// RAII structure used to release the shared read access of a lock when dropped.
/// Keeps a handle to an `Arc` so that the lock is not dropped until the guard is.
pub struct ArcRwLockReadGuardian<T: 'static> {
    _handle: sync::Arc<sync::RwLock<T>>,
    inner: sync::RwLockReadGuard<'static, T>,
}

impl<T> Deref for ArcRwLockReadGuardian<T> {
    type Target = T;
    fn deref(&self) -> &Self::Target {
        &*self.inner
    }
}

impl<T> ArcRwLockReadGuardian<T> {
    /// Locks the given rwlock with shared read access, blocking the current thread until it can be
    /// acquired.
    ///
    /// The calling thread will be blocked until there are no more writers which hold the lock.
    /// There may be other readers currently inside the lock when this method returns. This method
    /// does not provide any guarantees with respect to the ordering of whether contentious readers
    /// or writers will acquire the lock first.
    ///
    /// Returns an RAII guardian which will release this thread's shared access once it is dropped.
    pub fn take(handle: sync::Arc<sync::RwLock<T>>) -> sync::LockResult<ArcRwLockReadGuardian<T>> {
        use std::mem;

        // We want to express that it's safe to keep the read guard around for as long as the Arc
        // is around. Unfortunately, we can't say this directly with lifetimes, because we have to
        // move the Arc below, which Rust doesn't know allows the borrow to continue. We therefore
        // transmute to a 'static RwLockReadGuard, and ensure that any borrows we expose are
        // bounded by the lifetime of the guardian (which also holds the Arc).
        let rlock: sync::LockResult<sync::RwLockReadGuard<'static, T>> =
            unsafe { mem::transmute(handle.read()) };

        match rlock {
            Ok(guard) => {
                Ok(ArcRwLockReadGuardian {
                    _handle: handle,
                    inner: guard,
                })
            }
            Err(guard) => {
                Err(sync::PoisonError::new(ArcRwLockReadGuardian {
                    _handle: handle,
                    inner: guard.into_inner(),
                }))
            }
        }
    }
}

impl<T> From<sync::Arc<sync::RwLock<T>>> for ArcRwLockReadGuardian<T> {
    fn from(handle: sync::Arc<sync::RwLock<T>>) -> Self {
        ArcRwLockReadGuardian::take(handle).unwrap()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync;

    #[test]
    fn arc_rw_read() {
        let base = sync::Arc::new(sync::RwLock::new(true));

        // the use of scopes below is necessary so that we can drop base at the end.
        // otherwise, all the x1's (i.e., base.read()) would hold on to borrows.
        // this is part of the problem that Guardian is trying to solve.

        let x2 = {
            let x1 = base.read().unwrap();
            let x2 = ArcRwLockReadGuardian::take(base.clone()).unwrap();

            // guardian dereferences correctly
            assert_eq!(&*x1, &*x2);

            // guardian holds read lock
            drop(x1);
            assert!(base.try_write().is_err(), "guardian holds read lock");

            x2
        };

        {
            // guardian can be moved
            let x1 = base.read().unwrap();
            let x2_ = x2;
            assert_eq!(&*x1, &*x2_);

            // moving guardian does not release lock
            drop(x1);
            assert!(base.try_write().is_err(), "guardian still holds read lock");

            // dropping guardian drops read lock
            drop(x2_);
            assert!(base.try_write().is_ok(), "guardian drops read lock");
        }

        // guardian works even after all other Arcs have been dropped
        let x = ArcRwLockReadGuardian::take(base).unwrap();
        assert_eq!(&*x, &true);
    }
}
