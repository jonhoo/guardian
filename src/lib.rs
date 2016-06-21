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

use std::rc;
use std::sync;
use std::ops::Deref;
use std::ops::DerefMut;

// ATTENTION READERS:
// Most of the code looks identical for Arc vs Rc, for RwLockRead vs RwLockWrite, and for Mutex vs
// RwLock. If you change anything for one type, be sure to also make the same changes to the other
// variants below.

// ****************************************************************************
// The basic wrapper types
// ****************************************************************************

/// RAII structure used to release the shared read access of a lock when dropped.
/// Keeps a handle to an `Arc` so that the lock is not dropped until the guard is.
///
/// The data protected by the mutex can be access through this guard via its `Deref` and `DerefMut`
/// implementations.
pub struct ArcRwLockReadGuardian<T: 'static> {
    _handle: sync::Arc<sync::RwLock<T>>,
    inner: sync::RwLockReadGuard<'static, T>,
}

/// RAII structure used to release the exclusive write access of a lock when dropped.
/// Keeps a handle to an `Arc` so that the lock is not dropped until the guard is.
///
/// The data protected by the mutex can be access through this guard via its `Deref` and `DerefMut`
/// implementations.
pub struct ArcRwLockWriteGuardian<T: 'static> {
    _handle: sync::Arc<sync::RwLock<T>>,
    inner: sync::RwLockWriteGuard<'static, T>,
}

/// An RAII implementation of a "scoped lock" of a mutex. When this structure is dropped (falls out
/// of scope), the lock will be unlocked. Keeps a handle to an `Arc` so that the lock is not
/// dropped until the guard is.
///
/// The data protected by the mutex can be access through this guard via its `Deref` and `DerefMut`
/// implementations.
pub struct ArcMutexGuardian<T: 'static> {
    _handle: sync::Arc<sync::Mutex<T>>,
    inner: sync::MutexGuard<'static, T>,
}

/// RAII structure used to release the shared read access of a lock when dropped.
/// Keeps a handle to an `Rc` so that the lock is not dropped until the guard is.
///
/// The data protected by the mutex can be access through this guard via its `Deref` and `DerefMut`
/// implementations.
pub struct RcRwLockReadGuardian<T: 'static> {
    _handle: rc::Rc<sync::RwLock<T>>,
    inner: sync::RwLockReadGuard<'static, T>,
}

/// RAII structure used to release the exclusive write access of a lock when dropped.
/// Keeps a handle to an `Rc` so that the lock is not dropped until the guard is.
///
/// The data protected by the mutex can be access through this guard via its `Deref` and `DerefMut`
/// implementations.
pub struct RcRwLockWriteGuardian<T: 'static> {
    _handle: rc::Rc<sync::RwLock<T>>,
    inner: sync::RwLockWriteGuard<'static, T>,
}

/// An RAII implementation of a "scoped lock" of a mutex. When this structure is dropped (falls out
/// of scope), the lock will be unlocked. Keeps a handle to an `Rc` so that the lock is not
/// dropped until the guard is.
///
/// The data protected by the mutex can be access through this guard via its `Deref` and `DerefMut`
/// implementations.
pub struct RcMutexGuardian<T: 'static> {
    _handle: rc::Rc<sync::Mutex<T>>,
    inner: sync::MutexGuard<'static, T>,
}

// ****************************************************************************
// Traits: Deref
// ****************************************************************************

impl<T> Deref for ArcRwLockReadGuardian<T> {
    type Target = T;
    fn deref(&self) -> &Self::Target {
        &*self.inner
    }
}

impl<T> Deref for ArcRwLockWriteGuardian<T> {
    type Target = T;
    fn deref(&self) -> &Self::Target {
        &*self.inner
    }
}

impl<T> Deref for ArcMutexGuardian<T> {
    type Target = T;
    fn deref(&self) -> &Self::Target {
        &*self.inner
    }
}

impl<T> Deref for RcRwLockReadGuardian<T> {
    type Target = T;
    fn deref(&self) -> &Self::Target {
        &*self.inner
    }
}

impl<T> Deref for RcRwLockWriteGuardian<T> {
    type Target = T;
    fn deref(&self) -> &Self::Target {
        &*self.inner
    }
}

impl<T> Deref for RcMutexGuardian<T> {
    type Target = T;
    fn deref(&self) -> &Self::Target {
        &*self.inner
    }
}

// ****************************************************************************
// Traits: DerefMut
// ****************************************************************************

impl<T> DerefMut for ArcRwLockWriteGuardian<T> {
    fn deref_mut(&mut self) -> &mut T {
        &mut *self.inner
    }
}

impl<T> DerefMut for RcRwLockWriteGuardian<T> {
    fn deref_mut(&mut self) -> &mut T {
        &mut *self.inner
    }
}

impl<T> DerefMut for ArcMutexGuardian<T> {
    fn deref_mut(&mut self) -> &mut T {
        &mut *self.inner
    }
}

impl<T> DerefMut for RcMutexGuardian<T> {
    fn deref_mut(&mut self) -> &mut T {
        &mut *self.inner
    }
}

// ****************************************************************************
// Traits: From
// ****************************************************************************

impl<T> From<sync::Arc<sync::RwLock<T>>> for ArcRwLockReadGuardian<T> {
    fn from(handle: sync::Arc<sync::RwLock<T>>) -> Self {
        ArcRwLockReadGuardian::take(handle).unwrap()
    }
}

impl<T> From<sync::Arc<sync::RwLock<T>>> for ArcRwLockWriteGuardian<T> {
    fn from(handle: sync::Arc<sync::RwLock<T>>) -> Self {
        ArcRwLockWriteGuardian::take(handle).unwrap()
    }
}

impl<T> From<sync::Arc<sync::Mutex<T>>> for ArcMutexGuardian<T> {
    fn from(handle: sync::Arc<sync::Mutex<T>>) -> Self {
        ArcMutexGuardian::take(handle).unwrap()
    }
}

impl<T> From<rc::Rc<sync::RwLock<T>>> for RcRwLockReadGuardian<T> {
    fn from(handle: rc::Rc<sync::RwLock<T>>) -> Self {
        RcRwLockReadGuardian::take(handle).unwrap()
    }
}

impl<T> From<rc::Rc<sync::RwLock<T>>> for RcRwLockWriteGuardian<T> {
    fn from(handle: rc::Rc<sync::RwLock<T>>) -> Self {
        RcRwLockWriteGuardian::take(handle).unwrap()
    }
}

impl<T> From<rc::Rc<sync::Mutex<T>>> for RcMutexGuardian<T> {
    fn from(handle: rc::Rc<sync::Mutex<T>>) -> Self {
        RcMutexGuardian::take(handle).unwrap()
    }
}

// ****************************************************************************
// impl ::take
// ****************************************************************************

macro_rules! take {
    ( $lock:ty, $guard:ty, $nguardian:ident, $guardiant:ty, $lfunc:ident ) => {
        pub fn take(handle: $lock) -> sync::LockResult<$guardiant> {
            use std::mem;

            // We want to express that it's safe to keep the read guard around for as long as the
            // Arc/Rc is around. Unfortunately, we can't say this directly with lifetimes, because
            // we have to move the Arc/Rc below, which Rust doesn't know allows the borrow to
            // continue. We therefore transmute to a 'static Guard, and ensure that any borrows we
            // expose are bounded by the lifetime of the guardian (which also holds the Arc/Rc).
            let lock: sync::LockResult<$guard> =
                unsafe { mem::transmute(handle.$lfunc()) };

            match lock {
                Ok(guard) => {
                    Ok($nguardian {
                        _handle: handle,
                        inner: guard,
                    })
                }
                Err(guard) => {
                    Err(sync::PoisonError::new($nguardian {
                        _handle: handle,
                        inner: guard.into_inner(),
                    }))
                }
            }
        }
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
    /// The guardian also holds a strong reference to the lock's `Arc`, which is dropped when the
    /// guard is.
    take!(sync::Arc<sync::RwLock<T>>, sync::RwLockReadGuard<'static, T>, ArcRwLockReadGuardian, ArcRwLockReadGuardian<T>, read);
}

impl<T> ArcRwLockWriteGuardian<T> {
    /// Locks this rwlock with exclusive write access, blocking the current thread until it can be
    /// acquired.
    ///
    /// This function will not return while other writers or other readers currently have access to
    /// the lock.
    ///
    /// Returns an RAII guard which will drop the write access of this rwlock when dropped.
    /// The guardian also holds a strong reference to the lock's `Arc`, which is dropped when the
    /// guard is.
    ///
    /// # Errors
    ///
    /// This function will return an error if the `RwLock` is poisoned. An `RwLock` is poisoned
    /// whenever a writer panics while holding an exclusive lock. An error will be returned when
    /// the lock is acquired.
    take!(sync::Arc<sync::RwLock<T>>, sync::RwLockWriteGuard<'static, T>, ArcRwLockWriteGuardian, ArcRwLockWriteGuardian<T>, write);
}

impl<T> ArcMutexGuardian<T> {
    /// Acquires a mutex, blocking the current thread until it is able to do so.
    ///
    /// This function will block the local thread until it is available to acquire the mutex. Upon
    /// returning, the thread is the only thread with the mutex held. An RAII guardian is returned
    /// to allow scoped unlock of the lock. When the guard goes out of scope, the mutex will be
    /// unlocked. The guardian also holds a strong reference to the lock's `Arc`, which is dropped
    /// when the guard is.
    ///
    /// # Errors
    ///
    /// If another user of this mutex panicked while holding the mutex, then this call will return
    /// an error once the mutex is acquired.
    take!(sync::Arc<sync::Mutex<T>>, sync::MutexGuard<'static, T>, ArcMutexGuardian, ArcMutexGuardian<T>, lock);
}

// And this is all the same as above, but with s/Arc/Rc/

impl<T> RcRwLockReadGuardian<T> {
    /// Locks the given rwlock with shared read access, blocking the current thread until it can be
    /// acquired.
    ///
    /// The calling thread will be blocked until there are no more writers which hold the lock.
    /// There may be other readers currently inside the lock when this method returns. This method
    /// does not provide any guarantees with respect to the ordering of whether contentious readers
    /// or writers will acquire the lock first.
    ///
    /// Returns an RAII guardian which will release this thread's shared access once it is dropped.
    /// The guardian also holds a strong reference to the lock's `Rc`, which is dropped when the
    /// guard is.
    take!(rc::Rc<sync::RwLock<T>>, sync::RwLockReadGuard<'static, T>, RcRwLockReadGuardian, RcRwLockReadGuardian<T>, read);
}

impl<T> RcRwLockWriteGuardian<T> {
    /// Locks this rwlock with exclusive write access, blocking the current thread until it can be
    /// acquired.
    ///
    /// This function will not return while other writers or other readers currently have access to
    /// the lock.
    ///
    /// Returns an RAII guard which will drop the write access of this rwlock when dropped.
    /// The guardian also holds a strong reference to the lock's `Rc`, which is dropped when the
    /// guard is.
    ///
    /// # Errors
    ///
    /// This function will return an error if the `RwLock` is poisoned. An `RwLock` is poisoned
    /// whenever a writer panics while holding an exclusive lock. An error will be returned when
    /// the lock is acquired.
    take!(rc::Rc<sync::RwLock<T>>, sync::RwLockWriteGuard<'static, T>, RcRwLockWriteGuardian, RcRwLockWriteGuardian<T>, write);
}

impl<T> RcMutexGuardian<T> {
    /// Acquires a mutex, blocking the current thread until it is able to do so.
    ///
    /// This function will block the local thread until it is available to acquire the mutex. Upon
    /// returning, the thread is the only thread with the mutex held. An RAII guardian is returned
    /// to allow scoped unlock of the lock. When the guard goes out of scope, the mutex will be
    /// unlocked. The guardian also holds a strong reference to the lock's `Rc`, which is dropped
    /// when the guard is.
    ///
    /// # Errors
    ///
    /// If another user of this mutex panicked while holding the mutex, then this call will return
    /// an error once the mutex is acquired.
    take!(rc::Rc<sync::Mutex<T>>, sync::MutexGuard<'static, T>, RcMutexGuardian, RcMutexGuardian<T>, lock);
}

// ****************************************************************************
// And finally all the tests
// ****************************************************************************

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync;
    use std::rc;

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

    #[test]
    fn arc_rw_write() {
        let base = sync::Arc::new(sync::RwLock::new(true));

        let mut x = ArcRwLockWriteGuardian::take(base.clone()).unwrap();

        // guardian dereferences correctly
        assert_eq!(&*x, &true);

        // guardian can write
        *x = false;
        assert_eq!(&*x, &false);

        // guardian holds write lock
        assert!(base.try_read().is_err(), "guardian holds write lock");

        // guardian can be moved
        let x_ = x;
        assert_eq!(&*x_, &false);

        // moving guardian does not release lock
        assert!(base.try_read().is_err(), "guardian still holds write lock");

        // dropping guardian drops write lock
        drop(x_);
        assert!(base.try_read().is_ok(), "guardian drops write lock");

        // guardian works even after all other Arcs have been dropped
        let x = ArcRwLockWriteGuardian::take(base).unwrap();
        assert_eq!(&*x, &false);
    }

    #[test]
    fn arc_mu() {
        let base = sync::Arc::new(sync::Mutex::new(true));

        let mut x = ArcMutexGuardian::take(base.clone()).unwrap();

        // guardian dereferences correctly
        assert_eq!(&*x, &true);

        // guardian can write
        *x = false;
        assert_eq!(&*x, &false);

        // guardian holds lock
        assert!(base.try_lock().is_err(), "guardian holds lock");

        // guardian can be moved
        let x_ = x;
        assert_eq!(&*x_, &false);

        // moving guardian does not release lock
        assert!(base.try_lock().is_err(), "guardian still holds lock");

        // dropping guardian drops lock
        drop(x_);
        assert!(base.try_lock().is_ok(), "guardian drops lock");

        // guardian works even after all other Arcs have been dropped
        let x = ArcMutexGuardian::take(base).unwrap();
        assert_eq!(&*x, &false);
    }

    #[test]
    fn rc_rw_read() {
        let base = rc::Rc::new(sync::RwLock::new(true));

        // the use of scopes below is necessary so that we can drop base at the end.
        // otherwise, all the x1's (i.e., base.read()) would hold on to borrows.
        // this is part of the problem that Guardian is trying to solve.

        let x2 = {
            let x1 = base.read().unwrap();
            let x2 = RcRwLockReadGuardian::take(base.clone()).unwrap();

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

        // guardian works even after all other Rcs have been dropped
        let x = RcRwLockReadGuardian::take(base).unwrap();
        assert_eq!(&*x, &true);
    }

    #[test]
    fn rc_rw_write() {
        let base = rc::Rc::new(sync::RwLock::new(true));

        let mut x = RcRwLockWriteGuardian::take(base.clone()).unwrap();

        // guardian dereferences correctly
        assert_eq!(&*x, &true);

        // guardian can write
        *x = false;
        assert_eq!(&*x, &false);

        // guardian holds write lock
        assert!(base.try_read().is_err(), "guardian holds write lock");

        // guardian can be moved
        let x_ = x;
        assert_eq!(&*x_, &false);

        // moving guardian does not release lock
        assert!(base.try_read().is_err(), "guardian still holds write lock");

        // dropping guardian drops write lock
        drop(x_);
        assert!(base.try_read().is_ok(), "guardian drops write lock");

        // guardian works even after all other Rcs have been dropped
        let x = RcRwLockWriteGuardian::take(base).unwrap();
        assert_eq!(&*x, &false);
    }

    #[test]
    fn rc_mu() {
        let base = rc::Rc::new(sync::Mutex::new(true));

        let mut x = RcMutexGuardian::take(base.clone()).unwrap();

        // guardian dereferences correctly
        assert_eq!(&*x, &true);

        // guardian can write
        *x = false;
        assert_eq!(&*x, &false);

        // guardian holds lock
        assert!(base.try_lock().is_err(), "guardian holds lock");

        // guardian can be moved
        let x_ = x;
        assert_eq!(&*x_, &false);

        // moving guardian does not release lock
        assert!(base.try_lock().is_err(), "guardian still holds lock");

        // dropping guardian drops lock
        drop(x_);
        assert!(base.try_lock().is_ok(), "guardian drops lock");

        // guardian works even after all other Rcs have been dropped
        let x = RcMutexGuardian::take(base).unwrap();
        assert_eq!(&*x, &false);
    }
}
