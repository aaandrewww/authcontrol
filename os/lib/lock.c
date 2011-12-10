#include <inc/lib.h>

void lock(lock_t *lock) {
    while (__sync_lock_test_and_set(lock, 1)) {
	    // No chance of getting the lock unless another process runs
	    sys_yield();
    }
}

void unlock(lock_t *lock) {
    // Make sure everything that happened before unlock is done
    __sync_synchronize();
   *lock = 0;
}
