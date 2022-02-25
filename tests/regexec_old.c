# 0 "regexec.c"
# 1 "/home/jonas/Repos/oniguruma//"
# 0 "<built-in>"
# 0 "<command-line>"
# 1 "/usr/include/stdc-predef.h" 1 3 4
# 0 "<command-line>" 2
# 1 "regexec.c"
# 30 "regexec.c"
# 1 "regint.h" 1
# 86 "regint.h"
# 1 "config.h" 1
# 87 "regint.h" 2
# 170 "regint.h"
# 1 "/usr/include/stdlib.h" 1 3 4
# 26 "/usr/include/stdlib.h" 3 4
# 1 "/usr/include/bits/libc-header-start.h" 1 3 4
# 33 "/usr/include/bits/libc-header-start.h" 3 4
# 1 "/usr/include/features.h" 1 3 4
# 392 "/usr/include/features.h" 3 4
# 1 "/usr/include/features-time64.h" 1 3 4
# 20 "/usr/include/features-time64.h" 3 4
# 1 "/usr/include/bits/wordsize.h" 1 3 4
# 21 "/usr/include/features-time64.h" 2 3 4
# 1 "/usr/include/bits/timesize.h" 1 3 4
# 19 "/usr/include/bits/timesize.h" 3 4
# 1 "/usr/include/bits/wordsize.h" 1 3 4
# 20 "/usr/include/bits/timesize.h" 2 3 4
# 22 "/usr/include/features-time64.h" 2 3 4
# 393 "/usr/include/features.h" 2 3 4
# 490 "/usr/include/features.h" 3 4
# 1 "/usr/include/sys/cdefs.h" 1 3 4
# 559 "/usr/include/sys/cdefs.h" 3 4
# 1 "/usr/include/bits/wordsize.h" 1 3 4
# 560 "/usr/include/sys/cdefs.h" 2 3 4
# 1 "/usr/include/bits/long-double.h" 1 3 4
# 561 "/usr/include/sys/cdefs.h" 2 3 4
# 491 "/usr/include/features.h" 2 3 4
# 514 "/usr/include/features.h" 3 4
# 1 "/usr/include/gnu/stubs.h" 1 3 4
# 10 "/usr/include/gnu/stubs.h" 3 4
# 1 "/usr/include/gnu/stubs-64.h" 1 3 4
# 11 "/usr/include/gnu/stubs.h" 2 3 4
# 515 "/usr/include/features.h" 2 3 4
# 34 "/usr/include/bits/libc-header-start.h" 2 3 4
# 27 "/usr/include/stdlib.h" 2 3 4





# 1 "/usr/lib/gcc/x86_64-pc-linux-gnu/11.2.0/include/stddef.h" 1 3 4
# 209 "/usr/lib/gcc/x86_64-pc-linux-gnu/11.2.0/include/stddef.h" 3 4

# 209 "/usr/lib/gcc/x86_64-pc-linux-gnu/11.2.0/include/stddef.h" 3 4
typedef long unsigned int size_t;
# 321 "/usr/lib/gcc/x86_64-pc-linux-gnu/11.2.0/include/stddef.h" 3 4
typedef int wchar_t;
# 33 "/usr/include/stdlib.h" 2 3 4







# 1 "/usr/include/bits/waitflags.h" 1 3 4
# 41 "/usr/include/stdlib.h" 2 3 4
# 1 "/usr/include/bits/waitstatus.h" 1 3 4
# 42 "/usr/include/stdlib.h" 2 3 4
# 56 "/usr/include/stdlib.h" 3 4
# 1 "/usr/include/bits/floatn.h" 1 3 4
# 119 "/usr/include/bits/floatn.h" 3 4
# 1 "/usr/include/bits/floatn-common.h" 1 3 4
# 24 "/usr/include/bits/floatn-common.h" 3 4
# 1 "/usr/include/bits/long-double.h" 1 3 4
# 25 "/usr/include/bits/floatn-common.h" 2 3 4
# 120 "/usr/include/bits/floatn.h" 2 3 4
# 57 "/usr/include/stdlib.h" 2 3 4


typedef struct
  {
    int quot;
    int rem;
  } div_t;



typedef struct
  {
    long int quot;
    long int rem;
  } ldiv_t;





__extension__ typedef struct
  {
    long long int quot;
    long long int rem;
  } lldiv_t;
# 98 "/usr/include/stdlib.h" 3 4
extern size_t __ctype_get_mb_cur_max (void) __attribute__ ((__nothrow__ , __leaf__)) ;



extern double atof (const char *__nptr)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1))) ;

extern int atoi (const char *__nptr)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1))) ;

extern long int atol (const char *__nptr)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1))) ;



__extension__ extern long long int atoll (const char *__nptr)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1))) ;



extern double strtod (const char *__restrict __nptr,
        char **__restrict __endptr)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));



extern float strtof (const char *__restrict __nptr,
       char **__restrict __endptr) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));

extern long double strtold (const char *__restrict __nptr,
       char **__restrict __endptr)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
# 177 "/usr/include/stdlib.h" 3 4
extern long int strtol (const char *__restrict __nptr,
   char **__restrict __endptr, int __base)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));

extern unsigned long int strtoul (const char *__restrict __nptr,
      char **__restrict __endptr, int __base)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));



__extension__
extern long long int strtoq (const char *__restrict __nptr,
        char **__restrict __endptr, int __base)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));

__extension__
extern unsigned long long int strtouq (const char *__restrict __nptr,
           char **__restrict __endptr, int __base)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));




__extension__
extern long long int strtoll (const char *__restrict __nptr,
         char **__restrict __endptr, int __base)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));

__extension__
extern unsigned long long int strtoull (const char *__restrict __nptr,
     char **__restrict __endptr, int __base)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
# 361 "/usr/include/stdlib.h" 3 4
extern __inline __attribute__ ((__gnu_inline__)) int
__attribute__ ((__nothrow__ , __leaf__)) atoi (const char *__nptr)
{
  return (int) strtol (__nptr, (char **) ((void *)0), 10);
}
extern __inline __attribute__ ((__gnu_inline__)) long int
__attribute__ ((__nothrow__ , __leaf__)) atol (const char *__nptr)
{
  return strtol (__nptr, (char **) ((void *)0), 10);
}


__extension__ extern __inline __attribute__ ((__gnu_inline__)) long long int
__attribute__ ((__nothrow__ , __leaf__)) atoll (const char *__nptr)
{
  return strtoll (__nptr, (char **) ((void *)0), 10);
}
# 386 "/usr/include/stdlib.h" 3 4
extern char *l64a (long int __n) __attribute__ ((__nothrow__ , __leaf__)) ;


extern long int a64l (const char *__s)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1))) ;




# 1 "/usr/include/sys/types.h" 1 3 4
# 27 "/usr/include/sys/types.h" 3 4


# 1 "/usr/include/bits/types.h" 1 3 4
# 27 "/usr/include/bits/types.h" 3 4
# 1 "/usr/include/bits/wordsize.h" 1 3 4
# 28 "/usr/include/bits/types.h" 2 3 4
# 1 "/usr/include/bits/timesize.h" 1 3 4
# 19 "/usr/include/bits/timesize.h" 3 4
# 1 "/usr/include/bits/wordsize.h" 1 3 4
# 20 "/usr/include/bits/timesize.h" 2 3 4
# 29 "/usr/include/bits/types.h" 2 3 4


typedef unsigned char __u_char;
typedef unsigned short int __u_short;
typedef unsigned int __u_int;
typedef unsigned long int __u_long;


typedef signed char __int8_t;
typedef unsigned char __uint8_t;
typedef signed short int __int16_t;
typedef unsigned short int __uint16_t;
typedef signed int __int32_t;
typedef unsigned int __uint32_t;

typedef signed long int __int64_t;
typedef unsigned long int __uint64_t;






typedef __int8_t __int_least8_t;
typedef __uint8_t __uint_least8_t;
typedef __int16_t __int_least16_t;
typedef __uint16_t __uint_least16_t;
typedef __int32_t __int_least32_t;
typedef __uint32_t __uint_least32_t;
typedef __int64_t __int_least64_t;
typedef __uint64_t __uint_least64_t;



typedef long int __quad_t;
typedef unsigned long int __u_quad_t;







typedef long int __intmax_t;
typedef unsigned long int __uintmax_t;
# 141 "/usr/include/bits/types.h" 3 4
# 1 "/usr/include/bits/typesizes.h" 1 3 4
# 142 "/usr/include/bits/types.h" 2 3 4
# 1 "/usr/include/bits/time64.h" 1 3 4
# 143 "/usr/include/bits/types.h" 2 3 4


typedef unsigned long int __dev_t;
typedef unsigned int __uid_t;
typedef unsigned int __gid_t;
typedef unsigned long int __ino_t;
typedef unsigned long int __ino64_t;
typedef unsigned int __mode_t;
typedef unsigned long int __nlink_t;
typedef long int __off_t;
typedef long int __off64_t;
typedef int __pid_t;
typedef struct { int __val[2]; } __fsid_t;
typedef long int __clock_t;
typedef unsigned long int __rlim_t;
typedef unsigned long int __rlim64_t;
typedef unsigned int __id_t;
typedef long int __time_t;
typedef unsigned int __useconds_t;
typedef long int __suseconds_t;
typedef long int __suseconds64_t;

typedef int __daddr_t;
typedef int __key_t;


typedef int __clockid_t;


typedef void * __timer_t;


typedef long int __blksize_t;




typedef long int __blkcnt_t;
typedef long int __blkcnt64_t;


typedef unsigned long int __fsblkcnt_t;
typedef unsigned long int __fsblkcnt64_t;


typedef unsigned long int __fsfilcnt_t;
typedef unsigned long int __fsfilcnt64_t;


typedef long int __fsword_t;

typedef long int __ssize_t;


typedef long int __syscall_slong_t;

typedef unsigned long int __syscall_ulong_t;



typedef __off64_t __loff_t;
typedef char *__caddr_t;


typedef long int __intptr_t;


typedef unsigned int __socklen_t;




typedef int __sig_atomic_t;
# 30 "/usr/include/sys/types.h" 2 3 4



typedef __u_char u_char;
typedef __u_short u_short;
typedef __u_int u_int;
typedef __u_long u_long;
typedef __quad_t quad_t;
typedef __u_quad_t u_quad_t;
typedef __fsid_t fsid_t;


typedef __loff_t loff_t;




typedef __ino_t ino_t;
# 59 "/usr/include/sys/types.h" 3 4
typedef __dev_t dev_t;




typedef __gid_t gid_t;




typedef __mode_t mode_t;




typedef __nlink_t nlink_t;




typedef __uid_t uid_t;





typedef __off_t off_t;
# 97 "/usr/include/sys/types.h" 3 4
typedef __pid_t pid_t;





typedef __id_t id_t;




typedef __ssize_t ssize_t;





typedef __daddr_t daddr_t;
typedef __caddr_t caddr_t;





typedef __key_t key_t;




# 1 "/usr/include/bits/types/clock_t.h" 1 3 4






typedef __clock_t clock_t;
# 127 "/usr/include/sys/types.h" 2 3 4

# 1 "/usr/include/bits/types/clockid_t.h" 1 3 4






typedef __clockid_t clockid_t;
# 129 "/usr/include/sys/types.h" 2 3 4
# 1 "/usr/include/bits/types/time_t.h" 1 3 4
# 10 "/usr/include/bits/types/time_t.h" 3 4
typedef __time_t time_t;
# 130 "/usr/include/sys/types.h" 2 3 4
# 1 "/usr/include/bits/types/timer_t.h" 1 3 4






typedef __timer_t timer_t;
# 131 "/usr/include/sys/types.h" 2 3 4
# 144 "/usr/include/sys/types.h" 3 4
# 1 "/usr/lib/gcc/x86_64-pc-linux-gnu/11.2.0/include/stddef.h" 1 3 4
# 145 "/usr/include/sys/types.h" 2 3 4



typedef unsigned long int ulong;
typedef unsigned short int ushort;
typedef unsigned int uint;




# 1 "/usr/include/bits/stdint-intn.h" 1 3 4
# 24 "/usr/include/bits/stdint-intn.h" 3 4
typedef __int8_t int8_t;
typedef __int16_t int16_t;
typedef __int32_t int32_t;
typedef __int64_t int64_t;
# 156 "/usr/include/sys/types.h" 2 3 4


typedef __uint8_t u_int8_t;
typedef __uint16_t u_int16_t;
typedef __uint32_t u_int32_t;
typedef __uint64_t u_int64_t;


typedef int register_t __attribute__ ((__mode__ (__word__)));
# 176 "/usr/include/sys/types.h" 3 4
# 1 "/usr/include/endian.h" 1 3 4
# 24 "/usr/include/endian.h" 3 4
# 1 "/usr/include/bits/endian.h" 1 3 4
# 35 "/usr/include/bits/endian.h" 3 4
# 1 "/usr/include/bits/endianness.h" 1 3 4
# 36 "/usr/include/bits/endian.h" 2 3 4
# 25 "/usr/include/endian.h" 2 3 4
# 35 "/usr/include/endian.h" 3 4
# 1 "/usr/include/bits/byteswap.h" 1 3 4
# 33 "/usr/include/bits/byteswap.h" 3 4
static __inline __uint16_t
__bswap_16 (__uint16_t __bsx)
{

  return __builtin_bswap16 (__bsx);



}






static __inline __uint32_t
__bswap_32 (__uint32_t __bsx)
{

  return __builtin_bswap32 (__bsx);



}
# 69 "/usr/include/bits/byteswap.h" 3 4
__extension__ static __inline __uint64_t
__bswap_64 (__uint64_t __bsx)
{

  return __builtin_bswap64 (__bsx);



}
# 36 "/usr/include/endian.h" 2 3 4
# 1 "/usr/include/bits/uintn-identity.h" 1 3 4
# 32 "/usr/include/bits/uintn-identity.h" 3 4
static __inline __uint16_t
__uint16_identity (__uint16_t __x)
{
  return __x;
}

static __inline __uint32_t
__uint32_identity (__uint32_t __x)
{
  return __x;
}

static __inline __uint64_t
__uint64_identity (__uint64_t __x)
{
  return __x;
}
# 37 "/usr/include/endian.h" 2 3 4
# 177 "/usr/include/sys/types.h" 2 3 4


# 1 "/usr/include/sys/select.h" 1 3 4
# 30 "/usr/include/sys/select.h" 3 4
# 1 "/usr/include/bits/select.h" 1 3 4
# 31 "/usr/include/sys/select.h" 2 3 4


# 1 "/usr/include/bits/types/sigset_t.h" 1 3 4



# 1 "/usr/include/bits/types/__sigset_t.h" 1 3 4




typedef struct
{
  unsigned long int __val[(1024 / (8 * sizeof (unsigned long int)))];
} __sigset_t;
# 5 "/usr/include/bits/types/sigset_t.h" 2 3 4


typedef __sigset_t sigset_t;
# 34 "/usr/include/sys/select.h" 2 3 4



# 1 "/usr/include/bits/types/struct_timeval.h" 1 3 4







struct timeval
{




  __time_t tv_sec;
  __suseconds_t tv_usec;

};
# 38 "/usr/include/sys/select.h" 2 3 4

# 1 "/usr/include/bits/types/struct_timespec.h" 1 3 4
# 11 "/usr/include/bits/types/struct_timespec.h" 3 4
struct timespec
{



  __time_t tv_sec;




  __syscall_slong_t tv_nsec;
# 31 "/usr/include/bits/types/struct_timespec.h" 3 4
};
# 40 "/usr/include/sys/select.h" 2 3 4



typedef __suseconds_t suseconds_t;





typedef long int __fd_mask;
# 59 "/usr/include/sys/select.h" 3 4
typedef struct
  {






    __fd_mask __fds_bits[1024 / (8 * (int) sizeof (__fd_mask))];


  } fd_set;






typedef __fd_mask fd_mask;
# 91 "/usr/include/sys/select.h" 3 4

# 102 "/usr/include/sys/select.h" 3 4
extern int select (int __nfds, fd_set *__restrict __readfds,
     fd_set *__restrict __writefds,
     fd_set *__restrict __exceptfds,
     struct timeval *__restrict __timeout);
# 127 "/usr/include/sys/select.h" 3 4
extern int pselect (int __nfds, fd_set *__restrict __readfds,
      fd_set *__restrict __writefds,
      fd_set *__restrict __exceptfds,
      const struct timespec *__restrict __timeout,
      const __sigset_t *__restrict __sigmask);
# 153 "/usr/include/sys/select.h" 3 4

# 180 "/usr/include/sys/types.h" 2 3 4





typedef __blksize_t blksize_t;






typedef __blkcnt_t blkcnt_t;



typedef __fsblkcnt_t fsblkcnt_t;



typedef __fsfilcnt_t fsfilcnt_t;
# 227 "/usr/include/sys/types.h" 3 4
# 1 "/usr/include/bits/pthreadtypes.h" 1 3 4
# 23 "/usr/include/bits/pthreadtypes.h" 3 4
# 1 "/usr/include/bits/thread-shared-types.h" 1 3 4
# 44 "/usr/include/bits/thread-shared-types.h" 3 4
# 1 "/usr/include/bits/pthreadtypes-arch.h" 1 3 4
# 21 "/usr/include/bits/pthreadtypes-arch.h" 3 4
# 1 "/usr/include/bits/wordsize.h" 1 3 4
# 22 "/usr/include/bits/pthreadtypes-arch.h" 2 3 4
# 45 "/usr/include/bits/thread-shared-types.h" 2 3 4

# 1 "/usr/include/bits/atomic_wide_counter.h" 1 3 4
# 25 "/usr/include/bits/atomic_wide_counter.h" 3 4
typedef union
{
  __extension__ unsigned long long int __value64;
  struct
  {
    unsigned int __low;
    unsigned int __high;
  } __value32;
} __atomic_wide_counter;
# 47 "/usr/include/bits/thread-shared-types.h" 2 3 4




typedef struct __pthread_internal_list
{
  struct __pthread_internal_list *__prev;
  struct __pthread_internal_list *__next;
} __pthread_list_t;

typedef struct __pthread_internal_slist
{
  struct __pthread_internal_slist *__next;
} __pthread_slist_t;
# 76 "/usr/include/bits/thread-shared-types.h" 3 4
# 1 "/usr/include/bits/struct_mutex.h" 1 3 4
# 22 "/usr/include/bits/struct_mutex.h" 3 4
struct __pthread_mutex_s
{
  int __lock;
  unsigned int __count;
  int __owner;

  unsigned int __nusers;



  int __kind;

  short __spins;
  short __elision;
  __pthread_list_t __list;
# 53 "/usr/include/bits/struct_mutex.h" 3 4
};
# 77 "/usr/include/bits/thread-shared-types.h" 2 3 4
# 89 "/usr/include/bits/thread-shared-types.h" 3 4
# 1 "/usr/include/bits/struct_rwlock.h" 1 3 4
# 23 "/usr/include/bits/struct_rwlock.h" 3 4
struct __pthread_rwlock_arch_t
{
  unsigned int __readers;
  unsigned int __writers;
  unsigned int __wrphase_futex;
  unsigned int __writers_futex;
  unsigned int __pad3;
  unsigned int __pad4;

  int __cur_writer;
  int __shared;
  signed char __rwelision;




  unsigned char __pad1[7];


  unsigned long int __pad2;


  unsigned int __flags;
# 55 "/usr/include/bits/struct_rwlock.h" 3 4
};
# 90 "/usr/include/bits/thread-shared-types.h" 2 3 4




struct __pthread_cond_s
{
  __atomic_wide_counter __wseq;
  __atomic_wide_counter __g1_start;
  unsigned int __g_refs[2] ;
  unsigned int __g_size[2];
  unsigned int __g1_orig_size;
  unsigned int __wrefs;
  unsigned int __g_signals[2];
};

typedef unsigned int __tss_t;
typedef unsigned long int __thrd_t;

typedef struct
{
  int __data ;
} __once_flag;
# 24 "/usr/include/bits/pthreadtypes.h" 2 3 4



typedef unsigned long int pthread_t;




typedef union
{
  char __size[4];
  int __align;
} pthread_mutexattr_t;




typedef union
{
  char __size[4];
  int __align;
} pthread_condattr_t;



typedef unsigned int pthread_key_t;



typedef int pthread_once_t;


union pthread_attr_t
{
  char __size[56];
  long int __align;
};

typedef union pthread_attr_t pthread_attr_t;




typedef union
{
  struct __pthread_mutex_s __data;
  char __size[40];
  long int __align;
} pthread_mutex_t;


typedef union
{
  struct __pthread_cond_s __data;
  char __size[48];
  __extension__ long long int __align;
} pthread_cond_t;





typedef union
{
  struct __pthread_rwlock_arch_t __data;
  char __size[56];
  long int __align;
} pthread_rwlock_t;

typedef union
{
  char __size[8];
  long int __align;
} pthread_rwlockattr_t;





typedef volatile int pthread_spinlock_t;




typedef union
{
  char __size[32];
  long int __align;
} pthread_barrier_t;

typedef union
{
  char __size[4];
  int __align;
} pthread_barrierattr_t;
# 228 "/usr/include/sys/types.h" 2 3 4



# 396 "/usr/include/stdlib.h" 2 3 4






extern long int random (void) __attribute__ ((__nothrow__ , __leaf__));


extern void srandom (unsigned int __seed) __attribute__ ((__nothrow__ , __leaf__));





extern char *initstate (unsigned int __seed, char *__statebuf,
   size_t __statelen) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (2)));



extern char *setstate (char *__statebuf) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));







struct random_data
  {
    int32_t *fptr;
    int32_t *rptr;
    int32_t *state;
    int rand_type;
    int rand_deg;
    int rand_sep;
    int32_t *end_ptr;
  };

extern int random_r (struct random_data *__restrict __buf,
       int32_t *__restrict __result) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));

extern int srandom_r (unsigned int __seed, struct random_data *__buf)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (2)));

extern int initstate_r (unsigned int __seed, char *__restrict __statebuf,
   size_t __statelen,
   struct random_data *__restrict __buf)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (2, 4)));

extern int setstate_r (char *__restrict __statebuf,
         struct random_data *__restrict __buf)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));





extern int rand (void) __attribute__ ((__nothrow__ , __leaf__));

extern void srand (unsigned int __seed) __attribute__ ((__nothrow__ , __leaf__));



extern int rand_r (unsigned int *__seed) __attribute__ ((__nothrow__ , __leaf__));







extern double drand48 (void) __attribute__ ((__nothrow__ , __leaf__));
extern double erand48 (unsigned short int __xsubi[3]) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));


extern long int lrand48 (void) __attribute__ ((__nothrow__ , __leaf__));
extern long int nrand48 (unsigned short int __xsubi[3])
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));


extern long int mrand48 (void) __attribute__ ((__nothrow__ , __leaf__));
extern long int jrand48 (unsigned short int __xsubi[3])
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));


extern void srand48 (long int __seedval) __attribute__ ((__nothrow__ , __leaf__));
extern unsigned short int *seed48 (unsigned short int __seed16v[3])
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
extern void lcong48 (unsigned short int __param[7]) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));





struct drand48_data
  {
    unsigned short int __x[3];
    unsigned short int __old_x[3];
    unsigned short int __c;
    unsigned short int __init;
    __extension__ unsigned long long int __a;

  };


extern int drand48_r (struct drand48_data *__restrict __buffer,
        double *__restrict __result) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));
extern int erand48_r (unsigned short int __xsubi[3],
        struct drand48_data *__restrict __buffer,
        double *__restrict __result) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));


extern int lrand48_r (struct drand48_data *__restrict __buffer,
        long int *__restrict __result)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));
extern int nrand48_r (unsigned short int __xsubi[3],
        struct drand48_data *__restrict __buffer,
        long int *__restrict __result)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));


extern int mrand48_r (struct drand48_data *__restrict __buffer,
        long int *__restrict __result)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));
extern int jrand48_r (unsigned short int __xsubi[3],
        struct drand48_data *__restrict __buffer,
        long int *__restrict __result)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));


extern int srand48_r (long int __seedval, struct drand48_data *__buffer)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (2)));

extern int seed48_r (unsigned short int __seed16v[3],
       struct drand48_data *__buffer) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));

extern int lcong48_r (unsigned short int __param[7],
        struct drand48_data *__buffer)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));




extern void *malloc (size_t __size) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__))
     __attribute__ ((__alloc_size__ (1))) ;

extern void *calloc (size_t __nmemb, size_t __size)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__)) __attribute__ ((__alloc_size__ (1, 2))) ;






extern void *realloc (void *__ptr, size_t __size)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__warn_unused_result__)) __attribute__ ((__alloc_size__ (2)));


extern void free (void *__ptr) __attribute__ ((__nothrow__ , __leaf__));







extern void *reallocarray (void *__ptr, size_t __nmemb, size_t __size)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__warn_unused_result__))
     __attribute__ ((__alloc_size__ (2, 3)))
    __attribute__ ((__malloc__ (__builtin_free, 1)));


extern void *reallocarray (void *__ptr, size_t __nmemb, size_t __size)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__ (reallocarray, 1)));



# 1 "/usr/include/alloca.h" 1 3 4
# 24 "/usr/include/alloca.h" 3 4
# 1 "/usr/lib/gcc/x86_64-pc-linux-gnu/11.2.0/include/stddef.h" 1 3 4
# 25 "/usr/include/alloca.h" 2 3 4







extern void *alloca (size_t __size) __attribute__ ((__nothrow__ , __leaf__));






# 575 "/usr/include/stdlib.h" 2 3 4





extern void *valloc (size_t __size) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__))
     __attribute__ ((__alloc_size__ (1))) ;




extern int posix_memalign (void **__memptr, size_t __alignment, size_t __size)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1))) ;




extern void *aligned_alloc (size_t __alignment, size_t __size)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__)) __attribute__ ((__alloc_align__ (1)))
     __attribute__ ((__alloc_size__ (2))) ;



extern void abort (void) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));



extern int atexit (void (*__func) (void)) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));







extern int at_quick_exit (void (*__func) (void)) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));






extern int on_exit (void (*__func) (int __status, void *__arg), void *__arg)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));





extern void exit (int __status) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));





extern void quick_exit (int __status) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));





extern void _Exit (int __status) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));




extern char *getenv (const char *__name) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1))) ;
# 654 "/usr/include/stdlib.h" 3 4
extern int putenv (char *__string) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));





extern int setenv (const char *__name, const char *__value, int __replace)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (2)));


extern int unsetenv (const char *__name) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));






extern int clearenv (void) __attribute__ ((__nothrow__ , __leaf__));
# 682 "/usr/include/stdlib.h" 3 4
extern char *mktemp (char *__template) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
# 695 "/usr/include/stdlib.h" 3 4
extern int mkstemp (char *__template) __attribute__ ((__nonnull__ (1))) ;
# 717 "/usr/include/stdlib.h" 3 4
extern int mkstemps (char *__template, int __suffixlen) __attribute__ ((__nonnull__ (1))) ;
# 738 "/usr/include/stdlib.h" 3 4
extern char *mkdtemp (char *__template) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1))) ;
# 791 "/usr/include/stdlib.h" 3 4
extern int system (const char *__command) ;
# 808 "/usr/include/stdlib.h" 3 4
extern char *realpath (const char *__restrict __name,
         char *__restrict __resolved) __attribute__ ((__nothrow__ , __leaf__)) ;






typedef int (*__compar_fn_t) (const void *, const void *);
# 828 "/usr/include/stdlib.h" 3 4
extern void *bsearch (const void *__key, const void *__base,
        size_t __nmemb, size_t __size, __compar_fn_t __compar)
     __attribute__ ((__nonnull__ (1, 2, 5))) ;


# 1 "/usr/include/bits/stdlib-bsearch.h" 1 3 4
# 19 "/usr/include/bits/stdlib-bsearch.h" 3 4
extern __inline __attribute__ ((__gnu_inline__)) void *
bsearch (const void *__key, const void *__base, size_t __nmemb, size_t __size,
  __compar_fn_t __compar)
{
  size_t __l, __u, __idx;
  const void *__p;
  int __comparison;

  __l = 0;
  __u = __nmemb;
  while (__l < __u)
    {
      __idx = (__l + __u) / 2;
      __p = (const void *) (((const char *) __base) + (__idx * __size));
      __comparison = (*__compar) (__key, __p);
      if (__comparison < 0)
 __u = __idx;
      else if (__comparison > 0)
 __l = __idx + 1;
      else
 {

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wcast-qual"

   return (void *) __p;

#pragma GCC diagnostic pop

 }
    }

  return ((void *)0);
}
# 834 "/usr/include/stdlib.h" 2 3 4




extern void qsort (void *__base, size_t __nmemb, size_t __size,
     __compar_fn_t __compar) __attribute__ ((__nonnull__ (1, 4)));
# 848 "/usr/include/stdlib.h" 3 4
extern int abs (int __x) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__)) ;
extern long int labs (long int __x) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__)) ;


__extension__ extern long long int llabs (long long int __x)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__)) ;






extern div_t div (int __numer, int __denom)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__)) ;
extern ldiv_t ldiv (long int __numer, long int __denom)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__)) ;


__extension__ extern lldiv_t lldiv (long long int __numer,
        long long int __denom)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__)) ;
# 880 "/usr/include/stdlib.h" 3 4
extern char *ecvt (double __value, int __ndigit, int *__restrict __decpt,
     int *__restrict __sign) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (3, 4))) ;




extern char *fcvt (double __value, int __ndigit, int *__restrict __decpt,
     int *__restrict __sign) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (3, 4))) ;




extern char *gcvt (double __value, int __ndigit, char *__buf)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (3))) ;




extern char *qecvt (long double __value, int __ndigit,
      int *__restrict __decpt, int *__restrict __sign)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (3, 4))) ;
extern char *qfcvt (long double __value, int __ndigit,
      int *__restrict __decpt, int *__restrict __sign)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (3, 4))) ;
extern char *qgcvt (long double __value, int __ndigit, char *__buf)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (3))) ;




extern int ecvt_r (double __value, int __ndigit, int *__restrict __decpt,
     int *__restrict __sign, char *__restrict __buf,
     size_t __len) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (3, 4, 5)));
extern int fcvt_r (double __value, int __ndigit, int *__restrict __decpt,
     int *__restrict __sign, char *__restrict __buf,
     size_t __len) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (3, 4, 5)));

extern int qecvt_r (long double __value, int __ndigit,
      int *__restrict __decpt, int *__restrict __sign,
      char *__restrict __buf, size_t __len)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (3, 4, 5)));
extern int qfcvt_r (long double __value, int __ndigit,
      int *__restrict __decpt, int *__restrict __sign,
      char *__restrict __buf, size_t __len)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (3, 4, 5)));





extern int mblen (const char *__s, size_t __n) __attribute__ ((__nothrow__ , __leaf__));


extern int mbtowc (wchar_t *__restrict __pwc,
     const char *__restrict __s, size_t __n) __attribute__ ((__nothrow__ , __leaf__));


extern int wctomb (char *__s, wchar_t __wchar) __attribute__ ((__nothrow__ , __leaf__));



extern size_t mbstowcs (wchar_t *__restrict __pwcs,
   const char *__restrict __s, size_t __n) __attribute__ ((__nothrow__ , __leaf__))
    __attribute__ ((__access__ (__read_only__, 2)));

extern size_t wcstombs (char *__restrict __s,
   const wchar_t *__restrict __pwcs, size_t __n)
     __attribute__ ((__nothrow__ , __leaf__))
  __attribute__ ((__access__ (__write_only__, 1, 3)))
  __attribute__ ((__access__ (__read_only__, 2)));






extern int rpmatch (const char *__response) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1))) ;
# 967 "/usr/include/stdlib.h" 3 4
extern int getsubopt (char **__restrict __optionp,
        char *const *__restrict __tokens,
        char **__restrict __valuep)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2, 3))) ;
# 1013 "/usr/include/stdlib.h" 3 4
extern int getloadavg (double __loadavg[], int __nelem)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
# 1023 "/usr/include/stdlib.h" 3 4
# 1 "/usr/include/bits/stdlib-float.h" 1 3 4
# 24 "/usr/include/bits/stdlib-float.h" 3 4
extern __inline __attribute__ ((__gnu_inline__)) double
__attribute__ ((__nothrow__ , __leaf__)) atof (const char *__nptr)
{
  return strtod (__nptr, (char **) ((void *)0));
}
# 1024 "/usr/include/stdlib.h" 2 3 4
# 1035 "/usr/include/stdlib.h" 3 4

# 171 "regint.h" 2







# 1 "/usr/include/string.h" 1 3 4
# 26 "/usr/include/string.h" 3 4
# 1 "/usr/include/bits/libc-header-start.h" 1 3 4
# 27 "/usr/include/string.h" 2 3 4






# 1 "/usr/lib/gcc/x86_64-pc-linux-gnu/11.2.0/include/stddef.h" 1 3 4
# 34 "/usr/include/string.h" 2 3 4
# 43 "/usr/include/string.h" 3 4
extern void *memcpy (void *__restrict __dest, const void *__restrict __src,
       size_t __n) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));


extern void *memmove (void *__dest, const void *__src, size_t __n)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));





extern void *memccpy (void *__restrict __dest, const void *__restrict __src,
        int __c, size_t __n)
    __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2))) __attribute__ ((__access__ (__write_only__, 1, 4)));




extern void *memset (void *__s, int __c, size_t __n) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));


extern int memcmp (const void *__s1, const void *__s2, size_t __n)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1, 2)));
# 80 "/usr/include/string.h" 3 4
extern int __memcmpeq (const void *__s1, const void *__s2, size_t __n)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1, 2)));
# 107 "/usr/include/string.h" 3 4
extern void *memchr (const void *__s, int __c, size_t __n)
      __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1)));
# 141 "/usr/include/string.h" 3 4
extern char *strcpy (char *__restrict __dest, const char *__restrict __src)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));

extern char *strncpy (char *__restrict __dest,
        const char *__restrict __src, size_t __n)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));


extern char *strcat (char *__restrict __dest, const char *__restrict __src)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));

extern char *strncat (char *__restrict __dest, const char *__restrict __src,
        size_t __n) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));


extern int strcmp (const char *__s1, const char *__s2)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1, 2)));

extern int strncmp (const char *__s1, const char *__s2, size_t __n)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1, 2)));


extern int strcoll (const char *__s1, const char *__s2)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1, 2)));

extern size_t strxfrm (char *__restrict __dest,
         const char *__restrict __src, size_t __n)
    __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (2))) __attribute__ ((__access__ (__write_only__, 1, 3)));



# 1 "/usr/include/bits/types/locale_t.h" 1 3 4
# 22 "/usr/include/bits/types/locale_t.h" 3 4
# 1 "/usr/include/bits/types/__locale_t.h" 1 3 4
# 27 "/usr/include/bits/types/__locale_t.h" 3 4
struct __locale_struct
{

  struct __locale_data *__locales[13];


  const unsigned short int *__ctype_b;
  const int *__ctype_tolower;
  const int *__ctype_toupper;


  const char *__names[13];
};

typedef struct __locale_struct *__locale_t;
# 23 "/usr/include/bits/types/locale_t.h" 2 3 4

typedef __locale_t locale_t;
# 173 "/usr/include/string.h" 2 3 4


extern int strcoll_l (const char *__s1, const char *__s2, locale_t __l)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1, 2, 3)));


extern size_t strxfrm_l (char *__dest, const char *__src, size_t __n,
    locale_t __l) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (2, 4)))
     __attribute__ ((__access__ (__write_only__, 1, 3)));





extern char *strdup (const char *__s)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__)) __attribute__ ((__nonnull__ (1)));






extern char *strndup (const char *__string, size_t __n)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__)) __attribute__ ((__nonnull__ (1)));
# 246 "/usr/include/string.h" 3 4
extern char *strchr (const char *__s, int __c)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1)));
# 273 "/usr/include/string.h" 3 4
extern char *strrchr (const char *__s, int __c)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1)));
# 293 "/usr/include/string.h" 3 4
extern size_t strcspn (const char *__s, const char *__reject)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1, 2)));


extern size_t strspn (const char *__s, const char *__accept)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1, 2)));
# 323 "/usr/include/string.h" 3 4
extern char *strpbrk (const char *__s, const char *__accept)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1, 2)));
# 350 "/usr/include/string.h" 3 4
extern char *strstr (const char *__haystack, const char *__needle)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1, 2)));




extern char *strtok (char *__restrict __s, const char *__restrict __delim)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (2)));



extern char *__strtok_r (char *__restrict __s,
    const char *__restrict __delim,
    char **__restrict __save_ptr)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (2, 3)));

extern char *strtok_r (char *__restrict __s, const char *__restrict __delim,
         char **__restrict __save_ptr)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (2, 3)));
# 407 "/usr/include/string.h" 3 4
extern size_t strlen (const char *__s)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1)));




extern size_t strnlen (const char *__string, size_t __maxlen)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1)));




extern char *strerror (int __errnum) __attribute__ ((__nothrow__ , __leaf__));
# 432 "/usr/include/string.h" 3 4
extern int strerror_r (int __errnum, char *__buf, size_t __buflen) __asm__ ("" "__xpg_strerror_r") __attribute__ ((__nothrow__ , __leaf__))

                        __attribute__ ((__nonnull__ (2)))
    __attribute__ ((__access__ (__write_only__, 2, 3)));
# 458 "/usr/include/string.h" 3 4
extern char *strerror_l (int __errnum, locale_t __l) __attribute__ ((__nothrow__ , __leaf__));



# 1 "/usr/include/strings.h" 1 3 4
# 23 "/usr/include/strings.h" 3 4
# 1 "/usr/lib/gcc/x86_64-pc-linux-gnu/11.2.0/include/stddef.h" 1 3 4
# 24 "/usr/include/strings.h" 2 3 4










extern int bcmp (const void *__s1, const void *__s2, size_t __n)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1, 2)));


extern void bcopy (const void *__src, void *__dest, size_t __n)
  __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));


extern void bzero (void *__s, size_t __n) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
# 68 "/usr/include/strings.h" 3 4
extern char *index (const char *__s, int __c)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1)));
# 96 "/usr/include/strings.h" 3 4
extern char *rindex (const char *__s, int __c)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1)));






extern int ffs (int __i) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));





extern int ffsl (long int __l) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
__extension__ extern int ffsll (long long int __ll)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));



extern int strcasecmp (const char *__s1, const char *__s2)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1, 2)));


extern int strncasecmp (const char *__s1, const char *__s2, size_t __n)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1, 2)));






extern int strcasecmp_l (const char *__s1, const char *__s2, locale_t __loc)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1, 2, 3)));



extern int strncasecmp_l (const char *__s1, const char *__s2,
     size_t __n, locale_t __loc)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1, 2, 4)));



# 463 "/usr/include/string.h" 2 3 4



extern void explicit_bzero (void *__s, size_t __n) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)))
    __attribute__ ((__access__ (__write_only__, 1, 2)));



extern char *strsep (char **__restrict __stringp,
       const char *__restrict __delim)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));




extern char *strsignal (int __sig) __attribute__ ((__nothrow__ , __leaf__));
# 489 "/usr/include/string.h" 3 4
extern char *__stpcpy (char *__restrict __dest, const char *__restrict __src)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));
extern char *stpcpy (char *__restrict __dest, const char *__restrict __src)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));



extern char *__stpncpy (char *__restrict __dest,
   const char *__restrict __src, size_t __n)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));
extern char *stpncpy (char *__restrict __dest,
        const char *__restrict __src, size_t __n)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));
# 539 "/usr/include/string.h" 3 4

# 179 "regint.h" 2




# 1 "/usr/include/ctype.h" 1 3 4
# 28 "/usr/include/ctype.h" 3 4

# 46 "/usr/include/ctype.h" 3 4
enum
{
  _ISupper = ((0) < 8 ? ((1 << (0)) << 8) : ((1 << (0)) >> 8)),
  _ISlower = ((1) < 8 ? ((1 << (1)) << 8) : ((1 << (1)) >> 8)),
  _ISalpha = ((2) < 8 ? ((1 << (2)) << 8) : ((1 << (2)) >> 8)),
  _ISdigit = ((3) < 8 ? ((1 << (3)) << 8) : ((1 << (3)) >> 8)),
  _ISxdigit = ((4) < 8 ? ((1 << (4)) << 8) : ((1 << (4)) >> 8)),
  _ISspace = ((5) < 8 ? ((1 << (5)) << 8) : ((1 << (5)) >> 8)),
  _ISprint = ((6) < 8 ? ((1 << (6)) << 8) : ((1 << (6)) >> 8)),
  _ISgraph = ((7) < 8 ? ((1 << (7)) << 8) : ((1 << (7)) >> 8)),
  _ISblank = ((8) < 8 ? ((1 << (8)) << 8) : ((1 << (8)) >> 8)),
  _IScntrl = ((9) < 8 ? ((1 << (9)) << 8) : ((1 << (9)) >> 8)),
  _ISpunct = ((10) < 8 ? ((1 << (10)) << 8) : ((1 << (10)) >> 8)),
  _ISalnum = ((11) < 8 ? ((1 << (11)) << 8) : ((1 << (11)) >> 8))
};
# 79 "/usr/include/ctype.h" 3 4
extern const unsigned short int **__ctype_b_loc (void)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern const __int32_t **__ctype_tolower_loc (void)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern const __int32_t **__ctype_toupper_loc (void)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
# 108 "/usr/include/ctype.h" 3 4
extern int isalnum (int) __attribute__ ((__nothrow__ , __leaf__));
extern int isalpha (int) __attribute__ ((__nothrow__ , __leaf__));
extern int iscntrl (int) __attribute__ ((__nothrow__ , __leaf__));
extern int isdigit (int) __attribute__ ((__nothrow__ , __leaf__));
extern int islower (int) __attribute__ ((__nothrow__ , __leaf__));
extern int isgraph (int) __attribute__ ((__nothrow__ , __leaf__));
extern int isprint (int) __attribute__ ((__nothrow__ , __leaf__));
extern int ispunct (int) __attribute__ ((__nothrow__ , __leaf__));
extern int isspace (int) __attribute__ ((__nothrow__ , __leaf__));
extern int isupper (int) __attribute__ ((__nothrow__ , __leaf__));
extern int isxdigit (int) __attribute__ ((__nothrow__ , __leaf__));



extern int tolower (int __c) __attribute__ ((__nothrow__ , __leaf__));


extern int toupper (int __c) __attribute__ ((__nothrow__ , __leaf__));




extern int isblank (int) __attribute__ ((__nothrow__ , __leaf__));
# 142 "/usr/include/ctype.h" 3 4
extern int isascii (int __c) __attribute__ ((__nothrow__ , __leaf__));



extern int toascii (int __c) __attribute__ ((__nothrow__ , __leaf__));



extern int _toupper (int) __attribute__ ((__nothrow__ , __leaf__));
extern int _tolower (int) __attribute__ ((__nothrow__ , __leaf__));
# 206 "/usr/include/ctype.h" 3 4
extern __inline __attribute__ ((__gnu_inline__)) int
__attribute__ ((__nothrow__ , __leaf__)) tolower (int __c)
{
  return __c >= -128 && __c < 256 ? (*__ctype_tolower_loc ())[__c] : __c;
}

extern __inline __attribute__ ((__gnu_inline__)) int
__attribute__ ((__nothrow__ , __leaf__)) toupper (int __c)
{
  return __c >= -128 && __c < 256 ? (*__ctype_toupper_loc ())[__c] : __c;
}
# 251 "/usr/include/ctype.h" 3 4
extern int isalnum_l (int, locale_t) __attribute__ ((__nothrow__ , __leaf__));
extern int isalpha_l (int, locale_t) __attribute__ ((__nothrow__ , __leaf__));
extern int iscntrl_l (int, locale_t) __attribute__ ((__nothrow__ , __leaf__));
extern int isdigit_l (int, locale_t) __attribute__ ((__nothrow__ , __leaf__));
extern int islower_l (int, locale_t) __attribute__ ((__nothrow__ , __leaf__));
extern int isgraph_l (int, locale_t) __attribute__ ((__nothrow__ , __leaf__));
extern int isprint_l (int, locale_t) __attribute__ ((__nothrow__ , __leaf__));
extern int ispunct_l (int, locale_t) __attribute__ ((__nothrow__ , __leaf__));
extern int isspace_l (int, locale_t) __attribute__ ((__nothrow__ , __leaf__));
extern int isupper_l (int, locale_t) __attribute__ ((__nothrow__ , __leaf__));
extern int isxdigit_l (int, locale_t) __attribute__ ((__nothrow__ , __leaf__));

extern int isblank_l (int, locale_t) __attribute__ ((__nothrow__ , __leaf__));



extern int __tolower_l (int __c, locale_t __l) __attribute__ ((__nothrow__ , __leaf__));
extern int tolower_l (int __c, locale_t __l) __attribute__ ((__nothrow__ , __leaf__));


extern int __toupper_l (int __c, locale_t __l) __attribute__ ((__nothrow__ , __leaf__));
extern int toupper_l (int __c, locale_t __l) __attribute__ ((__nothrow__ , __leaf__));
# 327 "/usr/include/ctype.h" 3 4

# 184 "regint.h" 2
# 198 "regint.h"
# 1 "regenc.h" 1
# 41 "regenc.h"
# 1 "oniguruma.h" 1
# 99 "oniguruma.h"

# 99 "oniguruma.h"
typedef unsigned char OnigUChar;
typedef unsigned long OnigCodePoint;
typedef unsigned int OnigCtype;
typedef unsigned int OnigDistance;



typedef unsigned int OnigCaseFoldType;

extern OnigCaseFoldType OnigDefaultCaseFoldFlag;
# 128 "oniguruma.h"
typedef struct {
  int byte_len;
  int code_len;
  OnigCodePoint code[3];
} OnigCaseFoldCodeItem;

typedef struct {
  OnigCodePoint esc;
  OnigCodePoint anychar;
  OnigCodePoint anytime;
  OnigCodePoint zero_or_one_time;
  OnigCodePoint one_or_more_time;
  OnigCodePoint anychar_anytime;
} OnigMetaCharTableType;

typedef int (*OnigApplyAllCaseFoldFunc)(OnigCodePoint from, OnigCodePoint* to, int to_len, void* arg);

typedef struct OnigEncodingTypeST {
  int (*mbc_enc_len)(const OnigUChar* p);
  const char* name;
  int max_enc_len;
  int min_enc_len;
  int (*is_mbc_newline)(const OnigUChar* p, const OnigUChar* end);
  OnigCodePoint (*mbc_to_code)(const OnigUChar* p, const OnigUChar* end);
  int (*code_to_mbclen)(OnigCodePoint code);
  int (*code_to_mbc)(OnigCodePoint code, OnigUChar *buf);
  int (*mbc_case_fold)(OnigCaseFoldType flag, const OnigUChar** pp, const OnigUChar* end, OnigUChar* to);
  int (*apply_all_case_fold)(OnigCaseFoldType flag, OnigApplyAllCaseFoldFunc f, void* arg);
  int (*get_case_fold_codes_by_str)(OnigCaseFoldType flag, const OnigUChar* p, const OnigUChar* end, OnigCaseFoldCodeItem acs[]);
  int (*property_name_to_ctype)(struct OnigEncodingTypeST* enc, OnigUChar* p, OnigUChar* end);
  int (*is_code_ctype)(OnigCodePoint code, OnigCtype ctype);
  int (*get_ctype_code_range)(OnigCtype ctype, OnigCodePoint* sb_out, const OnigCodePoint* ranges[]);
  OnigUChar* (*left_adjust_char_head)(const OnigUChar* start, const OnigUChar* p);
  int (*is_allowed_reverse_match)(const OnigUChar* p, const OnigUChar* end);
} OnigEncodingType;

typedef OnigEncodingType* OnigEncoding;

extern OnigEncodingType OnigEncodingASCII;
extern OnigEncodingType OnigEncodingISO_8859_1;
extern OnigEncodingType OnigEncodingISO_8859_2;
extern OnigEncodingType OnigEncodingISO_8859_3;
extern OnigEncodingType OnigEncodingISO_8859_4;
extern OnigEncodingType OnigEncodingISO_8859_5;
extern OnigEncodingType OnigEncodingISO_8859_6;
extern OnigEncodingType OnigEncodingISO_8859_7;
extern OnigEncodingType OnigEncodingISO_8859_8;
extern OnigEncodingType OnigEncodingISO_8859_9;
extern OnigEncodingType OnigEncodingISO_8859_10;
extern OnigEncodingType OnigEncodingISO_8859_11;
extern OnigEncodingType OnigEncodingISO_8859_13;
extern OnigEncodingType OnigEncodingISO_8859_14;
extern OnigEncodingType OnigEncodingISO_8859_15;
extern OnigEncodingType OnigEncodingISO_8859_16;
extern OnigEncodingType OnigEncodingUTF8;
extern OnigEncodingType OnigEncodingUTF16_BE;
extern OnigEncodingType OnigEncodingUTF16_LE;
extern OnigEncodingType OnigEncodingUTF32_BE;
extern OnigEncodingType OnigEncodingUTF32_LE;
extern OnigEncodingType OnigEncodingEUC_JP;
extern OnigEncodingType OnigEncodingEUC_TW;
extern OnigEncodingType OnigEncodingEUC_KR;
extern OnigEncodingType OnigEncodingEUC_CN;
extern OnigEncodingType OnigEncodingSJIS;
extern OnigEncodingType OnigEncodingKOI8;
extern OnigEncodingType OnigEncodingKOI8_R;
extern OnigEncodingType OnigEncodingCP1251;
extern OnigEncodingType OnigEncodingBIG5;
extern OnigEncodingType OnigEncodingGB18030;
# 328 "oniguruma.h"
extern
OnigUChar* onigenc_step_back (OnigEncoding enc, const OnigUChar* start, const OnigUChar* s, int n);



extern
int onigenc_init (void);
extern
int onigenc_set_default_encoding (OnigEncoding enc);
extern
OnigEncoding onigenc_get_default_encoding (void);
extern
void onigenc_set_default_caseconv_table (const OnigUChar* table);
extern
OnigUChar* onigenc_get_right_adjust_char_head_with_prev (OnigEncoding enc, const OnigUChar* start, const OnigUChar* s, const OnigUChar** prev);
extern
OnigUChar* onigenc_get_prev_char_head (OnigEncoding enc, const OnigUChar* start, const OnigUChar* s);
extern
OnigUChar* onigenc_get_left_adjust_char_head (OnigEncoding enc, const OnigUChar* start, const OnigUChar* s);
extern
OnigUChar* onigenc_get_right_adjust_char_head (OnigEncoding enc, const OnigUChar* start, const OnigUChar* s);
extern
int onigenc_strlen (OnigEncoding enc, const OnigUChar* p, const OnigUChar* end);
extern
int onigenc_strlen_null (OnigEncoding enc, const OnigUChar* p);
extern
int onigenc_str_bytelen_null (OnigEncoding enc, const OnigUChar* p);
# 368 "oniguruma.h"
typedef unsigned int OnigOptionType;
# 394 "oniguruma.h"
typedef struct {
  unsigned int op;
  unsigned int op2;
  unsigned int behavior;
  OnigOptionType options;
  OnigMetaCharTableType meta_char_table;
} OnigSyntaxType;

extern OnigSyntaxType OnigSyntaxASIS;
extern OnigSyntaxType OnigSyntaxPosixBasic;
extern OnigSyntaxType OnigSyntaxPosixExtended;
extern OnigSyntaxType OnigSyntaxEmacs;
extern OnigSyntaxType OnigSyntaxGrep;
extern OnigSyntaxType OnigSyntaxGnuRegex;
extern OnigSyntaxType OnigSyntaxJava;
extern OnigSyntaxType OnigSyntaxPerl;
extern OnigSyntaxType OnigSyntaxPerl_NG;
extern OnigSyntaxType OnigSyntaxRuby;
# 426 "oniguruma.h"
extern OnigSyntaxType* OnigDefaultSyntax;
# 595 "oniguruma.h"
typedef struct OnigCaptureTreeNodeStruct {
  int group;
  int beg;
  int end;
  int allocated;
  int num_childs;
  struct OnigCaptureTreeNodeStruct** childs;
} OnigCaptureTreeNode;


struct re_registers {
  int allocated;
  int num_regs;
  int* beg;
  int* end;

  OnigCaptureTreeNode* history_root;
};
# 623 "oniguruma.h"
typedef struct re_registers OnigRegion;

typedef struct {
  OnigEncoding enc;
  OnigUChar* par;
  OnigUChar* par_end;
} OnigErrorInfo;

typedef struct {
  int lower;
  int upper;
} OnigRepeatRange;

typedef void (*OnigWarnFunc) (const char* s);
extern void onig_null_warn (const char* s);
# 651 "oniguruma.h"
typedef struct re_pattern_buffer {

  unsigned char* p;
  unsigned int used;
  unsigned int alloc;

  int state;
  int num_mem;
  int num_repeat;
  int num_null_check;
  int num_comb_exp_check;
  int num_call;
  unsigned int capture_history;
  unsigned int bt_mem_start;
  unsigned int bt_mem_end;
  int stack_pop_level;
  int repeat_range_alloc;
  OnigRepeatRange* repeat_range;

  OnigEncoding enc;
  OnigOptionType options;
  OnigSyntaxType* syntax;
  OnigCaseFoldType case_fold_flag;
  void* name_table;


  int optimize;
  int threshold_len;
  int anchor;
  OnigDistance anchor_dmin;
  OnigDistance anchor_dmax;
  int sub_anchor;
  unsigned char *exact;
  unsigned char *exact_end;
  unsigned char map[256];
  int *int_map;
  int *int_map_backward;
  OnigDistance dmin;
  OnigDistance dmax;


  struct re_pattern_buffer* chain;
} OnigRegexType;

typedef OnigRegexType* OnigRegex;


  typedef OnigRegexType regex_t;



typedef struct {
  int num_of_elements;
  OnigEncoding pattern_enc;
  OnigEncoding target_enc;
  OnigSyntaxType* syntax;
  OnigOptionType option;
  OnigCaseFoldType case_fold_flag;
} OnigCompileInfo;


extern
int onig_init (void);
extern
int onig_error_code_to_str (OnigUChar* s, int err_code, ...);
extern
void onig_set_warn_func (OnigWarnFunc f);
extern
void onig_set_verb_warn_func (OnigWarnFunc f);
extern
int onig_new (OnigRegex*, const OnigUChar* pattern, const OnigUChar* pattern_end, OnigOptionType option, OnigEncoding enc, OnigSyntaxType* syntax, OnigErrorInfo* einfo);
extern
int onig_reg_init (regex_t* reg, OnigOptionType option, OnigCaseFoldType case_fold_flag, OnigEncoding enc, OnigSyntaxType* syntax);
int onig_new_without_alloc (OnigRegex, const OnigUChar* pattern, const OnigUChar* pattern_end, OnigOptionType option, OnigEncoding enc, OnigSyntaxType* syntax, OnigErrorInfo* einfo);
extern
int onig_new_deluxe (OnigRegex* reg, const OnigUChar* pattern, const OnigUChar* pattern_end, OnigCompileInfo* ci, OnigErrorInfo* einfo);
extern
void onig_free (OnigRegex);
extern
void onig_free_body (OnigRegex);
extern
int onig_recompile (OnigRegex, const OnigUChar* pattern, const OnigUChar* pattern_end, OnigOptionType option, OnigEncoding enc, OnigSyntaxType* syntax, OnigErrorInfo* einfo);
extern
int onig_recompile_deluxe (OnigRegex reg, const OnigUChar* pattern, const OnigUChar* pattern_end, OnigCompileInfo* ci, OnigErrorInfo* einfo);
extern
int onig_search (OnigRegex, const OnigUChar* str, const OnigUChar* end, const OnigUChar* start, const OnigUChar* range, OnigRegion* region, OnigOptionType option);
extern
int onig_match (OnigRegex, const OnigUChar* str, const OnigUChar* end, const OnigUChar* at, OnigRegion* region, OnigOptionType option);
extern
OnigRegion* onig_region_new (void);
extern
void onig_region_init (OnigRegion* region);
extern
void onig_region_free (OnigRegion* region, int free_self);
extern
void onig_region_copy (OnigRegion* to, OnigRegion* from);
extern
void onig_region_clear (OnigRegion* region);
extern
int onig_region_resize (OnigRegion* region, int n);
extern
int onig_region_set (OnigRegion* region, int at, int beg, int end);
extern
int onig_name_to_group_numbers (OnigRegex reg, const OnigUChar* name, const OnigUChar* name_end, int** nums);
extern
int onig_name_to_backref_number (OnigRegex reg, const OnigUChar* name, const OnigUChar* name_end, OnigRegion *region);
extern
int onig_foreach_name (OnigRegex reg, int (*func)(const OnigUChar*, const OnigUChar*,int,int*,OnigRegex,void*), void* arg);
extern
int onig_number_of_names (OnigRegex reg);
extern
int onig_number_of_captures (OnigRegex reg);
extern
int onig_number_of_capture_histories (OnigRegex reg);
extern
OnigCaptureTreeNode* onig_get_capture_tree (OnigRegion* region);
extern
int onig_capture_tree_traverse (OnigRegion* region, int at, int(*callback_func)(int,int,int,int,int,void*), void* arg);
extern
int onig_noname_group_capture_is_active (OnigRegex reg);
extern
OnigEncoding onig_get_encoding (OnigRegex reg);
extern
OnigOptionType onig_get_options (OnigRegex reg);
extern
OnigCaseFoldType onig_get_case_fold_flag (OnigRegex reg);
extern
OnigSyntaxType* onig_get_syntax (OnigRegex reg);
extern
int onig_set_default_syntax (OnigSyntaxType* syntax);
extern
void onig_copy_syntax (OnigSyntaxType* to, OnigSyntaxType* from);
extern
unsigned int onig_get_syntax_op (OnigSyntaxType* syntax);
extern
unsigned int onig_get_syntax_op2 (OnigSyntaxType* syntax);
extern
unsigned int onig_get_syntax_behavior (OnigSyntaxType* syntax);
extern
OnigOptionType onig_get_syntax_options (OnigSyntaxType* syntax);
extern
void onig_set_syntax_op (OnigSyntaxType* syntax, unsigned int op);
extern
void onig_set_syntax_op2 (OnigSyntaxType* syntax, unsigned int op2);
extern
void onig_set_syntax_behavior (OnigSyntaxType* syntax, unsigned int behavior);
extern
void onig_set_syntax_options (OnigSyntaxType* syntax, OnigOptionType options);
extern
int onig_set_meta_char (OnigSyntaxType* syntax, unsigned int what, OnigCodePoint code);
extern
void onig_copy_encoding (OnigEncoding to, OnigEncoding from);
extern
OnigCaseFoldType onig_get_default_case_fold_flag (void);
extern
int onig_set_default_case_fold_flag (OnigCaseFoldType case_fold_flag);
extern
unsigned int onig_get_match_stack_limit_size (void);
extern
int onig_set_match_stack_limit_size (unsigned int size);
extern
int onig_end (void);
extern
const char* onig_version (void);
extern
const char* onig_copyright (void);
# 42 "regenc.h" 2

typedef struct {
  OnigCodePoint from;
  OnigCodePoint to;
} OnigPairCaseFoldCodes;
# 99 "regenc.h"
typedef struct {
  OnigUChar *name;
  int ctype;
  short int len;
} PosixBracketEntryType;
# 115 "regenc.h"
extern int onigenc_ascii_apply_all_case_fold (OnigCaseFoldType flag, OnigApplyAllCaseFoldFunc f, void* arg);
extern int onigenc_ascii_get_case_fold_codes_by_str (OnigCaseFoldType flag, const OnigUChar* p, const OnigUChar* end, OnigCaseFoldCodeItem items[]);
extern int onigenc_apply_all_case_fold_with_map (int map_size, const OnigPairCaseFoldCodes map[], int ess_tsett_flag, OnigCaseFoldType flag, OnigApplyAllCaseFoldFunc f, void* arg);
extern int onigenc_get_case_fold_codes_by_str_with_map (int map_size, const OnigPairCaseFoldCodes map[], int ess_tsett_flag, OnigCaseFoldType flag, const OnigUChar* p, const OnigUChar* end, OnigCaseFoldCodeItem items[]);
extern int onigenc_not_support_get_ctype_code_range (OnigCtype ctype, OnigCodePoint* sb_out, const OnigCodePoint* ranges[]);
extern int onigenc_is_mbc_newline_0x0a (const OnigUChar* p, const OnigUChar* end);



extern int onigenc_ascii_mbc_case_fold (OnigCaseFoldType flag, const OnigUChar** p, const OnigUChar* end, OnigUChar* lower);
extern int onigenc_single_byte_mbc_enc_len (const OnigUChar* p);
extern OnigCodePoint onigenc_single_byte_mbc_to_code (const OnigUChar* p, const OnigUChar* end);
extern int onigenc_single_byte_code_to_mbclen (OnigCodePoint code);
extern int onigenc_single_byte_code_to_mbc (OnigCodePoint code, OnigUChar *buf);
extern OnigUChar* onigenc_single_byte_left_adjust_char_head (const OnigUChar* start, const OnigUChar* s);
extern int onigenc_always_true_is_allowed_reverse_match (const OnigUChar* s, const OnigUChar* end);
extern int onigenc_always_false_is_allowed_reverse_match (const OnigUChar* s, const OnigUChar* end);


extern OnigCodePoint onigenc_mbn_mbc_to_code (OnigEncoding enc, const OnigUChar* p, const OnigUChar* end);
extern int onigenc_mbn_mbc_case_fold (OnigEncoding enc, OnigCaseFoldType flag, const OnigUChar** p, const OnigUChar* end, OnigUChar* lower);
extern int onigenc_mb2_code_to_mbclen (OnigCodePoint code);
extern int onigenc_mb2_code_to_mbc (OnigEncoding enc, OnigCodePoint code, OnigUChar *buf);
extern int onigenc_minimum_property_name_to_ctype (OnigEncoding enc, OnigUChar* p, OnigUChar* end);
extern int onigenc_unicode_property_name_to_ctype (OnigEncoding enc, OnigUChar* p, OnigUChar* end);
extern int onigenc_mb2_is_code_ctype (OnigEncoding enc, OnigCodePoint code, unsigned int ctype);
extern int onigenc_mb4_code_to_mbclen (OnigCodePoint code);
extern int onigenc_mb4_code_to_mbc (OnigEncoding enc, OnigCodePoint code, OnigUChar *buf);
extern int onigenc_mb4_is_code_ctype (OnigEncoding enc, OnigCodePoint code, unsigned int ctype);



extern int onigenc_unicode_is_code_ctype (OnigCodePoint code, unsigned int ctype);
extern int onigenc_utf16_32_get_ctype_code_range (OnigCtype ctype, OnigCodePoint *sb_out, const OnigCodePoint* ranges[]);
extern int onigenc_unicode_ctype_code_range (int ctype, const OnigCodePoint* ranges[]);
extern int onigenc_unicode_get_case_fold_codes_by_str (OnigEncoding enc, OnigCaseFoldType flag, const OnigUChar* p, const OnigUChar* end, OnigCaseFoldCodeItem items[]);
extern int onigenc_unicode_mbc_case_fold (OnigEncoding enc, OnigCaseFoldType flag, const OnigUChar** pp, const OnigUChar* end, OnigUChar* fold);
extern int onigenc_unicode_apply_all_case_fold (OnigCaseFoldType flag, OnigApplyAllCaseFoldFunc f, void* arg);
# 163 "regenc.h"
extern const OnigUChar OnigEncISO_8859_1_ToLowerCaseTable[];
extern const OnigUChar OnigEncISO_8859_1_ToUpperCaseTable[];

extern int
onigenc_with_ascii_strncmp (OnigEncoding enc, const OnigUChar* p, const OnigUChar* end, const OnigUChar* sascii , int n);
extern OnigUChar*
onigenc_step (OnigEncoding enc, const OnigUChar* p, const OnigUChar* end, int n);


extern int onig_is_in_code_range (const OnigUChar* p, OnigCodePoint code);

extern OnigEncoding OnigEncDefaultCharEncoding;
extern const OnigUChar OnigEncAsciiToLowerCaseTable[];
extern const OnigUChar OnigEncAsciiToUpperCaseTable[];
extern const unsigned short OnigEncAsciiCtypeTable[];
# 199 "regint.h" 2
# 259 "regint.h"
typedef unsigned int BitStatusType;
# 320 "regint.h"
typedef unsigned int Bits;



typedef Bits BitSet[((1 << 8) / (sizeof(Bits) * 8))];
typedef Bits* BitSetRef;
# 343 "regint.h"
typedef struct _BBuf {
  OnigUChar* p;
  unsigned int used;
  unsigned int alloc;
} BBuf;
# 443 "regint.h"
enum OpCode {
  OP_FINISH = 0,
  OP_END = 1,

  OP_EXACT1 = 2,
  OP_EXACT2,
  OP_EXACT3,
  OP_EXACT4,
  OP_EXACT5,
  OP_EXACTN,
  OP_EXACTMB2N1,
  OP_EXACTMB2N2,
  OP_EXACTMB2N3,
  OP_EXACTMB2N,
  OP_EXACTMB3N,
  OP_EXACTMBN,

  OP_EXACT1_IC,
  OP_EXACTN_IC,

  OP_CCLASS,
  OP_CCLASS_MB,
  OP_CCLASS_MIX,
  OP_CCLASS_NOT,
  OP_CCLASS_MB_NOT,
  OP_CCLASS_MIX_NOT,
  OP_CCLASS_NODE,

  OP_ANYCHAR,
  OP_ANYCHAR_ML,
  OP_ANYCHAR_STAR,
  OP_ANYCHAR_ML_STAR,
  OP_ANYCHAR_STAR_PEEK_NEXT,
  OP_ANYCHAR_ML_STAR_PEEK_NEXT,

  OP_WORD,
  OP_NOT_WORD,
  OP_WORD_BOUND,
  OP_NOT_WORD_BOUND,
  OP_WORD_BEGIN,
  OP_WORD_END,

  OP_BEGIN_BUF,
  OP_END_BUF,
  OP_BEGIN_LINE,
  OP_END_LINE,
  OP_SEMI_END_BUF,
  OP_BEGIN_POSITION,

  OP_BACKREF1,
  OP_BACKREF2,
  OP_BACKREFN,
  OP_BACKREFN_IC,
  OP_BACKREF_MULTI,
  OP_BACKREF_MULTI_IC,
  OP_BACKREF_WITH_LEVEL,

  OP_MEMORY_START,
  OP_MEMORY_START_PUSH,
  OP_MEMORY_END_PUSH,
  OP_MEMORY_END_PUSH_REC,
  OP_MEMORY_END,
  OP_MEMORY_END_REC,

  OP_FAIL,
  OP_JUMP,
  OP_PUSH,
  OP_POP,
  OP_PUSH_OR_JUMP_EXACT1,
  OP_PUSH_IF_PEEK_NEXT,
  OP_REPEAT,
  OP_REPEAT_NG,
  OP_REPEAT_INC,
  OP_REPEAT_INC_NG,
  OP_REPEAT_INC_SG,
  OP_REPEAT_INC_NG_SG,
  OP_NULL_CHECK_START,
  OP_NULL_CHECK_END,
  OP_NULL_CHECK_END_MEMST,
  OP_NULL_CHECK_END_MEMST_PUSH,

  OP_PUSH_POS,
  OP_POP_POS,
  OP_PUSH_POS_NOT,
  OP_FAIL_POS,
  OP_PUSH_STOP_BT,
  OP_POP_STOP_BT,
  OP_LOOK_BEHIND,
  OP_PUSH_LOOK_BEHIND_NOT,
  OP_FAIL_LOOK_BEHIND_NOT,

  OP_CALL,
  OP_RETURN,

  OP_STATE_CHECK_PUSH,
  OP_STATE_CHECK_PUSH_OR_JUMP,
  OP_STATE_CHECK,
  OP_STATE_CHECK_ANYCHAR_STAR,
  OP_STATE_CHECK_ANYCHAR_ML_STAR,


  OP_SET_OPTION_PUSH,
  OP_SET_OPTION
};

typedef int RelAddrType;
typedef int AbsAddrType;
typedef int LengthType;
typedef int RepeatNumType;
typedef short int MemNumType;
typedef short int StateCheckNumType;
typedef void* PointerType;
# 678 "regint.h"
typedef struct {
  int type;


} NodeBase;

typedef struct {
  NodeBase base;
  unsigned int flags;
  BitSet bs;
  BBuf* mbuf;
} CClassNode;

typedef long OnigStackIndex;

typedef struct _OnigStackType {
  unsigned int type;
  union {
    struct {
      OnigUChar *pcode;
      OnigUChar *pstr;
      OnigUChar *pstr_prev;



    } state;
    struct {
      int count;
      OnigUChar *pcode;
      int num;
    } repeat;
    struct {
      OnigStackIndex si;
    } repeat_inc;
    struct {
      int num;
      OnigUChar *pstr;

      OnigStackIndex start;
      OnigStackIndex end;
    } mem;
    struct {
      int num;
      OnigUChar *pstr;
    } null_check;

    struct {
      OnigUChar *ret_addr;
      int num;
      OnigUChar *pstr;
    } call_frame;

  } u;
} OnigStackType;

typedef struct {
  void* stack_p;
  int stack_n;
  OnigOptionType options;
  OnigRegion* region;
  const OnigUChar* start;

  int best_len;
  OnigUChar* best_s;





} OnigMatchArg;
# 771 "regint.h"
extern OnigUChar* onig_error_code_to_format (int code);
extern void onig_snprintf_with_pattern (OnigUChar buf[], int bufsize, OnigEncoding enc, OnigUChar* pat, OnigUChar* pat_end, const OnigUChar *fmt, ...);
extern int onig_bbuf_init (BBuf* buf, int size);
extern int onig_compile (regex_t* reg, const OnigUChar* pattern, const OnigUChar* pattern_end, OnigErrorInfo* einfo);
extern void onig_chain_reduce (regex_t* reg);
extern void onig_chain_link_add (regex_t* to, regex_t* add);
extern void onig_transfer (regex_t* to, regex_t* from);
extern int onig_is_code_in_cc (OnigEncoding enc, OnigCodePoint code, CClassNode* cc);
extern int onig_is_code_in_cc_len (int enclen, OnigCodePoint code, CClassNode* cc);


typedef void hash_table_type;
typedef unsigned long hash_data_type;

extern hash_table_type* onig_st_init_strend_table_with_size (int size);
extern int onig_st_lookup_strend (hash_table_type* table, const OnigUChar* str_key, const OnigUChar* end_key, hash_data_type *value);
extern int onig_st_insert_strend (hash_table_type* table, const OnigUChar* str_key, const OnigUChar* end_key, hash_data_type value);
# 802 "regint.h"
extern int onigenc_property_list_add_property (OnigUChar* name, const OnigCodePoint* prop, hash_table_type **table, const OnigCodePoint*** plist, int *pnum, int *psize);

typedef int (*ONIGENC_INIT_PROPERTY_LIST_FUNC_TYPE)(void);

extern int onigenc_property_list_init (ONIGENC_INIT_PROPERTY_LIST_FUNC_TYPE);
# 31 "regexec.c" 2
# 41 "regexec.c"
static void history_tree_free(OnigCaptureTreeNode* node);

static void
history_tree_clear(OnigCaptureTreeNode* node)
{
  int i;

  if ((((void*)(node)) != (void*)0)) {
    for (i = 0; i < node->num_childs; i++) {
      if ((((void*)(node->childs[i])) != (void*)0)) {
        history_tree_free(node->childs[i]);
      }
    }
    for (i = 0; i < node->allocated; i++) {
      node->childs[i] = (OnigCaptureTreeNode* )0;
    }
    node->num_childs = 0;
    node->beg = -1;
    node->end = -1;
    node->group = -1;
  }
}

static void
history_tree_free(OnigCaptureTreeNode* node)
{
  history_tree_clear(node);
  free(node);
}

static void
history_root_free(OnigRegion* r)
{
  if ((((void*)(r->history_root)) != (void*)0)) {
    history_tree_free(r->history_root);
    r->history_root = (OnigCaptureTreeNode* )0;
  }
}

static OnigCaptureTreeNode*
history_node_new(void)
{
  OnigCaptureTreeNode* node;

  node = (OnigCaptureTreeNode* )malloc(sizeof(OnigCaptureTreeNode));
  if ((((void*)(node)) == (void*)0)) return 
# 86 "regexec.c" 3 4
 ((void *)0)
# 86 "regexec.c"
                        ;
  node->childs = (OnigCaptureTreeNode** )0;
  node->allocated = 0;
  node->num_childs = 0;
  node->group = -1;
  node->beg = -1;
  node->end = -1;

  return node;
}

static int
history_tree_add_child(OnigCaptureTreeNode* parent, OnigCaptureTreeNode* child)
{


  if (parent->num_childs >= parent->allocated) {
    int n, i;

    if ((((void*)(parent->childs)) == (void*)0)) {
      n = 8;
      parent->childs =
        (OnigCaptureTreeNode** )malloc(sizeof(OnigCaptureTreeNode*) * n);
    }
    else {
      n = parent->allocated * 2;
      parent->childs =
        (OnigCaptureTreeNode** )realloc(parent->childs,
                                         sizeof(OnigCaptureTreeNode*) * n);
    }
    if ((((void*)(parent->childs)) == (void*)0)) return -5;
    for (i = parent->allocated; i < n; i++) {
      parent->childs[i] = (OnigCaptureTreeNode* )0;
    }
    parent->allocated = n;
  }

  parent->childs[parent->num_childs] = child;
  parent->num_childs++;
  return 0;
}

static OnigCaptureTreeNode*
history_tree_clone(OnigCaptureTreeNode* node)
{
  int i;
  OnigCaptureTreeNode *clone, *child;

  clone = history_node_new();
  if ((((void*)(clone)) == (void*)0)) return 
# 135 "regexec.c" 3 4
 ((void *)0)
# 135 "regexec.c"
                         ;

  clone->beg = node->beg;
  clone->end = node->end;
  for (i = 0; i < node->num_childs; i++) {
    child = history_tree_clone(node->childs[i]);
    if ((((void*)(child)) == (void*)0)) {
      history_tree_free(clone);
      return (OnigCaptureTreeNode* )0;
    }
    history_tree_add_child(clone, child);
  }

  return clone;
}

extern OnigCaptureTreeNode*
onig_get_capture_tree(OnigRegion* region)
{
  return region->history_root;
}


extern void
onig_region_clear_old(OnigRegion* region)
{
  int i;

  for (i = 0; i < region->num_regs; i++) {
    region->beg[i] = region->end[i] = -1;
  }

  history_root_free(region);

}

extern int
onig_region_resize_old(OnigRegion* region, int n)
{
  region->num_regs = n;

  if (n < 10)
    n = 10;

  if (region->allocated == 0) {
    region->beg = (int* )malloc(n * sizeof(int));
    region->end = (int* )malloc(n * sizeof(int));

    if (region->beg == 0 || region->end == 0)
      return -5;

    region->allocated = n;
  }
  else if (region->allocated < n) {
    region->beg = (int* )realloc(region->beg, n * sizeof(int));
    region->end = (int* )realloc(region->end, n * sizeof(int));

    if (region->beg == 0 || region->end == 0)
      return -5;

    region->allocated = n;
  }

  return 0;
}

static int
onig_region_resize_old_clear(OnigRegion* region, int n)
{
  int r;

  r = onig_region_resize_old(region, n);
  if (r != 0) return r;
  onig_region_clear_old(region);
  return 0;
}

extern int
onig_region_set_old(OnigRegion* region, int at, int beg, int end)
{
  if (at < 0) return -30;

  if (at >= region->allocated) {
    int r = onig_region_resize_old(region, at + 1);
    if (r < 0) return r;
  }

  region->beg[at] = beg;
  region->end[at] = end;
  return 0;
}

extern void
onig_region_init_old(OnigRegion* region)
{
  region->num_regs = 0;
  region->allocated = 0;
  region->beg = (int* )0;
  region->end = (int* )0;
  region->history_root = (OnigCaptureTreeNode* )0;
}

extern OnigRegion*
onig_region_new_old(void)
{
  OnigRegion* r;

  r = (OnigRegion* )malloc(sizeof(OnigRegion));
  onig_region_init_old(r);
  return r;
}

extern void
onig_region_free_old(OnigRegion* r, int free_self)
{
  if (r) {
    if (r->allocated > 0) {
      if (r->beg) free(r->beg);
      if (r->end) free(r->end);
      r->allocated = 0;
    }

    history_root_free(r);

    if (free_self) free(r);
  }
}

extern void
onig_region_copy_old(OnigRegion* to, OnigRegion* from)
{

  int i;

  if (to == from) return;

  if (to->allocated == 0) {
    if (from->num_regs > 0) {
      to->beg = (int* )malloc((sizeof(int) * from->num_regs));
      to->end = (int* )malloc((sizeof(int) * from->num_regs));
      to->allocated = from->num_regs;
    }
  }
  else if (to->allocated < from->num_regs) {
    to->beg = (int* )realloc(to->beg, (sizeof(int) * from->num_regs));
    to->end = (int* )realloc(to->end, (sizeof(int) * from->num_regs));
    to->allocated = from->num_regs;
  }

  for (i = 0; i < from->num_regs; i++) {
    to->beg[i] = from->beg[i];
    to->end[i] = from->end[i];
  }
  to->num_regs = from->num_regs;


  history_root_free(to);

  if ((((void*)(from->history_root)) != (void*)0)) {
    to->history_root = history_tree_clone(from->history_root);
  }

}
# 412 "regexec.c"
static unsigned int MatchStackLimitSize_old = 0;

extern unsigned int
onig_get_match_stack_limit_size_old(void)
{
  return MatchStackLimitSize_old;
}

extern int
onig_set_match_stack_limit_size_old(unsigned int size)
{
  MatchStackLimitSize_old = size;
  return 0;
}

static int
stack_double_old(OnigStackType** arg_stk_base, OnigStackType** arg_stk_end,
      OnigStackType** arg_stk, OnigStackType* stk_alloc, OnigMatchArg* msa)
{
  unsigned int n;
  OnigStackType *x, *stk_base, *stk_end, *stk;

  stk_base = *arg_stk_base;
  stk_end = *arg_stk_end;
  stk = *arg_stk;

  n = stk_end - stk_base;
  if (stk_base == stk_alloc && (((void*)(msa->stack_p)) == (void*)0)) {
    x = (OnigStackType* )malloc(sizeof(OnigStackType) * n * 2);
    if ((((void*)(x)) == (void*)0)) {
      do{ if (stk_base != stk_alloc) { msa->stack_p = stk_base; msa->stack_n = stk_end - stk_base; };} while(0);
      return -5;
    }
    memcpy(x, stk_base, n * sizeof(OnigStackType));
    n *= 2;
  }
  else {
    n *= 2;
    if (MatchStackLimitSize_old != 0 && n > MatchStackLimitSize_old) {
      if ((unsigned int )(stk_end - stk_base) == MatchStackLimitSize_old)
        return -15;
      else
        n = MatchStackLimitSize_old;
    }
    x = (OnigStackType* )realloc(stk_base, sizeof(OnigStackType) * n);
    if ((((void*)(x)) == (void*)0)) {
      do{ if (stk_base != stk_alloc) { msa->stack_p = stk_base; msa->stack_n = stk_end - stk_base; };} while(0);
      return -5;
    }
  }
  *arg_stk = x + (stk - stk_base);
  *arg_stk_base = x;
  *arg_stk_end = x + n;
  return 0;
}
# 976 "regexec.c"
static int string_cmp_ic_old(OnigEncoding enc, int case_fold_flag,
    OnigUChar* s1, OnigUChar** ps2, int mblen)
{
  OnigUChar buf1[18];
  OnigUChar buf2[18];
  OnigUChar *p1, *p2, *end1, *s2, *end2;
  int len1, len2;

  s2 = *ps2;
  end1 = s1 + mblen;
  end2 = s2 + mblen;
  while (s1 < end1) {
    len1 = (enc)->mbc_case_fold(case_fold_flag,(const OnigUChar** )&s1,end1,buf1);
    len2 = (enc)->mbc_case_fold(case_fold_flag,(const OnigUChar** )&s2,end2,buf2);
    if (len1 != len2) return 0;
    p1 = buf1;
    p2 = buf2;
    while (len1-- > 0) {
      if (*p1 != *p2) return 0;
      p1++;
      p2++;
    }
  }

  *ps2 = s2;
  return 1;
}
# 1036 "regexec.c"
static int
make_capture_history_tree(OnigCaptureTreeNode* node, OnigStackType** kp,
                          OnigStackType* stk_top, OnigUChar* str, regex_t* reg)
{
  int n, r;
  OnigCaptureTreeNode* child;
  OnigStackType* k = *kp;

  while (k < stk_top) {
    if (k->type == 0x0100) {
      n = k->u.mem.num;
      if (n <= 31 &&
          ((n) < (int )(sizeof(BitStatusType) * 8) ? ((reg->capture_history) & (1 << n)) : ((reg->capture_history) & 1)) != 0) {
        child = history_node_new();
        if ((((void*)(child)) == (void*)0)) return -5;
        child->group = n;
        child->beg = (int )(k->u.mem.pstr - str);
        r = history_tree_add_child(node, child);
        if (r != 0) return r;
        *kp = (k + 1);
        r = make_capture_history_tree(child, kp, stk_top, str, reg);
        if (r != 0) return r;

        k = *kp;
        child->end = (int )(k->u.mem.pstr - str);
      }
    }
    else if (k->type == 0x8200) {
      if (k->u.mem.num == node->group) {
        node->end = (int )(k->u.mem.pstr - str);
        *kp = k;
        return 0;
      }
    }
    k++;
  }

  return 1;
}



static int mem_is_in_memp(int mem, int num, OnigUChar* memp)
{
  int i;
  MemNumType m;

  for (i = 0; i < num; i++) {
    do{ m = *(MemNumType* )memp; (memp) += sizeof(MemNumType);} while(0);
    if (mem == (int )m) return 1;
  }
  return 0;
}

static int backref_match_at_old_nested_level(regex_t* reg
  , OnigStackType* top, OnigStackType* stk_base
  , int ignore_case, int case_fold_flag
  , int nest, int mem_num, OnigUChar* memp, OnigUChar** s, const OnigUChar* send)
{
  OnigUChar *ss, *p, *pstart, *pend = ((OnigUChar* )0);
  int level;
  OnigStackType* k;

  level = 0;
  k = top;
  k--;
  while (k >= stk_base) {
    if (k->type == 0x0800) {
      level--;
    }
    else if (k->type == 0x0900) {
      level++;
    }
    else if (level == nest) {
      if (k->type == 0x0100) {
 if (mem_is_in_memp(k->u.mem.num, mem_num, memp)) {
   pstart = k->u.mem.pstr;
   if (pend != ((OnigUChar* )0)) {
     if (pend - pstart > send - *s) return 0;
     p = pstart;
     ss = *s;

     if (ignore_case != 0) {
       if (string_cmp_ic_old(reg->enc, case_fold_flag,
    pstart, &ss, (int )(pend - pstart)) == 0)
  return 0;
     }
     else {
       while (p < pend) {
  if (*p++ != *ss++) return 0;
       }
     }

     *s = ss;
     return 1;
   }
 }
      }
      else if (k->type == 0x8200) {
 if (mem_is_in_memp(k->u.mem.num, mem_num, memp)) {
   pend = k->u.mem.pstr;
 }
      }
    }
    k--;
  }

  return 0;
}
# 1228 "regexec.c"
typedef int regoff_t_old;

typedef struct {
  regoff_t_old rm_so;
  regoff_t_old rm_eo;
} posix_regmatch_t_old;



static int
match_at_old(regex_t* reg, const OnigUChar* str, const OnigUChar* end,

  const OnigUChar* right_range,

  const OnigUChar* sstart, OnigUChar* sprev, OnigMatchArg* msa)
{
  static OnigUChar FinishCode[] = { OP_FINISH };

  int i, n, num_mem, best_len, pop_level;
  LengthType tlen, tlen2;
  MemNumType mem;
  RelAddrType addr;
  OnigOptionType option = reg->options;
  OnigEncoding encode = reg->enc;
  OnigCaseFoldType case_fold_flag = reg->case_fold_flag;
  OnigUChar *s, *q, *sbegin;
  OnigUChar *p = reg->p;
  char *alloca_base;
  OnigStackType *stk_alloc, *stk_base, *stk, *stk_end;
  OnigStackType *stkp;
  OnigStackIndex si;
  OnigStackIndex *repeat_stk;
  OnigStackIndex *mem_start_stk, *mem_end_stk;





  n = reg->num_repeat + reg->num_mem * 2;

  do { if (msa->stack_p) { alloca_base = (char* )
# 1268 "regexec.c" 3 4
 __builtin_alloca (
# 1268 "regexec.c"
 sizeof(char*) * (n)
# 1268 "regexec.c" 3 4
 )
# 1268 "regexec.c"
 ; stk_alloc = (OnigStackType* )(msa->stack_p); stk_base = stk_alloc; stk = stk_base; stk_end = stk_base + msa->stack_n; } else { alloca_base = (char* )
# 1268 "regexec.c" 3 4
 __builtin_alloca (
# 1268 "regexec.c"
 sizeof(char*) * (n) + sizeof(OnigStackType) * (160)
# 1268 "regexec.c" 3 4
 )
# 1268 "regexec.c"
 ; stk_alloc = (OnigStackType* )(alloca_base + sizeof(char*) * (n)); stk_base = stk_alloc; stk = stk_base; stk_end = stk_base + (160); }} while(0);
  pop_level = reg->stack_pop_level;
  num_mem = reg->num_mem;
  repeat_stk = (OnigStackIndex* )alloca_base;

  mem_start_stk = (OnigStackIndex* )(repeat_stk + reg->num_repeat);
  mem_end_stk = mem_start_stk + num_mem;
  mem_start_stk--;

  mem_end_stk--;

  for (i = 1; i <= num_mem; i++) {
    mem_start_stk[i] = mem_end_stk[i] = -1;
  }
# 1290 "regexec.c"
  do { stk->type = (0x0001); stk->u.state.pcode = (FinishCode); stk++;} while(0);
  best_len = -1;
  s = (OnigUChar* )sstart;
  while (1) {
# 1314 "regexec.c"
    sbegin = s;
    switch (*p++) {
    case OP_END: ;
      n = s - sstart;
      if (n > best_len) {
 OnigRegion* region;

 if (((option) & ((((1U << 1) << 1) << 1) << 1))) {
   if (n > msa->best_len) {
     msa->best_len = n;
     msa->best_s = (OnigUChar* )sstart;
   }
   else
     goto end_best_len;
        }

 best_len = n;
 region = msa->region;
 if (region) {

   if (((msa->options) & (((((((((((1U << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1))) {
     posix_regmatch_t_old* rmt = (posix_regmatch_t_old* )region;

     rmt[0].rm_so = sstart - str;
     rmt[0].rm_eo = s - str;
     for (i = 1; i <= num_mem; i++) {
       if (mem_end_stk[i] != -1) {
  if (((i) < (int )(sizeof(BitStatusType) * 8) ? ((reg->bt_mem_start) & (1 << i)) : ((reg->bt_mem_start) & 1)))
    rmt[i].rm_so = (stk_base + (mem_start_stk[i]))->u.mem.pstr - str;
  else
    rmt[i].rm_so = (OnigUChar* )((void* )(mem_start_stk[i])) - str;

  rmt[i].rm_eo = (((i) < (int )(sizeof(BitStatusType) * 8) ? ((reg->bt_mem_end) & (1 << i)) : ((reg->bt_mem_end) & 1))
    ? (stk_base + (mem_end_stk[i]))->u.mem.pstr
    : (OnigUChar* )((void* )mem_end_stk[i])) - str;
       }
       else {
  rmt[i].rm_so = rmt[i].rm_eo = -1;
       }
     }
   }
   else {

     region->beg[0] = sstart - str;
     region->end[0] = s - str;
     for (i = 1; i <= num_mem; i++) {
       if (mem_end_stk[i] != -1) {
  if (((i) < (int )(sizeof(BitStatusType) * 8) ? ((reg->bt_mem_start) & (1 << i)) : ((reg->bt_mem_start) & 1)))
    region->beg[i] = (stk_base + (mem_start_stk[i]))->u.mem.pstr - str;
  else
    region->beg[i] = (OnigUChar* )((void* )mem_start_stk[i]) - str;

  region->end[i] = (((i) < (int )(sizeof(BitStatusType) * 8) ? ((reg->bt_mem_end) & (1 << i)) : ((reg->bt_mem_end) & 1))
      ? (stk_base + (mem_end_stk[i]))->u.mem.pstr
      : (OnigUChar* )((void* )mem_end_stk[i])) - str;
       }
       else {
  region->beg[i] = region->end[i] = -1;
       }
     }


     if (reg->capture_history != 0) {
              int r;
              OnigCaptureTreeNode* node;

              if ((((void*)(region->history_root)) == (void*)0)) {
                region->history_root = node = history_node_new();
                if ((((void*)(node)) == (void*)0)) return -5;
              }
              else {
                node = region->history_root;
                history_tree_clear(node);
              }

              node->group = 0;
              node->beg = sstart - str;
              node->end = s - str;

              stkp = stk_base;
              r = make_capture_history_tree(region->history_root, &stkp,
                                            stk, (OnigUChar* )str, reg);
              if (r < 0) {
                best_len = r;
                goto finish;
              }
     }


   }

 }
      }


    end_best_len:

      ;

      if (((option) & (((((1U << 1) << 1) << 1) << 1) | (((((1U << 1) << 1) << 1) << 1) << 1)))) {
 if (((option) & (((((1U << 1) << 1) << 1) << 1) << 1)) && s == sstart) {
   best_len = -1;
   goto fail;
 }
 if (((option) & ((((1U << 1) << 1) << 1) << 1)) && (s < right_range)) {
   goto fail;
 }
      }


      goto finish;
      break;

    case OP_EXACT1: ;





      if (*p != *s++) goto fail;
      if (s + (0) > right_range) goto fail;
      p++;
      ;
      break;

    case OP_EXACT1_IC: ;
      {
 int len;
 OnigUChar *q, lowbuf[18];

 if (s + (1) > right_range) goto fail;
 len = (encode)->mbc_case_fold(case_fold_flag,(const OnigUChar** )&s,end,lowbuf)


                      ;
 if (s + (0) > right_range) goto fail;
 q = lowbuf;
 while (len-- > 0) {
   if (*p != *q) {
            goto fail;
          }
   p++; q++;
 }
      }
      ;
      break;

    case OP_EXACT2: ;
      if (s + (2) > right_range) goto fail;
      if (*p != *s) goto fail;
      p++; s++;
      if (*p != *s) goto fail;
      sprev = s;
      p++; s++;
      ;
      continue;
      break;

    case OP_EXACT3: ;
      if (s + (3) > right_range) goto fail;
      if (*p != *s) goto fail;
      p++; s++;
      if (*p != *s) goto fail;
      p++; s++;
      if (*p != *s) goto fail;
      sprev = s;
      p++; s++;
      ;
      continue;
      break;

    case OP_EXACT4: ;
      if (s + (4) > right_range) goto fail;
      if (*p != *s) goto fail;
      p++; s++;
      if (*p != *s) goto fail;
      p++; s++;
      if (*p != *s) goto fail;
      p++; s++;
      if (*p != *s) goto fail;
      sprev = s;
      p++; s++;
      ;
      continue;
      break;

    case OP_EXACT5: ;
      if (s + (5) > right_range) goto fail;
      if (*p != *s) goto fail;
      p++; s++;
      if (*p != *s) goto fail;
      p++; s++;
      if (*p != *s) goto fail;
      p++; s++;
      if (*p != *s) goto fail;
      p++; s++;
      if (*p != *s) goto fail;
      sprev = s;
      p++; s++;
      ;
      continue;
      break;

    case OP_EXACTN: ;
      do{ tlen = *(LengthType* )p; (p) += sizeof(LengthType);} while(0);
      if (s + (tlen) > right_range) goto fail;
      while (tlen-- > 0) {
 if (*p++ != *s++) goto fail;
      }
      sprev = s - 1;
      ;
      continue;
      break;

    case OP_EXACTN_IC: ;
      {
 int len;
 OnigUChar *q, *endp, lowbuf[18];

 do{ tlen = *(LengthType* )p; (p) += sizeof(LengthType);} while(0);
 endp = p + tlen;

 while (p < endp) {
   sprev = s;
   if (s + (1) > right_range) goto fail;
   len = (encode)->mbc_case_fold(case_fold_flag,(const OnigUChar** )&s,end,lowbuf)


                        ;
   if (s + (0) > right_range) goto fail;
   q = lowbuf;
   while (len-- > 0) {
     if (*p != *q) goto fail;
     p++; q++;
   }
 }
      }

      ;
      continue;
      break;

    case OP_EXACTMB2N1: ;
      if (s + (2) > right_range) goto fail;
      if (*p != *s) goto fail;
      p++; s++;
      if (*p != *s) goto fail;
      p++; s++;
      ;
      break;

    case OP_EXACTMB2N2: ;
      if (s + (4) > right_range) goto fail;
      if (*p != *s) goto fail;
      p++; s++;
      if (*p != *s) goto fail;
      p++; s++;
      sprev = s;
      if (*p != *s) goto fail;
      p++; s++;
      if (*p != *s) goto fail;
      p++; s++;
      ;
      continue;
      break;

    case OP_EXACTMB2N3: ;
      if (s + (6) > right_range) goto fail;
      if (*p != *s) goto fail;
      p++; s++;
      if (*p != *s) goto fail;
      p++; s++;
      if (*p != *s) goto fail;
      p++; s++;
      if (*p != *s) goto fail;
      p++; s++;
      sprev = s;
      if (*p != *s) goto fail;
      p++; s++;
      if (*p != *s) goto fail;
      p++; s++;
      ;
      continue;
      break;

    case OP_EXACTMB2N: ;
      do{ tlen = *(LengthType* )p; (p) += sizeof(LengthType);} while(0);
      if (s + (tlen * 2) > right_range) goto fail;
      while (tlen-- > 0) {
 if (*p != *s) goto fail;
 p++; s++;
 if (*p != *s) goto fail;
 p++; s++;
      }
      sprev = s - 2;
      ;
      continue;
      break;

    case OP_EXACTMB3N: ;
      do{ tlen = *(LengthType* )p; (p) += sizeof(LengthType);} while(0);
      if (s + (tlen * 3) > right_range) goto fail;
      while (tlen-- > 0) {
 if (*p != *s) goto fail;
 p++; s++;
 if (*p != *s) goto fail;
 p++; s++;
 if (*p != *s) goto fail;
 p++; s++;
      }
      sprev = s - 3;
      ;
      continue;
      break;

    case OP_EXACTMBN: ;
      do{ tlen = *(LengthType* )p; (p) += sizeof(LengthType);} while(0);
      do{ tlen2 = *(LengthType* )p; (p) += sizeof(LengthType);} while(0);
      tlen2 *= tlen;
      if (s + (tlen2) > right_range) goto fail;
      while (tlen2-- > 0) {
 if (*p != *s) goto fail;
 p++; s++;
      }
      sprev = s - tlen;
      ;
      continue;
      break;

    case OP_CCLASS: ;
      if (s + (1) > right_range) goto fail;
      if (((((BitSetRef )p))[*s / (sizeof(Bits) * 8)] & (1 << (*s % (sizeof(Bits) * 8)))) == 0) goto fail;
      p += sizeof(BitSet);
      s += (encode)->mbc_enc_len(s);
      ;
      break;

    case OP_CCLASS_MB: ;
      if (! ((encode)->mbc_enc_len(s) != 1)) goto fail;

    cclass_mb:
      do{ tlen = *(LengthType* )p; (p) += sizeof(LengthType);} while(0);
      {
 OnigCodePoint code;
 OnigUChar *ss;
 int mb_len;

 if (s + (1) > right_range) goto fail;
 mb_len = (encode)->mbc_enc_len(s);
 if (s + (mb_len) > right_range) goto fail;
 ss = s;
 s += mb_len;
 code = (encode)->mbc_to_code((ss),(s));


 if (! onig_is_in_code_range(p, code)) goto fail;





      }
      p += tlen;
      ;
      break;

    case OP_CCLASS_MIX: ;
      if (s + (1) > right_range) goto fail;
      if (((encode)->mbc_enc_len(s) != 1)) {
 p += sizeof(BitSet);
 goto cclass_mb;
      }
      else {
 if (((((BitSetRef )p))[*s / (sizeof(Bits) * 8)] & (1 << (*s % (sizeof(Bits) * 8)))) == 0)
   goto fail;

 p += sizeof(BitSet);
 do{ tlen = *(LengthType* )p; (p) += sizeof(LengthType);} while(0);
 p += tlen;
 s++;
      }
      ;
      break;

    case OP_CCLASS_NOT: ;
      if (s + (1) > right_range) goto fail;
      if (((((BitSetRef )p))[*s / (sizeof(Bits) * 8)] & (1 << (*s % (sizeof(Bits) * 8)))) != 0) goto fail;
      p += sizeof(BitSet);
      s += (encode)->mbc_enc_len(s);
      ;
      break;

    case OP_CCLASS_MB_NOT: ;
      if (s + (1) > right_range) goto fail;
      if (! ((encode)->mbc_enc_len(s) != 1)) {
 s++;
 do{ tlen = *(LengthType* )p; (p) += sizeof(LengthType);} while(0);
 p += tlen;
 goto cc_mb_not_success;
      }

    cclass_mb_not:
      do{ tlen = *(LengthType* )p; (p) += sizeof(LengthType);} while(0);
      {
 OnigCodePoint code;
 OnigUChar *ss;
 int mb_len = (encode)->mbc_enc_len(s);

 if (! (s + (mb_len) <= right_range)) {
          if (s + (1) > right_range) goto fail;
   s = (OnigUChar* )end;
   p += tlen;
   goto cc_mb_not_success;
 }

 ss = s;
 s += mb_len;
 code = (encode)->mbc_to_code((ss),(s));


 if (onig_is_in_code_range(p, code)) goto fail;





      }
      p += tlen;

    cc_mb_not_success:
      ;
      break;

    case OP_CCLASS_MIX_NOT: ;
      if (s + (1) > right_range) goto fail;
      if (((encode)->mbc_enc_len(s) != 1)) {
 p += sizeof(BitSet);
 goto cclass_mb_not;
      }
      else {
 if (((((BitSetRef )p))[*s / (sizeof(Bits) * 8)] & (1 << (*s % (sizeof(Bits) * 8)))) != 0)
   goto fail;

 p += sizeof(BitSet);
 do{ tlen = *(LengthType* )p; (p) += sizeof(LengthType);} while(0);
 p += tlen;
 s++;
      }
      ;
      break;

    case OP_CCLASS_NODE: ;
      {
 OnigCodePoint code;
        void *node;
        int mb_len;
        OnigUChar *ss;

        if (s + (1) > right_range) goto fail;
        do{ node = *(PointerType* )p; (p) += sizeof(PointerType);} while(0);
 mb_len = (encode)->mbc_enc_len(s);
 ss = s;
 s += mb_len;
 if (s + (0) > right_range) goto fail;
 code = (encode)->mbc_to_code((ss),(s));
 if (onig_is_code_in_cc_len(mb_len, code, node) == 0) goto fail;
      }
      ;
      break;

    case OP_ANYCHAR: ;
      if (s + (1) > right_range) goto fail;
      n = (encode)->mbc_enc_len(s);
      if (s + (n) > right_range) goto fail;
      if ((encode)->is_mbc_newline((s),(end))) goto fail;
      s += n;
      ;
      break;

    case OP_ANYCHAR_ML: ;
      if (s + (1) > right_range) goto fail;
      n = (encode)->mbc_enc_len(s);
      if (s + (n) > right_range) goto fail;
      s += n;
      ;
      break;

    case OP_ANYCHAR_STAR: ;
      while ((s < right_range)) {
 do { do { if (stk_end - stk < (1)) { int r = stack_double_old(&stk_base, &stk_end, &stk, stk_alloc, msa); if (r != 0) { do{ if (stk_base != stk_alloc) { msa->stack_p = stk_base; msa->stack_n = stk_end - stk_base; };} while(0); return r; } }} while(0); stk->type = (0x0001); stk->u.state.pcode = (p); stk->u.state.pstr = (s); stk->u.state.pstr_prev = (sprev); stk++;} while(0);
 n = (encode)->mbc_enc_len(s);
        if (s + (n) > right_range) goto fail;
        if ((encode)->is_mbc_newline((s),(end))) goto fail;
        sprev = s;
        s += n;
      }
      ;
      break;

    case OP_ANYCHAR_ML_STAR: ;
      while ((s < right_range)) {
 do { do { if (stk_end - stk < (1)) { int r = stack_double_old(&stk_base, &stk_end, &stk, stk_alloc, msa); if (r != 0) { do{ if (stk_base != stk_alloc) { msa->stack_p = stk_base; msa->stack_n = stk_end - stk_base; };} while(0); return r; } }} while(0); stk->type = (0x0001); stk->u.state.pcode = (p); stk->u.state.pstr = (s); stk->u.state.pstr_prev = (sprev); stk++;} while(0);
 n = (encode)->mbc_enc_len(s);
 if (n > 1) {
   if (s + (n) > right_range) goto fail;
   sprev = s;
   s += n;
 }
 else {
   sprev = s;
   s++;
 }
      }
      ;
      break;

    case OP_ANYCHAR_STAR_PEEK_NEXT: ;
      while ((s < right_range)) {
 if (*p == *s) {
   do { do { if (stk_end - stk < (1)) { int r = stack_double_old(&stk_base, &stk_end, &stk, stk_alloc, msa); if (r != 0) { do{ if (stk_base != stk_alloc) { msa->stack_p = stk_base; msa->stack_n = stk_end - stk_base; };} while(0); return r; } }} while(0); stk->type = (0x0001); stk->u.state.pcode = (p + 1); stk->u.state.pstr = (s); stk->u.state.pstr_prev = (sprev); stk++;} while(0);
 }
 n = (encode)->mbc_enc_len(s);
        if (s + (n) > right_range) goto fail;
        if ((encode)->is_mbc_newline((s),(end))) goto fail;
        sprev = s;
        s += n;
      }
      p++;
      ;
      break;

    case OP_ANYCHAR_ML_STAR_PEEK_NEXT:;
      while ((s < right_range)) {
 if (*p == *s) {
   do { do { if (stk_end - stk < (1)) { int r = stack_double_old(&stk_base, &stk_end, &stk, stk_alloc, msa); if (r != 0) { do{ if (stk_base != stk_alloc) { msa->stack_p = stk_base; msa->stack_n = stk_end - stk_base; };} while(0); return r; } }} while(0); stk->type = (0x0001); stk->u.state.pcode = (p + 1); stk->u.state.pstr = (s); stk->u.state.pstr_prev = (sprev); stk++;} while(0);
 }
 n = (encode)->mbc_enc_len(s);
 if (n > 1) {
   if (s + (n) > right_range) goto fail;
   sprev = s;
   s += n;
 }
 else {
   sprev = s;
   s++;
 }
      }
      p++;
      ;
      break;
# 1906 "regexec.c"
    case OP_WORD: ;
      if (s + (1) > right_range) goto fail;
      if (! (encode)->is_code_ctype((encode)->mbc_to_code((s),(end)),12))
 goto fail;

      s += (encode)->mbc_enc_len(s);
      ;
      break;

    case OP_NOT_WORD: ;
      if (s + (1) > right_range) goto fail;
      if ((encode)->is_code_ctype((encode)->mbc_to_code((s),(end)),12))
 goto fail;

      s += (encode)->mbc_enc_len(s);
      ;
      break;

    case OP_WORD_BOUND: ;
      if (((s) == str)) {
 if (s + (1) > right_range) goto fail;
 if (! (encode)->is_code_ctype((encode)->mbc_to_code((s),(end)),12))
   goto fail;
      }
      else if (((s) == end)) {
 if (! (encode)->is_code_ctype((encode)->mbc_to_code((sprev),(end)),12))
   goto fail;
      }
      else {
 if ((encode)->is_code_ctype((encode)->mbc_to_code((s),(end)),12)
     == (encode)->is_code_ctype((encode)->mbc_to_code((sprev),(end)),12))
   goto fail;
      }
      ;
      continue;
      break;

    case OP_NOT_WORD_BOUND: ;
      if (((s) == str)) {
 if ((s < right_range) && (encode)->is_code_ctype((encode)->mbc_to_code((s),(end)),12))
   goto fail;
      }
      else if (((s) == end)) {
 if ((encode)->is_code_ctype((encode)->mbc_to_code((sprev),(end)),12))
   goto fail;
      }
      else {
 if ((encode)->is_code_ctype((encode)->mbc_to_code((s),(end)),12)
     != (encode)->is_code_ctype((encode)->mbc_to_code((sprev),(end)),12))
   goto fail;
      }
      ;
      continue;
      break;


    case OP_WORD_BEGIN: ;
      if ((s < right_range) && (encode)->is_code_ctype((encode)->mbc_to_code((s),(end)),12)) {
 if (((s) == str) || !(encode)->is_code_ctype((encode)->mbc_to_code((sprev),(end)),12)) {
   ;
   continue;
 }
      }
      goto fail;
      break;

    case OP_WORD_END: ;
      if (!((s) == str) && (encode)->is_code_ctype((encode)->mbc_to_code((sprev),(end)),12)) {
 if (((s) == end) || !(encode)->is_code_ctype((encode)->mbc_to_code((s),(end)),12)) {
   ;
   continue;
 }
      }
      goto fail;
      break;


    case OP_BEGIN_BUF: ;
      if (! ((s) == str)) goto fail;

      ;
      continue;
      break;

    case OP_END_BUF: ;
      if (! ((s) == end)) goto fail;

      ;
      continue;
      break;

    case OP_BEGIN_LINE: ;
      if (((s) == str)) {
 if (((msa->options) & (((((((((1U << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1))) goto fail;
 ;
 continue;
      }
      else if ((encode)->is_mbc_newline((sprev),(end)) && !((s) == end)) {
 ;
 continue;
      }
      goto fail;
      break;

    case OP_END_LINE: ;
      if (((s) == end)) {



   if (((msa->options) & ((((((((((1U << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1))) goto fail;
   ;
   continue;



      }
      else if ((encode)->is_mbc_newline((s),(end))) {
 ;
 continue;
      }






      goto fail;
      break;

    case OP_SEMI_END_BUF: ;
      if (((s) == end)) {



   if (((msa->options) & ((((((((((1U << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1))) goto fail;
   ;
   continue;



      }
      else if ((encode)->is_mbc_newline((s),(end)) &&
        ((s + (encode)->mbc_enc_len(s)) == end)) {
 ;
 continue;
      }
# 2062 "regexec.c"
      goto fail;
      break;

    case OP_BEGIN_POSITION: ;
      if (s != msa->start)
 goto fail;

      ;
      continue;
      break;

    case OP_MEMORY_START_PUSH: ;
      do{ mem = *(MemNumType* )p; (p) += sizeof(MemNumType);} while(0);
      do { do { if (stk_end - stk < (1)) { int r = stack_double_old(&stk_base, &stk_end, &stk, stk_alloc, msa); if (r != 0) { do{ if (stk_base != stk_alloc) { msa->stack_p = stk_base; msa->stack_n = stk_end - stk_base; };} while(0); return r; } }} while(0); stk->type = 0x0100; stk->u.mem.num = (mem); stk->u.mem.pstr = (s); stk->u.mem.start = mem_start_stk[mem]; stk->u.mem.end = mem_end_stk[mem]; mem_start_stk[mem] = ((stk) - stk_base); mem_end_stk[mem] = -1; stk++;} while(0);
      ;
      continue;
      break;

    case OP_MEMORY_START: ;
      do{ mem = *(MemNumType* )p; (p) += sizeof(MemNumType);} while(0);
      mem_start_stk[mem] = (OnigStackIndex )((void* )s);
      ;
      continue;
      break;

    case OP_MEMORY_END_PUSH: ;
      do{ mem = *(MemNumType* )p; (p) += sizeof(MemNumType);} while(0);
      do { do { if (stk_end - stk < (1)) { int r = stack_double_old(&stk_base, &stk_end, &stk, stk_alloc, msa); if (r != 0) { do{ if (stk_base != stk_alloc) { msa->stack_p = stk_base; msa->stack_n = stk_end - stk_base; };} while(0); return r; } }} while(0); stk->type = 0x8200; stk->u.mem.num = (mem); stk->u.mem.pstr = (s); stk->u.mem.start = mem_start_stk[mem]; stk->u.mem.end = mem_end_stk[mem]; mem_end_stk[mem] = ((stk) - stk_base); stk++;} while(0);
      ;
      continue;
      break;

    case OP_MEMORY_END: ;
      do{ mem = *(MemNumType* )p; (p) += sizeof(MemNumType);} while(0);
      mem_end_stk[mem] = (OnigStackIndex )((void* )s);
      ;
      continue;
      break;


    case OP_MEMORY_END_PUSH_REC: ;
      do{ mem = *(MemNumType* )p; (p) += sizeof(MemNumType);} while(0);
      do { int level = 0; stkp = stk; while (stkp > stk_base) { stkp--; if ((stkp->type & 0x8000) != 0 && stkp->u.mem.num == (mem)) { level++; } else if (stkp->type == 0x0100 && stkp->u.mem.num == (mem)) { if (level == 0) break; level--; } }} while(0);
      do { do { if (stk_end - stk < (1)) { int r = stack_double_old(&stk_base, &stk_end, &stk, stk_alloc, msa); if (r != 0) { do{ if (stk_base != stk_alloc) { msa->stack_p = stk_base; msa->stack_n = stk_end - stk_base; };} while(0); return r; } }} while(0); stk->type = 0x8200; stk->u.mem.num = (mem); stk->u.mem.pstr = (s); stk->u.mem.start = mem_start_stk[mem]; stk->u.mem.end = mem_end_stk[mem]; mem_end_stk[mem] = ((stk) - stk_base); stk++;} while(0);
      mem_start_stk[mem] = ((stkp) - stk_base);
      ;
      continue;
      break;

    case OP_MEMORY_END_REC: ;
      do{ mem = *(MemNumType* )p; (p) += sizeof(MemNumType);} while(0);
      mem_end_stk[mem] = (OnigStackIndex )((void* )s);
      do { int level = 0; stkp = stk; while (stkp > stk_base) { stkp--; if ((stkp->type & 0x8000) != 0 && stkp->u.mem.num == (mem)) { level++; } else if (stkp->type == 0x0100 && stkp->u.mem.num == (mem)) { if (level == 0) break; level--; } }} while(0);

      if (((mem) < (int )(sizeof(BitStatusType) * 8) ? ((reg->bt_mem_start) & (1 << mem)) : ((reg->bt_mem_start) & 1)))
 mem_start_stk[mem] = ((stkp) - stk_base);
      else
 mem_start_stk[mem] = (OnigStackIndex )((void* )stkp->u.mem.pstr);

      do { do { if (stk_end - stk < (1)) { int r = stack_double_old(&stk_base, &stk_end, &stk, stk_alloc, msa); if (r != 0) { do{ if (stk_base != stk_alloc) { msa->stack_p = stk_base; msa->stack_n = stk_end - stk_base; };} while(0); return r; } }} while(0); stk->type = 0x8400; stk->u.mem.num = (mem); stk++;} while(0);
      ;
      continue;
      break;


    case OP_BACKREF1: ;
      mem = 1;
      goto backref;
      break;

    case OP_BACKREF2: ;
      mem = 2;
      goto backref;
      break;

    case OP_BACKREFN: ;
      do{ mem = *(MemNumType* )p; (p) += sizeof(MemNumType);} while(0);
    backref:
      {
 int len;
 OnigUChar *pstart, *pend;



 if (mem > num_mem) goto fail;
 if (mem_end_stk[mem] == -1) goto fail;
 if (mem_start_stk[mem] == -1) goto fail;

 if (((mem) < (int )(sizeof(BitStatusType) * 8) ? ((reg->bt_mem_start) & (1 << mem)) : ((reg->bt_mem_start) & 1)))
   pstart = (stk_base + (mem_start_stk[mem]))->u.mem.pstr;
 else
   pstart = (OnigUChar* )((void* )mem_start_stk[mem]);

 pend = (((mem) < (int )(sizeof(BitStatusType) * 8) ? ((reg->bt_mem_end) & (1 << mem)) : ((reg->bt_mem_end) & 1))
  ? (stk_base + (mem_end_stk[mem]))->u.mem.pstr
  : (OnigUChar* )((void* )mem_end_stk[mem]));
 n = pend - pstart;
 if (s + (n) > right_range) goto fail;
 sprev = s;
 do { while (n-- > 0) { if (*pstart++ != *s++) goto fail; }} while(0);
 while (sprev + (len = (encode)->mbc_enc_len(sprev)) < s)
   sprev += len;

 ;
 continue;
      }
      break;

    case OP_BACKREFN_IC: ;
      do{ mem = *(MemNumType* )p; (p) += sizeof(MemNumType);} while(0);
      {
 int len;
 OnigUChar *pstart, *pend;



 if (mem > num_mem) goto fail;
 if (mem_end_stk[mem] == -1) goto fail;
 if (mem_start_stk[mem] == -1) goto fail;

 if (((mem) < (int )(sizeof(BitStatusType) * 8) ? ((reg->bt_mem_start) & (1 << mem)) : ((reg->bt_mem_start) & 1)))
   pstart = (stk_base + (mem_start_stk[mem]))->u.mem.pstr;
 else
   pstart = (OnigUChar* )((void* )mem_start_stk[mem]);

 pend = (((mem) < (int )(sizeof(BitStatusType) * 8) ? ((reg->bt_mem_end) & (1 << mem)) : ((reg->bt_mem_end) & 1))
  ? (stk_base + (mem_end_stk[mem]))->u.mem.pstr
  : (OnigUChar* )((void* )mem_end_stk[mem]));
 n = pend - pstart;
 if (s + (n) > right_range) goto fail;
 sprev = s;
 do { if (string_cmp_ic_old(encode, case_fold_flag, pstart, &s, n) == 0) goto fail; } while(0);
 while (sprev + (len = (encode)->mbc_enc_len(sprev)) < s)
   sprev += len;

 ;
 continue;
      }
      break;

    case OP_BACKREF_MULTI: ;
      {
 int len, is_fail;
 OnigUChar *pstart, *pend, *swork;

 do{ tlen = *(LengthType* )p; (p) += sizeof(LengthType);} while(0);
 for (i = 0; i < tlen; i++) {
   do{ mem = *(MemNumType* )p; (p) += sizeof(MemNumType);} while(0);

   if (mem_end_stk[mem] == -1) continue;
   if (mem_start_stk[mem] == -1) continue;

   if (((mem) < (int )(sizeof(BitStatusType) * 8) ? ((reg->bt_mem_start) & (1 << mem)) : ((reg->bt_mem_start) & 1)))
     pstart = (stk_base + (mem_start_stk[mem]))->u.mem.pstr;
   else
     pstart = (OnigUChar* )((void* )mem_start_stk[mem]);

   pend = (((mem) < (int )(sizeof(BitStatusType) * 8) ? ((reg->bt_mem_end) & (1 << mem)) : ((reg->bt_mem_end) & 1))
    ? (stk_base + (mem_end_stk[mem]))->u.mem.pstr
    : (OnigUChar* )((void* )mem_end_stk[mem]));
   n = pend - pstart;
   if (s + (n) > right_range) goto fail;
   sprev = s;
   swork = s;
   do { is_fail = 0; while (n-- > 0) { if (*pstart++ != *swork++) { is_fail = 1; break; } }} while(0);
   if (is_fail) continue;
   s = swork;
   while (sprev + (len = (encode)->mbc_enc_len(sprev)) < s)
     sprev += len;

   p += (sizeof(MemNumType) * (tlen - i - 1));
   break;
 }
 if (i == tlen) goto fail;
 ;
 continue;
      }
      break;

    case OP_BACKREF_MULTI_IC: ;
      {
 int len, is_fail;
 OnigUChar *pstart, *pend, *swork;

 do{ tlen = *(LengthType* )p; (p) += sizeof(LengthType);} while(0);
 for (i = 0; i < tlen; i++) {
   do{ mem = *(MemNumType* )p; (p) += sizeof(MemNumType);} while(0);

   if (mem_end_stk[mem] == -1) continue;
   if (mem_start_stk[mem] == -1) continue;

   if (((mem) < (int )(sizeof(BitStatusType) * 8) ? ((reg->bt_mem_start) & (1 << mem)) : ((reg->bt_mem_start) & 1)))
     pstart = (stk_base + (mem_start_stk[mem]))->u.mem.pstr;
   else
     pstart = (OnigUChar* )((void* )mem_start_stk[mem]);

   pend = (((mem) < (int )(sizeof(BitStatusType) * 8) ? ((reg->bt_mem_end) & (1 << mem)) : ((reg->bt_mem_end) & 1))
    ? (stk_base + (mem_end_stk[mem]))->u.mem.pstr
    : (OnigUChar* )((void* )mem_end_stk[mem]));
   n = pend - pstart;
   if (s + (n) > right_range) goto fail;
   sprev = s;
   swork = s;
   do { if (string_cmp_ic_old(encode, case_fold_flag, pstart, &swork, n) == 0) is_fail = 1; else is_fail = 0; } while(0);
   if (is_fail) continue;
   s = swork;
   while (sprev + (len = (encode)->mbc_enc_len(sprev)) < s)
     sprev += len;

   p += (sizeof(MemNumType) * (tlen - i - 1));
   break;
 }
 if (i == tlen) goto fail;
 ;
 continue;
      }
      break;


    case OP_BACKREF_WITH_LEVEL:
      {
 int len;
 OnigOptionType ic;
 LengthType level;

 do{ ic = *(OnigOptionType* )p; (p) += sizeof(OnigOptionType);} while(0);
 do{ level = *(LengthType* )p; (p) += sizeof(LengthType);} while(0);
 do{ tlen = *(LengthType* )p; (p) += sizeof(LengthType);} while(0);

 sprev = s;
 if (backref_match_at_old_nested_level(reg, stk, stk_base, ic
    , case_fold_flag, (int )level, (int )tlen, p, &s, end)) {
   while (sprev + (len = (encode)->mbc_enc_len(sprev)) < s)
     sprev += len;

   p += (sizeof(MemNumType) * tlen);
 }
 else
   goto fail;

 ;
 continue;
      }

      break;
# 2325 "regexec.c"
    case OP_NULL_CHECK_START: ;
      do{ mem = *(MemNumType* )p; (p) += sizeof(MemNumType);} while(0);
      do { do { if (stk_end - stk < (1)) { int r = stack_double_old(&stk_base, &stk_end, &stk, stk_alloc, msa); if (r != 0) { do{ if (stk_base != stk_alloc) { msa->stack_p = stk_base; msa->stack_n = stk_end - stk_base; };} while(0); return r; } }} while(0); stk->type = 0x3000; stk->u.null_check.num = (mem); stk->u.null_check.pstr = (s); stk++;} while(0);
      ;
      continue;
      break;

    case OP_NULL_CHECK_END: ;
      {
 int isnull;

 do{ mem = *(MemNumType* )p; (p) += sizeof(MemNumType);} while(0);
 do { OnigStackType* k = stk; while (1) { k--; ; if (k->type == 0x3000) { if (k->u.null_check.num == (mem)) { (isnull) = (k->u.null_check.pstr == (s)); break; } } }} while(0);
 if (isnull) {




 null_check_found:

   switch (*p++) {
   case OP_JUMP:
   case OP_PUSH:
     p += sizeof(RelAddrType);
     break;
   case OP_REPEAT_INC:
   case OP_REPEAT_INC_NG:
   case OP_REPEAT_INC_SG:
   case OP_REPEAT_INC_NG_SG:
     p += sizeof(MemNumType);
     break;
   default:
     goto unexpected_bytecode_error;
     break;
   }
 }
      }
      ;
      continue;
      break;


    case OP_NULL_CHECK_END_MEMST: ;
      {
 int isnull;

 do{ mem = *(MemNumType* )p; (p) += sizeof(MemNumType);} while(0);
 do { OnigStackType* k = stk; while (1) { k--; ; if (k->type == 0x3000) { if (k->u.null_check.num == (mem)) { if (k->u.null_check.pstr != (s)) { (isnull) = 0; break; } else { OnigUChar* endp; (isnull) = 1; while (k < stk) { if (k->type == 0x0100) { if (k->u.mem.end == -1) { (isnull) = 0; break; } if (((k->u.mem.num) < (int )(sizeof(BitStatusType) * 8) ? ((reg->bt_mem_end) & (1 << k->u.mem.num)) : ((reg->bt_mem_end) & 1))) endp = (stk_base + (k->u.mem.end))->u.mem.pstr; else endp = (OnigUChar* )k->u.mem.end; if ((stk_base + (k->u.mem.start))->u.mem.pstr != endp) { (isnull) = 0; break; } else if (endp != s) { (isnull) = -1; } } k++; } break; } } } }} while(0);
 if (isnull) {




   if (isnull == -1) goto fail;
   goto null_check_found;
 }
      }
      ;
      continue;
      break;



    case OP_NULL_CHECK_END_MEMST_PUSH:
      ;
      {
 int isnull;

 do{ mem = *(MemNumType* )p; (p) += sizeof(MemNumType);} while(0);

 do { int level = 0; OnigStackType* k = stk; while (1) { k--; ; if (k->type == 0x3000) { if (k->u.null_check.num == (mem)) { if (level == 0) { if (k->u.null_check.pstr != (s)) { (isnull) = 0; break; } else { OnigUChar* endp; (isnull) = 1; while (k < stk) { if (k->type == 0x0100) { if (k->u.mem.end == -1) { (isnull) = 0; break; } if (((k->u.mem.num) < (int )(sizeof(BitStatusType) * 8) ? ((reg->bt_mem_end) & (1 << k->u.mem.num)) : ((reg->bt_mem_end) & 1))) endp = (stk_base + (k->u.mem.end))->u.mem.pstr; else endp = (OnigUChar* )k->u.mem.end; if ((stk_base + (k->u.mem.start))->u.mem.pstr != endp) { (isnull) = 0; break; } else if (endp != s) { (isnull) = -1; } } k++; } break; } } else { level--; } } } else if (k->type == 0x5000) { if (k->u.null_check.num == (mem)) level++; } }} while(0);



 if (isnull) {




   if (isnull == -1) goto fail;
   goto null_check_found;
 }
 else {
   do { do { if (stk_end - stk < (1)) { int r = stack_double_old(&stk_base, &stk_end, &stk, stk_alloc, msa); if (r != 0) { do{ if (stk_base != stk_alloc) { msa->stack_p = stk_base; msa->stack_n = stk_end - stk_base; };} while(0); return r; } }} while(0); stk->type = 0x5000; stk->u.null_check.num = (mem); stk++;} while(0);
 }
      }
      ;
      continue;
      break;


    case OP_JUMP: ;
      do{ addr = *(RelAddrType* )p; (p) += sizeof(RelAddrType);} while(0);
      p += addr;
      ;
      ;
      continue;
      break;

    case OP_PUSH: ;
      do{ addr = *(RelAddrType* )p; (p) += sizeof(RelAddrType);} while(0);
      do { do { if (stk_end - stk < (1)) { int r = stack_double_old(&stk_base, &stk_end, &stk, stk_alloc, msa); if (r != 0) { do{ if (stk_base != stk_alloc) { msa->stack_p = stk_base; msa->stack_n = stk_end - stk_base; };} while(0); return r; } }} while(0); stk->type = (0x0001); stk->u.state.pcode = (p + addr); stk->u.state.pstr = (s); stk->u.state.pstr_prev = (sprev); stk++;} while(0);
      ;
      continue;
      break;
# 2468 "regexec.c"
    case OP_POP: ;
      do { stk--; ; } while(0);
      ;
      continue;
      break;

    case OP_PUSH_OR_JUMP_EXACT1: ;
      do{ addr = *(RelAddrType* )p; (p) += sizeof(RelAddrType);} while(0);
      if (*p == *s && (s < right_range)) {
 p++;
 do { do { if (stk_end - stk < (1)) { int r = stack_double_old(&stk_base, &stk_end, &stk, stk_alloc, msa); if (r != 0) { do{ if (stk_base != stk_alloc) { msa->stack_p = stk_base; msa->stack_n = stk_end - stk_base; };} while(0); return r; } }} while(0); stk->type = (0x0001); stk->u.state.pcode = (p + addr); stk->u.state.pstr = (s); stk->u.state.pstr_prev = (sprev); stk++;} while(0);
 ;
 continue;
      }
      p += (addr + 1);
      ;
      continue;
      break;

    case OP_PUSH_IF_PEEK_NEXT: ;
      do{ addr = *(RelAddrType* )p; (p) += sizeof(RelAddrType);} while(0);
      if (*p == *s) {
 p++;
 do { do { if (stk_end - stk < (1)) { int r = stack_double_old(&stk_base, &stk_end, &stk, stk_alloc, msa); if (r != 0) { do{ if (stk_base != stk_alloc) { msa->stack_p = stk_base; msa->stack_n = stk_end - stk_base; };} while(0); return r; } }} while(0); stk->type = (0x0001); stk->u.state.pcode = (p + addr); stk->u.state.pstr = (s); stk->u.state.pstr_prev = (sprev); stk++;} while(0);
 ;
 continue;
      }
      p++;
      ;
      continue;
      break;

    case OP_REPEAT: ;
      {
 do{ mem = *(MemNumType* )p; (p) += sizeof(MemNumType);} while(0);
 do{ addr = *(RelAddrType* )p; (p) += sizeof(RelAddrType);} while(0);

 do { if (stk_end - stk < (1)) { int r = stack_double_old(&stk_base, &stk_end, &stk, stk_alloc, msa); if (r != 0) { do{ if (stk_base != stk_alloc) { msa->stack_p = stk_base; msa->stack_n = stk_end - stk_base; };} while(0); return r; } }} while(0);
 repeat_stk[mem] = ((stk) - stk_base);
 do { do { if (stk_end - stk < (1)) { int r = stack_double_old(&stk_base, &stk_end, &stk, stk_alloc, msa); if (r != 0) { do{ if (stk_base != stk_alloc) { msa->stack_p = stk_base; msa->stack_n = stk_end - stk_base; };} while(0); return r; } }} while(0); stk->type = 0x0700; stk->u.repeat.num = (mem); stk->u.repeat.pcode = (p); stk->u.repeat.count = 0; stk++;} while(0);

 if (reg->repeat_range[mem].lower == 0) {
   do { do { if (stk_end - stk < (1)) { int r = stack_double_old(&stk_base, &stk_end, &stk, stk_alloc, msa); if (r != 0) { do{ if (stk_base != stk_alloc) { msa->stack_p = stk_base; msa->stack_n = stk_end - stk_base; };} while(0); return r; } }} while(0); stk->type = (0x0001); stk->u.state.pcode = (p + addr); stk->u.state.pstr = (s); stk->u.state.pstr_prev = (sprev); stk++;} while(0);
 }
      }
      ;
      continue;
      break;

    case OP_REPEAT_NG: ;
      {
 do{ mem = *(MemNumType* )p; (p) += sizeof(MemNumType);} while(0);
 do{ addr = *(RelAddrType* )p; (p) += sizeof(RelAddrType);} while(0);

 do { if (stk_end - stk < (1)) { int r = stack_double_old(&stk_base, &stk_end, &stk, stk_alloc, msa); if (r != 0) { do{ if (stk_base != stk_alloc) { msa->stack_p = stk_base; msa->stack_n = stk_end - stk_base; };} while(0); return r; } }} while(0);
 repeat_stk[mem] = ((stk) - stk_base);
 do { do { if (stk_end - stk < (1)) { int r = stack_double_old(&stk_base, &stk_end, &stk, stk_alloc, msa); if (r != 0) { do{ if (stk_base != stk_alloc) { msa->stack_p = stk_base; msa->stack_n = stk_end - stk_base; };} while(0); return r; } }} while(0); stk->type = 0x0700; stk->u.repeat.num = (mem); stk->u.repeat.pcode = (p); stk->u.repeat.count = 0; stk++;} while(0);

 if (reg->repeat_range[mem].lower == 0) {
   do { do { if (stk_end - stk < (1)) { int r = stack_double_old(&stk_base, &stk_end, &stk, stk_alloc, msa); if (r != 0) { do{ if (stk_base != stk_alloc) { msa->stack_p = stk_base; msa->stack_n = stk_end - stk_base; };} while(0); return r; } }} while(0); stk->type = (0x0001); stk->u.state.pcode = (p); stk->u.state.pstr = (s); stk->u.state.pstr_prev = (sprev); stk++;} while(0);
   p += addr;
 }
      }
      ;
      continue;
      break;

    case OP_REPEAT_INC: ;
      do{ mem = *(MemNumType* )p; (p) += sizeof(MemNumType);} while(0);
      si = repeat_stk[mem];
      stkp = (stk_base + (si));

    repeat_inc:
      stkp->u.repeat.count++;
      if (stkp->u.repeat.count >= reg->repeat_range[mem].upper) {

      }
      else if (stkp->u.repeat.count >= reg->repeat_range[mem].lower) {
        do { do { if (stk_end - stk < (1)) { int r = stack_double_old(&stk_base, &stk_end, &stk, stk_alloc, msa); if (r != 0) { do{ if (stk_base != stk_alloc) { msa->stack_p = stk_base; msa->stack_n = stk_end - stk_base; };} while(0); return r; } }} while(0); stk->type = (0x0001); stk->u.state.pcode = (p); stk->u.state.pstr = (s); stk->u.state.pstr_prev = (sprev); stk++;} while(0);
        p = (stk_base + (si))->u.repeat.pcode;
      }
      else {
        p = stkp->u.repeat.pcode;
      }
      do { do { if (stk_end - stk < (1)) { int r = stack_double_old(&stk_base, &stk_end, &stk, stk_alloc, msa); if (r != 0) { do{ if (stk_base != stk_alloc) { msa->stack_p = stk_base; msa->stack_n = stk_end - stk_base; };} while(0); return r; } }} while(0); stk->type = 0x0300; stk->u.repeat_inc.si = (si); stk++;} while(0);
      ;
      ;
      continue;
      break;

    case OP_REPEAT_INC_SG: ;
      do{ mem = *(MemNumType* )p; (p) += sizeof(MemNumType);} while(0);
      do { int level = 0; stkp = stk; while (1) { stkp--; ; if (stkp->type == 0x0700) { if (level == 0) { if (stkp->u.repeat.num == (mem)) { break; } } } else if (stkp->type == 0x0800) level--; else if (stkp->type == 0x0900) level++; }} while(0);
      si = ((stkp) - stk_base);
      goto repeat_inc;
      break;

    case OP_REPEAT_INC_NG: ;
      do{ mem = *(MemNumType* )p; (p) += sizeof(MemNumType);} while(0);
      si = repeat_stk[mem];
      stkp = (stk_base + (si));

    repeat_inc_ng:
      stkp->u.repeat.count++;
      if (stkp->u.repeat.count < reg->repeat_range[mem].upper) {
        if (stkp->u.repeat.count >= reg->repeat_range[mem].lower) {
          OnigUChar* pcode = stkp->u.repeat.pcode;

          do { do { if (stk_end - stk < (1)) { int r = stack_double_old(&stk_base, &stk_end, &stk, stk_alloc, msa); if (r != 0) { do{ if (stk_base != stk_alloc) { msa->stack_p = stk_base; msa->stack_n = stk_end - stk_base; };} while(0); return r; } }} while(0); stk->type = 0x0300; stk->u.repeat_inc.si = (si); stk++;} while(0);
          do { do { if (stk_end - stk < (1)) { int r = stack_double_old(&stk_base, &stk_end, &stk, stk_alloc, msa); if (r != 0) { do{ if (stk_base != stk_alloc) { msa->stack_p = stk_base; msa->stack_n = stk_end - stk_base; };} while(0); return r; } }} while(0); stk->type = (0x0001); stk->u.state.pcode = (pcode); stk->u.state.pstr = (s); stk->u.state.pstr_prev = (sprev); stk++;} while(0);
        }
        else {
          p = stkp->u.repeat.pcode;
          do { do { if (stk_end - stk < (1)) { int r = stack_double_old(&stk_base, &stk_end, &stk, stk_alloc, msa); if (r != 0) { do{ if (stk_base != stk_alloc) { msa->stack_p = stk_base; msa->stack_n = stk_end - stk_base; };} while(0); return r; } }} while(0); stk->type = 0x0300; stk->u.repeat_inc.si = (si); stk++;} while(0);
        }
      }
      else if (stkp->u.repeat.count == reg->repeat_range[mem].upper) {
        do { do { if (stk_end - stk < (1)) { int r = stack_double_old(&stk_base, &stk_end, &stk, stk_alloc, msa); if (r != 0) { do{ if (stk_base != stk_alloc) { msa->stack_p = stk_base; msa->stack_n = stk_end - stk_base; };} while(0); return r; } }} while(0); stk->type = 0x0300; stk->u.repeat_inc.si = (si); stk++;} while(0);
      }
      ;
      ;
      continue;
      break;

    case OP_REPEAT_INC_NG_SG: ;
      do{ mem = *(MemNumType* )p; (p) += sizeof(MemNumType);} while(0);
      do { int level = 0; stkp = stk; while (1) { stkp--; ; if (stkp->type == 0x0700) { if (level == 0) { if (stkp->u.repeat.num == (mem)) { break; } } } else if (stkp->type == 0x0800) level--; else if (stkp->type == 0x0900) level++; }} while(0);
      si = ((stkp) - stk_base);
      goto repeat_inc_ng;
      break;

    case OP_PUSH_POS: ;
      do { do { if (stk_end - stk < (1)) { int r = stack_double_old(&stk_base, &stk_end, &stk, stk_alloc, msa); if (r != 0) { do{ if (stk_base != stk_alloc) { msa->stack_p = stk_base; msa->stack_n = stk_end - stk_base; };} while(0); return r; } }} while(0); stk->type = (0x0500); stk->u.state.pcode = (((OnigUChar* )0)); stk->u.state.pstr = (s); stk->u.state.pstr_prev = (sprev); stk++;} while(0);
      ;
      continue;
      break;

    case OP_POP_POS: ;
      {
 do { stkp = stk; while (1) { stkp--; ; if ((((stkp)->type & 0x10ff) != 0)) { stkp->type = 0x0a00; } else if (stkp->type == 0x0500) { stkp->type = 0x0a00; break; } }} while(0);
 s = stkp->u.state.pstr;
 sprev = stkp->u.state.pstr_prev;
      }
      ;
      continue;
      break;

    case OP_PUSH_POS_NOT: ;
      do{ addr = *(RelAddrType* )p; (p) += sizeof(RelAddrType);} while(0);
      do { do { if (stk_end - stk < (1)) { int r = stack_double_old(&stk_base, &stk_end, &stk, stk_alloc, msa); if (r != 0) { do{ if (stk_base != stk_alloc) { msa->stack_p = stk_base; msa->stack_n = stk_end - stk_base; };} while(0); return r; } }} while(0); stk->type = (0x0003); stk->u.state.pcode = (p + addr); stk->u.state.pstr = (s); stk->u.state.pstr_prev = (sprev); stk++;} while(0);
      ;
      continue;
      break;

    case OP_FAIL_POS: ;
      do { while (1) { stk--; ; if (stk->type == 0x0003) break; else if (stk->type == 0x0100) { mem_start_stk[stk->u.mem.num] = stk->u.mem.start; mem_end_stk[stk->u.mem.num] = stk->u.mem.end; } else if (stk->type == 0x0300) { (stk_base + (stk->u.repeat_inc.si))->u.repeat.count--; } else if (stk->type == 0x8200) { mem_start_stk[stk->u.mem.num] = stk->u.mem.start; mem_end_stk[stk->u.mem.num] = stk->u.mem.end; } ; }} while(0);
      goto fail;
      break;

    case OP_PUSH_STOP_BT: ;
      do { do { if (stk_end - stk < (1)) { int r = stack_double_old(&stk_base, &stk_end, &stk, stk_alloc, msa); if (r != 0) { do{ if (stk_base != stk_alloc) { msa->stack_p = stk_base; msa->stack_n = stk_end - stk_base; };} while(0); return r; } }} while(0); stk->type = (0x0600); stk++;} while(0);
      ;
      continue;
      break;

    case OP_POP_STOP_BT: ;
      do { OnigStackType *k = stk; while (1) { k--; ; if ((((k)->type & 0x10ff) != 0)) { k->type = 0x0a00; } else if (k->type == 0x0600) { k->type = 0x0a00; break; } }} while(0);
      ;
      continue;
      break;

    case OP_LOOK_BEHIND: ;
      do{ tlen = *(LengthType* )p; (p) += sizeof(LengthType);} while(0);
      s = (OnigUChar* )onigenc_step_back((encode),(str),(s),((int )tlen));
      if ((((void*)(s)) == (void*)0)) goto fail;
      sprev = (OnigUChar* )onigenc_get_prev_char_head(encode, str, s);
      ;
      continue;
      break;

    case OP_PUSH_LOOK_BEHIND_NOT: ;
      do{ addr = *(RelAddrType* )p; (p) += sizeof(RelAddrType);} while(0);
      do{ tlen = *(LengthType* )p; (p) += sizeof(LengthType);} while(0);
      q = (OnigUChar* )onigenc_step_back((encode),(str),(s),((int )tlen));
      if ((((void*)(q)) == (void*)0)) {


 p += addr;

      }
      else {
 do { do { if (stk_end - stk < (1)) { int r = stack_double_old(&stk_base, &stk_end, &stk, stk_alloc, msa); if (r != 0) { do{ if (stk_base != stk_alloc) { msa->stack_p = stk_base; msa->stack_n = stk_end - stk_base; };} while(0); return r; } }} while(0); stk->type = (0x0002); stk->u.state.pcode = (p + addr); stk->u.state.pstr = (s); stk->u.state.pstr_prev = (sprev); stk++;} while(0);
 s = q;
 sprev = (OnigUChar* )onigenc_get_prev_char_head(encode, str, s);
      }
      ;
      continue;
      break;

    case OP_FAIL_LOOK_BEHIND_NOT: ;
      do { while (1) { stk--; ; if (stk->type == 0x0002) break; else if (stk->type == 0x0100) { mem_start_stk[stk->u.mem.num] = stk->u.mem.start; mem_end_stk[stk->u.mem.num] = stk->u.mem.end; } else if (stk->type == 0x0300) { (stk_base + (stk->u.repeat_inc.si))->u.repeat.count--; } else if (stk->type == 0x8200) { mem_start_stk[stk->u.mem.num] = stk->u.mem.start; mem_end_stk[stk->u.mem.num] = stk->u.mem.end; } ; }} while(0);
      goto fail;
      break;


    case OP_CALL: ;
      do{ addr = *(AbsAddrType* )p; (p) += sizeof(AbsAddrType);} while(0);
      do { do { if (stk_end - stk < (1)) { int r = stack_double_old(&stk_base, &stk_end, &stk, stk_alloc, msa); if (r != 0) { do{ if (stk_base != stk_alloc) { msa->stack_p = stk_base; msa->stack_n = stk_end - stk_base; };} while(0); return r; } }} while(0); stk->type = 0x0800; stk->u.call_frame.ret_addr = (p); stk++;} while(0);
      p = reg->p + addr;
      ;
      continue;
      break;

    case OP_RETURN: ;
      do { int level = 0; OnigStackType* k = stk; while (1) { k--; ; if (k->type == 0x0800) { if (level == 0) { (p) = k->u.call_frame.ret_addr; break; } else level--; } else if (k->type == 0x0900) level++; }} while(0);
      do { do { if (stk_end - stk < (1)) { int r = stack_double_old(&stk_base, &stk_end, &stk, stk_alloc, msa); if (r != 0) { do{ if (stk_base != stk_alloc) { msa->stack_p = stk_base; msa->stack_n = stk_end - stk_base; };} while(0); return r; } }} while(0); stk->type = 0x0900; stk++;} while(0);
      ;
      continue;
      break;


    case OP_FINISH:
      goto finish;
      break;

    fail:
      ;

    case OP_FAIL: ;
      do { switch (pop_level) { case 0: while (1) { stk--; ; if ((stk->type & 0x00ff) != 0) break; ; } break; case 1: while (1) { stk--; ; if ((stk->type & 0x00ff) != 0) break; else if (stk->type == 0x0100) { mem_start_stk[stk->u.mem.num] = stk->u.mem.start; mem_end_stk[stk->u.mem.num] = stk->u.mem.end; } ; } break; default: while (1) { stk--; ; if ((stk->type & 0x00ff) != 0) break; else if (stk->type == 0x0100) { mem_start_stk[stk->u.mem.num] = stk->u.mem.start; mem_end_stk[stk->u.mem.num] = stk->u.mem.end; } else if (stk->type == 0x0300) { (stk_base + (stk->u.repeat_inc.si))->u.repeat.count--; } else if (stk->type == 0x8200) { mem_start_stk[stk->u.mem.num] = stk->u.mem.start; mem_end_stk[stk->u.mem.num] = stk->u.mem.end; } ; } break; }} while(0);
      p = stk->u.state.pcode;
      s = stk->u.state.pstr;
      sprev = stk->u.state.pstr_prev;
# 2709 "regexec.c"
      ;
      continue;
      break;

    default:
      goto bytecode_error;

    }
    sprev = sbegin;
  }

 finish:
  do{ if (stk_base != stk_alloc) { msa->stack_p = stk_base; msa->stack_n = stk_end - stk_base; };} while(0);
  return best_len;







 bytecode_error:
  do{ if (stk_base != stk_alloc) { msa->stack_p = stk_base; msa->stack_n = stk_end - stk_base; };} while(0);
  return -13;

 unexpected_bytecode_error:
  do{ if (stk_base != stk_alloc) { msa->stack_p = stk_base; msa->stack_n = stk_end - stk_base; };} while(0);
  return -14;
}


static OnigUChar*
slow_search_old(OnigEncoding enc, OnigUChar* target, OnigUChar* target_end,
     const OnigUChar* text, const OnigUChar* text_end, OnigUChar* text_range)
{
  OnigUChar *t, *p, *s, *end;

  end = (OnigUChar* )text_end;
  end -= target_end - target - 1;
  if (end > text_range)
    end = text_range;

  s = (OnigUChar* )text;

  while (s < end) {
    if (*s == *target) {
      p = s + 1;
      t = target + 1;
      while (t < target_end) {
 if (*t != *p++)
   break;
 t++;
      }
      if (t == target_end)
 return s;
    }
    s += (enc)->mbc_enc_len(s);
  }

  return (OnigUChar* )
# 2768 "regexec.c" 3 4
                 ((void *)0)
# 2768 "regexec.c"
                     ;
}

static int
str_lower_case_match_old(OnigEncoding enc, int case_fold_flag,
                     const OnigUChar* t, const OnigUChar* tend,
       const OnigUChar* p, const OnigUChar* end)
{
  int lowlen;
  OnigUChar *q, lowbuf[18];

  while (t < tend) {
    lowlen = (enc)->mbc_case_fold(case_fold_flag,(const OnigUChar** )&p,end,lowbuf);
    q = lowbuf;
    while (lowlen > 0) {
      if (*t++ != *q++) return 0;
      lowlen--;
    }
  }

  return 1;
}

static OnigUChar*
slow_search_old_ic(OnigEncoding enc, int case_fold_flag,
        OnigUChar* target, OnigUChar* target_end,
        const OnigUChar* text, const OnigUChar* text_end, OnigUChar* text_range)
{
  OnigUChar *s, *end;

  end = (OnigUChar* )text_end;
  end -= target_end - target - 1;
  if (end > text_range)
    end = text_range;

  s = (OnigUChar* )text;

  while (s < end) {
    if (str_lower_case_match_old(enc, case_fold_flag, target, target_end,
        s, text_end))
      return s;

    s += (enc)->mbc_enc_len(s);
  }

  return (OnigUChar* )
# 2813 "regexec.c" 3 4
                 ((void *)0)
# 2813 "regexec.c"
                     ;
}

static OnigUChar*
slow_search_old_backward(OnigEncoding enc, OnigUChar* target, OnigUChar* target_end,
       const OnigUChar* text, const OnigUChar* adjust_text,
       const OnigUChar* text_end, const OnigUChar* text_start)
{
  OnigUChar *t, *p, *s;

  s = (OnigUChar* )text_end;
  s -= (target_end - target);
  if (s > text_start)
    s = (OnigUChar* )text_start;
  else
    s = (enc)->left_adjust_char_head(adjust_text, s);

  while (s >= text) {
    if (*s == *target) {
      p = s + 1;
      t = target + 1;
      while (t < target_end) {
 if (*t != *p++)
   break;
 t++;
      }
      if (t == target_end)
 return s;
    }
    s = (OnigUChar* )onigenc_get_prev_char_head(enc, adjust_text, s);
  }

  return (OnigUChar* )
# 2845 "regexec.c" 3 4
                 ((void *)0)
# 2845 "regexec.c"
                     ;
}

static OnigUChar*
slow_search_old_backward_ic(OnigEncoding enc, int case_fold_flag,
   OnigUChar* target, OnigUChar* target_end,
   const OnigUChar* text, const OnigUChar* adjust_text,
   const OnigUChar* text_end, const OnigUChar* text_start)
{
  OnigUChar *s;

  s = (OnigUChar* )text_end;
  s -= (target_end - target);
  if (s > text_start)
    s = (OnigUChar* )text_start;
  else
    s = (enc)->left_adjust_char_head(adjust_text, s);

  while (s >= text) {
    if (str_lower_case_match_old(enc, case_fold_flag,
                             target, target_end, s, text_end))
      return s;

    s = (OnigUChar* )onigenc_get_prev_char_head(enc, adjust_text, s);
  }

  return (OnigUChar* )
# 2871 "regexec.c" 3 4
                 ((void *)0)
# 2871 "regexec.c"
                     ;
}

static OnigUChar*
bm_search_old_notrev_old(regex_t* reg, const OnigUChar* target, const OnigUChar* target_end,
   const OnigUChar* text, const OnigUChar* text_end,
   const OnigUChar* text_range)
{
  const OnigUChar *s, *se, *t, *p, *end;
  const OnigUChar *tail;
  int skip, tlen1;






  tail = target_end - 1;
  tlen1 = tail - target;
  end = text_range;
  if (end + tlen1 > text_end)
    end = text_end - tlen1;

  s = text;

  if ((((void*)(reg->int_map)) == (void*)0)) {
    while (s < end) {
      p = se = s + tlen1;
      t = tail;
      while (*p == *t) {
 if (t == target) return (OnigUChar* )s;
 p--; t--;
      }
      skip = reg->map[*se];
      t = s;
      do {
        s += (reg->enc)->mbc_enc_len(s);
      } while ((s - t) < skip && s < end);
    }
  }
  else {
    while (s < end) {
      p = se = s + tlen1;
      t = tail;
      while (*p == *t) {
 if (t == target) return (OnigUChar* )s;
 p--; t--;
      }
      skip = reg->int_map[*se];
      t = s;
      do {
        s += (reg->enc)->mbc_enc_len(s);
      } while ((s - t) < skip && s < end);
    }
  }

  return (OnigUChar* )
# 2927 "regexec.c" 3 4
                 ((void *)0)
# 2927 "regexec.c"
                     ;
}

static OnigUChar*
bm_search_old(regex_t* reg, const OnigUChar* target, const OnigUChar* target_end,
   const OnigUChar* text, const OnigUChar* text_end, const OnigUChar* text_range)
{
  const OnigUChar *s, *t, *p, *end;
  const OnigUChar *tail;

  end = text_range + (target_end - target) - 1;
  if (end > text_end)
    end = text_end;

  tail = target_end - 1;
  s = text + (target_end - target) - 1;
  if ((((void*)(reg->int_map)) == (void*)0)) {
    while (s < end) {
      p = s;
      t = tail;
      while (*p == *t) {
 if (t == target) return (OnigUChar* )p;
 p--; t--;
      }
      s += reg->map[*s];
    }
  }
  else {
    while (s < end) {
      p = s;
      t = tail;
      while (*p == *t) {
 if (t == target) return (OnigUChar* )p;
 p--; t--;
      }
      s += reg->int_map[*s];
    }
  }
  return (OnigUChar* )
# 2965 "regexec.c" 3 4
                 ((void *)0)
# 2965 "regexec.c"
                     ;
}

static int
set_bm_backward_skip_old_old(OnigUChar* s, OnigUChar* end, OnigEncoding enc __attribute__ ((unused)),
       int** skip)

{
  int i, len;

  if ((((void*)(*skip)) == (void*)0)) {
    *skip = (int* )malloc(sizeof(int) * 256);
    if ((((void*)(*skip)) == (void*)0)) return -5;
  }

  len = end - s;
  for (i = 0; i < 256; i++)
    (*skip)[i] = len;

  for (i = len - 1; i > 0; i--)
    (*skip)[s[i]] = i;

  return 0;
}

static OnigUChar*
bm_search_old_backward(regex_t* reg, const OnigUChar* target, const OnigUChar* target_end,
     const OnigUChar* text, const OnigUChar* adjust_text,
     const OnigUChar* text_end, const OnigUChar* text_start)
{
  const OnigUChar *s, *t, *p;

  s = text_end - (target_end - target);
  if (text_start < s)
    s = text_start;
  else
    s = (reg->enc)->left_adjust_char_head(adjust_text, s);

  while (s >= text) {
    p = s;
    t = target;
    while (t < target_end && *p == *t) {
      p++; t++;
    }
    if (t == target_end)
      return (OnigUChar* )s;

    s -= reg->int_map_backward[*s];
    s = (reg->enc)->left_adjust_char_head(adjust_text, s);
  }

  return (OnigUChar* )
# 3016 "regexec.c" 3 4
                 ((void *)0)
# 3016 "regexec.c"
                     ;
}

static OnigUChar*
map_search_old(OnigEncoding enc, OnigUChar map[],
    const OnigUChar* text, const OnigUChar* text_range)
{
  const OnigUChar *s = text;

  while (s < text_range) {
    if (map[*s]) return (OnigUChar* )s;

    s += (enc)->mbc_enc_len(s);
  }
  return (OnigUChar* )
# 3030 "regexec.c" 3 4
                 ((void *)0)
# 3030 "regexec.c"
                     ;
}

static OnigUChar*
map_search_old_backward(OnigEncoding enc, OnigUChar map[],
      const OnigUChar* text, const OnigUChar* adjust_text,
      const OnigUChar* text_start)
{
  const OnigUChar *s = text_start;

  while (s >= text) {
    if (map[*s]) return (OnigUChar* )s;

    s = onigenc_get_prev_char_head(enc, adjust_text, s);
  }
  return (OnigUChar* )
# 3045 "regexec.c" 3 4
                 ((void *)0)
# 3045 "regexec.c"
                     ;
}

extern int
onig_match_old(regex_t* reg, const OnigUChar* str, const OnigUChar* end, const OnigUChar* at, OnigRegion* region,
     OnigOptionType option)
{
  int r;
  OnigUChar *prev;
  OnigMatchArg msa;
# 3081 "regexec.c"
  do { (msa).stack_p = (void* )0; (msa).options = (option); (msa).region = (region); (msa).start = (at); (msa).best_len = -1;} while(0);







  if (region

      && !((option) & (((((((((((1U << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1))

      ) {
    r = onig_region_resize_old_clear(region, reg->num_mem + 1);
  }
  else
    r = 0;

  if (r == 0) {
    prev = (OnigUChar* )onigenc_get_prev_char_head(reg->enc, str, at);
    r = match_at_old(reg, str, end,

   end,

   at, prev, &msa);
  }

  if ((msa).stack_p) free((msa).stack_p);
  ;
  return r;
}

static int
forward_search_range_old(regex_t* reg, const OnigUChar* str, const OnigUChar* end, OnigUChar* s,
       OnigUChar* range, OnigUChar** low, OnigUChar** high, OnigUChar** low_prev)
{
  OnigUChar *p, *pprev = (OnigUChar* )
# 3117 "regexec.c" 3 4
                             ((void *)0)
# 3117 "regexec.c"
                                 ;






  p = s;
  if (reg->dmin > 0) {
    if ((((reg->enc)->max_enc_len) == 1)) {
      p += reg->dmin;
    }
    else {
      OnigUChar *q = p + reg->dmin;
      while (p < q) p += (reg->enc)->mbc_enc_len(p);
    }
  }

 retry:
  switch (reg->optimize) {
  case 1:
    p = slow_search_old(reg->enc, reg->exact, reg->exact_end, p, end, range);
    break;
  case 4:
    p = slow_search_old_ic(reg->enc, reg->case_fold_flag,
                       reg->exact, reg->exact_end, p, end, range);
    break;

  case 2:
    p = bm_search_old(reg, reg->exact, reg->exact_end, p, end, range);
    break;

  case 3:
    p = bm_search_old_notrev_old(reg, reg->exact, reg->exact_end, p, end, range);
    break;

  case 5:
    p = map_search_old(reg->enc, reg->map, p, range);
    break;
  }

  if (p && p < range) {
    if (p - reg->dmin < s) {
    retry_gate:
      pprev = p;
      p += (reg->enc)->mbc_enc_len(p);
      goto retry;
    }

    if (reg->sub_anchor) {
      OnigUChar* prev;

      switch (reg->sub_anchor) {
      case (1<<1):
 if (!((p) == str)) {
   prev = onigenc_get_prev_char_head(reg->enc,
         (pprev ? pprev : str), p);
   if (!(reg->enc)->is_mbc_newline((prev),(end)))
     goto retry_gate;
 }
 break;

      case (1<<5):
 if (((p) == end)) {






 }
 else if (! (reg->enc)->is_mbc_newline((p),(end))



                )
   goto retry_gate;
 break;
      }
    }

    if (reg->dmax == 0) {
      *low = p;
      if (low_prev) {
 if (*low > s)
   *low_prev = onigenc_get_prev_char_head(reg->enc, s, p);
 else
   *low_prev = onigenc_get_prev_char_head(reg->enc,
       (pprev ? pprev : str), p);
      }
    }
    else {
      if (reg->dmax != ~((OnigDistance )0)) {
 *low = p - reg->dmax;
 if (*low > s) {
   *low = onigenc_get_right_adjust_char_head_with_prev(reg->enc, s,
             *low, (const OnigUChar** )low_prev);
   if (low_prev && (((void*)(*low_prev)) == (void*)0))
     *low_prev = onigenc_get_prev_char_head(reg->enc,
         (pprev ? pprev : s), *low);
 }
 else {
   if (low_prev)
     *low_prev = onigenc_get_prev_char_head(reg->enc,
            (pprev ? pprev : str), *low);
 }
      }
    }

    *high = p - reg->dmin;






    return 1;
  }

  return 0;
}

static int set_bm_backward_skip_old_old (OnigUChar* s, OnigUChar* end, OnigEncoding enc, int** skip)
                    ;



static int
backward_search_range_old(regex_t* reg, const OnigUChar* str, const OnigUChar* end,
        OnigUChar* s, const OnigUChar* range, OnigUChar* adjrange,
        OnigUChar** low, OnigUChar** high)
{
  int r;
  OnigUChar *p;

  range += reg->dmin;
  p = s;

 retry:
  switch (reg->optimize) {
  case 1:
  exact_method:
    p = slow_search_old_backward(reg->enc, reg->exact, reg->exact_end,
        range, adjrange, end, p);
    break;

  case 4:
    p = slow_search_old_backward_ic(reg->enc, reg->case_fold_flag,
                                reg->exact, reg->exact_end,
                                range, adjrange, end, p);
    break;

  case 2:
  case 3:
    if ((((void*)(reg->int_map_backward)) == (void*)0)) {
      if (s - range < 100)
 goto exact_method;

      r = set_bm_backward_skip_old_old(reg->exact, reg->exact_end, reg->enc,
          &(reg->int_map_backward));
      if (r) return r;
    }
    p = bm_search_old_backward(reg, reg->exact, reg->exact_end, range, adjrange,
      end, p);
    break;

  case 5:
    p = map_search_old_backward(reg->enc, reg->map, range, adjrange, p);
    break;
  }

  if (p) {
    if (reg->sub_anchor) {
      OnigUChar* prev;

      switch (reg->sub_anchor) {
      case (1<<1):
 if (!((p) == str)) {
   prev = onigenc_get_prev_char_head(reg->enc, str, p);
   if (!(reg->enc)->is_mbc_newline((prev),(end))) {
     p = prev;
     goto retry;
   }
 }
 break;

      case (1<<5):
 if (((p) == end)) {
# 3313 "regexec.c"
 }
 else if (! (reg->enc)->is_mbc_newline((p),(end))



                ) {
   p = onigenc_get_prev_char_head(reg->enc, adjrange, p);
   if ((((void*)(p)) == (void*)0)) goto fail;
   goto retry;
 }
 break;
      }
    }


    if (reg->dmax != ~((OnigDistance )0)) {
      *low = p - reg->dmax;
      *high = p - reg->dmin;
      *high = onigenc_get_right_adjust_char_head(reg->enc, adjrange, *high);
    }





    return 1;
  }

 fail:



  return 0;
}


extern int
onig_search_old(regex_t* reg, const OnigUChar* str, const OnigUChar* end,
     const OnigUChar* start, const OnigUChar* range, OnigRegion* region, OnigOptionType option)
{
  int r;
  OnigUChar *s, *prev;
  OnigMatchArg msa;
  const OnigUChar *orig_start = start;

  const OnigUChar *orig_range = range;
# 3392 "regexec.c"
  if (region

      && !((option) & (((((((((((1U << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1))

      ) {
    r = onig_region_resize_old_clear(region, reg->num_mem + 1);
    if (r) goto finish_no_msa;
  }

  if (start > end || start < str) goto mismatch_no_msa;
# 3452 "regexec.c"
  if (reg->anchor != 0 && str < end) {
    OnigUChar *min_semi_end, *max_semi_end;

    if (reg->anchor & (1<<2)) {

    begin_position:
      if (range > start)
 range = start + 1;
      else
 range = start;
    }
    else if (reg->anchor & (1<<0)) {

      if (range > start) {
 if (start != str) goto mismatch_no_msa;
 range = str + 1;
      }
      else {
 if (range <= str) {
   start = str;
   range = str;
 }
 else
   goto mismatch_no_msa;
      }
    }
    else if (reg->anchor & (1<<3)) {
      min_semi_end = max_semi_end = (OnigUChar* )end;

    end_buf:
      if ((OnigDistance )(max_semi_end - str) < reg->anchor_dmin)
 goto mismatch_no_msa;

      if (range > start) {
 if ((OnigDistance )(min_semi_end - start) > reg->anchor_dmax) {
   start = min_semi_end - reg->anchor_dmax;
   if (start < end)
     start = onigenc_get_right_adjust_char_head(reg->enc, str, start);
   else {
     start = onigenc_get_prev_char_head(reg->enc, str, end);
   }
 }
 if ((OnigDistance )(max_semi_end - (range - 1)) < reg->anchor_dmin) {
   range = max_semi_end - reg->anchor_dmin + 1;
 }

 if (start >= range) goto mismatch_no_msa;
      }
      else {
 if ((OnigDistance )(min_semi_end - range) > reg->anchor_dmax) {
   range = min_semi_end - reg->anchor_dmax;
 }
 if ((OnigDistance )(max_semi_end - start) < reg->anchor_dmin) {
   start = max_semi_end - reg->anchor_dmin;
   start = (reg->enc)->left_adjust_char_head(str, start);
 }
 if (range > start) goto mismatch_no_msa;
      }
    }
    else if (reg->anchor & (1<<4)) {
      OnigUChar* pre_end = onigenc_step_back((reg->enc),(str),(end),(1));

      max_semi_end = (OnigUChar* )end;
      if ((reg->enc)->is_mbc_newline((pre_end),(end))) {
 min_semi_end = pre_end;
# 3525 "regexec.c"
 if (min_semi_end > str && start <= min_semi_end) {
   goto end_buf;
 }
      }
      else {
 min_semi_end = (OnigUChar* )end;
 goto end_buf;
      }
    }
    else if ((reg->anchor & (1<<15))) {
      goto begin_position;
    }
  }
  else if (str == end) {
    static const OnigUChar* address_for_empty_string = (OnigUChar* )"";





    if (reg->threshold_len == 0) {
      start = end = str = address_for_empty_string;
      s = (OnigUChar* )start;
      prev = (OnigUChar* )
# 3548 "regexec.c" 3 4
                     ((void *)0)
# 3548 "regexec.c"
                         ;

      do { (msa).stack_p = (void* )0; (msa).options = (option); (msa).region = (region); (msa).start = (start); (msa).best_len = -1;} while(0);




      r = match_at_old(reg, str, end, (end), s, prev, &msa); if (r != -1) { if (r >= 0) { if (! ((reg->options) & ((((1U << 1) << 1) << 1) << 1))) { goto match; } } else goto finish; };
      goto mismatch;
    }
    goto mismatch_no_msa;
  }






  do { (msa).stack_p = (void* )0; (msa).options = (option); (msa).region = (region); (msa).start = (orig_start); (msa).best_len = -1;} while(0);







  s = (OnigUChar* )start;
  if (range > start) {
    if (s > str)
      prev = onigenc_get_prev_char_head(reg->enc, str, s);
    else
      prev = (OnigUChar* )
# 3579 "regexec.c" 3 4
                     ((void *)0)
# 3579 "regexec.c"
                         ;

    if (reg->optimize != 0) {
      OnigUChar *sch_range, *low, *high, *low_prev;

      sch_range = (OnigUChar* )range;
      if (reg->dmax != 0) {
 if (reg->dmax == ~((OnigDistance )0))
   sch_range = (OnigUChar* )end;
 else {
   sch_range += reg->dmax;
   if (sch_range > end) sch_range = (OnigUChar* )end;
 }
      }

      if ((end - start) < reg->threshold_len)
        goto mismatch;

      if (reg->dmax != ~((OnigDistance )0)) {
 do {
   if (! forward_search_range_old(reg, str, end, s, sch_range,
         &low, &high, &low_prev)) goto mismatch;
   if (s < low) {
     s = low;
     prev = low_prev;
   }
   while (s <= high) {
     r = match_at_old(reg, str, end, (orig_range), s, prev, &msa); if (r != -1) { if (r >= 0) { if (! ((reg->options) & ((((1U << 1) << 1) << 1) << 1))) { goto match; } } else goto finish; };
     prev = s;
     s += (reg->enc)->mbc_enc_len(s);
   }
 } while (s < range);
 goto mismatch;
      }
      else {
 if (! forward_search_range_old(reg, str, end, s, sch_range,
       &low, &high, (OnigUChar** )
# 3615 "regexec.c" 3 4
                             ((void *)0)
# 3615 "regexec.c"
                                 )) goto mismatch;

        if ((reg->anchor & (1<<14)) != 0) {
          do {
            r = match_at_old(reg, str, end, (orig_range), s, prev, &msa); if (r != -1) { if (r >= 0) { if (! ((reg->options) & ((((1U << 1) << 1) << 1) << 1))) { goto match; } } else goto finish; };
            prev = s;
            s += (reg->enc)->mbc_enc_len(s);

            while (!(reg->enc)->is_mbc_newline((prev),(end)) && s < range) {
              prev = s;
              s += (reg->enc)->mbc_enc_len(s);
            }
          } while (s < range);
          goto mismatch;
        }
      }
    }

    do {
      r = match_at_old(reg, str, end, (orig_range), s, prev, &msa); if (r != -1) { if (r >= 0) { if (! ((reg->options) & ((((1U << 1) << 1) << 1) << 1))) { goto match; } } else goto finish; };
      prev = s;
      s += (reg->enc)->mbc_enc_len(s);
    } while (s < range);

    if (s == range) {
      r = match_at_old(reg, str, end, (orig_range), s, prev, &msa); if (r != -1) { if (r >= 0) { if (! ((reg->options) & ((((1U << 1) << 1) << 1) << 1))) { goto match; } } else goto finish; };
    }
  }
  else {

    if (orig_start < end)
      orig_start += (reg->enc)->mbc_enc_len(orig_start);


    if (reg->optimize != 0) {
      OnigUChar *low, *high, *adjrange, *sch_start;

      if (range < end)
 adjrange = (reg->enc)->left_adjust_char_head(str, range);
      else
 adjrange = (OnigUChar* )end;

      if (reg->dmax != ~((OnigDistance )0) &&
   (end - range) >= reg->threshold_len) {
 do {
   sch_start = s + reg->dmax;
   if (sch_start > end) sch_start = (OnigUChar* )end;
   if (backward_search_range_old(reg, str, end, sch_start, range, adjrange,
        &low, &high) <= 0)
     goto mismatch;

   if (s > high)
     s = high;

   while (s >= low) {
     prev = onigenc_get_prev_char_head(reg->enc, str, s);
     r = match_at_old(reg, str, end, (orig_start), s, prev, &msa); if (r != -1) { if (r >= 0) { if (! ((reg->options) & ((((1U << 1) << 1) << 1) << 1))) { goto match; } } else goto finish; };
     s = prev;
   }
 } while (s >= range);
 goto mismatch;
      }
      else {
 if ((end - range) < reg->threshold_len) goto mismatch;

 sch_start = s;
 if (reg->dmax != 0) {
   if (reg->dmax == ~((OnigDistance )0))
     sch_start = (OnigUChar* )end;
   else {
     sch_start += reg->dmax;
     if (sch_start > end) sch_start = (OnigUChar* )end;
     else
       sch_start = (reg->enc)->left_adjust_char_head(start, sch_start)
                           ;
   }
 }
 if (backward_search_range_old(reg, str, end, sch_start, range, adjrange,
      &low, &high) <= 0) goto mismatch;
      }
    }

    do {
      prev = onigenc_get_prev_char_head(reg->enc, str, s);
      r = match_at_old(reg, str, end, (orig_start), s, prev, &msa); if (r != -1) { if (r >= 0) { if (! ((reg->options) & ((((1U << 1) << 1) << 1) << 1))) { goto match; } } else goto finish; };
      s = prev;
    } while (s >= range);
  }

 mismatch:

  if (((reg->options) & ((((1U << 1) << 1) << 1) << 1))) {
    if (msa.best_len >= 0) {
      s = msa.best_s;
      goto match;
    }
  }

  r = -1;

 finish:
  if ((msa).stack_p) free((msa).stack_p);
  ;



  if (((reg->options) & (((((1U << 1) << 1) << 1) << 1) << 1)) && region

      && !((option) & (((((((((((1U << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1) << 1))

      ) {
    onig_region_clear_old(region);
  }





  return r;

 mismatch_no_msa:
  r = -1;
 finish_no_msa:
  ;




  return r;

 match:
  ;
  if ((msa).stack_p) free((msa).stack_p);
  return s - str;
}

extern OnigEncoding
onig_get_encoding_old(regex_t* reg)
{
  return reg->enc;
}

extern OnigOptionType
onig_get_options_old(regex_t* reg)
{
  return reg->options;
}

extern OnigCaseFoldType
onig_get_case_fold_flag_old(regex_t* reg)
{
  return reg->case_fold_flag;
}

extern OnigSyntaxType*
onig_get_syntax_old(regex_t* reg)
{
  return reg->syntax;
}

extern int
onig_number_of_captures_old(regex_t* reg)
{
  return reg->num_mem;
}

extern int
onig_number_of_capture_histories_old(regex_t* reg)
{

  int i, n;

  n = 0;
  for (i = 0; i <= 31; i++) {
    if (((i) < (int )(sizeof(BitStatusType) * 8) ? ((reg->capture_history) & (1 << i)) : ((reg->capture_history) & 1)) != 0)
      n++;
  }
  return n;



}

extern void
onig_copy_encoding_old(OnigEncoding to, OnigEncoding from)
{
  *to = *from;
}
