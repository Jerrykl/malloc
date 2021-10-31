# Memory Allocator

## Overview

The design of this memory allocator is mainly based on [TCMalloc](https://github.com/gperftools/gperftools). Different from TCMalloc which supports multi-threads, this memory allocator is a simple version of TCMalloc that supports only single-thread (though it is not that complicated to add **thread cache** to support multi-threads).

## Design

Since the design including **Objects**, **Page**, **Span**, **Page Map**, **Size Map**, **Page Heap** and **Central Cache** are the same as tcmalloc, for details of TCMalloc design please refer to [TCMalloc解密](https://wallenwang.com/2018/11/tcmalloc/) and [gperftools](https://github.com/gperftools/gperftools) which include the design and the source code of TCMalloc.

The difference is that this memory allocator is for single thread thus the **thread cache** is left out.

Besides, to manage large spans, i.e. spans of which size > kMaxPages, Skip List is used instead of std::set in TCMalloc.

- Trick

  Since there is only one thread doing allocating and freeing and the heap never shrinks, in the implementation of realloc, instead of do malloc before doing free, we could just free to coalesce some spans before doing malloc, and if the new pointer returned by malloc is the same as the old pointer, we could safely skip the step of memcpy to accelerate the speed of reallocating (for small objects the first 8 bytes should be reserved because the first 8 bytes would be used as pointer to linking to the next object when it is freed).

## Experiment

### Environment

CPU: Intel(R) Xeon(R) CPU E5-2680 v3 @ 2.50GHz

### Parameters

The **kPageSize** is set to 2K and **kMinSystemAlloc** is set to 1 to reduce waste and increase utility in small test cases for this lab.

The maximum size of small span is set to 1M, so there are **kMaxPages**, i.e. 512 kinds of small spans for one kind of span from 1 page to 512 pages.

```C
#define ADDR_BITS 64

#define kAlignment 8
#define kMinAlign kAlignment

#define kPageShift 11
#define kPageSize  (1 << kPageShift)        // page size

#define kMaxPages (1 << (20 - kPageShift))  // small span range
#define kMinSystemAlloc 1                   // minimum number of pages to fetch from system at a time

#define kMaxSize (256 * 1024)               // max size of objects
#define kMaxSmallSize 1024                  // used for compressing size-to-class array
#define kClassArraySize (((kMaxSize + 127 + (120 << 7)) >> 7) + 1)
#define kClassSizesMax 96
```

### Result & Analysis

Since the memory allocator allocate memory as a multiple of pages, which is 2K in the setting, as shown in the result below, the utility is low in some test cases in which the dataset is too small that there is much memory waste when allocating a page but only few of it is actually used.

```
Using default datafiles in ./data/

Results for your malloc:
  id     valid      util      secs filename
   0       yes  0.618631  0.008122 ./data/1.in
   1       yes  0.979627  0.005251 ./data/2.in
   2       yes  0.395671  0.000364 ./data/3.in
   3       yes  0.993844  0.001719 ./data/4.in
   4       yes  0.794076  0.001675 ./data/5.in
   5       yes  0.970310  0.005405 ./data/6.in
   6       yes  0.625180  0.000506 ./data/7.in
   7       yes  0.801056  0.006259 ./data/8.in
   8       yes  0.999775  0.000442 ./data/9.in
   9       yes  0.982566  0.006325 ./data/10.in
  10       yes  0.578328  0.012565 ./data/11.in
  11       yes  0.980906  0.005190 ./data/12.in
  12       yes  0.419166  0.000249 ./data/13.in
  13       yes  0.114244  0.000246 ./data/14.in
  14       yes  0.849917  0.001701 ./data/15.in
  15       yes  0.904467  0.489978 ./data/16.in
  16       yes  0.490084  0.000259 ./data/17.in
  17       yes  0.912204  0.004962 ./data/18.in
  18       yes  0.718464  0.000861 ./data/19.in
  19       yes  0.611788  0.000975 ./data/20.in
```

## References

[gperftools](https://github.com/gperftools/gperftools)