#include <assert.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <stdint.h>
#include <sys/mman.h>

#include "solve.h"
#include "utils.h"

#define NDEBUG

#ifndef NDEBUG
#define ASSERT(cond) assert(cond)
#else
#define ASSERT(cond) ((void) 0)
#endif

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

#define mem_alloc(size) mmap(NULL, size, PROT_READ | PROT_WRITE, MAP_ANONYMOUS | MAP_PRIVATE, -1, 0)
#define mem_free(addr, size) munmap(addr, size)

typedef uintptr_t PageID;
typedef uintptr_t Length;

/*
    Span
    file: span.h span.cc
*/
// -------------------------------------------------------------------------
typedef enum
{
    IN_USE = 1,
    ON_NORMAL_FREELIST = 2
}SpanLocation;

typedef struct Span
{
    PageID start;   // starting page number
    Length length;  // number of pages in span
    struct Span* next;     // used in linked list
    struct Span* prev;     // used in linked list

    struct Snode* node;

    void* objects;

    unsigned int refcount : 16; // number of non-free objects
    unsigned int size_class : 8; // size-class for small objects
    unsigned int location : 2;  // location 

}Span;

inline Span* new_span(PageID p, Length len);
inline void delete_span(Span* span);
inline void remove_span_from_list(Span* span);
inline void prepend_span_to_list(Span* list, Span* span);
inline void init_span_list(Span* span);
inline int span_list_is_empty(const Span* list);

void init_span_list(Span* list)
{
    list->prev = list;
    list->next = list;
}

Span* new_span(PageID p, Length len)
{
    Span* span = mem_alloc(sizeof(Span));
    span->start = p;
    span->length = len;
    span->location = IN_USE;
    return span;
}

void delete_span(Span* span)
{
    mem_free(span, sizeof(Span));
}

void remove_span_from_list(Span* span)
{
    span->prev->next = span->next;
    span->next->prev = span->prev;
    span->prev = NULL;
    span->next = NULL;
}

void prepend_span_to_list(Span* list, Span* span)
{
    ASSERT(span->next == NULL);
    ASSERT(span->prev == NULL);
    span->prev = list;
    span->next = list->next;
    span->next->prev = span;
    list->next = span;
}

int span_list_is_empty(const Span* list)
{
    return list->next == list;
}
// -------------------------------------------------------------------------
// Span end

/*
    Page Map
    a 3-level radix tree
    file: pagemap.h
*/
// -------------------------------------------------------------------------
typedef uintptr_t RT_Number;
#define RT_BITS (ADDR_BITS - kPageShift)

#define INTERIOR_BITS ((RT_BITS + 2) / 3)
#define INTERIOR_LENGTH (1 << INTERIOR_BITS)

#define LEAF_BITS (RT_BITS - 2*INTERIOR_BITS)
#define LEAF_LENGTH (1 << LEAF_BITS)

typedef struct RT_Node
{
    struct RT_Node* ptrs[INTERIOR_LENGTH];
}RT_Node;

typedef struct RT_Leaf
{
    void* values[LEAF_LENGTH];
}RT_Leaf;

inline RT_Node* RT_new_node();
inline RT_Leaf* RT_new_leaf();
inline void* RT_get(RT_Node* root, RT_Number k);
inline void RT_set(RT_Node* root, RT_Number k, void* v);
inline void RT_ensure(RT_Node* root, RT_Number start, size_t n);

RT_Node* RT_new_node()
{
    RT_Node* result = mmap(NULL, INTERIOR_LENGTH * sizeof(RT_Node*), PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    ASSERT(result > 0 && result != MAP_FAILED);
    return result;
}

RT_Leaf* RT_new_leaf()
{
    RT_Leaf* result = mmap(NULL, LEAF_LENGTH * sizeof(RT_Leaf*), PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    ASSERT(result > 0 && result != MAP_FAILED);
    return result;
}

void* RT_get(RT_Node* root, RT_Number k)
{
    const RT_Number i1 = k >> (LEAF_BITS + INTERIOR_BITS);
    const RT_Number i2 = (k >> LEAF_BITS) & (INTERIOR_LENGTH - 1);
    const RT_Number i3 = k & (LEAF_LENGTH - 1);
    ASSERT((k >> RT_BITS) == 0 && root->ptrs[i1] != NULL && root->ptrs[i1]->ptrs[i2] != NULL);
    return ((RT_Leaf*)(root->ptrs[i1]->ptrs[i2]))->values[i3];
}

void RT_set(RT_Node* root, RT_Number k, void* v)
{
    ASSERT(k >> RT_BITS == 0);
    const RT_Number i1 = k >> (LEAF_BITS + INTERIOR_BITS);
    const RT_Number i2 = (k >> LEAF_BITS) & (INTERIOR_LENGTH - 1);
    const RT_Number i3 = k & (LEAF_LENGTH - 1);
    ((RT_Leaf*)(root->ptrs[i1]->ptrs[i2]))->values[i3] = v;
}

void RT_ensure(RT_Node* root, RT_Number start, size_t n)
{
    RT_Number key;
    for (key = start; key <= start + n - 1; )
    {
        const RT_Number i1 = key >> (LEAF_BITS + INTERIOR_BITS);
        const RT_Number i2 = (key >> LEAF_BITS) & (INTERIOR_LENGTH - 1);

        // check for overflow
        ASSERT(i1 < INTERIOR_LENGTH && i2 < INTERIOR_LENGTH);

        // create 2nd level node if necessary
        if (root->ptrs[i1] == NULL)
        {
            RT_Node* node = RT_new_node();
            ASSERT(node != NULL);
            root->ptrs[i1] = node;
        }

        // make leaf node if necessary
        if (root->ptrs[i1]->ptrs[i2] == NULL)
        {
            RT_Leaf* leaf = RT_new_leaf();
            ASSERT(leaf != NULL);
            root->ptrs[i1]->ptrs[i2] = (RT_Node*)leaf;
        }

        // advance key to the next interior node
        key = ((key >> LEAF_BITS) + 1) << LEAF_BITS;
    }
}

void* RT_next(RT_Node* root, RT_Number k)
{
    while (k < ((RT_Number)1 << RT_BITS))
    {
        const RT_Number i1 = k >> (LEAF_BITS + INTERIOR_BITS);
        const RT_Number i2 = (k >> LEAF_BITS) & (INTERIOR_BITS - 1);
        if (root->ptrs[i1] == NULL)
        {
            // advance to the next top-level entry
            k = (i1 + 1) << (LEAF_BITS + INTERIOR_BITS);
        }
        else
        {
            RT_Leaf* leaf = (RT_Leaf*)(root->ptrs[i1]->ptrs[i2]);
            if (leaf != NULL)
            {
                RT_Number i3;
                for (i3 = (k & (LEAF_LENGTH - 1)); i3 < LEAF_LENGTH; i3++)
                    if (leaf->values[i3] != NULL)
                        return leaf->values[i3];
            }
            // advance to the next interior entry
            k = ((k >> LEAF_BITS) + 1) << LEAF_BITS;
        }
    }
    return NULL;
}
// -------------------------------------------------------------------------
// Page Map end

/*
    Skip List    
*/
// -------------------------------------------------------------------------
#define SKIPLIST_MAX_LEVEL 6
#define BIASED_COIN_SHIFT 1

typedef enum SkiplistStatus
{
    SKIPLIST_FAILED = -1,
    SKIPLIST_SUCCESS = 0
}SkiplistStatus;

typedef int SKeyType;
typedef Span* SValType;

typedef struct Snode
{
    SKeyType key;
    SValType value;
    struct Snode** backward;
    struct Snode** forward;
}Snode;

typedef struct Skiplist
{
    int level;
    int size;
    Snode* header;
}Skiplist;

inline void Skiplist_insert(Skiplist* list, SKeyType key, SValType value);
inline Snode* Skiplist_search_ge(Skiplist* list, SKeyType key);
inline SkiplistStatus Skiplist_delete_by_key(Skiplist* list, SKeyType key);
inline void Skiplist_delete_by_node(Skiplist* list, Snode* node);
inline Snode* Skiplist_search_e(Skiplist* list, SKeyType key);
inline SkiplistStatus Skiplist_fetch_ge(Skiplist* list, SKeyType key, SValType* val);

inline static int Skiplist_rand_level();
inline static void Skiplist_free(Snode* node);

Skiplist* Skiplist_init(Skiplist* list)
{
    int i;
    Snode* header = (Snode*)mem_alloc(sizeof(Snode));
    list->header = header;
    header->key = INT_MAX;
    header->backward = (Snode**)mem_alloc(sizeof(Snode*) * (SKIPLIST_MAX_LEVEL + 1));
    header->forward = (Snode**)mem_alloc(sizeof(Snode*) * (SKIPLIST_MAX_LEVEL + 1));
    for (i = 0; i <= SKIPLIST_MAX_LEVEL; i++)
    {
        header->backward[i] = list->header;
        header->forward[i] = list->header;
    }

    list->level = 1;
    list->size = 0;
    return list;
}

int Skiplist_rand_level()
{
    int level = 1;
    while (rand() < (RAND_MAX >> BIASED_COIN_SHIFT) && level < SKIPLIST_MAX_LEVEL)
        level++;
    return level;
}

void Skiplist_insert(Skiplist* list, SKeyType key, SValType value)
{
    Snode* prev[SKIPLIST_MAX_LEVEL + 1];
    Snode* node = list->header;
    int i, level;
    for (i = list->level; i >= 1; i--)
    {
        while(node->forward[i]->key < key)
            node = node->forward[i];
        prev[i] = node;
    }
    node = node->forward[1];

    level = Skiplist_rand_level();
    if (level > list->level)
    {
        for (i = list->level + 1; i <= level; i++)
            prev[i] = list->header;
        list->level = level;
    }

    node = (Snode*)mem_alloc(sizeof(Snode));
    node->key = key;
    node->value = value;
    node->backward = (Snode**)mem_alloc(sizeof(Snode*) * (level + 1));
    node->forward = (Snode**)mem_alloc(sizeof(Snode*) * (level + 1));
    node->backward[0] = (Snode*)(size_t)(level + 1); // used for free
    node->forward[0] = (Snode*)(size_t)(level + 1); // used for free
    for (i = 1; i <= level; i++)
    {
        node->backward[i] = prev[i];
        node->forward[i] = prev[i]->forward[i];
        node->forward[i]->backward[i] = node;
        prev[i]->forward[i] = node;
    }

    value->node = node;
}

Snode* Skiplist_search_e(Skiplist* list, SKeyType key)
{
    Snode* node = list->header;
    int i;
    for (i = list->level; i >= 1; i--)
        while (node->forward[i]->key < key)
            node = node->forward[i];
    if (node->forward[1]->key == key)
        return node->forward[1];
    return NULL;
}

Snode* Skiplist_search_ge(Skiplist* list, SKeyType key)
{
    Snode* node = list->header;
    int i;
    for (i = list->level; i >= 1; i--)
        while (node->forward[i]->key < key)
            node = node->forward[i];
    if (node->forward[1]->key < INT_MAX)
        return node->forward[1];
    return NULL;
}

void Skiplist_free(Snode* node)
{
    if (node)
    {
        mem_free(node->backward, sizeof(Snode*) * (size_t)node->forward[0]);
        mem_free(node->forward, sizeof(Snode*) * (size_t)node->forward[0]);
        mem_free(node, sizeof(Snode));
    }
}

SkiplistStatus Skiplist_delete_by_key(Skiplist* list, SKeyType key)
{
    int i;
    Snode* prev[SKIPLIST_MAX_LEVEL + 1];
    Snode* node = list->header;
    for (i = list->level; i >= 1; i--)
    {
        while (node->forward[i]->key < key)
            node = node->forward[i];
        prev[i] = node;
    }

    node = node->forward[1];
    if (node->key == key)
    {
        for (i = 1; i <= list->level; i++)
        {
            if (prev[i]->forward[i] != node)
                break;
            node->forward[i]->backward[i] = prev[i];
            prev[i]->forward[i] = node->forward[i];
        }
        Skiplist_free(node);

        while (list->level > 1 && list->header->forward[list->level] == list->header)
            list->level--;
        return SKIPLIST_SUCCESS;
    }
    return SKIPLIST_FAILED;
}

void Skiplist_delete_by_node(Skiplist* list, Snode* node)
{
    node->value->node = NULL;

    int i;
    for (i = 1; i <= (size_t)node->forward[i]; i++)
    {
        node->forward[i]->backward[i] = node->backward[i];
        node->backward[i]->forward[i] = node->forward[i];
    }
    Skiplist_free(node);
}

SkiplistStatus Skiplist_fetch_ge(Skiplist* list, SKeyType key, SValType* val)
{
    int i;
    Snode* prev[SKIPLIST_MAX_LEVEL + 1];
    Snode* node = list->header;
    for (i = list->level; i >= 1; i--)
    {
        while (node->forward[i]->key < key)
            node = node->forward[i];
        prev[i] = node;
    }

    node = node->forward[1];
    if (node->key < INT_MAX)
    {
        *val = node->value;
        for (i = 1; i <= list->level; i++)
        {
            if (prev[i]->forward[i] != node)
                break;
            node->forward[i]->backward[i] = prev[i];
            prev[i]->forward[i] = node->forward[i];
        }
        Skiplist_free(node);

        while (list->level > 1 && list->header->forward[list->level] == list->header)
            list->level--;
        return SKIPLIST_SUCCESS;
    }
    return SKIPLIST_FAILED;
}
// -------------------------------------------------------------------------
// Skip List end

/*
    Page Heap
    heap for page-level allocation
    allocate and free a contiguous runs of pages (called a "span")
    file: page_heap.h page_heap.cc
*/
// -------------------------------------------------------------------------

// struct PH_SmallSpanStats
// {
//     // For each free list of small spans, the length (in spans) of the
//     // normal and returned free lists for that size.
//     int64_t normal_length[kMaxPages];
// };

// struct PH_LargeSpanStats
// {
//     int64_t spans; // number of spans
//     int64_t normal_pages;
// };
inline Span* PH_new(Length n);
inline void PH_delete(Span* span);
inline void PH_register_size_class(Span* span, uint32_t sc);

inline static void PH_record_span(Span* span);
inline static void PH_remove_from_free_list(Span* span);
inline static void PH_insert_to_free_list(Span* span);
inline static Span* PH_carve(Span* span, Length n);
inline static Span* PH_fetch(Length n);
inline static void PH_grow_heap(Length n);
inline static Span* PH_check_and_handle_merge(Span* span, Span* other);
inline static void PH_merge_into_free_list(Span* span);

RT_Node* page_map;
Span small_span_free_list[kMaxPages];
Skiplist large_span_free_list;

void PH_init()
{
    int i;
    for (i = 0; i < kMaxPages; i++)
        init_span_list(&small_span_free_list[i]);
    Skiplist_init(&large_span_free_list);
}

void PH_record_span(Span* span)
{
    RT_set(page_map, span->start, span);
    if (span->length > 1)
        RT_set(page_map, span->start + span->length - 1, span);
}

void PH_remove_from_free_list(Span* span)
{
    if (span->length <= kMaxPages)
        remove_span_from_list(span);
    else
        Skiplist_delete_by_node(&large_span_free_list, span->node);
    // span that span->length > kMagPages has benn deleted in function carve by node
}

void PH_insert_to_free_list(Span* span)
{
    ASSERT(span->prev == NULL);
    ASSERT(span->next == NULL);

    if (span->length <= kMaxPages)
    {
        Span* list = &(small_span_free_list[span->length-1]);
        prepend_span_to_list(list, span);
    }
    else
        Skiplist_insert(&large_span_free_list, span->length, span);
}

Span* PH_carve(Span* span, Length n)
{
    ASSERT(span->location != IN_USE);
    PH_remove_from_free_list(span);
    const int old_location = span->location;
    span->location = IN_USE;
    const int extra = span->length - n;

    if (extra > 0)
    {
        Span* leftover = new_span(span->start + n, extra);
        leftover->location = old_location;
        PH_record_span(leftover);
        PH_insert_to_free_list(leftover);

        span->length = n;
        RT_set(page_map, span->start + n - 1, span);
    }
    return span;
}

Span* PH_fetch(Length n)
{
    ASSERT(n > 0);

    Span* span;
    Length s;
    // find the first span that size >= n in small span list
    for (s = n; s <= kMaxPages; s++)
    {
        span = &(small_span_free_list[s-1]);
        // if list not empty
        if (!span_list_is_empty(span))
        {
            ASSERT(span->next->location == ON_NORMAL_FREELIST);
            return PH_carve(span->next, n);
        }
    }
    // find the first span that size >= n in large span list
    Snode* node = Skiplist_search_ge(&large_span_free_list, n);
    if (node != NULL)
    {
        span = node->value;
        // Skiplist_delete_by_node(&large_span_free_list, node);
        ASSERT(span->location == ON_NORMAL_FREELIST);
        return PH_carve(span, n);
    }
    return NULL;
}

void PH_grow_heap(Length n)
{
    Length n_ask = (n > kMinSystemAlloc) ? n : (Length)kMinSystemAlloc;

    size_t actual_size = n_ask * kPageSize;
    void* ptr = mem_sbrk(actual_size);

    const PageID p = (uintptr_t)(ptr) >> kPageShift;
    ASSERT(p > 0);

    // make sure pagemap_ has entries for all of the new pages.
    // plus ensure one before and one after so coalescing code
    // does not need bounds-checking.
    RT_ensure(page_map, p-1, n_ask+2);
    Span* span = new_span(p, n_ask);
    PH_record_span(span);
    PH_delete(span); // coalesce if possible
}

// allocate a run of "n" pages.  Returns zero if out of memory.
Span* PH_new(Length n)
{
    Span* span = PH_fetch(n);
    if (span != NULL)
        return span;

    PH_grow_heap(n);
    return PH_fetch(n);
}

Span* PH_check_and_handle_merge(Span* span, Span* other)
{
    if (other == NULL)
        return other;

    if (span->location == ON_NORMAL_FREELIST && other->location == ON_NORMAL_FREELIST)
    {
        PH_remove_from_free_list(other);
        return other;
    }

    return NULL;
}

void PH_merge_into_free_list(Span* span)
{
    ASSERT(span->location != IN_USE);

    const PageID p = span->start;
    const Length n = span->length;

    Span* prev = PH_check_and_handle_merge(span, RT_get(page_map, p - 1));
    if (prev != NULL)
    {
        // merge previous span into current span
        ASSERT(prev->start + prev->length == p);
        const Length len = prev->length;
        delete_span(prev);
        span->length += len;
        span->start -= len;
        RT_set(page_map, span->start, span);
    }
    Span* next = PH_check_and_handle_merge(span, RT_get(page_map, p + n));
    if (next != NULL)
    {
        // merge next span into current span
        ASSERT(next->start == p + n);
        const Length len = next->length;
        delete_span(next);
        span->length += len;
        RT_set(page_map, span->start + span->length - 1, span);
    }

    PH_insert_to_free_list(span);
}

void PH_delete(Span* span)
{
    ASSERT(span->location == IN_USE);
    ASSERT(span->length > 0);
    ASSERT(span == RT_get(page_map, span->start));
    ASSERT(span == RT_get(page_map, span->start + span->length - 1));

    span->size_class = 0;
    span->location = ON_NORMAL_FREELIST;

    PH_merge_into_free_list(span);  // coalesce if possible
}

void PH_register_size_class(Span* span, uint32_t sc)
{
    span->size_class = sc;
    Length i;
    for (i = 1; i < span->length - 1; i++)
        RT_set(page_map, span->start + i, span);
}
// -------------------------------------------------------------------------
// Page Heap end

/*
    Size Map
    mapping from size to size_class and vice versa
    file: common.h common.cc
*/
// -------------------------------------------------------------------------
// mapping from size to size-class
unsigned char class_array[kClassArraySize];
// mapping from size-class to object size
int32_t class_to_size[kClassSizesMax];
// maaping from size-class to number of pages to allocate at a time
size_t class_to_pages[kClassSizesMax];

inline size_t SM_class_array_index(size_t s);
inline int SM_class(size_t s);
inline int SM_alignment_for_size(size_t size);
inline int SM_LgFloor(size_t n);
inline int32_t SM_class_to_size(uint32_t c);
inline size_t SM_class_to_pages(uint32_t cl);

size_t num_size_classes;

void SM_init()
{
    ASSERT(SM_class_array_index(0) == 0);
    ASSERT(SM_class_array_index(kMaxSize) < sizeof(class_array));

    int sc = 1;
    int alignment = kAlignment;
    size_t size;
    for (size = kAlignment; size <= kMaxSize; size += alignment)
    {
        alignment = SM_alignment_for_size(size);
        ASSERT((size % kAlignment) == 0);

        size_t psize = kPageSize;
        // allocate enough pages so leftover is less than 1/8 of total.
        // this bounds wasted space to at most 12.5%.
        while ((psize % size) > (psize >> 3))
            psize += kPageSize;
        const size_t pages = psize >> kPageShift;

        if (sc > 1 && pages == class_to_pages[sc-1])
        {
            // see if we can merge this into the previous class without
            // increasing the fragmentation of the previous class.
            const size_t objects = (pages << kPageShift) / size;
            const size_t prev_objects = (class_to_pages[sc-1] << kPageShift) / class_to_size[sc-1];
            if (objects == prev_objects)
            {
                // adjust previous class to current class
                class_to_size[sc-1] = size;
                continue;
            }
        }

        // add new class
        class_to_pages[sc] = pages;
        class_to_size[sc] = size;
        sc++;
    }
    num_size_classes = sc-1;
    ASSERT(num_size_classes <= kClassSizesMax);

    // initialize class_array
    int next_size = 0;
    int c;
    for (c = 1; c <= num_size_classes; c++)
    {
        const int max_size_in_class = class_to_size[c];
        int s;
        for (s = next_size; s <= max_size_in_class; s += kAlignment)
            class_array[SM_class_array_index(s)] = c;
        next_size = max_size_in_class + kAlignment;
    }

#ifndef NDEBUG
    // check sizes to be safe
    for (size = 0; size <= kMaxSize; )
    {
        const int sc = SM_class(size);
        ASSERT(sc > 0 && sc <= num_size_classes);
        if (sc > 1)
            ASSERT(size > class_to_size[sc-1]);
        const size_t s = class_to_size[sc];
        ASSERT(size <= s);

        if (size <= kMaxSmallSize)
            size += 8;
        else
            size += 128;
    }

    // check for alignment
    // i.e. we're checking that
    // align = (1 << shift), malloc(i * align) % align == 0,
    size_t align;
    for (align = kMinAlign; align <= kPageSize; align <<= 1)
        for (size = align; size < kPageSize; size += align)
            ASSERT(class_to_size[SM_class(size)] % align == 0);
#endif
}

int SM_LgFloor(size_t n)
{
    int log = 0;
    int i;
    for (i = 4; i >= 0; --i)
    {
        int shift = (1 << i);
        size_t x = n >> shift;
        if (x !=  0)
        {
            n = x;
            log += shift;
        }
    }
    ASSERT(n == 1);
    return log;
}

int SM_alignment_for_size(size_t size)
{
    int alignment = kAlignment;
    if (size > kMaxSize)
        alignment = kPageSize;
    else if (size >= 128)
        alignment = (1 << SM_LgFloor(size)) / 8;
    else if(size >= kMinAlign)
        alignment = kMinAlign; // alignment for vectorization
    return alignment;
}

int SM_class(size_t s)
{
    return class_array[SM_class_array_index(s)];
}

size_t SM_class_array_index(size_t s)
{
    ASSERT(s >= 0);
    ASSERT(s <= kMaxSize);

    if (s <= kMaxSmallSize)
        return (s + 7) >> 3;
    else
        return (s + 127 + (120 << 7)) >> 7;
}

int32_t SM_class_to_size(uint32_t cl)
{
    return class_to_size[cl];
}

size_t SM_class_to_pages(uint32_t cl)
{
    return class_to_pages[cl];
}
// -------------------------------------------------------------------------
// Size Map end

/*
    Central List
    file: central_freelist.h central_freelist.cc
*/
// -------------------------------------------------------------------------
typedef struct CentralFreeList
{
    size_t size_class;
    Span empty;         // header for list of empty spans
    Span nonempty;      // header for list of nonempty spans
    size_t num_spans;   // number of spans in empty plus nonempty
    size_t counter;     // number of free objects
}CentralFreeList;

CentralFreeList central_free_lists[kClassSizesMax];

inline void CFL_populate(CentralFreeList* list);
inline int CFL_fetch_from_one_span(CentralFreeList* list, int n, void** start, void** end);
inline int CFL_fetch(CentralFreeList* list, int n, void** start, void** end);
inline Span* CFL_object_to_span(void* object);
inline void CFL_release_to_spans(CentralFreeList* list, void* object);

void CFL_init()
{
    int i;
    for (i = 1; i <= num_size_classes; i++)
    {
        CentralFreeList* list = &central_free_lists[i];
        list->size_class = i;
        init_span_list(&list->empty);
        init_span_list(&list->nonempty);
        list->num_spans = 0;
        list->counter = 0;
    }
}

void CFL_populate(CentralFreeList* list)
{
    const size_t npages = SM_class_to_pages(list->size_class);

    Span* span;
    span = PH_new(npages);
    if (span)
        PH_register_size_class(span, list->size_class);
    ASSERT(span != NULL);
    ASSERT(span->length == npages);

    void** tail = &span->objects;
    char* ptr = (char*)(span->start << kPageShift);
    char* limit = ptr + (npages << kPageShift);
    const size_t size = SM_class_to_size(list->size_class);
    int nobjects = 0;
    // initialize pointers in this span
    while (ptr + size <= limit)
    {
        *tail = ptr;
        tail = (void**)ptr;
        ptr += size;
        nobjects++;
    }
    ASSERT(ptr <= limit);
    *tail = NULL;
    span->refcount = 0;

    prepend_span_to_list(&list->nonempty, span);
    list->num_spans++;
    list->counter += nobjects;
}

// fetch n objects fromw one span
int CFL_fetch_from_one_span(CentralFreeList* list, int n, void** start, void** end)
{
    if (span_list_is_empty(&list->nonempty))
        return 0;
    Span* span = (list->nonempty).next;

    ASSERT(span->objects != NULL);

    int result = 0;
    void *prev, *curr;
    curr = span->objects;

    do
    {
        prev = curr;
        curr = *(void**)curr;
    } while (++result < n && curr != NULL);

    // printf("obj: %x start: %x end: %x\n", span->objects, span->objects, prev);

    if (curr == NULL)
    {
        remove_span_from_list(span);
        prepend_span_to_list(&list->empty, span);
    }

    *start = span->objects;
    *end = prev;
    span->objects = curr;
    *(void**)*end = NULL;
    span->refcount += result;
    list->counter -= result;
    return result;
}

int CFL_fetch(CentralFreeList* list, int n, void** start, void** end)
{
    int result = CFL_fetch_from_one_span(list, n, start, end);
    if (result == 0)
    {
        CFL_populate(list);
        result = CFL_fetch_from_one_span(list, n, start, end);
    }
    ASSERT(result != 0);
    return result;
}

Span* CFL_object_to_span(void* object)
{
    const PageID p = (uintptr_t)object >> kPageShift;
    Span* span = RT_get(page_map, p);
    return span;
}

void CFL_release_to_spans(CentralFreeList* list, void* object)
{
    Span* span = CFL_object_to_span(object);
    ASSERT(span != NULL);
    ASSERT(span->refcount > 0);

    // if span is empty, move it to nonempty list
    if (span->objects == NULL)
    {
        remove_span_from_list(span);
        prepend_span_to_list(&list->nonempty, span);
    }

    list->counter++;
    span->refcount--;

    // delete span if refcount == 0
    if (span->refcount == 0)
    {
        list->counter -= (span->length << kPageShift) / SM_class_to_size(span->size_class);
        remove_span_from_list(span);
        list->num_spans--;

        PH_delete(span);
    }
    else
    {
        *(void**)object = span->objects;
        span->objects = object;
    }
}
// -------------------------------------------------------------------------
// Central List end

// -------------------------------------------------------------------------
inline void* my_fetch(size_t size);
inline void my_release(void* ptr);

inline Length bytes_to_pages(size_t bytes);
inline void* span_to_malloc_result(Span* span);
inline size_t get_alloc_size(void* ptr);

Length bytes_to_pages(size_t bytes)
{
    return (bytes >> kPageShift) + ((bytes & (kPageSize - 1)) > 0 ? 1 : 0);
}

void* span_to_malloc_result(Span* span)
{
    return (void*)(span->start << kPageShift);
}

size_t get_alloc_size(void* ptr)
{
    Span* span = CFL_object_to_span(ptr);
    size_t cl = span->size_class;

    if (cl > 0)
        return SM_class_to_size(cl);
    else
        return span->length << kPageShift;
}

void* my_fetch(size_t size)
{
    void *start = NULL, *end = NULL;
    if (size <= kMaxSize)
    {
        size_t cl = SM_class(size);
        CentralFreeList* list = &central_free_lists[cl];
        CFL_fetch(list, 1, &start, &end);
    }
    else
    {
        Span* span = PH_new(bytes_to_pages(size));
        ASSERT(span != NULL);
        start = span_to_malloc_result(span);
    }

    return start;
}

void my_release(void* ptr)
{
    Span* span = CFL_object_to_span(ptr);
    size_t cl = span->size_class;

    if (cl > 0)
    {
        CentralFreeList* list = &central_free_lists[cl];
        CFL_release_to_spans(list, ptr);
    }
    else
        PH_delete(span);
}
// -------------------------------------------------------------------------

inline void *my_malloc(size_t size);
inline void my_free(void *ptr);
inline void *my_realloc(void *ptr, size_t size);

int my_init() {
    char* ptr = mem_sbrk(0);
    // printf("%ld %d\n", ptr, (size_t)ptr % kPageSize);
    // printf("%ld\n", (((size_t)ptr) + kPageSize - 1) / kPageSize * kPageSize - (size_t)ptr);
    ptr = mem_sbrk(((size_t)ptr + kPageSize - 1) / kPageSize * kPageSize - (size_t)ptr);
    ptr = mem_sbrk(0);
    // printf("%ld\n", (((size_t)ptr) + kPageSize - 1) / kPageSize * kPageSize - (size_t)ptr);
    ASSERT((size_t)ptr % kPageSize == 0);
    page_map = RT_new_node();
    SM_init();
    PH_init();
    CFL_init();

    // int i;
    // for (i = 0; i < kClassSizesMax; i++)
    //     printf("[%d]%ld\t", class_to_size[i], class_to_pages[i]);
    return 0;
}

void *my_malloc(size_t size)
{
    if (size > 0)
        return my_fetch(size);
    else
        return NULL;
}

void my_free(void *ptr)
{
    if (ptr != NULL)
        my_release(ptr);
}

void *my_realloc(void *ptr, size_t size)
{
    if (size == 0)
    {
        my_free(ptr);
        return NULL;
    }
    if (ptr == NULL)
        return my_malloc(size);

    size_t old_size = get_alloc_size(ptr);

    // do not shrink if old_size * 0.875 <= size <= old_size
    if (size >= ((old_size >> 1) + (old_size >> 2)) && size <= old_size)
        return ptr;

#define SINGLE_THREAD

#ifdef SINGLE_THREAD
    if (old_size > kMaxSize)
    {
        my_free(ptr);
        void* new_ptr = my_malloc(size);
        if (ptr == new_ptr)
            return new_ptr; // memcpy skipped
    }
    uint64_t tmp;
    tmp = *(uint64_t*)ptr;
    my_free(ptr);
    void* new_ptr = my_malloc(size);
    *(uint64_t*)new_ptr = tmp;
    if (new_ptr == ptr)
        return new_ptr; // memcpy skipped

    size_t copy_size = old_size < size ? old_size : size;
    memcpy(new_ptr, ptr, copy_size);
    *(uint64_t*)new_ptr = tmp;
#else
    void* new_ptr = my_malloc(size);
    size_t copy_size = old_size < size ? old_size : size;
    memcpy(new_ptr, ptr, copy_size);
    my_free(ptr);
#endif

    return new_ptr;
}
