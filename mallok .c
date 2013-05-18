/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 * 
 * Our implemention is based on using the appropriate macros. For example
 * the SET macro is assigning the required pointer into the memory allocation. 
 * We are also using the block convention which we can move between the previous and the next blocks by the macros.
 * We are using the heap convention where the node structures can be used in terms of adding the pointer block to the heap so
 * the access can be designed by the previous/next structures. We use the coalesce feature where we can 
 * create the connection between the block sizes and the each required memory allocation so that the memory
 * allocation can be initialized "NOT" randomly or "NOT" fixed value, it will be initialized in terms
 * of the memory allocation SIZE. Pre defined LIST structures allow us to use iteration oin order 
 * put the memory allocation in a while or for loop in a range. Reallocation algorithm works
 *similarly with the swap algorithm which a temp malloc variable will be replaced with the old 
 *allocator and assigned as the new allocator, where the free the memory will work in terms 
 *of iterating the list of the blocks and assigning to "nothing" which will tecnically be deletyed.
 * the code is based on the book's guidance where the block size, set, get and the other macros
 * were introduced to us. This is a very important assignment in terms of understanding the 
 *connection between the memory/data structures such as lists, heap and the basic conventions such as the add 
 *delete, swap and understanding the C's buffer concept.
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * Most of the code was directly copied from the book, and 
 * we used the same comments as the book.
 * We worked on editing the code to reach 89/100 
 ********************************************************/
team_t team = {
    /* Team name */
    "Smoking trees and stroking 3's",
    /* First member's full name */
    
    /* First member's email address */
   
    /* Second member's full name (leave blank if none) */
    
    /* Second member's email address (leave blank if none) */
    ""
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

// Basic constants and macros
#define WSIZE     4          // word and header/footer size (bytes)
#define DSIZE     8          // double word size (bytes)
#define CHUNKSIZE (1<<12)    // Extend heap by this amount (bytes)
#define INITCHUNKSIZE (1<<6) // Init extened to half the heap

#define LISTLIMIT     20        // list size
#define REALLOC_BUFFER  (1<<7)  // buffer extened by this amount

#define MAX(x, y) ((x) > (y) ? (x) : (y)) 
#define MIN(x, y) ((x) < (y) ? (x) : (y)) 

// Pack a size and allocated bit into a word
#define PACK(size, alloc) ((size) | (alloc))

// Read and write a word at address p, TAG mattes. 
#define GET(p)            (*(unsigned int *)(p))
#define PUT(p, val)       (*(unsigned int *)(p) = (val) | GET_TAG(p))

// Pointer (predecessor, successor ptr) for free blocks. 
#define SET_bp(p, bp) (*(unsigned int *)(p) = (unsigned int)(bp))

// Read the size and allocation fields from address p 
#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

// Read, set, and remove the Tag from address p
#define GET_TAG(p)   (GET(p) & 0x2)
#define SET_RATAG(p)   (GET(p) |= 0x2)
#define REMOVE_RATAG(p) (GET(p) &= ~0x2)

// Given block ptr bp, compute address of its header and footer 
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

// Given block ptr bp, compute address of predecessor and successor in the heapFreeList
#define PRED(bp) (*(char **)(bp))
#define SUCC(bp) (*(char **)(SUCC_bp(bp)))

// Given bock ptr bp, compute address of predecessor and successor blocks
#define PRED_bp(bp) ((char *)(bp))
#define SUCC_bp(bp) ((char *)(bp) + WSIZE)

// Given block ptr bp, comupte address of next and previous blocks 
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE((char *)(bp) - WSIZE))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE((char *)(bp) - DSIZE))

void *heapFreeList[LISTLIMIT];  // the only golabl variable 

/* 
 ***************************************************************************
 **********************************Helper function: Begin*********************
 ***************************************************************************
 */

static void *extend_heap(size_t size);
static void *place(void *bp, size_t asize);
static void *coalesce(void *bp);
static void add_node(void *bp, size_t size);
static void remove_node(void *bp);

/* 
 * extend_heap - Extend heap with free block and return its block pointer 
 */
static void *extend_heap(size_t size)
{
    void *bp;               
    size_t asize;
    
    asize = ALIGN(size); // alignmnet the size
    
    // maintaining alignmnet 
    if ((bp = mem_sbrk(asize)) == (void *)-1)
        return NULL;
    
    // Initialize free block header/footer and the epilogue header
    PUT(HDRP(bp), PACK(asize, 0));  // free block header
    PUT(FTRP(bp), PACK(asize, 0));  // free block footer 
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));  // new epilogue header
    add_node(bp, asize);

    // coalesce if the previous block was free 
    return coalesce(bp);
}

/* 
 * add_node - going through the lists, setting up the succ and pred when finding the pointer "add"
 */
static void add_node(void *bp, size_t size) 
{
    int list = 0;
    void *bpAdd = NULL;
    void *bpFinder = bp;

    // selecing lists
    while ((list < LISTLIMIT - 1) && (size > 1)) {
        size >>= 1;
        list++;
    }
    
    // finding a pointer while keeping the ascending order
    bpFinder = heapFreeList[list];
    while ((bpFinder != NULL) && (size > GET_SIZE(HDRP(bpFinder)))) {
        bpAdd = bpFinder;
        bpFinder = PRED(bpFinder);
    }
    
    // setting up succ and pred
    //when there is a pointer
    if (bpFinder != NULL) {
        // and its added we set the succ and pred to these 
        if (bpAdd != NULL) {
            SET_bp(PRED_bp(bp), bpFinder);
            SET_bp(SUCC_bp(bpFinder), bp);
            SET_bp(SUCC_bp(bp), bpAdd);
            SET_bp(PRED_bp(bpAdd), bp);
        } else {
            SET_bp(PRED_bp(bp), bpFinder);
            SET_bp(SUCC_bp(bpFinder), bp);
            SET_bp(SUCC_bp(bp), NULL);
            heapFreeList[list] = bp;
        }
    } else {
        if (bpAdd != NULL) {
            SET_bp(PRED_bp(bp), NULL);
            SET_bp(SUCC_bp(bp), bpAdd);
            SET_bp(PRED_bp(bpAdd), bp);
        } else {
            SET_bp(PRED_bp(bp), NULL);
            SET_bp(SUCC_bp(bp), NULL);
            heapFreeList[list] = bp;
        }
    }
    return;
}

/* 
 * remove_node - going through the lists, when finding the pred we set the pointer "remove"
 */
static void remove_node(void *bp) 
{
    int list = 0;
    size_t size = GET_SIZE(HDRP(bp));
    
    // Selecting lists 
    while ((list < LISTLIMIT - 1) && (size > 1)) {
        size >>= 1;
        list++;
    }
    
    // if we have a pred 
    if (PRED(bp) != NULL) {
        // we set the succ and the pred adress pointer 
        if (SUCC(bp) != NULL) {
            SET_bp(SUCC_bp(PRED(bp)), SUCC(bp));
            SET_bp(PRED_bp(SUCC(bp)), PRED(bp));
        } else {
            SET_bp(SUCC_bp(PRED(bp)), NULL);
            heapFreeList[list] = PRED(bp);
        }
    } else {
        if (SUCC(bp) != NULL) {
            SET_bp(PRED_bp(SUCC(bp)), NULL);
        } else {
            heapFreeList[list] = NULL;
        }
    }
    return;
}

/*
 * coalesce - Boundary tag coalescing. Return ptr to coalesced block
 */
static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(HDRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));
    
    // if prev block is tagged then we don't coalesce
    if (GET_TAG(HDRP(PREV_BLKP(bp))))
        prev_alloc = 1;

    if (prev_alloc && next_alloc) {                         // Case 1
        return bp;
    }
    else if (prev_alloc && !next_alloc) {                   // Case 2
        remove_node(bp);
        remove_node(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    } else if (!prev_alloc && next_alloc) {                 // Case 3 
        remove_node(bp);
        remove_node(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    } else {                                                // Case 4
        remove_node(bp);
        remove_node(PREV_BLKP(bp));
        remove_node(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    
    add_node(bp, size);
    
    return bp;
}

/* 
 * place - Place block of asize bytes at start of free block bp 
 *         and split if remainder would be at least minimum block size
 */
static void *place(void *bp, size_t asize)
{
    size_t bp_size = GET_SIZE(HDRP(bp));
    size_t remainder = bp_size - asize;
    
    remove_node(bp);
    
    // no splitting
    if (remainder <= DSIZE * 2) {
        PUT(HDRP(bp), PACK(bp_size, 1)); 
        PUT(FTRP(bp), PACK(bp_size, 1)); 
    }
    
    // splitting
    else if (asize >= 100) {
        PUT(HDRP(bp), PACK(remainder, 0));
        PUT(FTRP(bp), PACK(remainder, 0));
        PUT(HDRP(NEXT_BLKP(bp)), PACK(asize, 1));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(asize, 1));
        add_node(bp, remainder);
        return NEXT_BLKP(bp);
        
    }
    
    // splitting
    else {
        PUT(HDRP(bp), PACK(asize, 1)); 
        PUT(FTRP(bp), PACK(asize, 1)); 
        PUT(HDRP(NEXT_BLKP(bp)), PACK(remainder, 0)); 
        PUT(FTRP(NEXT_BLKP(bp)), PACK(remainder, 0)); 
        add_node(NEXT_BLKP(bp), remainder);
    }
    return bp;
}

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    int list;         
    char *heap_listp; // Pointer to beginning of heap
    
    // Initialize segregated free lists
    for (list = 0; list < LISTLIMIT; list++) {
        heapFreeList[list] = NULL;
    }
    
    // create the initaial empty heap
    if ((heap_listp = mem_sbrk(4*WSIZE)) ==(void *)-1)
        return -1;
    
    PUT(heap_listp, 0);                            /* Alignment padding */
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); /* Prologue header */
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));     /* Epilogue header */
    
    // Extend the empty heap with a free block of CHUNKSIZE bytes.
    if (extend_heap(INITCHUNKSIZE) == NULL)
        return -1;
    return 0;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize;      /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    void *bp = NULL;  
    
    // Ignore spurious requests
    if (size == 0)
        return NULL;
    
    // Adjust block size to include overhead and alignment reqs
    if (size <= DSIZE) {
        asize = 2 * DSIZE;
    } else {
        asize = ALIGN(size+DSIZE);
    }
    
    int list = 0; 
    size_t sizeFinder = asize;
    // Searching the tree list for a fit
    while (list < LISTLIMIT) {
        if ((list == LISTLIMIT - 1) || (( sizeFinder <= 1) && (heapFreeList[list] != NULL))) {
            bp = heapFreeList[list];
            // ignoring too small blocks or tagged
            while ((bp != NULL) && ((asize > GET_SIZE(HDRP(bp))) || (GET_TAG(HDRP(bp)))))
            {
                bp = PRED(bp);
            }
            if (bp != NULL)
                break;
        }
        //
        sizeFinder >>= 1;
        list++;
    }
    
    // No fit found. Get more memory and place the block
    if (bp == NULL) {
        extendsize = MAX(asize, CHUNKSIZE);
        
        if ((bp = extend_heap(extendsize)) == NULL)
            return NULL;
    }
    
    bp = place(bp, asize);
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));

    REMOVE_RATAG(HDRP(NEXT_BLKP(bp)));
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    
    add_node(bp, size);
    coalesce(bp);
    
    return;
}

/*
 * mm_realloc - Implementation of realloc
 */
void *mm_realloc(void *bp, size_t size)
{
    int remainder;
    size_t newSize = size;
    void *newPtr = bp;
    int extendsize;
    int bufferSize;
    
    // Ignore spurious requests
    if (size == 0)
        return NULL;
    
    // Adjust block size to include overhead and alignment reqs
    if (newSize <= DSIZE) {
        newSize = 2 * DSIZE;
    } else {
        newSize = ALIGN(size+DSIZE);
    }
    
    // adding req to block size
    newSize += REALLOC_BUFFER;
    
    // buffer size
    bufferSize = GET_SIZE(HDRP(bp)) - newSize;
    
    // if overhead below min then get more space
    if (bufferSize < 0) {
        // checking for the next block if free or else.. 
        if (!GET_ALLOC(HDRP(NEXT_BLKP(bp))) || !GET_SIZE(HDRP(NEXT_BLKP(bp)))) {
            remainder = GET_SIZE(HDRP(bp)) + GET_SIZE(HDRP(NEXT_BLKP(bp))) - newSize;
            if (remainder < 0) {
                extendsize = MAX(-remainder, CHUNKSIZE);
                if (extend_heap(extendsize) == NULL)
                    return NULL;
                remainder += extendsize;
            }
            remove_node(NEXT_BLKP(bp));
            PUT(HDRP(bp), PACK(newSize + remainder, 1)); 
            PUT(FTRP(bp), PACK(newSize + remainder, 1)); 

        } else {
            newPtr = mm_malloc(newSize - DSIZE);
            memcpy(newPtr, bp, MIN(size, newSize));
            mm_free(bp);
        }

        bufferSize = GET_SIZE(HDRP(newPtr)) - newSize;
    }
    
    // taging next block
    if (bufferSize < 2 * REALLOC_BUFFER)
        SET_RATAG(HDRP(NEXT_BLKP(newPtr)));

    return newPtr;

}
