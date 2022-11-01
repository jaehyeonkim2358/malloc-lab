/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 * 
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
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
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "team_4",
    /* First member's full name */
    "JaeHyeon Kim",
    /* First member's email address */
    "jaehyeonkim2358@gmail.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

#define WSIZE               4
#define DSIZE               8
#define CHUNKSIZE           (1<<12)

#define MAX(x, y)           ((x) > (y) ? (x) : (y))

#define PACK(size, alloc)   ((size) | (alloc))

#define GET(p)              (*(unsigned int *)(p))
#define PUT(p, val)         (*(unsigned int *)(p) = (val))

#define GET_SIZE(p)         (GET(p) & ~0x7)
#define GET_ALLOC(p)        (GET(p) & 0x1)

#define HDRP(bp)            ((char *)(bp) - WSIZE)
#define FTRP(bp)            ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

#define NEXT_BLKP(bp)       ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)       ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))


/* explicit */
#define PRED(bp)            ((char *)(bp))
#define SUCC(bp)            ((char *)(bp) + WSIZE)


static char *heap_listp = NULL;
static char *root = NULL;

// free block을 절대 주소값을 기준으로 삽입
static void insert_node(char *bp) {
    char *succ;
    for(succ = GET(root); succ != NULL; succ = GET(SUCC(succ))) {
        if(bp < succ) {
            // bp의 predecessor, successor 설정
            PUT(PRED(bp), GET(PRED(succ)));
            PUT(SUCC(bp), succ);
            
            if(GET(PRED(succ)) != NULL) {
                PUT(SUCC(GET(PRED(succ))), bp);
            } else {
                PUT(root, bp);
            }
            
            PUT(PRED(succ), bp);
            return;
        } else if(GET(SUCC(succ)) == NULL) {
            PUT(PRED(bp), succ);
            PUT(SUCC(bp), 0);
            PUT(SUCC(succ), bp);
            return;
        }
    }
    // bp가 가용 리스트의 하나뿐인 블록의 주소일 경우
    PUT(root, bp);
    PUT(PRED(bp), 0);
    PUT(SUCC(bp), 0);
}


static void delete_node(char *bp) {
    if(GET(PRED(bp)) == NULL && GET(SUCC(bp)) == NULL) {            /* bp가 root면서 혼자 있을 때 */
        PUT(root, GET(SUCC(bp)));
    } else if(GET(PRED(bp)) != NULL && GET(SUCC(bp)) == NULL) {     /* bp가 root가 아니면서 list의 마지막 node일 때 */
        PUT(SUCC(GET(PRED(bp))), GET(SUCC(bp)));
    } else if(GET(PRED(bp)) == NULL && GET(SUCC(bp)) != NULL) {     /* bp가 root면서 뒤에 node가 존재할 때 */
        PUT(PRED(GET(SUCC(bp))), GET(PRED(bp)));
        PUT(root, GET(SUCC(bp)));
    } else {                                                        /* bp의 앞, 뒤에 node가 존재할 때 */
        PUT(PRED(GET(SUCC(bp))), GET(PRED(bp)));
        PUT(SUCC(GET(PRED(bp))), GET(SUCC(bp)));
    }

    // bp는 이제 가용 블럭이 아니므로, PRED, SUCC 정보를 지워줌
    PUT(PRED(bp), 0);
    PUT(SUCC(bp), 0);
}


static void *find_fit(size_t asize) {
    for(char *bp = GET(root); bp != NULL; bp = GET(SUCC(bp))) {
        if(GET_SIZE(HDRP(bp)) >= asize) {
            return bp;
        }
    }

    return NULL;
}


static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if(prev_alloc && next_alloc) {
        insert_node(bp);
        return bp;
    } else if(prev_alloc && !next_alloc) {
        delete_node(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
        insert_node(bp);
    } else if(!prev_alloc && next_alloc) {
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    } else {
        delete_node(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp))) + GET_SIZE(FTRP(PREV_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    return bp;
}

static void place(void *bp, size_t asize) {
    size_t csize = GET_SIZE(HDRP(bp));
    delete_node(bp);

    if(2 * DSIZE <= (csize-asize)) {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK((csize-asize), 0));
        PUT(FTRP(bp), PACK((csize-asize), 0));
        PUT(PRED(bp), 0);
        PUT(SUCC(bp), 0);
        coalesce(bp);
    } else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }

}

static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if((long)(bp = mem_sbrk(size)) == (void *)-1) {
        return NULL;
    }

    PUT(HDRP(bp), PACK(size, 0));           /* Free block header */
    PUT(FTRP(bp), PACK(size, 0));           /* Free block footer */
    PUT(PRED(bp), 0);                       /* Free block predecessor */
    PUT(SUCC(bp), 0);                       /* Free block successor */
    
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));   /* New epilogue header */

    return coalesce(bp);
}

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    if((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1) {
        return -1;
    }
    PUT(heap_listp, 0);                             /* Alignment padding */
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1));    /* Prologue header */
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1));    /* Prologue footer */
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));        /* Epilogue header */
    root = heap_listp;
    heap_listp += (2*WSIZE);

    if(extend_heap(CHUNKSIZE/WSIZE) == NULL) {
        return -1;
    }
    return 0;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize;       /* Adjusted block size */
    size_t extendsize;  /* Amount to extend heap if no fit */
    char *bp;

    if(size == 0) {
        return NULL;
    }

    if(size <= DSIZE) {
        asize = 2*DSIZE;
    } else {
        asize = DSIZE * ((size + DSIZE + (DSIZE-1)) / DSIZE);
    }

    if((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    extendsize = MAX(asize, CHUNKSIZE);
    if((bp = extend_heap(extendsize/WSIZE)) == NULL) {
        return NULL;
    }
    place(bp, asize);
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(PRED(bp), 0);
    PUT(SUCC(bp), 0);
    coalesce(bp);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;
    
    newptr = mm_malloc(size);
    if (newptr == NULL) {
        return NULL;  
    }
    copySize = GET_SIZE(HDRP(oldptr));
    if (size < copySize) {
        copySize = size;
    }
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}