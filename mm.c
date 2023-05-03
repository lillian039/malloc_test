/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 *
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  Blocks are never coalesced or reused.  The size of
 * a block is found at the first aligned word before the block (we need
 * it for realloc).
 *
 * This code is correct and blazingly fast, but very bad usage-wise since
 * it never frees anything.
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "mm.h"
#include "memlib.h"

/* If you want debugging output, use the following macro.  When you hand
 * in, remove the #define DEBUG line. */
#define DEBUG
#ifdef DEBUG
# define dbg_printf(...) printf(__VA_ARGS__)
#else
# define dbg_printf(...)
#endif


/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define SIZE_PTR(p)  ((size_t*)(((char*)(p)) - SIZE_T_SIZE))
//todo as follow

#define WSIZE 4 // word + footer/header size
#define DSIZE 8 // double word size
#define CHUNKSIZE (1<<12) // extend heap by this size

#define MAX(x, y) (x > y ? x : y)
//pack size and allocated bit into a word
#define PACK(size, alloc) ((size) | (alloc))

#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))
#define GET_SIZE(p) (GET(p) & ~0x7) //size of block
#define GET_ALLOC(p) (GET(p) & 0x1) //whether alloc

//I think bp is the ptr exactly after header
//I think size include context and footer and header
#define HDRP(bp) ((char *)bp - WSIZE) //header ptr
#define FTRP(bp) ((char *)bp + GET_SIZE(HDRP(bp)) - DSIZE) //footer ptr

#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

static char *heap_listp;

static void *coalesce(void *bp){
    //puts("coalesce");
    //printf("%ld\n",GET(bp));
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));

    size_t size = GET_SIZE(HDRP(bp));

    if(prev_alloc && next_alloc){
        return bp;
    }
    else if(prev_alloc && !next_alloc){//next 为空
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    else if(!prev_alloc && next_alloc){//prev 为空
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size,0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    else{
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));//next prev 均为空
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }    
    //puts("finish coalesce");
    return bp;
  
}

static void *extend_heap(size_t words){
    char *bp;
    size_t size;

    // allocate an even number of words to maintain alignment
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if((long)(bp = mem_sbrk(size)) == -1)return NULL;
    // initialize free block header/footer and the epilogue header
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)),PACK(0, 1));

    //coalesce if the previous block was free
    return coalesce(bp);
}

/*
 * mm_init - Called when a new trace starts.
 */
// prologue block 序言块，只有头部与脚部组成，大小为 1 word
// epilogue block 结尾块 大小为 0 的已分配块，仅有头组成
int mm_init(void)
{
    //puts("mm_init");
    heap_listp = mem_sbrk(4 * WSIZE);// 初始化头，只含 header footer
    PUT(heap_listp, 0);
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); // prologue header
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); // prologue footer
    PUT(heap_listp + (3 * WSIZE), PACK(0,1));// epilogue header
    heap_listp += 2 * WSIZE;
    if(extend_heap(CHUNKSIZE/WSIZE) == NULL)return -1;
    //puts("finish mm_init");
    //mm_checkheap(0);
    return 0;
}

static void place(void *bp, size_t asize){
    size_t size = GET_SIZE(HDRP(bp));
    size_t remain_size = size - asize;
    if(remain_size <= DSIZE){
        PUT(HDRP(bp), PACK(size, 1));
        PUT(FTRP(bp), PACK(size, 1));
        return;
    }
    PUT(HDRP(bp), PACK(asize, 1));
    PUT(FTRP(bp), PACK(asize, 1));
    void *remain_bp = NEXT_BLKP(bp);
    PUT(HDRP(remain_bp), PACK(remain_size, 0));
    PUT(FTRP(remain_bp), PACK(remain_size, 0));
}

static void *find_fit(size_t asize){
    //puts("find fit");
    char* bp = heap_listp;
    size_t size = GET_SIZE(HDRP(bp));
    while(size > 0){
        if(size >= asize && !GET_ALLOC(HDRP(bp)))return bp;
        bp = NEXT_BLKP(bp);
        size = GET_SIZE(HDRP(bp));
    }
    return NULL;
}

/*
 * malloc - Allocate a block by incrementing the brk pointer.
 *      Always allocate a block whose size is a multiple of the alignment.
 */
void *malloc(size_t size)
{
    size_t asize;
    size_t extendsize;
    char *bp;

    //ignore spurious request
    if(size == 0)return NULL;
    
    //adjust block size
    if(size <= DSIZE)asize = 2 * DSIZE;
    else asize = DSIZE * ((size + 2 * DSIZE - 1) / DSIZE);//add DSIZE 上取整

    //printf("malloc size: %d\n",asize);

    if((bp = find_fit(asize)) != NULL){
        place(bp, asize);
    }
    else {
    //No fit found. Get more memory and place the block
    extendsize = MAX(asize, CHUNKSIZE);
    if((bp = extend_heap(extendsize / WSIZE)) == NULL)return NULL;
    place(bp, asize);
    }

    //printf("malloc bp: %ld\n",bp);
    //mm_checkheap(0);
    //puts("finish malloc");
    return bp;
}



/*
 * free - We don't know how to free a block.  So we ignore this call.
 *      Computers have big memories; surely it won't be a problem.
 */
void free(void *ptr){
    //printf("free: %ld\n",ptr);

    if (ptr < mem_heap_lo() || ptr > mem_heap_hi()) return;
    if((long)ptr == 0)puts("?");
    /*Get gcc to be quiet */
    size_t size = GET_SIZE(HDRP(ptr));

    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    coalesce(ptr);
    //mm_checkheap(0);
    //puts("finish free");
}

/*
 * realloc - Change the size of the block by mallocing a new block,
 *      copying its data, and freeing the old block.  I'm too lazy
 *      to do better.
 */
void *realloc(void *oldptr, size_t size)
{
    //puts("realloc");
    size_t oldsize;
    void *newptr;

    /* If size == 0 then this is just free, and we return NULL. */
    if(size == 0) {
        free(oldptr);
        return 0;
    }

    /* If oldptr is NULL, then this is just malloc. */
    if(oldptr == NULL) {
        return malloc(size);
    }

    newptr = malloc(size);

    /* If realloc() fails the original block is left untouched  */
    if(!newptr) {
        return 0;
    }

    /* Copy the old data. */
    oldsize = *SIZE_PTR(oldptr);
    if(size < oldsize) oldsize = size;
    memcpy(newptr, oldptr, oldsize);

    /* Free the old block. */
    free(oldptr);
    //puts("finish realloc");

    return newptr;
}

/*
 * calloc - Allocate the block and set it to zero.
 */
void *calloc (size_t nmemb, size_t size)
{
    //puts("calloc");

    size_t bytes = nmemb * size;
    void *newptr;

    newptr = malloc(bytes);
    memset(newptr, 0, bytes);

    //puts("finish calloc");

    return newptr;
}

/*
 * mm_checkheap - There are no bugs in my code, so I don't need to check,
 *      so nah!
 */
void mm_checkheap(int verbose){
        /*Get gcc to be quiet. */
    char* bp = heap_listp;
    size_t size = GET_SIZE(HDRP(bp));
    int alloccc;
    printf("heap_list: %ld size: %u\n",bp,size);
    int cnt = 0;
    while(size > 0){
        cnt++;
        bp = NEXT_BLKP(bp);
        size = GET_SIZE(HDRP(bp));
        alloccc = GET_ALLOC(HDRP(bp));
        printf("block:%d address: %ld size: %lu alloc: %d\n",cnt,bp,size,alloccc);
    }
}
