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

//

#define WSIZE 4 // word + footer/header size
#define DSIZE 8 // double word size
#define INFORSIZE 24
#define CHUNKSIZE (1<<8) // extend heap by this size

#define MAX(x, y) (x > y ? x : y)
//pack size and allocated bit into a word
#define PACK(size, alloc) ((size) | (alloc))

#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

#define PUT_P(p, val) ((p) ? *(size_t *)(p) = (size_t)(val) : 0)
#define GET_P(p) ((p)? *(size_t *)(p) : 0)

#define GET_SIZE(p) (GET(p) & ~0x7) //size of block
#define GET_ALLOC(p) (GET(p) & 0x1) //whether alloc


#define HDRP(bp) ((char *)bp - WSIZE)
#define FTRP(bp) ((char *)bp + GET_SIZE(HDRP(bp)) - DSIZE)

#define PRED(bp) ((bp) ? (char *)(bp) : 0)
#define SUCC(bp) ((bp) ? (char *)(bp) + DSIZE : 0)

#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE((HDRP(bp) - WSIZE)))

#define NEXT_LISTP(bp) ((bp) ? GET_P(SUCC(bp)) : 0)
#define PREV_LISTP(bp) ((bp) ? GET_P(PRED(bp)) : 0)

static char *heap_listp, *free_head[8];

static inline int get_head(size_t size){
   // size_t size = GET_SIZE(HDRP(bp));
    if(size <= (1 << 4))return 0;
    else if(size <= (1 << 6))return 1;
    else if(size <= (1 << 8))return 2;
    else if(size <= (1 << 10))return 3;
    else if(size <= (1 << 12))return 4;
    else if(size <= (1 << 14))return 5;
    else if(size <= (1 << 16))return 6;
    else return 7;

}
static inline void remove_bp(void *bp){
    int head = get_head(GET_SIZE(HDRP(bp)));
    PUT_P(SUCC(PREV_LISTP(bp)),NEXT_LISTP(bp));
    PUT_P(PRED(NEXT_LISTP(bp)),PREV_LISTP(bp));
    if(bp == free_head[head])free_head[head] = (char *)NEXT_LISTP(free_head[head]);
}

static inline void put_bp(void *bp){
    int head = get_head(GET_SIZE(HDRP(bp)));
    PUT_P(SUCC(bp),free_head[head]);
    PUT_P(PRED(bp),0);
    PUT_P(PRED(free_head[head]),bp);
    free_head[head] = bp;
}

static inline void *coalesce(void *bp){
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));

    size_t size = GET_SIZE(HDRP(bp));

    if(prev_alloc && next_alloc){
        // do nothing
    }
    else if(prev_alloc && !next_alloc){//next 为空
        remove_bp(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    else if(!prev_alloc && next_alloc){//prev 为空
        remove_bp(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size,0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    else{
        remove_bp(NEXT_BLKP(bp));
        remove_bp(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));//next prev 均为空
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    put_bp(bp);
    return bp;
  
}

static inline void *extend_heap(size_t words){
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
    heap_listp = mem_sbrk(8 * WSIZE);// 初始化头，只含 header footer pred succ 尾 只含有 header pred
    PUT(heap_listp, 0);
    PUT(heap_listp + (1 * WSIZE), PACK(INFORSIZE, 1)); // prologue header
    PUT_P(heap_listp + (2 * WSIZE), 0); // prologue pred
    PUT_P(heap_listp + (4 * WSIZE), 0); // prologue succ
    PUT(heap_listp + (6 * WSIZE), PACK(INFORSIZE, 1)); // prologue footer

    PUT(heap_listp + (7 * WSIZE), PACK(0,1));// epilogue header
    heap_listp += 2 * WSIZE;
    for(int i = 0; i < 8; i++)free_head[i] = 0;
    if(extend_heap(CHUNKSIZE/WSIZE) == NULL)return -1;

    return 0;
}

static inline void place(void *bp, size_t asize){
    size_t size = GET_SIZE(HDRP(bp));
    size_t remain_size = size - asize;
    if(remain_size <= INFORSIZE){ 
        remove_bp(bp);
        PUT(HDRP(bp), PACK(size, 1));
        PUT(FTRP(bp), PACK(size, 1));
    }
    else{
        remove_bp(bp);
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        void *remain_bp = NEXT_BLKP(bp);
        PUT(HDRP(remain_bp), PACK(remain_size, 0));
        PUT(FTRP(remain_bp), PACK(remain_size, 0));
        put_bp(remain_bp);
    }
}

static inline void *find_fit(size_t asize){
    //puts("find fit");
    int head = get_head(asize);
    char* bp = free_head[head];
    size_t size;
    while(bp != 0){
        size = GET_SIZE(HDRP(bp));
        if(size >= asize)return bp;
        bp = (char *)NEXT_LISTP(bp);
    }
    for(int i = head + 1; i < 8; i++){
        char* bp = free_head[i];
        if (bp != 0)return bp;
    }
    // puts("finish find fit");
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
    asize = ALIGN(MAX(size + DSIZE ,INFORSIZE));
    if((bp = find_fit(asize)) != NULL)place(bp, asize);
    else {
        //No fit found. Get more memory and place the block
        extendsize = MAX(asize, CHUNKSIZE);
        if((bp = extend_heap(extendsize / WSIZE)) == NULL)return NULL;
        place(bp, asize);
    }
    return bp;
}

/*
 * free - We don't know how to free a block.  So we ignore this call.
 *      Computers have big memories; surely it won't be a problem.
 */
void free(void *ptr){
    //puts("free");
    if (ptr < mem_heap_lo() || ptr > mem_heap_hi()) return;
    // if(GET_ALLOC(HDRP(ptr)) == 0)return;

    /*Get gcc to be quiet */
    size_t size = GET_SIZE(HDRP(ptr));

    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    coalesce(ptr);
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
    if(verbose == 1){ //traverse free list
        printf("free list:\n");
        char* bp = free_head[0];
        int cnt = 0;
        size_t size;
        while(bp != 0){
            cnt++;
            size = GET_SIZE(HDRP(bp));
            printf("block:%d address: %ld size: %lu next_list: %lu prev_list: %lu next_block: %lu prev_block : %lu\n",
            cnt,(size_t)bp,size,NEXT_LISTP(bp), PREV_LISTP(bp), (size_t)NEXT_BLKP(bp),(size_t)PREV_BLKP(bp));
            bp = (char *)NEXT_LISTP(bp);
        }
        puts("finish check free list");
    }
    else if(verbose == 2){ //traverse whole list
        char* bp = heap_listp;
        int alloc;
        size_t size = GET_SIZE(HDRP(bp));
        printf("heap list: %ld size: %lu\n",(size_t)bp,size);
        int cnt = 0;
        while(size > 0){
            cnt++;
            bp = NEXT_BLKP(bp);
            size = GET_SIZE(HDRP(bp));
            alloc = GET_ALLOC(HDRP(bp));
            printf("block:%d address: %ld size: %lu next_list: %lu prev_list: %lu next_block: %lu prev_block : %lu alloc :%d\n",
            cnt,(size_t)bp,size,NEXT_LISTP(bp), PREV_LISTP(bp), (size_t)NEXT_BLKP(bp),(size_t)PREV_BLKP(bp),alloc);
        }
        puts("finish check heap list");
    }
}
