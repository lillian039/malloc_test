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
#define MAXLIST 20
#define MINSIZE 48

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

static char *heap_listp,*epilogue, *free_head[MAXLIST];

static inline int get_head(size_t size){
    int i = 0;
    for( ; i < MAXLIST; i++)if(size <= (size_t)(MINSIZE << i))return i;
    return MAXLIST-1;
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
    epilogue = NEXT_BLKP(bp);
    //coalesce if the previous block was free
    return coalesce(bp);
}

/*
 * mm_init - Called when a new trace starts.
 */
// prologue block 序言块，只有头部,脚部,pred succ 组成，大小为 6 word
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
    epilogue = heap_listp + (8 * WSIZE);
    for(int i = 0; i < MAXLIST; i++)free_head[i] = 0;
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
    for(int i = head + 1; i < MAXLIST; i++){
        bp = free_head[i];
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
        //mm_checkheap(0);
    }
    return bp;
}

/*
 * free - We don't know how to free a block.  So we ignore this call.
 *      Computers have big memories; surely it won't be a problem.
 */
void free(void *ptr){
    if (ptr < mem_heap_lo() || ptr > mem_heap_hi()) return;
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
/*
const I use: 
ALIGNMENT 8
WSIZE 4
DSIZE 8
INFORSIZE 24
CHUNKSIZE (1<<8) // extend heap by this size
MAXLIST 20
MINSIZE 48
*/
void mm_checkheap(int verbose){
    if(verbose == 0){
        printf("prologue: header: %lu footer: %lu alloc: %d size: %u \n",
        (size_t)HDRP(heap_listp),(size_t)FTRP(heap_listp),GET_ALLOC(HDRP(heap_listp)), GET_SIZE(HDRP(heap_listp)));
        printf("epilogue: header: %lu alloc: %d size: %u\n",(size_t)HDRP(epilogue),GET_ALLOC(HDRP(epilogue)),GET_SIZE(HDRP(epilogue)));

    }
    else if(verbose == 1){ //traverse free list
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
    else if(verbose == 3){ //check boundry
        //puts("check boundry");
        char* bp = heap_listp;
        size_t size = GET_SIZE(HDRP(bp));
        while(size > 0){
            if((size_t)bp < (size_t)mem_heap_lo() || (size_t)bp > (size_t)mem_heap_hi()){
                puts("illegal ptr");
                exit(0);
            }
            bp = NEXT_BLKP(bp);
            size = GET_SIZE(HDRP(bp));
        }
    }
    else if(verbose == 4){ //check header and footer
        //puts("check header and footer");
        char* bp = heap_listp;
        size_t size_h = GET_SIZE(HDRP(bp));
        size_t size_f = GET_SIZE(FTRP(bp));
        size_t alloc_h = GET_ALLOC(HDRP(bp));
        size_t alloc_f = GET_ALLOC(FTRP(bp));
        while(size_h > 0){
            if(size_h != size_f){
                puts("size unmatch");
                exit(0);
            }
            if(alloc_f != alloc_h){
                puts("alloc unmatch");
                exit(0);
            }
            bp = NEXT_BLKP(bp);
            size_h = GET_SIZE(HDRP(bp));
            size_f = GET_SIZE(FTRP(bp));
            alloc_h = GET_ALLOC(HDRP(bp));
            alloc_f = GET_ALLOC(FTRP(bp));
        }
    }
    else if(verbose == 5){//check if there is two adjacent free block
        //puts("check free block");
        char* prev = heap_listp;
        char* now = NEXT_BLKP(heap_listp);
        size_t size = GET_SIZE(HDRP(now));
        while(size > 0){
            if(!GET_ALLOC(HDRP(prev)) && !GET_ALLOC(HDRP(now))){
                puts("two adjacent free block!");
                exit(0);
            }
            prev = NEXT_BLKP(prev);
            now = NEXT_BLKP(now);
            size = GET_SIZE(HDRP(now));
        }
    }
    else if(verbose == 6){ //check pred and succ
        for(int i = 0; i < MAXLIST; i++){
            if(free_head[i] == 0)return;
            char *prev = free_head[i];
            char *now = (char *)NEXT_LISTP(prev);
            while(now != 0){
                size_t succ = NEXT_LISTP(prev);
                size_t pred = PREV_LISTP(now);
                if(succ != (size_t)now || pred != (size_t)prev){
                    puts("pred succ not match!");
                    exit(0);
                }
                now = (char *)NEXT_LISTP(now);
                prev = (char *)NEXT_LISTP(prev);
            }
        }
    }
    else if(verbose == 7){//check if ptr in free list are in boundry
        for(int i = 0; i < MAXLIST; i++){
            char *bp = free_head[i];
            while(bp != 0){
                if((size_t)bp < (size_t)mem_heap_lo() || (size_t)bp > (size_t)mem_heap_hi()){
                    puts("illegal ptr");
                    exit(0);
                }
                bp = (char *)NEXT_LISTP(bp);
            }
        }
    }
    else if(verbose == 8){
        for(int i = 0; i < MAXLIST; i++){
            char *bp = free_head[i];
            while(bp != 0){
                size_t size = GET_SIZE(HDRP(bp));
                if(size > (size_t)(MINSIZE<< i) || (i > 0 && size <= (size_t)(MINSIZE << (i-1)))){
                    puts("size unmatch");
                    exit(0);
                }
                bp = (char *)NEXT_LISTP(bp);
            }
        }
    }
}
