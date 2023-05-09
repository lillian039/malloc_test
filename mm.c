/*
    Use explicit allocator, LIFO strategy and segregated fit

    The structure of my empty block:

    === header (4 byte) === (size | alloc_prev | alloc) alloc = 0
    === succ   (8 byte) === the location of next ptr on free list
    === prev   (8 byte) === the location of prev ptr on free list
    ===      block      === 
    === footer (4 byte) === (size | alloc) alloc = 0
        

    The structure of my allocated block:

    === header (4 byte) === (size | alloc_prev | alloc) alloc = 1
    ===       bp        === 
    ===      block      ===

    The structure of free list:

    I have MAXLIST size of free_list
    The free_list[i] collect all free block (48 << (i-1)) <= size <= (48 << i)
    if free_list[i] is empty, then free_list[i] = 0

    The operation of free_list:
    (1) get_head (size_t size): get the ptr's free list match it size
    (2) remove_bp (void *bp): remove bp from the free list it size match
    (3) put_bp (void *bp): put bp on the free list it size match

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

#define WSIZE 4 // word + footer/header size
#define DSIZE 8 // double word size
#define INFORSIZE 16
#define CHUNKSIZE (1<<8) // extend heap by this size
#define MAXLIST 20
#define MINSIZE 24

#define MAX(x, y) (x > y ? x : y)
//pack size and allocated bit into a word
#define PACK(size, alloc) ((size) | (alloc))

#define GET(p) ((p) ? *(unsigned int *)(p) : 0)
#define PUT(p, val) ((p) ? *(unsigned int *)(p) = (val) : 0)

//if bp == 0 then do nothing
#define PUT_P(p, val) ((p) ? (*(unsigned int *)(p) = val ? ((unsigned int)((char *)(val) - heap_listp)) : 0) : 0)
#define GET_P(p) ((p)? (GET(p) ? (GET(p) + heap_listp) : 0) : 0)

#define GET_SIZE(p) (GET(p) & ~0x7) //size of block
#define GET_ALLOC(p) (GET(p) & 0x1) //whether alloc
#define GET_PREV_ALLOC(p) (GET(p) & 0x2)


#define HDRP(bp) ((char *)bp - WSIZE)
#define FTRP(bp) ((char *)bp + GET_SIZE(HDRP(bp)) - DSIZE)

//if bp == 0 then do nothing
#define PRED(bp) ((bp) ? (char *)(bp) : 0)
#define SUCC(bp) ((bp) ? (char *)(bp) + WSIZE : 0)

#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE((HDRP(bp) - WSIZE)))

//if bp == 0 then do nothing
#define NEXT_LISTP(bp) ((bp) ? GET_P(SUCC(bp)) : 0)
#define PREV_LISTP(bp) ((bp) ? GET_P(PRED(bp)) : 0)

static char *heap_listp,*epilogue, *free_head[MAXLIST];

/*
    use size to determine which free_list it should be in
*/
static inline int get_head(size_t size){
    int i = 0;
    for( ; i < MAXLIST; i++)if(size <= (size_t)(MINSIZE << i))return i;
    return MAXLIST-1;
}
/*
    remove ptr from the free_list match it size
*/
static inline void remove_bp(void *bp){
    int head = get_head(GET_SIZE(HDRP(bp)));
    PUT_P(SUCC(PREV_LISTP(bp)),NEXT_LISTP(bp));
    PUT_P(PRED(NEXT_LISTP(bp)),PREV_LISTP(bp));
    if(bp == free_head[head])free_head[head] = (char *)NEXT_LISTP(free_head[head]);
}

/*  
    put ptr on the free_list match it size
    Always put it in head
*/
static inline void put_bp(void *bp){
    int head = get_head(GET_SIZE(HDRP(bp)));
    PUT_P(SUCC(bp),free_head[head]);
    PUT_P(PRED(bp),0);
    PUT_P(PRED(free_head[head]),bp);
    free_head[head] = bp;
}

/*
    find if bp can coalesce with its prev block and next block
    If it prev or next can coalesce, then remove it from free_list  
    coalesce them, and then put it back into free_list
*/
static inline void *coalesce(void *bp){
    size_t prev_alloc = GET_PREV_ALLOC(HDRP(bp));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if(prev_alloc && next_alloc){
        // do nothing
    }
    else if(prev_alloc && !next_alloc){//next 为空
        remove_bp(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 2));
        PUT(FTRP(bp), PACK(size, 2));
    }
    else if(!prev_alloc && next_alloc){//prev 为空
        remove_bp(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));

        bp = PREV_BLKP(bp);
        PUT(HDRP(bp), PACK(size, 2));
        PUT(FTRP(bp), PACK(size, 2));  
        
    }
    else{
        remove_bp(NEXT_BLKP(bp));
        remove_bp(PREV_BLKP(bp));

        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));//next prev 均为空
        bp = PREV_BLKP(bp);

        PUT(HDRP(bp), PACK(size, 2));
        PUT(FTRP(bp), PACK(size, 2));
    }
    put_bp(bp);
    return bp;
}

/*
    extend heap by size words
    set new block's size and let it be free block
    update new epilogue
    try to coalesce it with existed free block
*/
static inline void *extend_heap(size_t words){
    char *bp;
    size_t size;

    // allocate an even number of words to maintain alignment
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if((long)(bp = mem_sbrk(size)) == -1)return NULL;
    // initialize free block header/footer and the epilogue header

    PUT(HDRP(bp), PACK(size, GET_PREV_ALLOC(HDRP(bp))));
    PUT(FTRP(bp), PACK(size, GET_PREV_ALLOC(HDRP(bp))));

    PUT(HDRP(NEXT_BLKP(bp)),PACK(0, 1));
    epilogue = NEXT_BLKP(bp);

    return coalesce(bp);
}

/*
    mm_init - Called when a new trace starts.
    prologue block, with header, footer, pred, succ, alloc = 1, with total size 6 words
    epilogue block, only with header, size 0, alloca = 1
    initialize free_head[i] into empty part
*/
int mm_init(void)
{
    heap_listp = mem_sbrk(6 * WSIZE);
    PUT(heap_listp, 0);
    PUT(heap_listp + (1 * WSIZE), PACK(INFORSIZE, 3)); // prologue header
    
    heap_listp += 2 * WSIZE;
    PUT_P(heap_listp, 0); // prologue pred
    PUT_P(heap_listp + WSIZE, 0); // prologue succ
    PUT(heap_listp + (2 * WSIZE), PACK(INFORSIZE, 3)); // prologue footer
    PUT(heap_listp + (3 * WSIZE), PACK(0,3));// epilogue header

    epilogue = heap_listp + (3 * WSIZE);
    for(int i = 0; i < MAXLIST; i++)free_head[i] = 0;
    return 0;
}

/*
    place ptr of asize in bp
    If bp's remain is already less larger the size we need to put header,footer,pred_ptr,succ_ptr,
    then return the whole bp
    Otherwise, seperate bp in two part, one return for asize, and the remained part stay free and put back
    into free list.
*/
static inline void place(void *bp, size_t asize){
    size_t size = GET_SIZE(HDRP(bp));
    size_t remain_size = size - asize;
    if(remain_size <= INFORSIZE){ 
        remove_bp(bp);
        PUT(HDRP(bp), PACK(size, 3));
        PUT(FTRP(bp), PACK(size, 3));
        size_t next_size = GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(NEXT_BLKP(bp)),PACK(next_size, 3));
    }
    else{
        remove_bp(bp);
        PUT(HDRP(bp), PACK(asize, 3));
        PUT(FTRP(bp), PACK(asize, 3));
        void *remain_bp = NEXT_BLKP(bp);
        PUT(HDRP(remain_bp), PACK(remain_size, 2));
        PUT(FTRP(remain_bp), PACK(remain_size, 2));
        put_bp(remain_bp);
    }
}

/*
    find the block can put asize
    first find free list with (48 << (i-1)) <= size <= (48 << i)
    if there no match block, then find i+1 free list
    if i+1 free list is empty, then keep finding i+2
    if all larger free list is empty, it means there is no match free block, return null
*/
static inline void *find_fit(size_t asize){
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
    return NULL;
}

/*
    malloc - Allocate a block by incrementing the brk pointer.
    Add header and footer to size, and make the final size larger than the total size of footer,header,pred_ptr,succ_ptr
    Always allocate a block whose size is a multiple of the alignment.
    If we successfully find the fit free block, then place asize in bp.
    Otherwise, choose to extend heap, then we get the free block we want
 */
void *malloc(size_t size)
{
    size_t asize;
    size_t extendsize;
    char *bp;
    //ignore spurious request
    if(size == 0)return NULL;
    
    //adjust block size
    asize = ALIGN(MAX(size + WSIZE ,INFORSIZE));
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
    Firstly check if ptr is in heap boundry.
    Update the ptr's station to free
    Try to coalesce it with free block adjacent to it
 */
void free(void *ptr){
    if (ptr < mem_heap_lo() || ptr > mem_heap_hi()) return;

    size_t size = GET_SIZE(HDRP(ptr));
    size_t prev_alloc = GET_PREV_ALLOC(HDRP(ptr));

    PUT(HDRP(ptr), PACK(size, prev_alloc));
    PUT(FTRP(ptr), PACK(size, prev_alloc));
    
    size_t next_size = GET_SIZE(HDRP(NEXT_BLKP(ptr)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(ptr)));
    PUT(HDRP(NEXT_BLKP(ptr)),PACK(next_size,next_alloc));
    coalesce(ptr);
}

/*
    realloc - Change the size of the block by mallocing a new block,
    copying its data, and freeing the old block. 
 */
void *realloc(void *oldptr, size_t size)
{
    size_t oldsize;
    void *newptr;

    /* If size == 0 then this is just free, and we return NULL. */
    if(size == 0) {
        free(oldptr);
        return 0;
    }

    /* If oldptr is NULL, then this is just malloc. */
    if(oldptr == NULL)return malloc(size);
    newptr = malloc(size);

    /* If realloc() fails the original block is left untouched  */
    if(!newptr)return 0;

    /* Copy the old data. */
    oldsize = *SIZE_PTR(oldptr);
    if(size < oldsize) oldsize = size;
    memcpy(newptr, oldptr, oldsize);

    /* Free the old block. */
    free(oldptr);
    return newptr;
}

/*
    calloc - Allocate the block and set it to zero.
 */
void *calloc (size_t nmemb, size_t size)
{
    size_t bytes = nmemb * size;
    void *newptr;
    newptr = malloc(bytes);
    memset(newptr, 0, bytes);
    return newptr;
}

/*
    const I use: 
    ALIGNMENT 8
    WSIZE 4
    DSIZE 8
    INFORSIZE 16
    CHUNKSIZE (1<<8)
    MAXLIST 20
    MINSIZE 48

    check heap
    Each verbose is one kind of checking method
*/
void mm_checkheap(int verbose){
    // check prologue and epilogue
    if(verbose == 0){
        printf("prologue: header: %lu footer: %lu alloc: %d size: %u \n",
        (size_t)HDRP(heap_listp),(size_t)FTRP(heap_listp),GET_ALLOC(HDRP(heap_listp)), GET_SIZE(HDRP(heap_listp)));
        printf("epilogue: header: %lu alloc: %d size: %u\n",(size_t)HDRP(epilogue),GET_ALLOC(HDRP(epilogue)),GET_SIZE(HDRP(epilogue)));

    }
    // traverse free list
    else if(verbose == 1){ 
        for(int i = 0; i < MAXLIST; i++)
        {
        printf("free list: %d \n",i);
        char* bp = free_head[i];
        int cnt = 0;
        size_t size;
        while(bp != 0){
            cnt++;
            size = GET_SIZE(HDRP(bp));
            printf("block:%d address: %ld size: %lu next_list: %lu prev_list: %lu next_block: %lu\n",
            cnt,(size_t)bp,size,(size_t)NEXT_LISTP(bp), (size_t)PREV_LISTP(bp), (size_t)NEXT_BLKP(bp));
            bp = (char *)NEXT_LISTP(bp);
        }
        }
        puts("finish check free list");
    }
    // traverse whole heap list
    else if(verbose == 2){ 
        char* bp = heap_listp;
        int alloc;
        size_t size = GET_SIZE(HDRP(bp));
        printf("heap list: %ld size: %lu\n",(size_t)bp,size);
        int cnt = 0;
        while(size > 0){
            cnt++;
            bp = NEXT_BLKP(bp);
            size = GET_SIZE(HDRP(bp));
            if(size == 0)break;
            alloc = GET_ALLOC(HDRP(bp));
            int prev_alloc = GET_PREV_ALLOC(HDRP(bp));
            printf("block:%d address: %ld size: %lu next_list: %lu prev_list: %lu next_block: %lu prev_alloc : %d alloc :%d\n",
            cnt,(size_t)bp,size,(size_t)NEXT_LISTP(bp), (size_t)PREV_LISTP(bp), (size_t)NEXT_BLKP(bp),prev_alloc,alloc);
        }

        puts("finish check heap list");
    }
    // check whether all ptr in heap list are in heap boundry
    else if(verbose == 3){ 
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
    // check all ptr in heap list's header and footer's size and allcate station
    else if(verbose == 4){ 
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
    // check if there is two adjacent free block
    else if(verbose == 5){
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
    // check all ptr in free list's pred and succ
    else if(verbose == 6){ 
        for(int i = 0; i < MAXLIST; i++){
            if(free_head[i] == 0)return;
            char *prev = free_head[i];
            char *now = (char *)NEXT_LISTP(prev);
            while(now != 0){
                char * succ = NEXT_LISTP(prev);
                char * pred = PREV_LISTP(now);
                if(succ != now || pred != prev){
                    puts("pred succ not match!");
                    exit(0);
                }
                now = (char *)NEXT_LISTP(now);
                prev = (char *)NEXT_LISTP(prev);
            }
        }
    }
    // check if all ptr in free list are in boundry
    else if(verbose == 7){
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
    // check if ptr are in the correct free list match its size
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
    // iterating over each block and traversing the free linked list through the pointer to see if they match
    else if(verbose == 9){
        int free_cnt = 0;
        for (size_t id = 0; id < MAXLIST; id++){
            char *bp = free_head[id];
            while(bp){
                free_cnt++;
                if (GET_ALLOC(HDRP(bp))){
                    printf("block: %lu are allocated, but is in the free list\n", (size_t)(bp));
                    exit(0);
                }
                bp = (char *)NEXT_LISTP(bp);
            }
        }
        char *bp = heap_listp;
        while(GET_SIZE(HDRP(bp))){
            if (!GET_ALLOC(HDRP(bp))) free_cnt--;
            bp = NEXT_BLKP(bp);
        }
        if (free_cnt){
            puts("free block size different in free list and total list");
            exit(0);
        }
    }
}
