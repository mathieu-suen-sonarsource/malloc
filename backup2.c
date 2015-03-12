
#include <stdio.h>
#include <unistd.h>
#include <string.h>
#include <stdlib.h>
#include <assert.h>
#include "mm.h"
#include "memlib.h"

extern int verbose;
/* Team structure */
team_t team = {
    "implicit first fit", 
    "Telma Gudbjorg",
    "droh",
    "", "",
    "", ""
}; 


/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* $begin mallocmacros */
/* Basic constants and macros */
#define WSIZE       4       /* word size (bytes) */  
#define DSIZE       8       /* doubleword size (bytes) */
#define CHUNKSIZE  (1<<12)  /* initial heap size (bytes) */
#define OVERHEAD    8       /* overhead of header and footer (bytes) */

#define MAX(x, y) ((x) > (y)? (x) : (y))  

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p)       (*(size_t *)(p))
#define PUT(p, val)  (*(size_t *)(p) = (val))  

#define ALLOCATED(p) (*(unsigned int *)(p) = GET(p) | 0x2)
#define DEALLOCATED(p) (*(unsigned int *)(p) = GET(p) & ~0x2)

/* (which is about 54/100).* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((char *)(bp) - WSIZE)  
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))
/* $end mallocmacros */

#define BlockSize ALIGN(sizeof(BlockHeader) + WSIZE)
// minnimum size of block (header, footer, next, prev)                                                            

#ifdef DEBUG
#define CHECKHEAP(verbose) printf("%s\n", _func_); mm_checkheap(verbose);
#endif

typedef struct Block BlockHeader;

struct Block{
  size_t size_alloc;
  BlockHeader *next;
  BlockHeader *prev;
};

static BlockHeader *freeListRoot; // points to the root of the freeList   


/* Global variables */
static char *heap_listp;  /* pointer to first block */  

/* function prototypes for internal helper routines */
static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static BlockHeader *find_fit(size_t asize);
static void *coalesce(void *bp);
static void printblock(void *bp); 
static void checkblock(void *bp);
static void insert(BlockHeader *ptr, size_t size);
static void removeBlock(BlockHeader *ptr);
/* 
 * mm_init - Initialize the memory manager 
 */
/* $begin mminit */
int mm_init(void) 
{
  // mm_checkheap(verbose);
    BlockHeader *p = mem_sbrk(BlockSize);
    p->size_alloc = 1;
    p->next = p;
    p->prev = p;
    /* create the initial empty heap */
    if ((heap_listp = mem_sbrk(4*WSIZE)) == NULL)
        return -1;
    PUT(heap_listp, 0);                        /* alignment padding */
    PUT(heap_listp+WSIZE, PACK(OVERHEAD, 1));  /* prologue header */ 
    PUT(heap_listp+DSIZE, PACK(OVERHEAD, 1));  /* prologue footer */ 
    PUT(heap_listp+WSIZE+DSIZE, PACK(0, 1));   /* epilogue header */
    heap_listp += DSIZE;
   
    mm_checkheap(verbose);
    freeListRoot->size_alloc = 1;
    freeListRoot->next = NULL;
    freeListRoot->prev = NULL;
    
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
      return -1;
    return 0;
}
/* $end mminit */

/* 
 * mm_malloc - Allocate a block with at least size bytes of payload 
 */
/* $begin mmmalloc */
void *mm_malloc(size_t size) 
{    
  void *result;
  
    size_t asize;      /* adjusted block size */
    size_t extendsize; /* amount to extend heap if no fit */
    

    /* Ignore spurious requests */
    if (size <= 0)
        return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    asize = ALIGN(BlockSize + size);
    
    //mm_checkheap(verbose);
    /* Search the free list for a fit */
    BlockHeader *bp = find_fit(asize);
    
    /* if(freeListRoot == NULL){ //if freeList contains no free blocks we want to expand heap                       
      extendsize = MAX(asize, CHUNKSIZE);
      bp = extend_heap(extendsize);
      //here we wanna add this block to freelist;

    }*/
    if(bp == NULL){
      extendsize = MAX(asize, CHUNKSIZE);
      //mm_checkheap(verbose);
      bp = extend_heap(extendsize);
      //bp = find_fit(asize);
      if(bp == (void *)-1){
	return NULL;	
      }
      // printf("print 1\n");
      //mm_checkheap(verbose);
      place((void *)bp, asize);
      removeBlock(bp);
      //printf("print2\n");
    }

    else{
      //mm_checkheap(verbose);
      place((void *)bp, asize);
      removeBlock(bp);
      //remove from freeList
    }
    result = bp;
    //mm_checkheap(verbose);
    assert(result >= mem_heap_lo() && result < mem_heap_hi());
     return result;
} 
/* $end mmmalloc */

/* 
 * mm_free - Free a block 
 */
/* $begin mmfree */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    DEALLOCATED(HDRP(NEXT_BLKP(bp)));

   
    insert((BlockHeader *)bp, size);
    coalesce(bp);
}

static void insert(BlockHeader *ptr, size_t size){

  BlockHeader *head = freeListRoot;
  
  //if free list is empty
  if(freeListRoot == NULL){
    freeListRoot  = ptr;
    ptr->prev = NULL;
    ptr->next = NULL;
  }
  else{
    ptr->next = head;
    ptr->prev = NULL;
    head->prev = ptr;
    freeListRoot  = ptr;
  }


}
 
static void removeBlock(BlockHeader *ptr){
  //remove the block from the free list
  if(ptr->prev == NULL){
    //now the head pointer points to the node after discard (could be NULL)
    freeListRoot = ptr->next;
    //If the head is not NULL, then make sure its back link is set to NULL
    (ptr->next)->prev = NULL;
    

  }else{
    // Make the node preceeding the discard node point forward to the node coming after discard                                          
    (ptr->prev)->next = ptr->next;
    if (ptr->next != NULL) {
      // Make the node coming after discard point back to the node preceeding discard                                                    
      (ptr->next)->prev = ptr->prev;
    }
  }

}

/* $end mmfree */

/*
 * mm_realloc - naive implementation of mm_realloc
 */
void *mm_realloc(void *ptr, size_t size)
{/*
    void *newp;
    size_t copySize;

    if ((newp = mm_malloc(size)) == NULL) {
        printf("ERROR: mm_malloc failed in mm_realloc\n");
        exit(1);
    }
    copySize = GET_SIZE(HDRP(ptr));
    if (size < copySize)
        copySize = size;
    memcpy(newp, ptr, copySize);
    mm_free(ptr);
    return newp;
 */
  return NULL;
}

/* 
 * mm_checkheap - Check the heap for consistency 
 */
void mm_checkheap(int verbose) 
{
    char *bp = heap_listp;

    if (verbose)
        printf("Heap (%p):\n", heap_listp);

    if ((GET_SIZE(HDRP(heap_listp)) != DSIZE) || !GET_ALLOC(HDRP(heap_listp)))
        printf("Bad prologue header\n");
    checkblock(heap_listp);

    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if (verbose) 
            printblock(bp);
        checkblock(bp);
    }
     
    if (verbose)
        printblock(bp);
    if ((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp))))
        printf("Bad epilogue header\n");
}

/* The remaining routines are internal helper routines */

/* 
 * extend_heap - Extend heap with free block and return its block pointer
 */
/* $begin mmextendheap */
static void *extend_heap(size_t words) 
{
    char *bp;
    size_t size;
        
    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if ((bp = mem_sbrk(size)) == (void *)-1) 
        return NULL;

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));         /* free block header */
    PUT(FTRP(bp), PACK(size, 0));         /* free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* new epilogue header */
    

    
    //insert((BlockHeader *)bp, size);
    /* Coalesce if the previous block was free */
    return coalesce(bp);
}
/* $end mmextendheap */

/* 
 * place - Place block of asize bytes at start of free block bp 
 *         and split if remainder would be at least minimum block size
 */
/* $begin mmplace */
/* $begin mmplace-proto */
static void place(void *bp, size_t asize)
/* $end mmplace-proto */
{
    size_t csize = GET_SIZE(HDRP(bp));   

    if ((csize - asize) >= (DSIZE + OVERHEAD)) { 
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize-asize, 0));
        PUT(FTRP(bp), PACK(csize-asize, 0));
	//insert node here to free list
    }
    else { 
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}
/* $end mmplace */

/* 
 * find_fit - Find a fit for a block with asize bytes 
 */
static BlockHeader *find_fit(size_t asize)
{
  
  BlockHeader *i;
  for(i = freeListRoot; i != NULL && i != mem_heap_lo(); i = i->next){
    if(ALIGN(i->size_alloc) >= asize){
      return i;
    }

  }
  return NULL;
  /*
    void *bp;

    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
            return bp;
        }
    }
    return NULL;*/
}

/*
 * coalesce - boundary tag coalescing. Return ptr to coalesced block
 */
static void *coalesce(void *bp) 
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) {            /* Case 1 */
        return bp;
    }

    else if (prev_alloc && !next_alloc) {      /* Case 2 */
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size,0));
    }

    else if (!prev_alloc && next_alloc) {      /* Case 3 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    else {                                     /* Case 4 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + 
            GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    return bp;
}


static void printblock(void *bp) 
{
    size_t hsize, halloc, fsize, falloc;

    hsize = GET_SIZE(HDRP(bp));
    halloc = GET_ALLOC(HDRP(bp));  
    fsize = GET_SIZE(FTRP(bp));
    falloc = GET_ALLOC(FTRP(bp));  
    
    if (hsize == 0) {
        printf("%p: EOL\n", bp);
        return;
    }

    printf("%p: header: [%d:%c] footer: [%d:%c]\n", bp, 
           hsize, (halloc ? 'a' : 'f'), 
           fsize, (falloc ? 'a' : 'f')); 
}

static void checkblock(void *bp) 
{
    if ((size_t)bp % 8)
        printf("Error: %p is not doubleword aligned\n", bp);
    if (GET(HDRP(bp)) != GET(FTRP(bp)))
        printf("Error: header does not match footer\n");
}

