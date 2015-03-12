/*
 * This project will address malloclab with explicit free lists implentation.
 * Initially:
 * In our init function we initilize the heap by creating the epilouge header
 * which marks the end of the heap. In addition, we create prologue header
 * and footer which describes the size of the block.
 * The first step in allocating memory with mm_malloc is to initilize the
 * FreeListRoot to null, which will mark the beginning of our explicit free list.
 * For starters we initilize the heap with 16 bytes(which includes, earlier mentioned,
 * prologue header and footer as well as epilouge header). We want to preserver this heap
 * size until we are asked for more memory.
 *
 * Memory Allocation:
 * When allocating memory first we want to check if freeListRoot is pointing to null,
 * if so(heap is full), we want to extand the heap by max(of chuncksize or requested size).
 * After extention we move the epilouge header to the end of the heap
 * (new sbrk pointer, in other words, shift epilouge header by extended size). Addionally,
 * it is important to add the header and footer to the new free block as well as link prev
 * and next pointer into the linked list (note that after the heap expension, we will overwrite the
 * old epilogue with header ). When creating the first free block we set the prev
 * and next pointer to null, as there are no other free blocks in that list.
 * Finally we want to set the freeListRoot pointing to the new first free block.
 * Note: as we are adding/freeing more blocks we will be linking them together via prev and next pointers.
 *
 * Realloc:
 * Realloc will take a pointer to the beginning to the block we want to allocate, as well as the new size.
 * In case we want to expande the block, first we will check neighbors(left and right blocks) and if left
 * or right block is free and if size of current block plus the size of the free left or right neighbor
 * is less then or equal to the new size we simply expand the block into the free neighbor (Coalesce).
 * Otherwise, we free the current block and iterate through our explicit free list and look for a space
 * that could satisfy "newsize", if no such space, expand heap.
 * In case we want to shrink the block, first we will check the neighbor blocks, if they are free, we will combine
 * remaining space with left or right block (Coalesce). In case the left and right block are both allocated,
 * we will iterate through the free list and allocate the smallest block within the explicit free list 
 * that satisfies newize
 *
 * Heap Checker:
 * In order to avoid possible errors in our malloc implentation we are going to create a heap checker.
 * In our heap checker implentation we are going to check if our Explicit free list is linked in a
 * circle. We will check by creating two pointers(fast pointer and a turtle pointer) which will simply
 * iterate through the doubly linked list (both directions) and we will check if fast pointer equals
 * the turtle pointer. If so we can conclude that the list contains a circle,
 * which we want to avoid at all cost, beacuse they would create an infinite loop. Finally we want
 * to count number of free blocks on the heap and compare it to number of blocks in our Explicit
 * free list, in order to be aware of the possible unutilized memory.
 */

#include <stdio.h>
#include <unistd.h>
#include <string.h>
#include <stdlib.h>
#include "mm.h"
#include "memlib.h"
#include <assert.h>

/* Team structure */
team_t team = {
  /* Group name */
  "DovyTelma",
  /* First member's full name */
  "Telma Gudbjorg Eythorsdottir",
  /* First member's email address */
  "telma13@ru.is",
  /* Second member's full name (leave blank if none) */
  "Dovydas Stankevicius",
  /* Second member's email address (leave blank if none) */
  "dovydas13@ru.is",
  /* Leave blank */
  "",
  /* Leave blank */
  ""
};

/* $begin mallocmacros */
/* Basic constants and macros */
#define WSIZE       4       /* word size (bytes) */  
#define DSIZE       8       /* doubleword size (bytes) */
#define CHUNKSIZE  (1<<12)  /* initial heap size (bytes) */
#define OVERHEAD    8       /* overhead of header and footer (bytes) */
#define ALIGNMENT   8      /* Alignment */
#define HEAP_SIZE  24      /*Initial size for heap(including padding, prolouge header and footer, epilouge header as well as back_link and forward_link (for free list)) (6 * 4bytes)*/

#define MAX(x, y) ((x) > (y)? (x) : (y))  

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p)       (*(size_t *)(p))
#define PUT(p, val)  (*(size_t *)(p) = (val))  

/* (which is about 54/100).* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((char *)(bp) - WSIZE)  
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

#define ALIGN(p) (((size_t)(p) + (ALIGNMENT -1)) & ~0x7)

/*forward and back links for the free list*/
#define FORWARD_LINK(bp)  (*(void **)(bp + ALIGNMENT))
#define BACK_LINK(bp)     (*(void **)(bp))

/* $end mallocmacros */

/* Global variables */
static char *heap_listp;  /* pointer to first block */  
static char *FreeListRoot; /* Points to the head of the free lits */

/* function prototypes for internal helper routines */
static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);
static void printblock(void *bp); 
static void checkblock(void *bp);
static void put_on_heap(void *bp, size_t size, int bool);
static void remove_block(void *p);
static void add_block(void *p);
/* 
 * mm_init - Initialize the memory manager 
 */
/* $begin mminit */
int mm_init(void) 
{
    /* create the initial empty heap */
  if ((heap_listp = mem_sbrk(2*HEAP_SIZE)) == NULL)
        return -1;
    PUT(heap_listp, 0);                        /* alignment padding */
    PUT(heap_listp+WSIZE, PACK(HEAP_SIZE, 1));  /* prologue header */ 
    PUT(heap_listp+HEAP_SIZE, PACK(HEAP_SIZE, 1));  /* prologue footer */     
    PUT(heap_listp+WSIZE+(HEAP_SIZE), PACK(0, 1));   /* epilogue header */
    heap_listp += DSIZE;    
    
    
     /*Initializing forward and back links*/
    PUT(heap_listp+DSIZE, 0); //back link
    PUT(heap_listp+DSIZE+WSIZE, 0); // forward link

    /*initilize free list root to point to the head of the heap*/
    FreeListRoot = heap_listp;

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE/DSIZE) == NULL)
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
    size_t asize;      /* adjusted block size */
    size_t extendsize; /* amount to extend heap if no fit */
    char *bp;      

    /* Ignore spurious requests */
    if (size <= 0)
        return NULL;

    /* Adjust block size. */
    
    if((ALIGN(size) + DSIZE) < HEAP_SIZE)
        asize = HEAP_SIZE;
    else
      asize = ALIGN(size) + DSIZE;

    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize,CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
} 
/* $end mmmalloc */

/* 
 * mm_free - Free a block 
 */
/* $begin mmfree */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));
    put_on_heap(bp, size, 0);
    coalesce(bp);
}

/* $end mmfree */

/*using FIFO, always adding free block to the root of the list*/
static void add_block(void *p){

   void *head = (void*)FreeListRoot;
  /*if free list is empty, add the first block to the list*/
   if(FreeListRoot == NULL){
    FreeListRoot = p;
    BACK_LINK(p) = NULL;
    FORWARD_LINK(p) = NULL;
   }
   else{ //else add block to the top of the list
    FORWARD_LINK(p) = head;
    BACK_LINK(p) = NULL;
    BACK_LINK(head) = p;
    FreeListRoot = p;
   }
}

static void remove_block(void *p){
  
  /*temp variables for accessing backlinks and forward links*/
  void *temp_back = BACK_LINK(p);
  void *temp_forward = FORWARD_LINK(p);

  if(BACK_LINK(p) == NULL){ //if block is at head of the free list
    //Now the head pointer points to the node after discard(could be NULL)
    FreeListRoot = FORWARD_LINK(p); //make free list root point to next free block
    if(temp_forward != NULL){
      BACK_LINK(temp_forward) = BACK_LINK(p);   
    }
  }
  else{ /*if block is in middle of list, remove from list*/
    //Make the node preceeding the p point forward to the node coming after p
    FORWARD_LINK(temp_back) = FORWARD_LINK(p);
    if(temp_forward != NULL){
      //make the node coming after p point back to the node preeceding p
      BACK_LINK(temp_forward) = BACK_LINK(p);
    }
  }
}

/*
 * mm_realloc - naive implementation of mm_realloc
 */
void *mm_realloc(void *ptr, size_t size)
{  
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
    put_on_heap(bp, size, 0); /*put free block header and footer*/
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* new epilogue header */

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

    if ((csize - asize) >= (24)) { 
        put_on_heap(bp, asize, 1);
        remove_block(bp);
	bp = NEXT_BLKP(bp);
	put_on_heap(bp, csize-asize, 0);
       	coalesce(bp);
    }
    else { 
      put_on_heap(bp, csize, 1);
      remove_block(bp);
    }
}
/* $end mmplace */

/* 
 * find_fit - Find a fit for a block with asize bytes 
 */
static void *find_fit(size_t asize)
{
    /* first fit search */
    void *bp;

    for (bp = FreeListRoot; GET_ALLOC(HDRP(bp)) == 0; bp = FORWARD_LINK(bp)) {
      if ((size_t)GET_SIZE(HDRP(bp)) >= asize){
            return bp;
        }
    }
    return NULL; /* no fit */
}

/*
 * coalesce - boundary tag coalescing. Return ptr to coalesced block
 */
static void *coalesce(void *bp) 
{
  void *prevBlock = PREV_BLKP(bp);
  size_t prev_alloc = 0;
  
  if(GET_ALLOC(FTRP(prevBlock)) || prevBlock == bp){
    prev_alloc = 1;
  }
  
  size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
  size_t size = GET_SIZE(HDRP(bp));
  int flag = 0; //checking if we need to move the pointer we return, to the left (if we extend to the left, as is in Case 2 and Case 3) 
  
  if (prev_alloc && !next_alloc)                /* Case 1 */
  {
      size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
      remove_block(NEXT_BLKP(bp));
      put_on_heap(bp, size, 0);
  }

  else if (!prev_alloc && next_alloc)           /* Case 2 */
  {
      flag = 1;
      size += GET_SIZE(HDRP(PREV_BLKP(bp)));     
      put_on_heap(PREV_BLKP(bp), size, 0);
      remove_block(PREV_BLKP(bp));
  }

  else if (!prev_alloc && !next_alloc)         /* Case 3 */
  {
      flag = 1;
      size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(HDRP(NEXT_BLKP(bp)));
      remove_block(PREV_BLKP(bp));
      remove_block(NEXT_BLKP(bp));
      put_on_heap(PREV_BLKP(bp), size, 0);
  }
  if(flag){
    bp = PREV_BLKP(bp);
    add_block(bp);
    return bp;
  }
  add_block(bp);
  return bp;
}

static void put_on_heap(void *bp, size_t size, int bool){
  PUT(HDRP(bp), PACK(size, bool));
  PUT(FTRP(bp), PACK(size, bool));
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

