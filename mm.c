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
 * remaining space with left or right block (Coalesce). In case the left and right block are both allocated, we will iterate
 * through the free list and allocate the smallest block within the explicit free list that satisfies newize
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
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in below _AND_ in the
 * struct that follows.
 *
 * === User information ===
 * Group: 
 * User 1: 
 * SSN: X
 * User 2: 
 * SSN: X
 * === End User Information ===
 ********************************************************/
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

/* Basic constants and macros */
#define WSIZE       4       /* word size (bytes) */  
#define DSIZE       8       /* doubleword size (bytes) */
#define CHUNKSIZE  (1<<12)  /* initial heap size (bytes) */
#define OVERHEAD    8       /* overhead of header and footer (bytes) */
#define ALIGNMENT 8 /* single word (4) or double word (8) alignment */

#define MAX(x, y) ((x) > (y)? (x) : (y))  
/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc))
/* Read and write a word at address p */
#define GET(p)       (*(size_t *)(p))
#define PUT(p, val)  (*(size_t *)(p) = (val))
  
/* (which is about 54/100).* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7) /* <<<<<<<<<<<<<<<<<<<<<<< update code */
#define GET_ALLOC(p) (GET(p) & 0x1)  /* <<<<<<<<<<<<<<<<<<<<<<< update code */

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((char *)(bp) - WSIZE)  
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* Define free list structure */
#define NODE_PTR_SIZE ALIGN(sizeof(NodePtr))
typedef struct Node NodePtr;
struct Node{
  size_t size_alloc;
  NodePtr *forward_link;
  NodePtr *back_link;
};

static char *heap_listp;
static char *FreeListRoot;

/* helper functions */
void *find_fit(size_t size);
void addBlock(NodePtr* p, size_t size);
void remove_block(NodePtr *p, size_t size);
void mm_checkheap(int verbose);
void print_heap(); /* not mine, delete this function before handin */
static void printblock(void *bp); 
static void checkblock(void *bp);
void print_free();
/* functions from the book */
static void place(void *bp, size_t asize);
static void *extend_heap(size_t words);
static void *coalesce(void *bp); 


/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{    
    /* Question 1 */
    if ((heap_listp = mem_sbrk(4*WSIZE)) == NULL)
      return -1;

    NodePtr *p = (NodePtr*)(heap_listp + WSIZE + DSIZE);
    p->forward_link = NULL; //instead of making them point to themselves, point to null
    p->back_link = NULL;
    p->size_alloc = NODE_PTR_SIZE;
 
    PUT(heap_listp, 0);                        /* alignment padding */
    PUT(heap_listp+WSIZE, PACK(OVERHEAD, 1));  /* prologue header */ 
    PUT(heap_listp+DSIZE, PACK(OVERHEAD, 1));  /* prologue footer */ 
    PUT(heap_listp+WSIZE+DSIZE, PACK(0, 1));   /* epilogue header */
    heap_listp += DSIZE;

    FreeListRoot = NULL;
    /* not sure */
    // PUT(p, 16);                          /* alignment padding */
    // PUT(p + WSIZE, PACK(16, 1));  /* prologue header */ 
    // PUT(p + DSIZE, PACK(16, 1));  /* prologue footer */ 
    //PUT(p + WSIZE + DSIZE, PACK(0, 1)); /* epilogue header */
    /************/
    
    return 0;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
  /*every block will have NodePtr, prehaps in allocated blocks we do not want to store NodePtr only in free blocks! */
    int newsize = ALIGN(NODE_PTR_SIZE + size); 
    int extendsize;
    /* ignore spurious requests */
    if(size <= 0){
      return NULL;
    }
    
       
    NodePtr *p = NULL;
    if(FreeListRoot != NULL){
      p = find_fit(newsize);
    }

    if(p == NULL){ /* not in a free list */
        extendsize = MAX(newsize, CHUNKSIZE);	
        p = extend_heap(extendsize); 
	//p = find_fit(newsize);
	// p = mem_sbrk(extendsize);

	
	if (p == NULL) //have no space
	    return NULL;
	else {	
	  p->size_alloc = newsize & ~0x7;// not allocated
	  //p->size_alloc = newsize | 1; /* set block size to new size as well as mark it as allocated */
	  //p->forward_link = NULL;
	  //p->back_link = NULL; 
	}
	
	
       place(p, newsize);

    } else { //in a free list    
	place(p, newsize);
	remove_block(p, newsize);
    }
    
    void *result = (void *)((char *)p + NODE_PTR_SIZE);
    assert(result >= mem_heap_lo() && result < mem_heap_hi()); 
    return result;
}

/*************** Remove this before handin *********************/
/* This function iterates through the entire heap using implicit list techniques. 
 * This is very useful because we can see how we are allocating block after block and of course freeing
 * Use this function in gdb
 * call print_heap()
 */
void print_free(){

  NodePtr *p;
  if(FreeListRoot == NULL){
    printf("nothing in the freeList");
  }else{
    for(p = (NodePtr*)FreeListRoot; p != mem_heap_lo() && p != NULL; p = p->forward_link){
      printf("block at %p, size %d\n",p, (int)GET_SIZE(HDRP(p)));
    }
  }
}

void print_heap(){
  NodePtr* p = (NodePtr *)(heap_listp);
  while(p < (NodePtr *)mem_heap_hi()){
    printf("%p", p);
    printf("%s block at %p, size %d\n", GET_ALLOC(HDRP(p)) ? "allocated":"free", p, (int)GET_SIZE(HDRP(p))); /* and with 1 to see if the current block is allocated or not */
    p = (NodePtr*)((char* )p + GET_SIZE(HDRP(p))); /* we want to & with ~1 because we want to see the size without allocated bit */
    } /* so here we are not using p = p->forward_link; because we want to print the entire heap, therefore we should use size property */
}
/****************************************************************/

void remove_block(NodePtr *p, size_t size){
    p->size_alloc = size | 1; /* mark this block as allocated */
   
    if(p->back_link == NULL){
      FreeListRoot = (char*)p->forward_link;
      if(p->forward_link != NULL){
         (p->forward_link)->back_link = NULL;
      }
    }
    else{
      (p->back_link)->forward_link = p->forward_link;
      if(p->forward_link != NULL){
	(p->forward_link)->back_link = p->back_link;
      }
    }
    /* remove the block from the list */  
    
} 

void *find_fit(size_t size){
  NodePtr *ptr;
    /* ptr has to be less than mem_heap_lo() in order to make sure not to iterate in a circle */
    //NodePtr* FreeListRoot =  ((NodePtr*)mem_heap_lo())->forward_link; 
    for(ptr = (NodePtr *)FreeListRoot; ptr != mem_heap_lo() && ptr != NULL; ptr = ptr->forward_link){
      if (GET_SIZE(HDRP(ptr)) >= size) { //POSSIBLY REMOVE & ~1
         return ptr; /* return approprite block */ 
       }
    }
    return NULL; /* not found */ 
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr){

  NodePtr *p = (NodePtr*)ptr; //- NODE_PTR_SIZE;/* substract the offset, see malloc return statement */
    
    /* not sure about this */
    size_t size = GET_SIZE(HDRP(ptr)); //get size of the block    
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    /***********************/

    addBlock(p, size);
    /* TODO: coalesce(p)*/
}  

void addBlock(NodePtr* p, size_t size){ 
    p->size_alloc = size & ~0x7; /* mark the block as freed */
    
    NodePtr* head = (NodePtr *)FreeListRoot;
    /* add the block */
    if(FreeListRoot == NULL){
      FreeListRoot = (char *)p;
      p->back_link = NULL;
      p->forward_link = NULL;

    }
    else{
      p->forward_link = head;
      p->back_link = NULL;
      head->back_link = p;
      FreeListRoot = (char *)p;
    }
    //NodePtr* tmp = mem_heap_lo(); /* tmp points to the head of the free list*/
    
    /*p->forward_link = tmp->forward_link;
    p->back_link = tmp;
    tmp->forward_link = p;
    p->forward_link->back_link = p;*/
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
     return NULL;
}



/************************************** Given functions **********************************/
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
    addBlock((NodePtr*)bp, csize-asize);
  }
  else { 
    PUT(HDRP(bp), PACK(csize, 1));
    PUT(FTRP(bp), PACK(csize, 1));
  }
}
/* $end mmplace */

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

  
  /* Coalesce if the previous block was free */
  // return coalesce(bp);
  //addBlock((NodePtr*)bp);
  return bp;
}
/* $end mmextendheap */

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
