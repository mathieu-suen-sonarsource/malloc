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
 *
 *
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
 * Group: DovyTelma
 * User 1: telma13
 * SSN: 1204922099
 * User 2: dovydas13
 * SSN: 1006944179
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

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

//Basic constants and macros, chapter 9 page 830
#define WSIZE       4       /* word size (bytes) */
#define DSIZE       8       /* doubleword size (bytes) */
#define CHUNKSIZE  (1<<12)  /* initial heap size (bytes) */


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
static char *heapListPtr; //points to the first block of heap

void *fit_Block(size_t size);
static void placeMemory(void *p, size_t asize);
static void *extend_heap(size_t words);
/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
  BlockHeader *p = mem_sbrk(BlockSize);
  p->size_alloc = 1; //allocated!
  p->next = p;
  p->prev = p;

  if ((heapListPtr = mem_sbrk(4*WSIZE)) == NULL)
    return -1;
  PUT(heapListPtr, 0);                        // alignment padding
  PUT(heapListPtr+WSIZE, PACK(DSIZE, 1));     // prologue header
  PUT(heapListPtr+DSIZE, PACK(DSIZE, 1));     // prologue footer
  PUT(heapListPtr+WSIZE+DSIZE, PACK(0, 1));   // epilogue header

  heapListPtr += DSIZE; //do we need it?
  freeListRoot = NULL;
  return 0;
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *             Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size){ 
   //Got some base code from the book, chapter 9
   size_t asize;      /* adjusted block size */
   size_t extendsize; /* amount to extend heap if no fit */

    /* Ignore spurious requests */
    if (size == 0){
      return NULL;
    }

    /* Adjust block size to include overhead and alignment reqs. */
    asize = ALIGN(BlockSize + size);


     if(freeListRoot == NULL){ //if freeList contains no free blocks we want to expand heap
      extendsize = MAX(asize, CHUNKSIZE);
      extend_heap(extendsize);
      // mem_sbrk(extendsize);
     }

   BlockHeader *p = fit_Block(asize);//return a pointer to available block

    if(p == NULL){  //if there is no available block of size "asize"
      extendsize = MAX(asize, CHUNKSIZE);
      p = extend_heap(extendsize);
      //p = mem_sbrk(extendsize);
      if (p == (void *)-1){
        return NULL;
      } else {
	      //extend size of heap
	      //possibly change p->size_alloc to allocated 1
      }

      //TODO: remove p from free list (like bellow)
      //set state to allocated!
      placeMemory(p, asize); //after extending the heap we wanna allocate that memory
    } else {
      //if it returns a pointer we wanna allocate that memory here

      //todo: move this into remove function!
      p->size_alloc |= 1; //mark as allocated!
      
      //remove the block from the free list
      if (p->prev == NULL) {
        // Now the head pointer points to the node after discard (could be NULL)
        freeListRoot = p->next;
        // If the head is not NULL, then make sure that its back link is set to NULL
        if (freeListRoot != NULL) {
	  freeListRoot->prev = NULL;
        }
      }
      else {
        // Make the node preceeding the discard node point forward to the node coming after discard
        (p->prev)->next = p->next;
        if (p->next != NULL) {
	  // Make the node coming after discard point back to the node preceeding discard
	  (p->next)->prev = p->prev;
        }
      }
     
      placeMemory(p, asize); //now we can safely allocate the memory
    }
    return (char *)p + BlockSize;
}

void *fit_Block(size_t size){
  // Looking for space of size 8
  // ++++++++++++++++++++++++++
  // |XXXXX|       |XX|XXXX|  |
  // ++++++++++++++++++++++++++
  //       ^
  //returns the pointer to available block if none available then return null
  BlockHeader *p;
  for(p = ((BlockHeader *)mem_heap_lo())->next; p != mem_heap_lo() && p->size_alloc < size; p = p->next);
  if(p != mem_heap_lo()){
    return p;
  }
  else{
    return NULL;
  }
}

static void placeMemory(void *p, size_t asize){
  //Taken from book, chapter 9, page 856-857
  size_t csize = GET_SIZE(HDRP(p));

  if ((csize - asize) >= (DSIZE*2)) {
    PUT(HDRP(p), PACK(asize, 1));
    PUT(FTRP(p), PACK(asize, 1));
    p = NEXT_BLKP(p);
    PUT(HDRP(p), PACK(csize-asize, 0));
    PUT(FTRP(p), PACK(csize-asize, 0));
  }
  else {
    PUT(HDRP(p), PACK(csize, 1));
    PUT(FTRP(p), PACK(csize, 1));
    }

}


static void *extend_heap(size_t words){

    char *bp;
  size_t size;

  // Allocate an even number of words to maintain alignment
  size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
  if ((bp = mem_sbrk(size)) == (void *)-1)
    return NULL;

  // Initialize free block header/footer and the epilogue header
  PUT(HDRP(bp), PACK(size, 0));         // free block header
  PUT(FTRP(bp), PACK(size, 0));         // free block footer
  PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); // new epilogue header

  // Coalesce if the previous block was free
  //CHECKOUT Coalesce to merge neighbor blocks
  return bp;

  return NULL;
}


/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
  

  
  //TODO free block from given ptr
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
  //TODO realloc
  return NULL;
}
