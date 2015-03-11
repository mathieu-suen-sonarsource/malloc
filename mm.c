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

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

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

#define FreeListRoot ((NodePtr*)mem_heap_lo())->forward_link 

/* helper functions */
void *find_fit(size_t size);
void print_heap(); /* not mine, delete this function before handin */

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    NodePtr *p = mem_sbrk(NODE_PTR_SIZE);
    p->forward_link = p;
    p->back_link = p;
    p->size_alloc = NODE_PTR_SIZE; /* when coalesing this is important */
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
    NodePtr *p = find_fit(newsize);
    if(p == NULL){ /* not in a free list */
        p = mem_sbrk(newsize);
	if (p == (void *)-1) //have no space
	  return NULL;
	else {
	  p->size_alloc = newsize | 1; /* set block size to new size as well as mark it as allocated */
	  p->forward_link = NULL;
	  p->back_link = NULL; 
	}
    } else { //in a free list
        p->size_alloc |= 1; /* mark this block as allocated */
	/* remove the block from the list */
	p->back_link->forward_link = p->forward_link;
	p->forward_link->back_link = p->back_link; 
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
void print_heap(){
    NodePtr* p = mem_heap_lo();
    while(p < (NodePtr *)mem_heap_hi()){
      printf("%s block at %p, size %d\n", (p->size_alloc & 1) ? "allocated":"free", p, (int)(p->size_alloc & ~1)); /* and with 1 to see if the current block is allocated or not */
      p = (NodePtr*)((char* )p + (p->size_alloc & ~1)); /* we want to & with ~1 because we want to see the size without allocated bit */
    } /* so here we are not using p = p->forward_link; because we want to print the entire heap, therefore we should use size property */
}
/****************************************************************/

void remove_block(NodePtr *p){
    //removes the specified block from the free list
    p->back_link->forward_link = p->forward_link;
    p->forward_link->back_link = p->back_link;
} 

void *find_fit(size_t size){
    NodePtr *ptr;
    /*
    for(ptr = ((NodePtr*)mem_heap_lo())->forward_link; ptr != mem_heap_lo() && ptr->size_alloc < size; ptr = ptr->forward_link);
    if(ptr != mem_heap_lo()){
      return ptr;
    }
    */
    
    /* ptr has to be less than mem_heap_lo() in order to make sure not to iterate in a circle */
    for(ptr = FreeListRoot; ptr != mem_heap_lo(); ptr = ptr->forward_link){
      if (ptr->size_alloc < size) {
        return ptr; /* found appropriate block */
      }
    }
   
    return NULL; /* not found */ 
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
     return NULL;
}
