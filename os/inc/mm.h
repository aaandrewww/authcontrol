#ifndef JOS_INC_MM_H
#define JOS_INC_MM_H

typedef uint32_t Align;    /* for alignment to long boundary */

union header {             /* block header: */
    struct {
	union header *ptr; /* next block if on free list */
	unsigned size;     /* size of this block */
    } s;
    Align x;               /* force alignment of blocks */
};

typedef union header Header;

typedef struct heap {
    uint8_t *heap;
    uint8_t *mem_brk;
    size_t size;
    Header base;
    Header *freep;
} Heap;

void *  malloc(size_t bytes);
void    free(void *p);
void    freeall(void);
void    init_heap(Heap *newHeap, void *mem, size_t size);
Heap *  set_heap(Heap *heap);

#endif  // !JOS_INC_MM_H
