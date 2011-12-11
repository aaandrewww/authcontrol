#include <inc/types.h>
#include <inc/lib.h>

static Heap *theHeap = NULL;

void
init_heap(Heap *newHeap, void *mem, size_t size)
{
    newHeap->heap = (uint8_t *)mem;
    newHeap->mem_brk = newHeap->heap;
    newHeap->size = size;
    newHeap->freep = NULL;
}

Heap *
set_heap(Heap *heap){
    Heap *oldHeap = theHeap;
    theHeap = heap;
    return oldHeap;
}

void *
sbrk(size_t bytes)
{
    uint8_t *old_brk = theHeap->mem_brk;

    if ((bytes < 0) || ((theHeap->mem_brk + bytes) > theHeap->heap + theHeap->size)) {
        return NULL;
    }
    theHeap->mem_brk += bytes;
    return (void *)old_brk;
}

/* morecore: get more memory from the operating system */
Header *
morecore(uint32_t nunits)
{
    uint8_t *cp;
    Header *up;

    cp = (uint8_t *)sbrk(nunits * sizeof(Header));
    if (cp == NULL)                 /* no space at all */
	return NULL;
    up = (Header *) cp;
    up->s.size = nunits;
    free((void *)(up+1));
    return theHeap->freep;
}

/* malloc: general purpose storage allocator */
void *
malloc(size_t nbytes)
{
    Header *p, *prevp;
    uint32_t nunits;

    nunits = (nbytes+sizeof(Header)-1)/sizeof(Header) + 1;
    if ((prevp = theHeap->freep) == NULL) { /* no free list yet */
	theHeap->base.s.ptr = theHeap->freep = prevp = &theHeap->base;
	theHeap->base.s.size = 0;
    }
    for (p = prevp->s.ptr; ; prevp = p, p = p->s.ptr) {
	if (p->s.size >= nunits) {        /*big enough */
	    if (p->s.size == nunits)        /* exactly */
		prevp->s.ptr = p->s.ptr;
	    else {                /* allocate tail end */
		p->s.size -= nunits;
		p += p->s.size;
		p->s.size = nunits;
	    }
	    theHeap->freep = prevp;
	    return (void *)(p+1);
	}
	if (p == theHeap->freep)    /* wrapped around free list */
	    if ((p = morecore(nunits)) == NULL)
		return NULL;              /* none left */
    }
}

/* free: put block ap in free list */
void
free(void *ap)
{
    Header *bp, *p;

    bp = (Header *)ap - 1;    /* point to block header */
    for (p = theHeap->freep; !(bp > p && bp < p->s.ptr); p = p->s.ptr)
	if (p >= p->s.ptr && (bp > p || bp < p->s.ptr))
	    break; /* freed block at start or end of arena */

    if (bp + bp->s.size == p->s.ptr) { /* join to upper nbr */
	bp->s.size += p->s.ptr->s.size;
	bp->s.ptr = p->s.ptr->s.ptr;
    } else {
	bp->s.ptr = p->s.ptr;
    }
    if (p + p->s.size == bp) {          /* join to lower nbr */
	p->s.size += bp->s.size;
	p->s.ptr = bp->s.ptr;
    } else {
	p->s.ptr = bp;
    }
    theHeap->freep = p;
}

/* freeall: free all allocated memory */
void
freeall(void)
{
    theHeap->mem_brk = theHeap->heap;
    theHeap->freep = NULL;
}
