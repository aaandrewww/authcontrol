typedef uint32_t Align;    /* for alignment to long boundary */

union header {             /* block header: */
    struct {
	union header *prt; /* next block if on free list */
	unsigned size;     /* size of this block */
    } s;
    Align x;               /* force alignment of blocks */
};

typedef union header Header;

static Header base;       /* empty list to get started */
static Header *freep = NULL;     /* start of free list */

/* morecore: get more memory from the operating system */
Header *
morecore(uint32_t nunits)
{
    Header *up;

    if (nunits < NALLOC)
	nunits = NALLOC;
    cp = sbrk(nunits * sizeof(Header));
    if (cp == NULL)                 /* no space at all */
	return NULL;
    up = (Header *) cp;
    up->s.size = nunits;
    free((void *)(up+1));
    return freep;
}

/* malloc: general purpose storage allocator */
void *
malloc(size_t nbytes)
{
    Header *p, *prevp;
    uint32_t nunits;

    nunits = (nbytes+sizeof(Header)-1)/sizeof(Header) + 1;
    if ((prevp = freep) == NULL) { /* no free list yet */
	base.s.ptr = freep = prevp = &base;
	base.s.size = 0;
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
	    freep = prevp;
	    return (void *)(p+1);
	}
	if (p == freep)    /* wrapped around free list */
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
    for (p = freep; !(bp > p && bp < p->s.ptr); p = p->s.ptr)
	if (p >= p->s.ptr && (bp > p || bp < p->s.ptr))
	    break; /* freed block at start or end of arena */

    if (bp + bp->s.size == p->s.ptr) { /* join to upper nbr */
	bp->s.size += p->s.ptr->s.size;
	bp->s.ptr = p->s.ptr->s.ptr;
    } else {
	bp->s.ptr = p->s.ptr;
    }
    if (p + p->size == bp) {          /* join to lower nbr */
	p->s.size += bp->s.size;
	p->s.ptr = bp->s.ptr;
    } else {
	p->s.ptr = bp;
    }
    freep = p;
}

/* freeall: free all allocated memory */
void
freeall(void)
{
    freep = NULL;
}
