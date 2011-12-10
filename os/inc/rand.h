#ifndef JOS_INC_RAND_H
#define JOS_INC_STRING_H

#include <inc/types.h>

void     seed_rand(uint32_t seed);
uint32_t rand();
uint32_t rand_beneath(uint32_t bound);

#endif /* not JOS_INC_RAND_H */
