// A basic pseudo-random number generator based on the Mersenne twister
// pseudocode from Wikipedia...
//
// Beware magic numbers...

#include <inc/rand.h>
#include <inc/stdio.h>

// Create a length 624 array to store the state of the generator
uint32_t mt[624];
uint32_t index = 0;
 
// Initialize the generator from a seed
void
seed_rand(uint32_t seed)
{
	mt[0] = seed;
	for (uint32_t i = 1; i < 624; i++) { // loop over each other element
		mt[i] = 1812433253 * (mt[i-1] ^ (mt[i-1] >> 30)) + i; // 0x6c078965
	}
}
 
// Generate an array of 624 untempered numbers
void
generate_numbers()
{
	for (uint32_t i = 0; i < 624; i++) {
		uint32_t y = (mt[i] & 0xE0000000) + (mt[(i+1)%624] & ~(0xE0000000));
		mt[i] = mt[(i + 397)%624] ^ (y >> 1);
		if ((y % 2) != 0) { // y is odd
			mt[i] = mt[i] ^ (0x9908b0df); // 2567483615
		}
	}
}

// Extract a tempered pseudorandom number based on the index-th value,
// calling generate_numbers() every 624 numbers
uint32_t
rand()
{
	if (index == 0) generate_numbers();
 
	uint32_t y = mt[index];
	y = y ^ (y >> 11);
	y = y ^ ((y << 7) & (0x9d2c5680));   //2636928640
	y = y ^ ((y << 15) & (0xefc60000));  // 4022730752
	y = y ^ (y >> 18);

	index = (index + 1) % 624;
	return y;
}

uint32_t inline
next_pow_of_2(uint32_t v)
{
	v--;
	v |= v >> 1;
	v |= v >> 2;
	v |= v >> 4;
	v |= v >> 8;
	v |= v >> 16;
	v++;
	v += (v == 0); // Fix 0 should return 1
	return v;
}

uint32_t
rand_beneath(uint32_t bound)
{
	// Mask away everything above the nearest power of 2
	uint32_t bound_mask = (next_pow_of_2(bound));
        bound_mask = ((bound_mask == bound) ? (bound_mask << 1) : bound_mask) - 1;

	// Find a random number bigger than the bound
	uint32_t res;
	do {
		res = rand() & bound_mask;
	} while (res >= bound);

	return res;
}
