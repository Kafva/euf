// - - - - - - - - - - - - - - - - - - // 
#include <stdlib.h>
#include <limits.h>

typedef char XML_Char;
typedef struct block {
  struct block *next;
  int size;
  XML_Char s[1];
} BLOCK;

#define offsetof(t, d) __builtin_offsetof(t, d)

static size_t
poolBytesToAllocateFor(int blockSize) {
  /* Unprotected math would be:
  ** return offsetof(BLOCK, s) + blockSize * sizeof(XML_Char);
  **
  ** Detect overflow, avoiding _signed_ overflow undefined behavior
  ** For a + b * c we check b * c in isolation first, so that addition of a
  ** on top has no chance of making us accept a small non-negative number
  */
  const size_t stretch = sizeof(XML_Char); /* can be 4 bytes */

  if (blockSize <= 0)
    return 0;

  if (blockSize > (int)(INT_MAX / stretch))
    return 0;

  {
    const int stretchedBlockSize = blockSize * (int)stretch;
    const int bytesToAllocate
        = (int)(offsetof(BLOCK, s) + (unsigned)stretchedBlockSize);
    if (bytesToAllocate < 0)
      return 0;

    return (size_t)bytesToAllocate;
  }
}


static size_t
poolBytesToAllocateFor_old(int blockSize) {
  /* Unprotected math would be:
  ** return offsetof(BLOCK, s) + blockSize * sizeof(XML_Char);
  **
  ** Detect overflow, avoiding _signed_ overflow undefined behavior
  ** For a + b * c we check b * c in isolation first, so that addition of a
  ** on top has no chance of making us accept a small non-negative number
  */
  const size_t stretch = sizeof(XML_Char); /* can be 4 bytes */

  if (blockSize <= 1)
    return 0;

  if (blockSize > (int)(INT_MAX / stretch))
    return 0;

  {
    const int stretchedBlockSize = blockSize * (int)stretch;
    const int bytesToAllocate
        = (int)(offsetof(BLOCK, s) + (unsigned)stretchedBlockSize);
    if (bytesToAllocate < 0)
      return 0;

    return (size_t)bytesToAllocate;
  }
}

// - - - - - - - - - - - - - - - - - - - //



int main(){
	#ifdef CBMC
	
	int blockSize1, blockSize2;
	__CPROVER_assume( blockSize1 == blockSize2 );

	size_t res 				= poolBytesToAllocateFor(blockSize1);
	size_t res_old 		= poolBytesToAllocateFor(blockSize2);
	//unsigned long res_old = getDebugLevel_old_b026324c6904b2a("test", 0);

	__CPROVER_assert(res == res_old, "Same");
	#endif

	return 0;
}

