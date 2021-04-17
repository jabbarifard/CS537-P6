#include "param.h"
#include "types.h"
#include "user.h"

#define PGSIZE 4096

/*
 *  Print the queue in order (starting at the head) whenever
 *  a page is decrypted (print the queue after modifying it
 *  during decryption).
 *
 *  Then run this program and compare the printed output
 *  from decrypt to the print statements in this program.
 */

int main(void) {
  printf(1, "\n\nqueuetest starting\n\n");

  printf(1, "\n********************expected queue state:\n");
  printf(1, "0   , 2000\n");

  // Allocate 6 pages and decrypt them
  char *ptr = sbrk(6 * PGSIZE);
  for (int i = 0; i < 6; i++)
    ptr[i * PGSIZE] = ptr[i * PGSIZE + 1];

  printf(1, "\n********************expected queue state:\n");
  printf(1, "0   , 2000, 3000, 4000, 5000, 6000, 7000, 8000\n");

  // Allocate 1 more page and decrypt it
  // This should evict the first page on the heap
  // (It will first evict the code and the stack but those will
  //  be added back to the working set because they're used often)
  printf(1, "\nAllocating 9th page...\n");
  char* ptr2 = sbrk(PGSIZE);
  ptr2[0] = ptr2[1];

  printf(1, "\n********************expected queue state:\n");
  printf(1, "2000, 3000, 4000, 5000, 6000, 7000, 8000, 9000\n");
  printf(1, "3000, 4000, 5000, 6000, 7000, 8000, 9000, 0   \n");
  printf(1, "4000, 5000, 6000, 7000, 8000, 9000, 0   , 2000\n");

  // Deallocate 6 pages; decrypt the remaining page on the heap
  printf(1, "\nDeallocating 6 pages...\n");
  sbrk(-1 * 6 * PGSIZE);
  ptr[0] = ptr[1];

  printf(1, "\n********************expected queue state:\n");
  printf(1, "0   , 2000, 3000\n");

  printf(1, "\n");
  exit();
}
