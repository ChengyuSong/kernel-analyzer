// t_cells_boundedarr_last.c — rule 1 bound clause, the other side: the
// declared array is T's last field (it ends at T's end), so the index is
// meant to run on into the trailing data and reaches the function pointer
// stored there.
#include <stdlib.h>
typedef void (*fn)(void);
void inarr(void) {}
void intail(void) {}
struct L { long n; fn a[4]; };
int main(int argc, char **argv) {
  struct L *l = malloc(sizeof(struct L) + 64);
  l->a[0] = inarr;
  *(fn *)((char *)(l + 1) + 8) = intail;
  l->a[argc](); // CHECK: inarr intail
  return 0;
}
