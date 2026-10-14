// t_cells_p2iconst_field.c — the kernel shape of t_cells_p2iconst, kept
// sound: a ptrtoint constant stored into a struct field as an integer
// (realmode's trampoline_header->start = (u64)secondary_startup_64) and
// loaded elsewhere, then turned back into a pointer, still carries its
// object; an unrelated integer constant (an ERR_PTR code) does not.
// LOG: the constant-int node holds no fact
#include <stdlib.h>
typedef void (*fn)(void);
struct trampoline_header { unsigned long start; unsigned int flags; };
void secondary_startup(void) {}
void other(void) {}
__attribute__((noinline)) void setup(struct trampoline_header *h) {
  h->start = (unsigned long)secondary_startup;
  h->flags = 3;
}
__attribute__((noinline)) fn errptr(int e) { return (fn)(long)e; }
int main(int argc, char **argv) {
  struct trampoline_header *h = malloc(sizeof *h);
  setup(h);
  fn g = errptr(-22);
  if ((unsigned long)g < (unsigned long)-4095) g = other;
  fn f = argc > 2 ? (fn)h->start : g;
  f(); // CHECK: secondary_startup other
  return 0;
}
