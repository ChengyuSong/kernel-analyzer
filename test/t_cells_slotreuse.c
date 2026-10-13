// t_cells_slotreuse.c — the census's limit (plan 3.53, row 3): a result
// slot that also holds another value (binutils _bfd_pei_swap_sym_in:
// `name` holds a lookup's result, then the bfd_alloc copy) leaves the
// creating site unclassified, counted: no bytes mark, so the block keeps
// rule 1's first typed use.
// LOG: 1 result slots also hold other values \(unclassified\)
// LOG: \(0 used as bytes from mint\)
#include <stdlib.h>
#include <string.h>
typedef void (*fn)(void);
struct S { long a; fn f; long b; };
void sfn(void) {}
char *keep;
struct S *obj;
__attribute__((noinline)) const char *lookup(const char *s) { return s + 1; }
__attribute__((noinline)) void copy_name(const char *s) {
  char *name = (char *)lookup(s);
  if (name[0] == '/') {
    name = malloc(strlen(s) + 1);
    strcpy(name, s);
  }
  keep = name;
}
__attribute__((noinline)) void *pick(int k) { return k ? (void *)keep : (void *)obj; }
int main(int argc, char **argv) {
  copy_name(argv[0]);
  obj = malloc(sizeof(struct S));
  struct S *p = pick(argc);
  p->f = sfn;
  obj->f(); // CHECK: sfn
  return keep[0];
}
