// t_cells_bytesbuf.c — ruling A, byte part: a block every creating site
// uses only as bytes (a string: strcpy, char stores) is used as bytes
// from mint (a mark, not a label), so a struct written later through an
// imprecise pointer is the rule (b) row "struct written into storage used
// as bytes", flow kept, instead of its label (libpcap sdup).
// LOG: \(1 used as bytes from mint\)
// LOG: struct written into storage used as bytes \(not admitted as its layout; the value flows to the raw cell\): [1-9]
#include <stdlib.h>
#include <string.h>
typedef void (*fn)(void);
struct S { long a; fn f; long b; };
void sfn(void) {}
char *name;
struct S *obj;
__attribute__((noinline)) char *sdup(const char *s) {
  char *cp = malloc(strlen(s) + 1);
  strcpy(cp, s);
  return cp;
}
__attribute__((noinline)) void *pick(int k) { return k ? (void *)name : (void *)obj; }
int main(int argc, char **argv) {
  name = sdup(argv[0]);
  obj = malloc(sizeof(struct S));
  struct S *p = pick(argc);
  p->f = sfn;
  obj->f(); // CHECK: sfn
  return name[0];
}
