// t_cells_cursorbuf.c — census cursor rule (plan 3.53, Fable 2026-10-13):
// a block filled through a post-incremented pointer (`*ep++ = d`,
// libpcap pcap_ether_aton's 6-byte buffer) is used as bytes at its site:
// the cursor slot's other stores are reloads plus a constant, so it is
// followed. The block is marked used as bytes at mint, and a struct
// written later through an imprecise pointer is the bytes row.
// LOG: 1 result slots are cursors walking the block
// LOG: \(1 used as bytes from mint\)
// LOG: struct written into storage used as bytes \(not admitted as its layout; the value flows to the raw cell\): [1-9]
#include <stdlib.h>
typedef void (*fn)(void);
struct S { long a; fn f; long b; };
void sfn(void) {}
unsigned char *mac;
struct S *obj;
__attribute__((noinline)) unsigned char *aton(const char *s) {
  unsigned char *e, *ep;
  e = ep = malloc(6);
  while (*s) *ep++ = (unsigned char)*s++;
  return e;
}
__attribute__((noinline)) void *pick(int k) { return k ? (void *)mac : (void *)obj; }
int main(int argc, char **argv) {
  mac = aton(argv[0]);
  obj = malloc(sizeof(struct S));
  struct S *p = pick(argc);
  p->f = sfn;
  obj->f(); // CHECK: sfn
  return mac[0];
}
