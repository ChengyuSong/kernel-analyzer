// RF (Fable 2026-10-24), the soundness case: a refill is the allocation's
// own result. One buffer holds three regions, as rsrc_process_section's
// write_data (peXXigen.c:4326-4335): start = p, leaf = p + nl, str = leaf +
// ns, data = str + ns, each cursor bumped by its own writer. At -O3 the
// store into W.str is gep (gep p, nl), ns. The chunk-base walk from p joins
// start, leaf and data (data's store reaches it through str's value) and
// refuses that pool (start is read as data), but before RF the refill test
// walked str's two GEPs to malloc, so str alone was a certified pool. Its
// hand-outs became chunks "apart from every element": the function pointer
// written through a hand-out and read back through start was lost (the
// call read nothing). With RF the store is at a nonzero offset of the
// allocation and not the header form: not a refill, str is a cursor over
// p's one object, and the read through start finds f.
// CFLAGS: -O3
#include <stdlib.h>
#include <string.h>
struct wd { char *start; char *leaf; char *str; char *data; };
struct wd W; // external: a static one is split into scalars at -O3
struct ent { void (*fn)(void); long x; };
void f(void) {}
__attribute__((noinline)) char *take_leaf(size_t n) {
  char *r = W.leaf;
  W.leaf = r + n;
  return r;
}
__attribute__((noinline)) char *take_str(size_t n) {
  char *r = W.str;
  W.str = r + n;
  return r;
}
__attribute__((noinline)) char *take_data(size_t n) {
  char *r = W.data;
  W.data = r + n;
  return r;
}
__attribute__((noinline)) void setup(size_t nl, size_t ns) {
  char *p = malloc(nl + 2 * ns + 64);
  W.start = p;
  W.leaf = p + nl;
  W.str = W.leaf + ns;
  W.data = W.str + ns;
}
int main(int argc, char **argv) {
  (void)argv;
  setup(16 * (size_t)argc, 16 * (size_t)argc);
  memset(take_leaf(8), 0, 8);
  memset(take_data(8), 0, 8);
  struct ent *e = (struct ent *)take_str(sizeof *e);
  e->fn = f;
  size_t off = (size_t)((char *)e - W.start);
  struct ent *back = (struct ent *)(W.start + off);
  back->fn(); // CHECK: f
  return 0;
}
// LOG: refill at a nonzero offset of an allocation: not a refill \(the chunk is also held by wd\+0 wd\+24 wd\+8\): wd\+16 at setup
// LOG: pool candidate wd\+16 removed: refilled only at a nonzero offset of an allocation, not the header form
// NOLOG: POOL fields wd\+16
