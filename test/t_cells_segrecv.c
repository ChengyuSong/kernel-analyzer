// t_cells_segrecv.c — receiver kinds apply to every declared segment as
// they apply to the result (Fable 2026-10-13, sqlite3 #145). jsonParseCached:
// p = sqlite3_malloc64(sizeof(JsonParse) + nJson + 1); p->zJson = (char
// *)&p[1]: a constant-offset address stored into a char * field, so the
// segment at 48 is byte storage from mint (inert), as a char * result
// receiver marks a block; an int * variable declares a scalar array, a
// T ** variable an array of pointer slots. Flow through the bytes is kept
// (a function pointer copied in and out still arrives).
// LOG: segments the sites declare: [0-9]+ a struct .*, [1-9][0-9]* arrays of pointer slots, [1-9][0-9]* arrays of a declared scalar, [1-9][0-9]* bytes \(a char receiver\); [1-9][0-9]* sites declare one through a struct field
// LOG: [1-9][0-9]* more byte-used from mint by a char receiver
#include <stdlib.h>
#include <string.h>
typedef void (*fn)(void);
struct JsonParse { int n; char *zJson; fn hook; long pad[3]; };
struct Hdr { long k; fn h; };
void gfn(void) {}
void hfn(void) {}
void pfn(void) {}
void *(*xMalloc)(size_t) = malloc;
__attribute__((noinline)) void *sqlite3Malloc(size_t n) { return xMalloc(n); }
int main(int argc, char **argv) {
  size_t nJson = strlen(argv[0]);
  struct JsonParse *p = sqlite3Malloc(sizeof(*p) + nJson + 1);
  memset(p, 0, sizeof(*p));
  p->zJson = (char *)&p[1];
  memcpy(p->zJson, argv[0], nJson + 1);
  p->hook = hfn;
  fn g = gfn;
  memcpy(p->zJson + argc, &g, sizeof g);
  fn f;
  memcpy(&f, p->zJson + argc, sizeof f);
  f(); // CHECK: gfn CHECK-NOT: hfn
  struct Hdr *h = sqlite3Malloc(sizeof(*h) + argc * sizeof(int) + argc * sizeof(fn));
  int *counts = (int *)&h[1];
  counts[argc] = 3;
  h->h = hfn;
  struct Hdr *q = sqlite3Malloc(sizeof(*q) + argc * sizeof(fn));
  fn *slots = (fn *)&q[1];
  slots[argc] = pfn;
  q->h = hfn;
  slots[argc]();
  return counts[0];
}
