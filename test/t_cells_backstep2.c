// The same back-step where the T cannot become an array: the data after
// the header holds another struct (the extension is refused). A variable
// index over T then -1 reaches the header's field (element 0) and the
// data's any-offset cell.
// CFLAGS: -O3
#include <stdlib.h>
struct hdr { void (*fn)(void); long n; };
struct item { void (*g)(void); };
void f(void) {}
void g(void) {}
__attribute__((noinline)) struct hdr *make(size_t n) {
  struct hdr *h = malloc(sizeof(struct hdr) + n * sizeof(struct item));
  h->fn = f;
  h->n = (long)n;
  struct item *it = (struct item *)(h + 1);
  for (size_t i = 0; i < n; i++) it[i].g = g;
  return h;
}
int main(int argc, char **argv) {
  struct hdr *h = make((size_t)argc);
  struct hdr *q = h + (argc - 1);
  q[-1].fn(); // CHECK: f
  return 0;
}
