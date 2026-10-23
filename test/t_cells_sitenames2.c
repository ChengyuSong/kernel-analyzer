// t_cells_sitenames2.c — site names (B): a merged store, the shape O3's
// SLP vectorizer emits for adjacent field stores (elfxx-x86.c:778 in
// nm-O3): one <2 x i64> store through a byte address (no struct step) over
// two whole i64 fields of L, written here as a vector store so the case
// does not depend on the vectorizer. Checked by (i); the site is named.
// LOG: site names \(B\): mk .*:[0-9]+ malloc: struct.s: named; .*store on L's fields 1
#include <stdlib.h>
typedef long v2 __attribute__((vector_size(16)));
struct s { void (*f)(void); long x; long y; };
void fa(void) {}
struct s *g;
void mk(void) {
  struct s *p = malloc(sizeof *p);
  p->f = fa;
  *(v2 *)((char *)p + 8) = (v2){1, 2};
  g = p;
}
void call(void) { g->f(); } // CHECK: fa
