// t_cells_fieldrecv.c — row 3 (plan 3.53): 1b reads a struct-field
// receiver's declared member type as it reads a variable's. libpcap
// opt_init: `opt_state->space = (bpf_u_int32 *)malloc(..)`, used through
// a cursor `p += nodewords` (a variable step: followed, no accesses), so the
// field's declared scalar is the site's declaration: an array of i32 at
// mint, and a struct written through an imprecise pointer is the
// declared-scalar row instead of its label.
// LOG: 2 receivers are struct fields
// LOG: 1 arrays of a declared scalar
// LOG: struct written into storage declared scalar \(ruling A; folded into the array's element cells, flow kept\): [1-9]
#include <stdlib.h>
typedef void (*fn)(void);
struct S { long a; fn f; long b; };
struct state { unsigned *space; unsigned **dom; int n, words; };
void sfn(void) {}
struct state st;
struct S *obj;
__attribute__((noinline)) void init(int n, int words) {
  st.space = (unsigned *)malloc(2 * n * words * sizeof(*st.space));
  st.dom = malloc(n * sizeof(unsigned *));
  unsigned *p = st.space;
  for (int i = 0; i < n; i++) {
    st.dom[i] = p;
    p += words;
  }
}
__attribute__((noinline)) void *pick(int k) { return k ? (void *)st.space : (void *)obj; }
int main(int argc, char **argv) {
  init(argc + 2, argc + 1);
  obj = malloc(sizeof(struct S));
  struct S *p = pick(argc);
  p->f = sfn;
  obj->f(); // CHECK: sfn
  return st.space[1];
}
