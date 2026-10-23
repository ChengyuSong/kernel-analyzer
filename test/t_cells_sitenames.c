// t_cells_sitenames.c — site names (B, Fable 2026-10-21/22): a fresh
// allocation site whose mint label is L is named L for the covers when
// every write found from it is checked against L ((i)) and its size
// conforms ((iii)); else it is an untyped allocation, OPEN or FAIL with
// its reason. One site per function; each LOG line pins one verdict.
// LOG: site names \(B\): p_plain .*:[0-9]+ malloc: struct.s: named
// LOG: site names \(B\): p_trail .*:[0-9]+ malloc: struct.t: named; \(iii\) runtime \(sizeof\(L\) \+ k trailing elements
// LOG: site names \(B\): p_copy .*:[0-9]+ malloc: struct.s: named; .*copy K-to-K 1
// LOG: site names \(B\): p_union .*:[0-9]+ malloc: struct.u: named; .*union slot 1
// LOG: site names \(B\): p_atom .*:[0-9]+ malloc: struct.d: named; .*store on L's fields 1
// LOG: site names \(B\): p_bytes .*:[0-9]+ malloc: struct.d: named; .*bodiless bytes over no pointer field 1
// LOG: site names \(B\): p_wrap .*:[0-9]+ mk: struct.s: named
// LOG: site names \(B\): p_memset .*:[0-9]+ malloc: struct.s: named; .*memset of a non-pointer byte 1
// LOG: site names \(B\): o_d1 .*:[0-9]+ malloc: struct.s: open \(copy\): a copy from an open source \(D1\)
// LOG: site names \(B\): o_ind .*:[0-9]+ malloc: struct.s: open \(call\): passed to an indirect call
// LOG: site names \(B\): o_noatom .*:[0-9]+ malloc: struct.s: open \(call\): passed to bodiless ext_unknown \(no summary\)
// LOG: site names \(B\): o_bytes .*:[0-9]+ malloc: struct.s: open \(bodiless write\): bytes written by setlinebuf's summary
// LOG: site names \(B\): o_vararg .*:[0-9]+ malloc: struct.s: open \(vararg\): passed as a vararg to va_take
// LOG: site names \(B\): mk2 .*:[0-9]+ malloc: struct.s: open \(return\)
// LOG: site names \(B\): o_memsetp .*:[0-9]+ malloc: struct.s: open \(memset\): a memset of a ptrtoint-derived value
// LOG: site names \(B\): f_ptrtoint .*:[0-9]+ malloc: struct.d: FAIL: \+0 8B i64: a pointer into a non-pointer field of struct.d
// LOG: site names \(B\): f_ptrarr .*:[0-9]+ malloc: i64\[\]: FAIL: \+8 8B ptr: a pointer into a non-pointer field of i64\[\]
// LOG: site names \(B\): f_beyond .*:[0-9]+ malloc: struct.s: FAIL: \+40 8B i64 past struct.s's extent \(24\)
#include <stdlib.h>
#include <string.h>
#include <stdarg.h>
struct s { void (*f)(void); long x; long y; };
struct t { long n; struct s a[]; };
struct u { void (*f)(void); union { long l; void *q; } v; };
struct d { long a; long b; };
void fa(void) {}
void *g[32];
struct s gs = {fa, 0, 0};
extern void ext_unknown(void *);
extern void setlinebuf(void *);
extern int pthread_attr_setstacksize(void *, unsigned long);
void (*hook)(void *);
void va_take(int n, ...) { va_list ap; va_start(ap, n); g[20] = va_arg(ap, void *); va_end(ap); }
long getd(struct d *q) { return q->b; } // struct.d in the IR
// pass: whole fields of L
void p_plain(void) { struct s *p = malloc(sizeof *p); p->f = fa; p->x = 1; g[0] = p; }
// pass: a trailing array's elements (A1)
void p_trail(int n) { struct t *p = malloc(sizeof *p + n * sizeof(struct s)); p->n = n; p->a[1].f = fa; g[1] = p; }
// pass: a block copy from L's own name (K-to-K)
void p_copy(void) { struct s *p = malloc(sizeof *p); memcpy(p, &gs, sizeof *p); g[2] = p; }
// pass: a union slot is the union census's (iv)
void p_union(void) { struct u *p = malloc(sizeof *p); p->f = fa; *(long *)((char *)p + 8) = 3; g[3] = p; }
// pass: a bodiless callee's store atom on a whole field (B4)
void p_atom(void) { struct d *p = malloc(sizeof *p); pthread_attr_setstacksize(p, 4096); g[4] = p; }
// pass: a bodiless callee's byte atom over no pointer field (amendment 3)
void p_bytes(void) { struct d *p = malloc(sizeof *p); setlinebuf(p); g[5] = p; }
// pass: a wrapper's allocation, followed through its return
static struct s *mk(void) { return malloc(sizeof(struct s)); }
void p_wrap(void) { struct s *p = mk(); p->f = fa; g[6] = p; }
// pass: a memset of a non-pointer byte, any value (Fable 2026-10-22)
void p_memset(void) { struct s *p = malloc(sizeof *p); memset(p, 0xff, sizeof *p); p->f = fa; g[7] = p; }
// open: a copy from a source that names nothing (D1)
void o_d1(void *src) { struct s *p = malloc(sizeof *p); memcpy(p, src, sizeof *p); g[8] = p; }
// open: an indirect call (B1)
void o_ind(void) { struct s *p = malloc(sizeof *p); p->f = fa; hook(p); }
// open: a bodiless callee with no atom
void o_noatom(void) { struct s *p = malloc(sizeof *p); p->f = fa; ext_unknown(p); }
// open: a bodiless byte atom over a pointer field
void o_bytes(void) { struct s *p = malloc(sizeof *p); setlinebuf(p); p->f = fa; g[9] = p; }
// open: a vararg
void o_vararg(void) { struct s *p = malloc(sizeof *p); p->f = fa; va_take(1, p); }
// open: a return to an indirect caller
struct s *mk2(int k) { // not a fresh wrapper: it may return gs
  if (!k) return &gs;
  struct s *p = malloc(sizeof *p);
  p->x = k;
  return p;
}
struct s *(*mkp)(int) = mk2;
void o_retind(void) { struct s *p = mkp(1); p->f = fa; g[10] = p; }
// open: a memset whose byte is taken from a pointer
void o_memsetp(void) { struct s *p = malloc(sizeof *p); memset(p, (int)(long)fa, sizeof *p); p->f = fa; g[11] = p; }
// FAIL: a code pointer's bits into an integer field (B5)
void f_ptrtoint(void) { struct d *p = malloc(sizeof *p); *(long *)p = (long)fa; g[12] = p; }
// FAIL: a pointer into a scalar-array label (B5)
static void put_fn(long *q) { ((void **)q)[1] = (void *)fa; }
void f_ptrarr(void) { long *p = malloc(4 * sizeof(long)); p[0] = 1; put_fn(p); g[13] = p; }
// FAIL: a constant index beyond the extent
void f_beyond(void) { struct s *p = malloc(sizeof *p); p->f = fa; ((long *)p)[5] = 1; g[14] = p; }
void call(void) { ((struct s *)g[0])->f(); } // CHECK: fa
