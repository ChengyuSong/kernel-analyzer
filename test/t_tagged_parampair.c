// t_tagged_parampair.c — plan 3.51 parameter-pair tests (sqlite3's
// freeP4(db, pOp->p4type, pOp->p4.p)): the caller passes an object's tag
// and its content to a callee that switches on the tag parameter. The
// caller's read of the content admits the union over the callee's uses of
// what each use's case admits: the VTab and string writers, not the int
// writer whose tag no case names.
// PAIR: struct.Op+8 by +0
#include <stdlib.h>
#define P4_VTAB (-12)
#define P4_DYN (-7)
#define P4_INT (-3)
struct VTab { void (*unlock)(void); };
struct Str { void (*unlock)(void); };
struct Int { void (*unlock)(void); };
struct Op { signed char p4type; void *p4; };
void vfn(void) {}
void sfn(void) {}
void ifn(void) {}
static void vtabUnlock(struct VTab *v) { v->unlock(); } // CHECK: vfn CHECK-NOT: ifn
static void freeStr(struct Str *s) { free(s); }
static void freeP4(int t, void *p) {
  switch (t) {
  case P4_VTAB: vtabUnlock((struct VTab *)p); break;
  case P4_DYN: freeStr((struct Str *)p); break;
  }
}
void setVtab(struct Op *o, struct VTab *v) { o->p4 = v; o->p4type = P4_VTAB; }
void setStr(struct Op *o, struct Str *s) { o->p4 = s; o->p4type = P4_DYN; }
void setInt(struct Op *o, struct Int *i) { o->p4 = i; o->p4type = P4_INT; }
void freeOp(struct Op *o) { freeP4(o->p4type, o->p4); }
int main(int argc, char **argv) {
  struct Op *o = malloc(sizeof *o);
  struct VTab *v = malloc(sizeof *v);
  struct Str *s = malloc(sizeof *s);
  struct Int *i = malloc(sizeof *i);
  v->unlock = vfn;
  s->unlock = sfn;
  i->unlock = ifn;
  if (argc > 2) setVtab(o, v); else if (argc > 1) setStr(o, s); else setInt(o, i);
  freeOp(o);
  return 0;
}
