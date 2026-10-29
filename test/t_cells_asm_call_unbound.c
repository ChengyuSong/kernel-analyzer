// AC: a formal no register binds. h's formal 0 is tied to {di}; its
// formal 1 (rsi) has no constraint, tie or text move, so as an unbound
// pointer formal it receives every pointer input of the asm (P2 and Q),
// counted. Before AC h's read resolved to nothing.
// CFLAGS: -O1
// LOG: asm call in main to h \(by operand\); formal 0 <- tie; formal 1 unbound pointer <- 2 pointer inputs; return void
// LOG: asm calls wired by register: 1 sites, 1 callees \(by operand: 1, by literal name: 0\); formals bound by constraint 0, by tie 1, by text move 0; unbound: 1 pointer formals \(2 pointer inputs\), 0 integer formals
struct S { void (*f)(void); };
void fc(void) {}
void fd(void) {}
void fe(void) {}

__attribute__((used, noinline)) static void h(struct S *a, struct S *b) {
  b->f(); // CHECK: fd fe CHECK-NOT: fc
}

struct S P, P2, Q;

int main(void) {
  P.f = fc;
  P2.f = fe;
  Q.f = fd;
  struct S *x = &P2, *y = &Q;
  asm volatile("call %P[fn]" : "+D"(x) : [fn] "i"(h), "r"(y) : "rsi", "rax", "rcx", "rdx", "r8", "r9", "r10", "r11", "memory");
  return 0;
}
