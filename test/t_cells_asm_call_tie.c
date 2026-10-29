// AC: the copy_user shape, the argument tied to a {di} output ("+D"):
// formal 0 is bound by the tie. Before AC g's read resolved to nothing.
// CFLAGS: -O1
// LOG: asm call in main to g \(by operand\); formal 0 <- tie; return void
// LOG: asm calls wired by register: 1 sites, 1 callees \(by operand: 1, by literal name: 0\); formals bound by constraint 0, by tie 1, by text move 0;
struct S { void (*f)(void); };
void fc(void) {}
void fd(void) {}
void fe(void) {}

__attribute__((used, noinline)) static void g(struct S *s) {
  s->f(); // CHECK: fc CHECK-NOT: fd fe
}

struct S P, Q;

int main(void) {
  P.f = fc;
  Q.f = fd;
  struct S *p = &P;
  asm volatile("call %P[fn]" : "+D"(p) : [fn] "i"(g) : "rsi", "rax", "rcx", "rdx", "r8", "r9", "r10", "r11", "memory");
  return 0;
}
