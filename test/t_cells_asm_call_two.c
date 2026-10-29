// AC: two operand calls in one asm, each preceded by its own text move
// into %rdi. Each callee binds from the move before its own call (the
// asm's other "i" operands are added as alternatives only after every
// call token is read, so k2 is not read at k1's call). Before AC k2's
// read resolved to nothing.
// CFLAGS: -O1
// LOG: asm call in main to k1 \(by operand\); formal 0 <- text move; return void
// LOG: asm call in main to k2 \(by operand\); formal 0 <- text move; return void
// LOG: asm calls wired by register: 1 sites, 2 callees \(by operand: 2, by literal name: 0\); formals bound by constraint 0, by tie 0, by text move 2;
struct S { void (*f)(void); };
void fc(void) {}
void fd(void) {}

__attribute__((used, noinline)) static void k1(struct S *s) { s->f(); }
__attribute__((used, noinline)) static void k2(struct S *s) {
  s->f(); // CHECK: fd CHECK-NOT: fc
}

struct S A, B;

int main(void) {
  A.f = fc;
  B.f = fd;
  struct S *a = &A, *b = &B;
  asm volatile("movq %[a], %%rdi\n\tcall %P[f1]\n\tmovq %[b], %%rdi\n\tcall %P[f2]"
               :
               : [f1] "i"(k1), [f2] "i"(k2), [a] "r"(a), [b] "r"(b)
               : "rdi", "rsi", "rax", "rcx", "rdx", "r8", "r9", "r10", "r11");
  return 0;
}
