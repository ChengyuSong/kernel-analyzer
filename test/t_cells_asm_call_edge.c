// (b) (Fable 2026-10-28, plan 3.207): a function an inline asm calls is
// listed in --callgraph-json as a direct edge at the asm's line, in the
// caller's callees and in the callee's callers: an operand call (the
// irqstack shape), an ALTERNATIVE's operands (the called one and its
// replacement), and a literal name. Before (b) the asm sites had no edge.
// CFLAGS: -O1
// LOG: asm calls wired by register: 3 sites, 4 callees \(by operand: 3, by literal name: 1\);
struct S { void (*f)(void); };
void fa(void) {}

__attribute__((used, noinline)) static void handler(struct S *s) {
  s->f(); // CHECK: fa
}
__attribute__((used, noinline)) static void alt_a(struct S *s) {}
__attribute__((used, noinline)) static void alt_b(struct S *s) {}
__attribute__((used, noinline)) void lit(struct S *s) {}

struct S R;

int main(void) {
  R.f = fa;
  struct S *p = &R;
  asm volatile("movq %[arg], %%rdi\n\tcall %P[fn]" : : [fn] "i"(handler), [arg] "r"(p) : "rdi", "rsi", "rax", "rcx", "rdx", "r8", "r9", "r10", "r11", "memory"); // CGEDGE: main handler
  asm volatile("call %P[a]" : "+D"(p) : [a] "i"(alt_a), [b] "i"(alt_b) : "rsi", "rax", "rcx", "rdx", "r8", "r9", "r10", "r11", "memory"); // CGEDGE: main alt_a alt_b
  asm volatile("call lit" : : "D"(p) : "rsi", "rax", "rcx", "rdx", "r8", "r9", "r10", "r11", "memory"); // CGEDGE: main lit
  return 0;
}
