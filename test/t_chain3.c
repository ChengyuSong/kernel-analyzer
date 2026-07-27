struct nb { int (*call)(struct nb *, long, void *); struct nb *next; };
struct chain { struct nb *head; };
__attribute__((noinline, weak)) int chain_register(struct chain *c, struct nb *n) {
  n->next = c->head; c->head = n; return 0;
}
__attribute__((noinline, weak)) int chain_call(struct chain *c, long val, void *data) {
  for (struct nb *n = c->head; n; n = n->next) n->call(n, val, data);
  return 0;
}
static struct chain ch1;
__attribute__((noinline, weak)) int reg_wrap(struct nb *n) { return chain_register(&ch1, n); }
struct D { void (*fp)(void); };
static void f1(void) {}
static struct D d1 = { f1 };
static int cb1(struct nb *n, long a, void *p) { ((struct D *)p)->fp(); return 0; }
static struct nb nb1 = { cb1, 0 };
int main(void) { reg_wrap(&nb1); chain_call(&ch1, 1, &d1); return 0; }
