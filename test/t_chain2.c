/* Composition lift for keyed pair-channels (task #29): reg_wrap
 * forwards its block formal into chain_register with a CONSTANT key
 * (the register_reboot_notifier shape). --cfl-confirm-invoke must
 * derive `reg_wrap CHAINREG(@ch1,*arg0+0,f0)`, after which the
 * wrapper-mediated registration pairs exactly like a direct one.
 *
 * Expected with t_chain.summ + --cfl-confirm-invoke:
 *   cb1->f1 (via lifted wrapper on ch1), cb2->f2 (direct on ch2),
 *   dispatcher icall drained. Without the lift, nb1 rides the pooled
 *   channel: chain icall {cb1,cb2}, cb1/cb2 x {d1,d2} smear.
 */
struct nb {
  int (*call)(struct nb *, long, void *);
  struct nb *next;
};
struct chain {
  struct nb *head;
};

__attribute__((noinline, weak)) int chain_register(struct chain *c,
                                                   struct nb *n) {
  n->next = c->head;
  c->head = n;
  return 0;
}

__attribute__((noinline, weak)) int chain_call(struct chain *c, long val,
                                               void *data) {
  for (struct nb *n = c->head; n; n = n->next)
    n->call(n, val, data);
  return 0;
}

static struct chain ch1, ch2;

__attribute__((noinline, weak)) int reg_wrap(struct nb *n) {
  return chain_register(&ch1, n); /* constant key, forwarded block */
}

struct D {
  void (*fp)(void);
};

static void f1(void) {}
static void f2(void) {}
static struct D d1 = { f1 };
static struct D d2 = { f2 };

static int cb1(struct nb *n, long a, void *p) {
  ((struct D *)p)->fp(); /* expect f1 only */
  return 0;
}
static int cb2(struct nb *n, long a, void *p) {
  ((struct D *)p)->fp(); /* expect f2 only */
  return 0;
}

static struct nb nb1 = { cb1, 0 };
static struct nb nb2 = { cb2, 0 };

int main(void) {
  reg_wrap(&nb1);
  chain_register(&ch2, &nb2);
  chain_call(&ch1, 1, &d1);
  chain_call(&ch2, 2, &d2);
  return 0;
}
