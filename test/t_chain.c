/* Keyed pair-channel atoms (task #29): the notifier shape. The fn is
 * NOT a call parameter — it lives in a const-initialized block global;
 * registration links the block into a chain keyed by a head global;
 * a separate dispatcher walks the chain and calls
 * n->call(n, val, data) with dispatch-time data.
 *
 * With t_chain.summ (CHAINREG on chain_register, CHAINCALL on
 * chain_call): per-key pairing — cb1 is a callee of the ch1 dispatch
 * site with p<-&d1 and self<-&nb1, cb2 of the ch2 site with &d2 —
 * inner icalls exact: cb1->f1, cb2->f2 (2 pairs); the dispatcher's
 * own icall drains (invocations attributed at the dispatch sites).
 * Without: chain icall {cb1,cb2}, p pooled {&d1,&d2} -> 6 pairs.
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
static struct chain ch1, ch2;

int main(void) {
  chain_register(&ch1, &nb1);
  chain_register(&ch2, &nb2);
  chain_call(&ch1, 1, &d1);
  chain_call(&ch2, 2, &d2);
  return 0;
}
