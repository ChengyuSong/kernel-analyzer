struct ops { void (*fn)(void); int pad; };
struct box { long x; struct ops *o; };
/* leaf: plain field store */
void set_ops(struct ops **slot, struct ops *o) { *slot = o; }
/* mid: composes leaf through &b->o  => ST(*arg0@8<-arg1) */
void box_set(struct box *b, struct ops *o) { set_ops(&b->o, o); }
/* top: composes mid => same atom, two hops */
void box_init(struct box *b, struct ops *o) { box_set(b, o); }
/* ret-composition: leaf LD + caller returns it => LD(ret<-*arg0@8) */
struct ops *get_ops(struct box *b) { return b->o; }
struct ops *box_get(struct box *b) { return get_ops(b); }
/* --- v2.2 rule micros --- */
struct seqb { unsigned long len; char *bufp; char buf[64]; struct ops *o2; };
/* interior-value self store (seq_buf_init shape) => ST(*arg0@8<-arg0@16) */
void seqb_init(struct seqb *s) { s->bufp = s->buf; }
/* unsafe extern callee, literal+scalar args only (printk shape) */
extern int myprintf(const char *fmt, ...);
/* NOOP-provable leaf: consumes ptr, returns count */
static int __attribute__((noinline)) mylen(const char *p) {
  int n = 0; while (p[n]) n++; return n;
}
/* rule A(narrow)+C: calls unsafe myprintf with literal, stores clean
   NOOP-callee int ret into own field => still NOOP+atom provable
   (atoms: none needed; len store is int, clean) */
void seqb_log(struct seqb *s, const char *msg) {
  myprintf("seqb: %d\n", 42);
  s->len = (unsigned long)mylen(msg);
}
/* composes seqb_init AND seqb_log => atoms of init only */
void seqb_setup(struct seqb *s, const char *m) { seqb_init(s); seqb_log(s, m); }
/* --- v2.3 int-domain micros --- */
struct sbuf { char *bp; unsigned long size; unsigned long len; };
/* self-slot += of NOOP-callee ret => NOOP-provable (rule C2) */
void sb_add(struct sbuf *s, const char *m) { s->len += mylen(m); }
/* cross-field int slot copy => MV(*arg0@16<-*arg0@8) */
void sb_overflow(struct sbuf *s) { s->len = s->size + 1; }
/* int slot ret => LD(ret<-*arg0@16) */
unsigned long sb_len(struct sbuf *s) { return s->len + 1; }
/* composes: calls sb_overflow (atoms) + sb_add (noop) */
void sb_flush(struct sbuf *s, const char *m) { sb_add(s, m); sb_overflow(s); }
/* --- v2.2b global-container micros --- */
static struct ops *g_cur;
static struct box g_box;
void set_gcur(struct ops *o) { g_cur = o; }              /* ST(*@g_cur<-arg0) */
struct ops *get_gcur(void) { return g_cur; }             /* LD(ret<-*@g_cur) */
void set_gbox_ops(struct ops *o) { g_box.o = o; }        /* ST(*@g_box@8<-arg0) */
void wrap_setg(struct ops *o) { set_gcur(o); }           /* composes global ST */
struct box *addr_gbox(void) { return &g_box; }           /* ALIAS(ret<-@g_box) */
void cross_g(struct box *b) { b->o = g_cur; }            /* MV(*arg0@8<-*@g_cur) */
