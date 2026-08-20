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
