// CFLAGS: -O2
// Plan 3.55 R1, negative: a word stored as ptrtoint(p) + 8 is not a tagged
// pointer (8 reaches past the tag bits into the address): the field fails,
// with the site and the shape named.
// LOG: LinkWord: struct.cell\+0: FAIL
// LOG: FAIL struct.cell\+0: store: (add|or) of a constant >= 8 at put:
struct cell { unsigned long w; };
void put(struct cell *c, char *p) { c->w = (unsigned long)p + 8; }
char *get(struct cell *c) { return (char *)(c->w & ~3UL); }
struct cell c0;
char buf[16];
int main(void) {
  put(&c0, buf);
  return get(&c0) == buf;
}
