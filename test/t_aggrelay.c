/* Regression: first-class aggregate ({ptr,ptr}) call args and returns must
 * carry pointer identity through handleCall (harfbuzz closure-relay bug).
 * Pattern: fptr -> struct pair returned BY VALUE -> passed BY VALUE -> icall.
 * Expect 2 ICALL pairs (h1, h2) in both K=0 and K=13 flows-to modes. */

typedef struct pair {
  void *fst;
  void *snd;
} pair;

static int h1(int x) { return x + 1; }
static int h2(int x) { return x + 2; }

typedef int (*handler_t)(int);

/* aggregate RETURN: {ptr,ptr} comes back in registers as a literal struct */
static pair wrap(handler_t f, void *ctx) {
  pair p;
  p.fst = (void *)f;
  p.snd = ctx;
  return p;
}

/* aggregate ARG: {ptr,ptr} passed by value as a literal struct */
static int invoke(pair p, int v) {
  handler_t f = (handler_t)p.fst;
  return f(v);
}

/* relay hop: aggregate flows through another by-value call + return */
static pair relay(pair p) { return p; }

int data1 = 1, data2 = 2;

int main(void) {
  pair a = wrap(h1, &data1);
  pair b = wrap(h2, &data2);
  int r = invoke(relay(a), 10);
  r += invoke(relay(b), 20);
  return r;
}
