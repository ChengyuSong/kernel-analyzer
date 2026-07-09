/* harfbuzz WouldApply-style pattern: function pointers packed into small
 * context structs as literals, structs passed (by pointer and by value)
 * into a shared helper that makes the indirect call. A sound analysis
 * must see all four handlers at the icall. Mirrors the fs13 miss found
 * by the source audit (would_match_input / ContextApplyFuncs). */

typedef int (*match_func_t)(int, const void *);

struct apply_funcs { match_func_t match; };
struct chain_funcs { match_func_t match[3]; };

int match_glyph(int g, const void *d) { return g == 1; }
int match_class(int g, const void *d) { return g == 2; }
int match_coverage(int g, const void *d) { return g == 3; }
int match_always(int g, const void *d) { return 1; }

__attribute__((noinline)) int would_match(match_func_t f, int g,
                                          const void *d) {
  return f(g, d); /* icall: must resolve all four match_* */
}

__attribute__((noinline)) int ctx_lookup(const struct apply_funcs *c, int g) {
  return would_match(c->match, g, 0);
}

__attribute__((noinline)) int chain_lookup(const struct chain_funcs *c,
                                           int g) {
  return would_match(c->match[1], g, 0);
}

/* Constant-initialized locals compile to a private __const global plus a
 * memcpy onto the stack slot — the exact harfbuzz lookup_context pattern
 * (fs mode missed these callees; the runtime-store variant below worked). */
struct wrap { struct apply_funcs funcs; const void *data; };

__attribute__((noinline)) int const_ctx_lookup(const struct wrap *w, int g) {
  return would_match(w->funcs.match, g, w->data);
}

int use_const(int g) {
  struct wrap w = {{match_coverage}, 0};
  return const_ctx_lookup(&w, g);
}

int use_const2(int g) {
  struct wrap w = {{match_glyph}, 0};
  return const_ctx_lookup(&w, g);
}

int use(int which, int g) {
  struct apply_funcs a = {which ? match_glyph : match_class};
  struct chain_funcs c = {{match_always, match_coverage, match_always}};
  return ctx_lookup(&a, g) + chain_lookup(&c, g) + use_const(g) +
         use_const2(g);
}

int main(int argc, char **argv) {
  (void)argv;
  return use(argc & 1, argc);
}
