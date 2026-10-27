// SO (Fable 2026-10-27): an indirect call applies one summary row per
// target at one site. Two targets, each NOOP-inferred with its own label
// atom 0 on arg0 +0 (tcpdump signature_verify's clear-checksum call:
// isis_clear_checksum_lifetime, rsvp_clear_checksum): two label sinks at
// one site. Their names carry the summarized function ("label sink of
// clear_a atom 0 arg0 +0 at verify::call ..."), so the node-facts writer,
// which asserts that no two nodes share a name, passes (before SO: "two
// nodes share the name 'label sink of atom 0 arg0 +0 at verify::call'").
// KAFLAGS: --cfl-cell-node-facts=/dev/null
// LOG: NoopProp: OK clear_a
// LOG: NoopProp: OK clear_b
// NOLOG: share the name
struct hdr_a { unsigned char kind; unsigned char sum[2]; unsigned short life; };
struct hdr_b { unsigned short len; unsigned char sum[2]; };

void clear_a(void *p) {
  struct hdr_a *h = p;
  h->sum[0] = 0;
  h->sum[1] = 0;
  h->life = 0;
}

void clear_b(void *p) {
  struct hdr_b *h = p;
  h->sum[0] = 0;
  h->sum[1] = 0;
}

int verify(void (*clear)(void *), unsigned char *buf) {
  clear(buf);
  return buf[0];
}

int main(int argc, char **argv) {
  unsigned char buf[16] = {0};
  return verify(argc > 1 ? clear_a : clear_b, buf);
}
