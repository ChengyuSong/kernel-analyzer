#ifndef KA_BASELINE_GRAMMAR_H
#define KA_BASELINE_GRAMMAR_H

// The points-to grammar the CFL baseline hands to GraCFL. It is also the
// specification the flows-to solver is proved against (proof/lean, and
// ka::valleyComponents in src/lib/SCC.h for the presolve's V).

#include <string>
#include <vector>

// Default P2 grammar for CFL-reachability analysis
static const std::vector<std::string> DefaultP2Grammar = {
  "M DV d",
  "DV -d V",
  "V MAM AMs",
  "MAM MAs Mq",
  "Mq",
  "Mq M",
  "MAs",
  "MAs MAs MA",
  "MA Mq -a",
  "AMs",
  "AMs AMs AM",
  "AM a Mq"
};

// Field-sensitive extension: shift-indexed valley grammar over Z_P u {T}.
// Field steps are residues mod P (P = numBuckets): a GEP of byte offset k
// emits terminal f<r> with r = k mod P; signed offsets fold into the
// residue, so container_of's negative steps compose correctly with
// positive ones (down 8 then down 8 matches flat down 16 when 8+8 ≡ 16).
// fx is the absorbing unknown-shift element T (variable-offset fallback).
//
// Chain nonterminals, indexed by net shift c:
//   Dn<c> ::= eps(c=0) | Dn<a> DS<b>    with c = (a+b) mod P; T absorbs
//   Up<c> ::= eps(c=0) | US<b> Up<a>
//   DS0 ::= a | M ; DS<r> ::= f<r> ; DSX ::= fx     (down steps)
//   US0 ::= -a | M ; US<r> ::= -f<r> ; USX ::= -fx  (up steps)
// Valley assembly — only net-zero and unknown are ever consumed:
//   V  ::= Up<a> Dn<a>  for every a  (exact shifts agree = same position)
//   VX ::= UpX Dn<b> | Up<a> DnX | UpX DnX          (unknown may be zero)
//   M  ::= -d V d | -d VX d
// V keeps its name so every existing consumer (presolve V-SCC, snapshots,
// resolution) works unchanged. Exact-mismatch pairs (a != b) get NO rule:
// provably different positions never alias.
inline std::vector<std::string> buildP2GrammarWithFields(unsigned numBuckets) {
  if (numBuckets == 0)
    return DefaultP2Grammar;
  const unsigned P = numBuckets;
  std::vector<std::string> g = {
    "M DV d",
    "DV -d V",
    "Mq",
    "Mq M",
    "DVX -d VX",
    "M DVX d",
  };
  auto n = [](const char *base, unsigned i) {
    return std::string(base) + std::to_string(i);
  };
  g.push_back("DS0 a");
  g.push_back("DS0 M");
  g.push_back("US0 -a");
  g.push_back("US0 M");
  g.push_back("DSX fx");
  g.push_back("USX -fx");
  for (unsigned r = 0; r < P; r++) {
    g.push_back(n("DS", r) + " f" + std::to_string(r));
    g.push_back(n("US", r) + " -f" + std::to_string(r));
  }
  g.push_back("Dn0");
  g.push_back("Up0");
  for (unsigned a = 0; a < P; a++)
    for (unsigned b = 0; b < P; b++) {
      unsigned c = (a + b) % P;
      g.push_back(n("Dn", c) + " " + n("Dn", a) + " " + n("DS", b));
      g.push_back(n("Up", c) + " " + n("US", b) + " " + n("Up", a));
    }
  for (unsigned a = 0; a < P; a++) {
    g.push_back("DnX " + n("Dn", a) + " DSX");
    g.push_back("DnX DnX " + n("DS", a));
    g.push_back("UpX USX " + n("Up", a));
    g.push_back("UpX " + n("US", a) + " UpX");
  }
  g.push_back("DnX DnX DSX");
  g.push_back("UpX USX UpX");
  for (unsigned a = 0; a < P; a++) {
    g.push_back("V " + n("Up", a) + " " + n("Dn", a));
    g.push_back("VX UpX " + n("Dn", a));
    g.push_back("VX " + n("Up", a) + " DnX");
  }
  g.push_back("VX UpX DnX");
  return g;
}

#endif
