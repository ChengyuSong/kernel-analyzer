// RUN: %clang -O0 -g -emit-llvm -c %s -o %t.bc
// RUN: %KAMain %t.bc --dump-distance=%t.distance.txt --dump-policy=%t.policy.txt --target-list=%S/BBtargets5.txt --entry-list=%S/entry.txt
// RUN: diff %t.distance.txt %S/ground_truth_distance5.txt
// RUN: diff %t.policy.txt %S/ground_truth_policy5.txt

/*
   Simple C program for reachability analysis testing with return edges.

   The expected outcome is that KAMain, when run over the generated LLVM bitcode,
   will produce a distance file and a policy file that match the provided ground truth.
*/

int target() {
  return 0;
}

int somethingelse() {
  return 0;
}

void foo(int i) {
  if (i)
    target();
  else
    somethingelse();
}

void bar() {
  target();
}

int main() {
  int i = 0;
  foo(i);
  bar();
  return 0;
}
