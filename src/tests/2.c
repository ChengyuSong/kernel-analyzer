// RUN: %clang -O0 -g -emit-llvm -c %s -o %t.bc
// RUN: %KAMain %t.bc --dump-distance=%t.distance.txt --dump-policy=%t.policy.txt --target-list=%S/BBtargets2.txt --entry-list=%S/entry.txt
// RUN: diff %t.distance.txt %S/ground_truth_distance2.txt
// RUN: diff %t.policy.txt %S/ground_truth_policy2.txt

/*
   Simple C program for reachability analysis testing with if-else.

   The expected outcome is that KAMain, when run over the generated LLVM bitcode,
   will produce a distance file and a policy file that match the provided ground truth.
*/

int foo() {
  int x = 0;
  int y = 1;
  if (x < y) {
    return 1;
  } else {
    return 2;
  }
}

int main() {
  return foo();
}
