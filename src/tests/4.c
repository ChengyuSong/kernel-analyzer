// RUN: %clang -O0 -g -emit-llvm -c %s -o %t.bc
// RUN: %KAMain %t.bc --dump-distance=%t.distance.txt --dump-policy=%t.policy.txt --target-list=%S/BBtargets4.txt --entry-list=%S/entry.txt
// RUN: diff %t.distance.txt %S/ground_truth_distance4.txt
// RUN: diff %t.policy.txt %S/ground_truth_policy4.txt

/*
   Simple C program for reachability analysis testing with indirect call targets.

   The expected outcome is that KAMain, when run over the generated LLVM bitcode,
   will produce a distance file and a policy file that match the provided ground truth.
*/

int target1() {
  return 1;
}

int target2() {
  return 2;
}

int indirect_call(int (*fp)()) {
  return fp();
}

int main() {
  int cond = 1;
  // Choose the target based on a condition (here, cond is always true).
  int (*func_ptr)() = cond ? target1 : target2;
  return indirect_call(func_ptr);
}
