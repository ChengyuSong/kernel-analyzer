// RUN: %clang -O0 -g -emit-llvm -c %s -o %t.bc
// RUN: %KAMain %t.bc --dump-distance=%t.distance.txt --dump-policy=%t.policy.txt --target-list=%S/BBtargets1.txt --entry-list=%S/entry.txt
// RUN: diff %t.distance.txt %S/ground_truth_distance1.txt
// RUN: diff %t.policy.txt %S/ground_truth_policy1.txt

/* 
   Simple C program for reachability analysis testing.

   This program contains two functions:
     - foo() calls bar()
     - main() calls foo()

   The expected outcome is that KAMain, when run over the generated LLVM bitcode,
   will produce a distance file and a policy file that match the provided ground truth.
*/

int bar() {
  return 0;
}

int foo() {
  return bar();
}

int main() {
  return foo();
}
