// RUN: %clang -O0 -g -emit-llvm -c %s -o %t.bc
// RUN: %KAMain %t.bc --dump-distance=%t.distance.txt --dump-policy=%t.policy.txt --target-list=%S/BBtargets3.txt --entry-list=%S/entry.txt
// RUN: diff %t.distance.txt %S/ground_truth_distance3.txt
// RUN: diff %t.policy.txt %S/ground_truth_policy3.txt

/*
   Simple C program for reachability analysis testing with a loop.

   The expected outcome is that KAMain, when run over the generated LLVM bitcode,
   will produce a distance file and a policy file that match the provided ground truth.
*/

int loop() {
  int sum = 0;
  for (int i = 0; i < 10; i++) {
      if (sum > 5)
        break;
      else
        sum += i;
  }
  return sum;
}

int main() {
  return loop();
}