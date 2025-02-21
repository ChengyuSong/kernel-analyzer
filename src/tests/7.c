// RUN: %clang -O0 -g -emit-llvm -c %s -o %t.bc
// RUN: %KAMain %t.bc --dump-distance=%t.distance.txt --dump-policy=%t.policy.txt --target-list=%S/BBtargets7.txt --entry-list=%S/entry.txt
// RUN: diff %t.distance.txt %S/ground_truth_distance7.txt
// RUN: diff %t.policy.txt %S/ground_truth_policy7.txt

/*
   Simple C program for reachability analysis testing with recursive calls.
   This test checks recursive calls by computing the factorial of a number.

   The expected outcome is that KAMain, when run over the generated LLVM bitcode,
   will produce a distance file and a policy file that match the provided ground truth.
*/

int factorial(int n) {
    if (n <= 1)
        return 1;
    else
        return n * factorial(n - 1);
}

int main() {
    int result = factorial(5);
    return result;
}
