// RUN: %clang -O0 -g -emit-llvm -c %s -o %t.bc
// RUN: %KAMain %t.bc --dump-distance=%t.distance.txt --dump-policy=%t.policy.txt --target-list=%S/BBtargets6.txt --entry-list=%S/entry.txt
// RUN: diff %t.distance.txt %S/ground_truth_distance6.txt
// RUN: diff %t.policy.txt %S/ground_truth_policy6.txt

/*
   Simple C program for reachability analysis testing with nested if statements.

   The expected outcome is that KAMain, when run over the generated LLVM bitcode,
   will produce a distance file and a policy file that match the provided ground truth.
*/

int target1() {return 0;}
int target2() {return 0;}
int target3() {return 0;}

int nested_if(int x, int y, int z) {
    if (x > 0) {
        if (y > 0) {
            if (z > 0) {
                target1();
                return 1;
            } else {
                target2();
                return 2;
            }
        } else {
            if (z > 0) {
                target2();
                return 3;
            } else {
                target3();
                return 4;
            }
        }
    } else {
        if (y > 0) {
            target3();
            return 5;
        } else {
            target1();
            return 6;
        }
    }
}

int main(int argc, char *argv[]) {
    int result = nested_if(argc, argc + 1, argc + 2);
    return result;
}