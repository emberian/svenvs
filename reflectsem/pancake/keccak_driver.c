/* Run the exported Pancake Keccak-f[1600] on one 200-byte state.
 * stdin: 25 little-endian words. stdout: the status word, then the state.
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

extern void *cml_heap, *cml_stack, *cml_stackend;
extern void cml_main(void);
extern uint64_t keccakF1600(uint64_t *state);

void cml_clear(void) {}
void cml_err(int code) { fprintf(stderr, "CakeML runtime error %d\n", code); exit(1); }

int main(void) {
    static uint64_t runtime[2 * 1024 * 1024];
    uint64_t state[25];
    if (fread(state, 8, 25, stdin) != 25 || fgetc(stdin) != EOF) {
        fprintf(stderr, "expected exactly 200 bytes\n");
        return 2;
    }
    cml_heap = runtime;
    cml_stack = runtime + 1024 * 1024;
    cml_stackend = runtime + 2 * 1024 * 1024;
    cml_main();
    uint64_t status = keccakF1600(state);
    return fwrite(&status, 8, 1, stdout) != 1 || fwrite(state, 8, 25, stdout) != 25 ||
           fflush(stdout) != 0;
}
