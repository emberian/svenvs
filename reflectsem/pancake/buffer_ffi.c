/* Transfer one complete Keccak state through the CakeML basis FFI. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

void ffiinput(unsigned char *config, long clen, unsigned char *buffer, long len) {
    (void)config;
    if (clen != 0 || len != 200 || fread(buffer, 1, 200, stdin) != 200)
        exit(2);
}

void ffioutput(unsigned char *config, long clen, unsigned char *buffer, long len) {
    const unsigned char zero[8] = {0};
    if (clen != 8 || memcmp(config, zero, 8) != 0 ||
        len != 200 || fwrite(buffer, 1, 200, stdout) != 200)
        exit(3);
}
