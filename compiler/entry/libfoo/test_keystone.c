#include <stdio.h>
#include <keystone/keystone.h>

// separate assembly instructions by ; or \n
#define CODE "INC ecx; DEC edx"

int main(int argc, char **argv)
{
    ks_engine *ks;
    ks_err err;
    size_t count;
    unsigned char *encode;
    size_t size;

    err = ks_open(KS_ARCH_X86, KS_MODE_32, &ks);
    if (err != KS_ERR_OK) {
        printf("ERROR: failed on ks_open(), quit\n");
        return -1;
    }

    if (ks_asm(ks, CODE, 0, &encode, &size, &count) != KS_ERR_OK) {
        printf("ERROR: ks_asm() failed & count = %lu, error = %u\n",
                count, ks_errno(ks));
    } else {
        size_t i;

        printf("%s = ", CODE);
        for (i = 0; i < size; i++) {
            printf("%02x ", encode[i]);
        }
        printf("\n");
        printf("Compiled: %lu bytes, statements: %lu\n", size, count);
    }

    // NOTE: free encode after usage to avoid leaking memory
    ks_free(encode);

    // close Keystone instance when done
    ks_close(ks);

    return 0;
}
