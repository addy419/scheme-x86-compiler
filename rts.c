#include <stdio.h>
#include <stdlib.h>

#define FIXNUM_MASK     3
#define FIXNUM_TAG      0
#define FIXNUM_SHIFT    2

#define CHAR_MASK       0xff
#define CHAR_SHIFT      8
#define CHAR_TAG        7

#define BOOL_MASK       0xff
#define BOOL_SHIFT      8
#define BOOL_TAG        15

#define PTR_MASK        7
#define PAIR_TAG        1
#define VEC_TAG         2
#define STR_TAG         3
#define SYM_TAG         5
#define CLOSURE_TAG     6

#define HEAP_SIZE 0x400000

__attribute__((__cdecl__))
extern int scheme_entry(void *heap);

void show(int x) {
    if((x & FIXNUM_MASK) == FIXNUM_TAG) {
        // integer
        printf("%d", x >> FIXNUM_SHIFT);
    } else if((x & CHAR_MASK) == CHAR_TAG) {
        // character
        printf("#\\%c", (char)(x >> CHAR_SHIFT));
    } else if((x & BOOL_MASK) == BOOL_TAG) {
        // boolean
        if((x >> BOOL_SHIFT) != 0) {
            printf("#t");
        } else {
            printf("#f");
        }
    } else if ((x & PTR_MASK) == PAIR_TAG) {
        // pair
        int *ptr = (int*) (x - PAIR_TAG);

        if(ptr == NULL) {
            printf("()");
        }
        else {
            int car = ptr[0];
            int cdr = ptr[1];
            putchar('(');
            show(car);

            while((cdr & PTR_MASK) == PAIR_TAG) {
                ptr = (int*) (cdr - PAIR_TAG);
                if(ptr == NULL) break;

                car = ptr[0];
                cdr = ptr[1];
                putchar(' ');
                show(car);
            }

            if((cdr & PTR_MASK) != PAIR_TAG) {
                printf(" . ");
                show(cdr);
            }

            putchar(')');
        }
    } else if((x & PTR_MASK) == STR_TAG) {
        int *ptr = (int*) (x - STR_TAG);
        int length = *ptr;
        char *str = (char*) (ptr + 1);

        putchar('"');
        while(length != 0) {
            putchar(*str++);
            length -= 1;
        }
        putchar('"');
    } else if((x & PTR_MASK) == VEC_TAG) {
        int *ptr = (int*) (x - VEC_TAG);
        int length = *ptr++;

        printf("#(");
        while(length != 1) {
            show(*ptr++);
            putchar(' ');
            length -= 1;
        }
        show(*ptr);
        putchar(')');
    }
}

/** 
 * This just calls a function named scheme_entry that our compiler generates, then prints the integer that it returns.
 * The __attribute__((__cdecl__)) part is a GCC-specific syntax extension that tells the compiler to use the "cdecl" calling convention when executing the function.
 * That means arguments are pushed onto the stack from right to left, and the return value is stored (since this is a 32-bit program) in the eax register.
 * Our assembly just has to read any arguments it needs, run the program, store the result in eax, then return back to the caller and make sure none of the other registers are modified.
**/
int main(int argc, const char **argv) {
    void *heap = aligned_alloc(8, HEAP_SIZE);
    int val = scheme_entry(heap);
    show(val);
    printf("\n");
    free(heap);
    return 0;
}
