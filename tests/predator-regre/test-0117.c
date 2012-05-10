#include <verifier-builtins.h>
#include <stdlib.h>

struct node_top {
    struct node_top *next;
    struct node_low *data;
};

struct node_low {
    struct node_low *next;
};

struct node_top* create_top(void)
{
    struct node_top *ptr = malloc(sizeof *ptr);
    if (!ptr)
        abort();

    ptr->next = NULL;
    ptr->data = NULL;

    return ptr;
}

struct node_low* create_low(void)
{
    struct node_low *ptr = malloc(sizeof *ptr);
    if (!ptr)
        abort();

    ptr->next = NULL;

    return ptr;
}

struct node_top* alloc1(void)
{
    struct node_top *pi = create_top();
    pi->data = create_low();
    return pi;
}

struct node_top* alloc2(void)
{
    struct node_top *pi = create_top();
    pi->data = create_low();
    pi->data->next = create_low();

    return pi;
}

struct node_top* alloc3(void)
{
    struct node_top *pi = create_top();
    pi->data = create_low();
    pi->data->next = create_low();
    pi->data->next->next = create_low();

    return pi;
}

struct node_top* create_sll(void)
{
    struct node_top *sll = alloc1();
    struct node_top *now = sll;

    // NOTE: running this on bare metal may cause the machine to swap a bit
    int i;
    for (i = 1; i; ++i) {
        now->next = alloc3();
        now = now->next;
        now->next = create_top();
        now = now->next;
        now->next = alloc2();
        now = now->next;
        now->next = alloc1();
        now = now->next;
    }

    return sll;
}

int main()
{
    struct node_top *sll = create_sll();
    ___sl_plot(NULL);

    // destroy the structure
    while (sll) {
        struct node_top *next = sll->next;

        struct node_low *data = sll->data;
        while (data) {
            struct node_low *data_next = data->next;
            free(data);
            data = data_next;
        }

        free(sll);
        sll = next;
    }

    return 0;
}

/**
 * @file test-0117.c
 *
 * @brief error-free variant of test-0116 (only a destructor added)
 *
 * @attention
 * This description is automatically imported from tests/predator-regre/README.
 * Any changes made to this comment will be thrown away on the next import.
 */
