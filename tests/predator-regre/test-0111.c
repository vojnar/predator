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
#ifdef PREDATOR
    pi->data = create_low();
    pi->data->next = create_low();
#else
    // a special quirk for tools that are not ready for real-world code sources
    struct node_low *help = create_low();
    pi->data = help;
    help->next = create_low();
#endif

    return pi;
}

struct node_top* create_sll(void)
{
    struct node_top *sll = alloc1();
    struct node_top *now = sll;

    // NOTE: running this on bare metal may cause the machine to swap a bit
    int i;
    for (i = 1; i; ++i) {
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

    return 0;
}

/**
 * @file test-0111.c
 *
 * @brief alternation of test-0110
 *
 * - two distinct types are used, which makes it harder to digest
 *
 * @attention
 * This description is automatically imported from tests/predator-regre/README.
 * Any changes made to this comment will be thrown away on the next import.
 */
