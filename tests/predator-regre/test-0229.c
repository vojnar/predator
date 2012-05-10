#include <stdlib.h>
#include <verifier-builtins.h>

struct item {
    struct item *next;
    struct item *data;
};

static void append(struct item **plist)
{
    struct item *item = malloc(sizeof *item);
    item->next = *plist;

    // shared data
    item->data = (item->next)
        ? item->next->data
        : malloc(sizeof *item);

    *plist = item;
}

int main()
{
    struct item *list = NULL;

    // create SLS 1+
    do
        append(&list);
    while (___sl_get_nondet_int());

    while (list) {
        struct item *next = list->next;
        // NOTE: the following #if causes a memleak
#if 0
        if (!next)
            free(list->data);
#endif
        ___sl_plot(NULL);

        free(list);
        list = next;
    }

    return 0;
}

/**
 * @file test-0229.c
 *
 * @brief non-artificial variant of test-0225.c
 *
 * @attention
 * This description is automatically imported from tests/predator-regre/README.
 * Any changes made to this comment will be thrown away on the next import.
 */
