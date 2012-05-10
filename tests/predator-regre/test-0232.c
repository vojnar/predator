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

    // create SLS 0+
    if (list) {
        struct item *next = list->next;

        // free shared data
        free(list->data);

        free(list);
        list = next;
    }

    // shared data is already freed when entering the loop
    ___sl_plot(NULL);

    while (list) {
        struct item *next = list->next;
        if (!next)
            // this causes a double free
            free(list->data);

        free(list);
        list = next;
    }

    return 0;
}

/**
 * @file test-0232.c
 *
 * @brief merge of test-0230 and test-0231 resulting in double free
 *
 * @attention
 * This description is automatically imported from tests/predator-regre/README.
 * Any changes made to this comment will be thrown away on the next import.
 */
