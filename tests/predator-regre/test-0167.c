#include <verifier-builtins.h>
#include <stdlib.h>

#define I_WANT_TO_SEE_5X_SPEEDUP 0

struct node {
    struct node     *next;
};

struct list {
    struct node     *slist;
    struct list     *next;
};

static void merge_single_node(struct node ***dst,
                              struct node **data)
{
    // pick up the current item and jump to the next one
    struct node *node = *data;
    *data = node->next;
    node->next = NULL;

    // insert the item into dst and move cursor
    **dst = node;
    *dst = &node->next;
}

static void merge_pair(struct node **dst,
                       struct node *sub1,
                       struct node *sub2)
{
    // merge two sorted sub-lists into one
    while (sub1 || sub2) {
        if (!sub2 || (sub1 && ___sl_get_nondet_int()))
            merge_single_node(&dst, &sub1);
        else
            merge_single_node(&dst, &sub2);
    }
}

static struct list* seq_sort_core(struct list *data)
{
    struct list *dst = NULL;

    while (data) {
        struct list *next = data->next;
        if (!next) {
            // take any odd/even padding as it is
            data->next = dst;
            dst = data;
            break;
        }

        // take the current sub-list and the next one and merge them into one
        merge_pair(&data->slist, data->slist, next->slist);
        data->next = dst;
        dst = data;

        // free the just processed sub-list and jump to the next pair
        data = next->next;
        free(next);
    }

    return dst;
}

static void seq_sort(struct list **data)
{
    struct list *list = *data;

    // do O(log N) iterations
    while (list && list->next) {
        ___sl_plot(NULL);
        list = seq_sort_core(list);
#if I_WANT_TO_SEE_5X_SPEEDUP
        *data = list;
#endif
    }

    *data = list;
}

int main()
{
    struct list *data = NULL;
    while (___sl_get_nondet_int()) {
        struct node *node = malloc(sizeof *node);
        if (!node)
            abort();

        node->next = NULL;

        struct list *item = malloc(sizeof *item);
        if (!item)
            abort();

        item->slist = node;
        item->next = data;
        data = item;
    }

    seq_sort(&data);

    while (data) {
        struct list *next = data->next;

        struct node *node = data->slist;
        while (node) {
            struct node *snext = node->next;
            free(node);
            node = snext;
        }

        free(data);
        data = next;
    }

    return 0;
}

/**
 * @file test-0167.c
 *
 * @brief state explosion minimal example taken from test-0124
 *
 * @attention
 * This description is automatically imported from tests/predator-regre/README.
 * Any changes made to this comment will be thrown away on the next import.
 */
