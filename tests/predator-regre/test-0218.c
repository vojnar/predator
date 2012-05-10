#include <verifier-builtins.h>

#include <stdlib.h>
#include <string.h>

typedef void *list_t[2];
typedef list_t *list_p;
typedef enum {
    LIST_BEG,
    LIST_END
} end_point_t;

typedef void *item_t[2];
typedef item_t *item_p;
typedef enum {
    ITEM_PREV,
    ITEM_NEXT
} direction_t;

int is_empty(list_p list)
{
    int no_beg = !(*list)[LIST_BEG];
    int no_end = !(*list)[LIST_END];

    ___SL_ASSERT(no_beg == no_end);

    return no_beg;
}

item_p create_item(end_point_t at, item_p *cursor)
{
    item_p item = malloc(sizeof *item);
    if (!item)
        abort();

    direction_t term_field, link_field;

    switch (at) {
        case LIST_BEG:
            link_field = ITEM_NEXT;
            term_field = ITEM_PREV;
            break;

        case LIST_END:
            link_field = ITEM_PREV;
            term_field = ITEM_NEXT;
            break;
    }

    /* seek random position */
    while ((*cursor) && (**cursor)[link_field] && ___sl_get_nondet_int())
        cursor = (item_p *) &(**cursor)[link_field];

    item_p link = *cursor;
    (*item)[link_field] = link;
    (*item)[term_field] = link ? (*link)[term_field] : NULL;

    ___sl_plot(NULL);

    if (link)
        (*link)[term_field] = item;

    *cursor = item;
    return item;
}

void append_one(list_p list, end_point_t to)
{
    item_p *cursor = (item_p *) &(*list)[to];
    item_p item = create_item(to, cursor);

    if (NULL == (*item)[ITEM_PREV])
        (*list)[LIST_BEG] = item;

    if (NULL == (*list)[ITEM_NEXT])
        (*list)[LIST_END] = item;
}

void remove_one(list_p list, end_point_t from)
{
    if (is_empty(list))
        /* list empty, nothing to remove */
        return;

    if ((*list)[LIST_BEG] == (*list)[LIST_END]) {
        free((*list)[LIST_BEG]);
        memset(*list, 0, sizeof *list);
        return;
    }

    const direction_t next_field = (LIST_BEG == from) ? ITEM_NEXT : ITEM_PREV;
    const direction_t term_field = (LIST_END == from) ? ITEM_NEXT : ITEM_PREV;

    item_p item = (*list)[from];
    item_p next = (*item)[next_field];
    (*next)[term_field] = NULL;
    (*list)[from] = next;

    free(item);
}

/* FIXME !!___sl_get_nondet_int() should work -- minimal example in test-0216 */
end_point_t rand_end_point(void)
{
    if (___sl_get_nondet_int())
        return LIST_BEG;
    else
        return LIST_END;
}

int main()
{
    static list_t list;

    while (___sl_get_nondet_int()) {
        while (___sl_get_nondet_int())
            append_one(&list, rand_end_point());

        while (___sl_get_nondet_int())
            remove_one(&list, rand_end_point());
    }

    end_point_t end_point;
    direction_t direction;

    if (___sl_get_nondet_int()) {
        /* destroy the list from begin to end */
        end_point = LIST_BEG;
        direction = ITEM_NEXT;
    }
    else {
        /* destroy the list from end to begin */
        end_point = LIST_END;
        direction = ITEM_PREV;
    }

    /* now please destroy the list */
    item_p cursor = list[end_point];
    while (cursor) {
        item_p next = (*cursor)[direction];
        free(cursor);
        cursor = next;
    }

    return 0;
}

/**
 * @file test-0218.c
 *
 * @brief simplification of test-0217 not using structs at all
 *
 * @attention
 * This description is automatically imported from tests/predator-regre/README.
 * Any changes made to this comment will be thrown away on the next import.
 */
