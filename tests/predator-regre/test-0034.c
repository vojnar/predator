#include <stdlib.h>
#include <stdbool.h>

#define NEW(type) \
    (type *) malloc(sizeof(type))

static struct stack_item {
    void                *data;
    struct stack_item   *next;
} *gl_stack;

static void gl_push(void *data)
{
    // allocate stack item
    struct stack_item *item = NEW(struct stack_item);
    if (!item)
        abort();

    // initialize stack item
    item->data = data;
    item->next = gl_stack;

    // replace the top of stack
    gl_stack = item;
}

static bool gl_pop(void **pData)
{
    if (!gl_stack)
        // empty stack
        return false;

    // read the top of stack
    *pData = gl_stack->data;
    gl_stack = gl_stack->next;
    return true;
}

static void gl_destroy_until(void *what)
{
    void *data;
    while(gl_pop(&data) && data != what);
}

int main()
{
    gl_push(NULL);
    gl_destroy_until(NULL);
    return 0;
}

/**
 * @file test-0034.c
 *
 * @brief a test-case for global variables (only one pointer)
 *
 * @attention
 * This description is automatically imported from tests/predator-regre/README.
 * Any changes made to this comment will be thrown away on the next import.
 */
