#include <stdlib.h>

struct str {
    void        *p0;
    union {
        void    *up0;
        void    *up1;
    };
    void        *p1;
};

#define NEW(type) (type *)malloc(sizeof(type))

#define ASSIGN_PTR_TO_SELF(self) self = &self

int main()
{
    struct str *s = NEW(struct str);
    if (!s)
        return EXIT_FAILURE;

    ASSIGN_PTR_TO_SELF(s->p0);
    ASSIGN_PTR_TO_SELF(s->p1);
    ASSIGN_PTR_TO_SELF(s->up0);
    ASSIGN_PTR_TO_SELF(s->up1);

    free(s);
    return EXIT_SUCCESS;
}

/**
 * @file test-0091.c
 *
 * @brief anonymous union within a struct (minimal example)
 *
 * @attention
 * This description is automatically imported from tests/predator-regre/README.
 * Any changes made to this comment will be thrown away on the next import.
 */
