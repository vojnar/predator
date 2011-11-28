#include <verifier-builtins.h>

int main()
{
    int i = ___sl_get_nondet_int();
    if (i < -1) {
        ___sl_plot("less-than-minus-one", &i);
        ___SL_ASSERT(i < -1);
    }
    else if (-1 < i) {
        ___sl_plot("more-than-minus-one", &i);
        ___SL_ASSERT(-1 < i);
    }
    else {
        ___sl_plot("equal-to-minus-one", &i);
        ___SL_ASSERT(-1 == i);
    }

    return 0;
}
