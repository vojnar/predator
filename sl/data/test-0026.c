#include "../sl.h"

int main() {
    void **p1;
    void **p2;

    if (p1 == p2) {
        sl_plot("test26-00");
        if (p1 != p2) {
            *p2 = (void *)0;
        } else {
            sl_plot("test26-02");
        }
    } else {
        sl_plot("test26-01");
    }

    return 0;
}
