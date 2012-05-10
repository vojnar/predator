/*
 * Singly linked list reversal
 *
 * boxes:
 */

#include <stdlib.h>

int main() {

	struct T {
		struct T* next;
	};

	struct T* x = NULL;
	struct T* y = NULL;

	while (__nondet()) {
		y = malloc(sizeof(struct T));
		y->next = x;
		x = y;
	}

	struct T* z = NULL;

	while (x != NULL) {
		y = x;
		x = x->next;
		y->next = z;
		z = y;
	}

	while (y != NULL) {
		x = y;
		y = y->next;
		free(x);
	}

	return 0;

}
