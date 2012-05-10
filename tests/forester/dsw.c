/*
 * The Deutsch-Schorr-Waite tree traversal algorithm
 *
 * boxes:
 */

#include <stdlib.h>

int __nondet();

int main() {

	struct TreeNode {
		struct TreeNode* left;
		struct TreeNode* right;
	};

	struct StackItem {
		struct StackItem* next;
		struct TreeNode* node;
	};

	struct TreeNode* root = malloc(sizeof(*root)), *n;
	root->left = NULL;
	root->right = NULL;

	while (__nondet()) {
		n = root;
		while (n->left && n->right) {
			if (__nondet())
				n = n->left;
			else
				n = n->right;
		}
		if (!n->left && __nondet()) {
			n->left = malloc(sizeof(*n));
			n->left->left = NULL;
			n->left->right = NULL;
		}
		if (!n->right && __nondet()) {
			n->right = malloc(sizeof(*n));
			n->right->left = NULL;
			n->right->right = NULL;
		}
	}

	struct TreeNode sentinel;

	n = root;
	struct TreeNode* pred = &sentinel;
	struct TreeNode* succ = NULL;

	while (n != &sentinel) {
		succ = n->left;
		n->left = n->right;
		n->right = pred;
		pred = n;
		n = succ;
		if (!n) {
			n = pred;
			pred = NULL;
		}
	}

	if (pred != root)
		((struct TreeNode*)NULL)->left = NULL;

	n = NULL;

	struct StackItem* s = malloc(sizeof(*s)), *st;
	s->next = NULL;
	s->node = root;

	while (s != NULL) {
		st = s;
		s = s->next;
		n = st->node;
		free(st);
		if (n->left) {
			st = malloc(sizeof(*st));
			st->next = s;
			st->node = n->left;
			s = st;
		}
		if (n->right) {
			st = malloc(sizeof(*st));
			st->next = s;
			st->node = n->right;
			s = st;
		}
		free(n);
	}

	return 0;

}
