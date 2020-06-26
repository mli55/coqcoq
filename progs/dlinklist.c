#include <stddef.h>

#define DEFAULT 0u

extern void *mallocN (int n); 
extern void freeN (void *p, int n);

struct node{
    unsigned int val;
    // for convenience, do not use signed int
    struct node * prev;
    struct node * next;
};

struct list{
    unsigned int size;
    struct node * head;
    struct node * tail;
};

struct list * list_new (){
    struct list * l = (struct list *) mallocN(sizeof (struct list));
    l->head = NULL;
    l->tail = NULL;
    l->size = 0;
    return l;
}

void list_free (struct list * l){
    struct node * tmp = l->head;
    while (tmp != NULL){
        l->head = tmp->next;
        freeN(tmp, sizeof (struct node));
        l->size -= 1;
        tmp = l->head;
    }
    freeN(l, sizeof (struct list));
}

struct node * begin (struct list * l){
    return l->head;
}

struct node * end (struct list * l){
    return l->tail;
}

struct node * rbegin (struct list * l){
    return l->tail;
}

struct node * rend (struct list * l){
    return l->head;
}

struct node * next (struct node * p){
    return p->next;
}

struct node * rnext (struct node * p){
    return p->prev;
}

unsigned get_size (struct list * l){
    return l->size;
}

void push_back (struct list * l, unsigned int v){
    struct node * nd = (struct node *) mallocN(sizeof (struct node));
    nd->val = v;
    nd->next = NULL;
    nd->prev = l->tail;
    l->size += 1;
    if (l->tail == NULL){
        l->head = nd;
    }else {
        l->tail->next = nd;
    }
}

unsigned int pop_back (struct list * l){
    if (l->tail == NULL){
        return DEFAULT;
    }
    unsigned int res = l->tail->val;
    struct node * tmp = l->tail;
    l->tail = tmp->prev;
    freeN(tmp, sizeof (struct node));
    l->size -= 1;
    if (l->tail == NULL){
        // empty list
        l->head = NULL;
    }else {
        l->tail->next = NULL;
    }
    return res;
}

void push_front (struct list * l, unsigned int v){
    struct node * nd = (struct node *) mallocN(sizeof (struct node));
    nd->val = v;
    nd->prev = NULL;
    nd->next = l->head;
    l->size += 1;
    if (l->head == NULL){
        l->tail = nd;
    }else {
        l->head->prev = nd;
    }
}

unsigned int pop_front (struct list * l){
    if (l->head == NULL){
        return DEFAULT;
    }
    unsigned int res = l->head->val;
    struct node * tmp = l->head;
    l->head = tmp->next;
    freeN(tmp, sizeof (struct node));
    l->size -= 1;
    if (l->head == NULL){
        // empty list
        l->tail = NULL;
    }else {
        l->head->prev = NULL;
    }
    return res;
}

struct node * move (struct list * l, unsigned int pos){
    struct node * res = l->head;
    while (pos > 0){
        res = res->next;
        pos -= 1u;
    }
    return res;
}

void insert (struct list * l, int pos, unsigned int v){
    // position : 0-based
    if (pos == 0){
        push_front(l, v);
    }else if (pos == l->size){
        push_back(l, v);
    }else {
        struct node * res = move(l, pos);
        struct node * nd = (struct node *) mallocN(sizeof (struct node));
        nd->val = v;
        nd->prev = res->prev;
        nd->next = res;
        res->prev->next = nd;
        res->prev = nd;
        l->size += 1;
    }
}

void delete (struct list * l, unsigned int pos, unsigned int v){
    // position : 0-based
    if (pos == 0){
        pop_front(l);
    }else if (pos == l->size - 1){
        pop_back(l);
    }else {
        struct node * res = move(l, pos);
        res->prev->next = res->next;
        res->next->prev = res->prev;
        freeN(res, sizeof (struct node));
        l->size -= 1;
    }
}

void merge (struct list * l1, struct list * l2){
    if (l2->head != NULL){
        l2->head->prev = l1->tail;
    }else {
        freeN(l2, sizeof (struct list));
        return ;
    }
    if (l1->tail != NULL){
        l1->tail->next = l2->head;
    }else {
        l1->head = l2->head;
    }
    l1->tail = l2->tail;
    l1->size += l2->size;
    freeN(l2, sizeof (struct list));
}

struct list * split_K (struct list * l, unsigned int k){
    // return the latter list
    struct list * res = list_new();
    if (k == 0){
        res->head = l->head;
        res->tail = l->tail;
        res->size = l->size;
        l->head = NULL;
        l->tail = NULL;
        l->size = 0u;
    }else if (k < l->size){
        struct node * nd = move(l, k);
        res->tail = l->tail;
        l->tail = nd->prev;
        res->head = nd;
        nd->prev->next = NULL;
        nd->prev = NULL;
        res->size = l->size - k;
        l->size = k;
    }
    return res;
}