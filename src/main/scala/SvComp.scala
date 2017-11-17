package analysis

object SvComp {

  val alternating_list_falseunreachcall = """
  #define NULL 0
  typedef struct list {
    int value;
    struct node *next;
  };

  int main() {
    int flag = 1;
    val n = 100;
    int i = 0;

    /* Build a list of the form (1->2)*->0 */
   struct list* a = (struct list*) malloc(sizeof(struct list));
   struct list* t = (struct list*) NULL;
   struct list* p = a;
   while (i < n) {
     if (flag == 1) {
       p->value = 2;
       flag = 0;
     } else {
       p->value = 1;
       flag = 1;
     }
     t = (struct list *) malloc(sizeof(struct list));
     p->next = t;
     p = p->next;
     i = i + 1;
   }
   p->value = 3;

   /* Check it */
  struct list *p1 = a;
  flag = 1;
  while (p1->value != 3) {
    if (flag == 1) {
      flag = 0;
      if (p1->value != 1)
        goto ERROR;
      } else {
        flag = 1;
        if (p1->value != 2)
          goto ERROR;
      }
      p1 = p1->next;
  }

  return 0;

  ERROR: assert(0);
  return 1;
  }
  """

  val list_search_trueunreachcall = """
  struct list {
    int value;
    struct list *next;
  };


  mlist* search_list(mlist *l, int k){
    l = head;
    while(l!=NULL && l->key!=k) {
      l = l->next;
    }
    return l;
  }

  int delete_list(mlist *l){
    mlist *tmp;
    tmp = head;
    if (head != l) {
      while(tmp->next!=l) {
        tmp = tmp->next;
      }
      } else {
        head = l->next;
      }
      tmp->next = l->next;
      free(l);
      return 0;
  }

  int insert_list(mlist *l, int k){

    l = (mlist*)malloc(sizeof(mlist));

    if (head==NULL) {
      l->key = k;
      l->next = NULL;
    } else {
      l->key = k;
      l->next = head;
    }
    head = l;

    return 0;
  }

  int main(void){
    struct list *head;

    int i;
    struct list *mylist = (struct list *) NULL;
    struct list *temp = (struct list *) NULL;

    insert_list(mylist,2);
    insert_list(mylist,5);
    insert_list(mylist,1);
    insert_list(mylist,3);

    mylist = head;

    while(mylist) {
       mylist = mylist->next;
    }

    temp = search_list(mylist,2);
    __VERIFIER_assert(temp->key==2);
    delete_list(temp);

    mylist = head;

    while(mylist) {
       mylist = mylist->next;
    }
    return 0;
}

    """

val simple_falseunreachcall = """
struct list {
  int value;
  struct list *next;
};

int main() {
  /* Build a list of the form 1->...->1->0 */
  struct list* a = (struct list*) malloc(sizeof(struct list))
  struct list* t;
  struct list* p = a;
  a->value = 2;

  int i = 0;
  while (i < 100) {
    p->value = 1;
    t = (struct list*) malloc(sizeof(struct list));
    p->next = t;
    p = p->next;
    i = i + 1;
  }
  p->value = 2;
  p->next = 0;
  p = a;
  while (p != (struct list*)0) {
    assert(p->value == 2) {
    p = p->next;
  }
  return 0;
}
"""

val list_flag_falseunreachcall = """
struct list {
  int value;
  struct list *next;
};

int main() {
  int flag = __VERIFIER_nondet_int();
  struct list* p = (struct list*) malloc(sizeof(struct list));
  p->value = 3;
  p->next = (struct list*) 0;

  /* Build a list of the form x->x->x->...->x->3
   *    * with x depending on some flag
   *       */
  int i = 0;
  int n = __VERIFIER_nondet_int();
  while (i < n) {
    i = i + 1;
    struct list *t = (struct list*) malloc(sizeof(struct list));
    if (flag == 1) {
      t->value = 1;
    } else {
      t->value = 2;
    }
    /*** TVLA forgets at this point the dependence
     *          between p->value and the value of flag        ***/
    t->next = p;
    p = t;
  }

  /* Check it */
  if (flag == 1)
    while (p->value == 2)
      p = p->next;
  else
    while (p->value == 1)
      p = p->next;
  assert(p->value == 3);
}
"""

val list_simple_build_from_end_trueunreachcall = """
struct list {
  int value;
  struct list *next;
};

int main() {
  /* Build a list of the form 1->...->1->0 */
  struct list* p = (struct list*)0;
  val n = __VERIFIER_nondet_int();
  int i = 0;
  while (i < n) {
    struct list* t = (struct list*) malloc(sizeof(struct list));
    t->value = 1;
    t->next = p;
    p = t;
    i = i + 1;
  }
  while (p != (struct list *)0) {
    assert(p->value == 1) {
    p = p->next;
  }

  return 0;
}
"""




}
