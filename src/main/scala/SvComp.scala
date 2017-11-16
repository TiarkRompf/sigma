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

    /* Build a list of the form (1->2)*->0 */
   struct list* a = (struct list*) malloc(sizeof(struct list));
   struct list* t = (struct list*) NULL;
   struct list* p = a;
   while (__VERIFIER_nondet_int() != 0) {
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
   }
   p->value = 3;

   /* Check it */
  p = a;
  flag = 1;
  while (p->value != 3) {
    if (flag == 1) {
      flag = 0;
      if (p->value != 1)
        goto ERROR;
      } else {
        flag = 1;
        if (p->value != 2)
          goto ERROR;
      }
      p = p->next;
  }

  return 0;

  ERROR: assert(0);
  return 1;
  }
  """


}
