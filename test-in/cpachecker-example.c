/*int main() {
  int i = 0;
  int a = 100;

  while (i < a) {
    i = i + 1
  }
  return rval;
}*/

int main() {
  int i = 0;
  int a = 0;
  int rval;

  while (1) {
    if (i == 20) {
       goto LOOPEND;
    } else {
       i++;
       a++;
    }
    TEST:
    if (i != a) {
      goto ERROR;
    }
  }

  LOOPEND:

  if (a != 20) {
     goto ERROR;
  }

  rval = 0; goto EXIT;

  ERROR:
  rval = -1; goto EXIT;
  
  EXIT:
  return rval;
}