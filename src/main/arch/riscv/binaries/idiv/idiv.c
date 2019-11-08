/*@ requires a >= 0;
  @ requires b > 0;
  @ requires \valid(r);
  @ assigns *r;
  @ ensures \let q = \result; a == b*q + *r;
  @ ensures 0 <= *r < b;
  @*/
int idiv(int a, int b, int *r) {
  int q = 0;
  int p = a;
  /*@ loop invariant (a == b * q + p) && (0 <= p <= a);
    @ loop assigns q, p;
    @ loop variant p; 
    @*/
  while (p >= b) {
    q++;
    p -= b;
  }
  //@ assert (a == b * q + p) && (0 <= p < b);
  *r = p;
  return q;
}

