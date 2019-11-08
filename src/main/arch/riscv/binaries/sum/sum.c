/*@ axiomatic Sigma {
  @ logic int sigma(int *x, integer n);
  @ axiom sigma_empty:
  @   \forall int* x; sigma(x, 0) == 0;
  @ axiom sigma_next:
  @   \forall int* x, integer n; (n > 0) ==> sigma(x, n) == sigma(x, n-1) + x[n-1];
  @ }
  @*/

/*@ requires n >= 0;
  @ requires \valid(x + (0..n-1));
  @ assigns \nothing;
  @ ensures \result == sigma(x, n);
  @*/
int sum(int x[], int n) {
  int s = 0;
  /*@ loop invariant 0 <= i <= n;
    @ loop invariant s == sigma(x, i);
    @ loop assigns i, s;
    @ loop variant n - i; 
    @*/
  for (int i = 0; i < n; i++) {
    s += x[i];
  }
  return s;
}
