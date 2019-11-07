#include <stddef.h>

/*@ requires \typeof(s) <: \type(char *);
    requires \valid((char *)s+(0..count-1));
    assigns ((char *)s)[0..count-1];
    ensures \forall char *p;
      (char *)s <= p < (char *)s + count ==> *p == (char)c;
    ensures \result == s;
*/
void *memset(void *s, int c, size_t count) {
  char *xs = s;
  //@ ghost ocount = count;

  /*@ loop invariant \valid((char *)s+(0..ocount-1));
      loop invariant 0 <= count <= ocount;
      loop invariant (char *)s <= xs || xs <= (char *)s + ocount;
      loop invariant xs - s == ocount - count;
      loop invariant \forall char *p;
        (char *)s <= p < xs ==> *p == (char) c;
      loop assigns count, ((char *)s)[0..ocount-1];
      loop variant count;
  */
  while (count--)
    *xs++ = (char) c;

  return s;
}

