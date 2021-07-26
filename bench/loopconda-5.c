features int[0,31] A;

int main() {
  unsigned int x=__VERIFIER_nondet_uint();
  int y=0;
  while (x >= 0) {  
    x = x - 1;
	if (y<A) y=y+1; else y=y-1; 
  }
  assert (y<=1);
  return 0;
}