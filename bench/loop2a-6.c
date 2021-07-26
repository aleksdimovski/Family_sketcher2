/*
TERMINATION

suggested parameters:
- partition abstract domain = boxes [default]
- function abstract domain = affine [default]
- backward widening delay = 2 [default]
*/

features int[0,63] A;
features int[0,63] B;

int main() {
  int x, y=A;	
	
  while (x <= 10) 
	if (y>B) x = x + 1; else x = x-1; 
	
  assert (y>2);
  return 0;
}