/* from Podelski & Rybalchenko VMCAI 2004 paper
TERMINATION

suggested parameters:
- partition abstract domain = boxes [default]
- function abstract domain = affine [default]
- backward widening delay = 5
*/

features int[0,63] A;

void main() {
  int x=[0,31];
  int y=0; 
	
  while (x > 0) {
    x = - A * x + 10; 
    y = y + 1; 
  }
	
  assert(y<=2); 
  
}