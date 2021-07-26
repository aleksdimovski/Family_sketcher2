/* from Podelski & Rybalchenko VMCAI 2004 paper
TERMINATION

suggested parameters:
- partition abstract domain = boxes [default]
- function abstract domain = affine [default]
- backward widening delay = 5
*/

features int[11,11] A;

void main() {
  int x=[0,7];
  int y=0; 
	
  while (y <= 5) {
    x = - A * x + 10; 
    y = y + 1; 
  }
	
  assert(y<=2); 
  
}