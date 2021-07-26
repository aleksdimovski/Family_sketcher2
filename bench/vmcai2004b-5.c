/* from Podelski & Rybalchenko VMCAI 2004 paper
TERMINATION

suggested parameters:
- partition abstract domain = boxes [default]
- function abstract domain = affine [default]
- backward widening delay = 5
*/

features int[0,31] A;
features int[0,31] B;

void main() {
  int x=A;
  int y=0; 
	
  while (x > 0) {
    x = - B * x + 10; 
    y = y + 1; 
  }
	
  assert(y<=2); 
  
}