//features int[0,7] A;
features int[0,7] B;

int main() {
  int x=5;
  int y=0;
  while (x > B) {  
    x = x - 1;
	y = y + 1;
  }
  assert (y<=2);
  return 0;
}