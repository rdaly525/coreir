#include "srem4.h"

#include <iostream>
#include <bitset>

using namespace std;

int main() {
  uint8_t A[3];
  A[0] = 3;
  A[1] = 2;
  A[2] = -27;

  // -15 % 2 == -1
  uint8_t expected = 0b11111;

  uint8_t res = 234;

  cout << "3 srem before      = " << bitset<8>(expected) << endl;
  cout << "3 srem before      = " << bitset<8>(res) << endl;
  
  simulate(&res, A);

  cout << "3 srem expected = " << bitset<8>(expected) << endl;
  cout << "3 srem res      = " << bitset<8>(res) << endl;

  if (expected == res) {
    return 0;
  }

  return 1;
}
