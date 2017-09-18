#include "srem4.h"

#include <iostream>
#include <bitset>

using namespace std;

int main() {
  uint8_t A[3];
  A[0] = 27;
  A[1] = 14;
  // -15 in 6 bit signed
  A[2] = 1 | (1 << 4) | (1 << 5);


  // -1
  uint8_t expected = 0b1;

  uint8_t res = 234;

  cout << "3 srem before       = " << bitset<8>(expected) << endl;
  cout << "3 srem before       = " << bitset<8>(res) << endl;

  cout << "A0 srem before      = " << bitset<8>(A[0]) << endl;
  cout << "A1 srem before      = " << bitset<8>(A[1]) << endl;
  cout << "A2 srem before      = " << bitset<8>(A[2]) << endl;
  
  simulate(&res, A);

  cout << "3 srem expected = " << bitset<8>(expected) << endl;
  cout << "3 srem res      = " << bitset<8>(res) << endl;

  if (expected == res) {
    return 0;
  }

  return 1;
}
