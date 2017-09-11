#include "sdiv5.h"

#include <iostream>
#include <bitset>

using namespace std;

int main() {
  uint8_t A[2];
  A[0] = (1 << 4) + 1;
  A[1] = 2;

  // -15 / 2 == -7
  uint8_t expected = 0b11001

  uint8_t res = 234;

  simulate(&res, A);

  cout << "sdiv expected = " << bitset<8>(expected) << endl;
  cout << "sdiv res      = " << bitset<8>(res) << endl;

  if (expected == res) {
    return 0;
  }

  return 1;
}
