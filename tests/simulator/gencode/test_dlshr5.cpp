#include "dlshr5.h"

#include <bitset>
#include <iostream>

using namespace std;

int main () {
  uint8_t A[2];
  A[0] = 1 << 4;
  A[1] = 3;

  uint8_t res;

  simulate(&res, A);

  uint8_t expected = 1 << 1;

  cout << "dlshr5 expected = " << bitset<8>(expected) << endl;
  cout << "dlshr5 res      = " << bitset<8>(res) << endl;

  if (res == expected) {
    return 0;
  }

  return 1;
}
