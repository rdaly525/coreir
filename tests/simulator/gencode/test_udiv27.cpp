#include "udiv27.h"

#include <iostream>

using namespace std;

int main() {
  uint32_t A[2];
  A[0] = 25;
  A[1] = 5;

  uint32_t expected = 5;
  uint32_t res = 30;

  simulate(&res, A);

  cout << "udiv expected = " << expected << endl;
  cout << "udiv res      = " << res << endl;

  if (expected == res) {
    return 0;
  }

  return 1;
}
