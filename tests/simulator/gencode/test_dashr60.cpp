#include "dashr60.h"

#include <bitset>
#include <iostream>

using namespace std;

int main() {
  uint64_t A1[2];
  A1[0] = 1ULL << 59;
  A1[1] = 3ULL;

  uint64_t expected1 = (1ULL << 59) | (1ULL << 58) | (1ULL << 57) | (1ULL << 56);
  uint64_t res1 = 34;

  cout << "About to simulate dashr" << endl;

  simulate(&res1, A1);

  cout << "Expected1 = " << std::bitset<64>(expected1) << endl;
  cout << "Result1   = " << std::bitset<64>(res1) << endl;

  uint64_t A2[2];
  A2[0] = 1ULL << 58;
  A2[1] = 5ULL;
  
  uint64_t expected2 = (1ULL << 53);
  uint64_t res2 = 23;

  simulate(&res2, A2);

  cout << "Expected2 = " << std::bitset<64>(expected2) << endl;
  cout << "Result2   = " << std::bitset<64>(res2) << endl;
  
  if ((expected1 == res1) && (expected2 == res2)) {
    return 0;
  }

  return 1;

}
//correct mask uint64_t dmask = (((1ULL << (self_A[1])) - 1) << (59 - self_A[1] + 1));
