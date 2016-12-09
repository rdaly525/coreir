#include <map>
#include <vector>


typedef vector<std::pair<string,Type*>> recordparam_t

class record_t {
  map<string,Type*> strmap;
  vector<string> order;
  
  public :
    record_t(recordparam_t r) {
    for(recordparam_t::iterator it=r.begin(); it!=r.end(); ++it) {
      strmap.emplace(it->first,it->second);
      order.push_back(it->first);
    }
    
    class iterator {

    }
    iterator begin() {

    }
    iterator end() {

    }
    push
 
  }
}

