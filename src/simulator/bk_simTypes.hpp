//Algorithm:
//Convert from MIR to SIMIR
//  This requires flattening type system and basically flattening nested hierarchy.
//Topologically sort all the primitives by connection. 
//  If cannot be sorted, => combinational loop error
//Have main instance.
//Set the inputs of main to the correct data and set each to dirty.
//propigate the values/dirty of inputs to sinks (or skipsinks)
//foreach prim in topological sort:
//  continue if neither input is dirty
//  Simulate Prim and set output value to dirty
//  unset dirty on inputs of prim.
//  propigate output value.
//Read outputs on main.


typedef void (*setType)(void*,void*);
typedef void* (*getType)(void*);
struct simPrivStruct {
  void* (*init)(void);
  setType* inputSets;
  getType* outputGets;
  void (*simulate)(void*);
}
void* createPrimitive(simPrivStruct s);
//////////////////////////////////////////////////////////

//User code trying to make an add4 primitive;

struct add4_t {
  uint8_t inA;
  uint8_t inB;
  uint8_t out;
}

void* add4_init() {
  return malloc(sizeof(struct add4));
}
void add4_inASet(void* data, void* value) {
  uint8_t val = *((uint8_t*) value);
  add4_t datacast = (add4_t*)data;
  datacast->inA = val;
}

void add4_inBSet(void* data, void* value) {
  uint8_t val = *((uint8_t*) value);
  add4_t datacast = (add4_t*)data;
  datacast->inB = val;
}

void* add4_outGet(void* data) {
  add4_t datacast = (add4_t*)data;
  return (void*)(datacast->inB);
}

void add4_simulate(void* data) {
  add4_t datacast = (add4_t*)data;
  datacast->out = (0xF & datacast->inA) + (0xF & datacast->inB);
}

simPrivStruct simAdd4;
simAdd.init = add4_init;
simAdd.inputSets = {add4_inASet,add4_inBSet};
simAdd.outputGets = {add4_outGet};
simAdd.simulate = add4_simulate;



class simInstance {
  string name;
  simInstance* parentInst;
  
  //reference from outside instance
  vector<simWire*> outputs; 
  vector<simWire*> inputs; 
};

//Has to instantiate the simWires
class simPrimitive;
  // checks if inputs are dirty (or not) and runs the function
  vector<simWire*> outputs; 
  virtual void simulate()=0;

}


class simAdd : public simPrimitive {
  simWire* inA;
  simWire* inB;
  simWire* out;
  void simulate() {
    if (inA->dirty || inB->dirty) {
    
    }
  }
  void returnOutput() {
    return out;
  }
};


class simWire {
  string name
  BaseType* type
  simInstance* inst;

  simWire* source;
  vector<simWire*> sinks;
  
  simWire* skipSource;
  vector<simWire*> skipSinks;

  bool dirty;
  wireValue* value;
};




