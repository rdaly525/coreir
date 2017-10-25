#ifndef COREIR_TYPEGEN_PYTHON_HPP_
#define COREIR_TYPEGEN_PYTHON_HPP_

#include "typegen.h"
#include <Python.h>

namespace CoreIR {

class TypeGenFromPython : public TypeGen {
  std::string moduleName;
  std::string functionName;

  public:
    TypeGenFromPython(Namespace* ns, std::string name, Params params,
                      std::string moduleName, std::string functionName, bool
                      flipped=false) :
        TypeGen(ns,name,params,flipped), moduleName(moduleName),
        functionName(functionName) {}

    Type* createType(Context* c, Values values) {
      Type* type_ptr = NULL;
      Py_Initialize();
      // Add cwd to path (not added by default when using the embedded
      // interpreter)
      PyRun_SimpleString( "import sys\nsys.path.append(\".\")\n" );
      PyObject *py_module = PyImport_ImportModule(moduleName.c_str());
      if (py_module != NULL) {
        Py_INCREF(py_module);
        PyObject *py_typeGenFunc = PyObject_GetAttrString(py_module, functionName.c_str());
        if (py_typeGenFunc && PyCallable_Check(py_typeGenFunc)) {
          Py_INCREF(py_typeGenFunc);
          int size = values.size();
          char** names = c->newStringArray(size);
          Value** values_ptrs = c->newValueArray(size);
          int count = 0;
          for (auto element : values) {
              std::size_t name_length = element.first.size();
              names[count] = c->newStringBuffer(name_length + 1);
              memcpy(names[count], element.first.c_str(), name_length + 1);
              values_ptrs[count] = element.second;
              count++;
          }
          char signature[] = "llli";
          PyObject* value_object = PyObject_CallFunction(py_typeGenFunc, signature,
                  (void *) c, (void *) names, (void *) values_ptrs, size);
          if (!value_object) {
            if (PyErr_Occurred()) PyErr_Print();
            std::cerr << "Error calling typegen function " << functionName << std::endl;
          } else {
            type_ptr = (Type *) PyLong_AsVoidPtr(value_object);
            Py_DECREF(value_object);
          }
          Py_DECREF(py_typeGenFunc);
        } else {
          if (PyErr_Occurred()) PyErr_Print();
          std::cerr << "Cannot find function " << functionName << std::endl;
        }
        Py_DECREF(py_module);
      } else {
        PyErr_Print();
        std::cerr << "Failed to load " << moduleName << std::endl;
        ASSERT(0, "Failed to load module");
      }

      Py_Finalize();

      // FIXME: Can we free char** names and Value** values_ptrs because
      // they are no longer used since the interpreter's been finalized?
      // Currently they will be cleaned up eventually by the context, but
      // if we can free here that should reduce memory consumption
      return type_ptr;
    }
  
};

}

#endif //COREIR_TYPEGEN_PYTHON_HPP_
