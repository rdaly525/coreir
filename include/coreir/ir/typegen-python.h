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
      Py_Initialize();
      PyObject *py_coreir_module = PyImport_ImportModule("coreir");
      PyObject *py_module = PyImport_ImportModule(moduleName.c_str());
      if (py_module != NULL) {
        Py_INCREF(py_module);
        Py_INCREF(py_coreir_module);
        PyObject *py_typeGenFunc = PyObject_GetAttrString(py_module, functionName.c_str());
        if (py_typeGenFunc && PyCallable_Check(py_typeGenFunc)) {
          Py_INCREF(py_typeGenFunc);
          PyObject* py_args = PyTuple_New(2);  // (context, args)
          Py_XINCREF(py_args);
          PyObject* py_coreir_context_module = PyObject_GetAttrString(py_coreir_module, "context");
          Py_XINCREF(py_coreir_context_module);
          PyObject* py_coreir_context_class = PyObject_GetAttrString(py_coreir_context_module, "Context");
          Py_XINCREF(py_coreir_context_class);
          PyObject* py_coreir_context_pointer = PyObject_GetAttrString(py_coreir_context_module, "COREContext_p");
          Py_XINCREF(py_coreir_context_pointer);
          PyObject* py_coreir_type_module = PyObject_GetAttrString(py_coreir_module, "type");
          Py_XINCREF(py_coreir_type_module);
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
          PyObject* value_object = PyObject_CallFunction(py_typeGenFunc, "llli",
                  &c, (void *) names, (void *) values_ptrs, size);
          if (PyErr_Occurred()) PyErr_Print();
          std::cout << value_object << std::endl;

          // PyObject* context_object_args = Py_BuildValue("o", context_pointer_object);
          // PyObject* context_object =
          //     PyObject_CallObject(py_coreir_context_class,
          //             context_object_args);
          // Py_DECREF(context_object_args);
          //  
          // PyObject* typegen_args = Py_BuildValue("(o, o)", context_object, args_object);
          // // PyObject* py_type_object = PyObject_CallObject(py_typeGenFunc, typegen_args);
          // PyObject_CallObject(py_typeGenFunc, typegen_args);
          // Py_DECREF(typegen_args);


          // Py_XDECREF(py_coreir_context_module);
          // Py_XDECREF(py_coreir_context_class);
          // Py_XINCREF(py_coreir_context_pointer);
          // Py_XDECREF(py_coreir_type_module);
          // Py_XDECREF(py_coreir_args_class);
          // Py_XDECREF(py_coreir_args_pointer);
          // Py_DECREF(py_typeGenFunc);
        } else {
          if (PyErr_Occurred()) PyErr_Print();
          std::cerr << "Cannot find function " << functionName << std::endl;
        }
        Py_DECREF(py_module);
        Py_DECREF(py_coreir_module);
      } else {
        PyErr_Print();
        std::cerr << "Failed to load " << moduleName << std::endl;
        ASSERT(0, "Failed to load module");
      }

      Py_Finalize();
      std::cout << "Reached end of typegen" << std::endl;
      std::exit(1);
      return NULL;
    }
  
};

}

#endif //COREIR_TYPEGEN_PYTHON_HPP_
