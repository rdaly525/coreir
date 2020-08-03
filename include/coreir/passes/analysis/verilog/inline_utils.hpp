#include "coreir.h"
#include "verilogAST/transformer.hpp"

#ifndef COREIR_VERILOG_INLINE_UTILS_HPP_
#define COREIR_VERILOG_INLINE_UTILS_HPP_
namespace vAST = verilogAST;

class UnaryOpReplacer : public vAST::Transformer {
  std::unique_ptr<vAST::Expression> in;

 public:
  UnaryOpReplacer(std::unique_ptr<vAST::Expression> in) : in(std::move(in)){};

  virtual std::unique_ptr<vAST::Expression> visit(
    std::unique_ptr<vAST::Expression> node);
};

class BinaryOpReplacer : public vAST::Transformer {
  std::unique_ptr<vAST::Expression> in0;
  std::unique_ptr<vAST::Expression> in1;

 public:
  BinaryOpReplacer(
    std::unique_ptr<vAST::Expression> in0,
    std::unique_ptr<vAST::Expression> in1)
      : in0(std::move(in0)),
        in1(std::move(in1)){};

  virtual std::unique_ptr<vAST::Expression> visit(
    std::unique_ptr<vAST::Expression> node);
};

class MuxReplacer : public vAST::Transformer {
  std::unique_ptr<vAST::Expression> in0;
  std::unique_ptr<vAST::Expression> in1;
  std::unique_ptr<vAST::Expression> sel;

 public:
  MuxReplacer(
    std::unique_ptr<vAST::Expression> in0,
    std::unique_ptr<vAST::Expression> in1,
    std::unique_ptr<vAST::Expression> sel)
      : in0(std::move(in0)),
        in1(std::move(in1)),
        sel(std::move(sel)){};

  virtual std::unique_ptr<vAST::Expression> visit(
    std::unique_ptr<vAST::Expression> node);
};

bool is_inlined(std::string primitive_type, std::string name);

bool can_inline_binary_op(CoreIR::Module* module, bool _inline);

std::unique_ptr<vAST::Expression> get_primitive_expr(
  CoreIR::Instance* instance);

std::unique_ptr<vAST::StructuralStatement> inline_binary_op(
  std::pair<std::string, CoreIR::Instance*> instance,
  std::unique_ptr<vAST::Connections> verilog_connections,
  bool disable_width_cast);

bool can_inline_unary_op(CoreIR::Module* module, bool _inline);

std::unique_ptr<vAST::StructuralStatement> inline_unary_op(
  std::pair<std::string, CoreIR::Instance*> instance,
  std::unique_ptr<vAST::Connections> verilog_connections,
  bool is_wire);

bool can_inline_const_op(CoreIR::Module* module, bool _inline);

bool can_inline_mux_op(CoreIR::Module* module, bool _inline);

std::unique_ptr<vAST::StructuralStatement> inline_mux_op(
  std::pair<std::string, CoreIR::Instance*> instance,
  std::unique_ptr<vAST::Connections> verilog_connections);

bool can_inline_slice_op(CoreIR::Module* module, bool _inline);

bool is_muxn(CoreIR::Module* module);

std::unique_ptr<vAST::Always> make_muxn_if(
  std::unique_ptr<vAST::Connections> verilog_connections,
  int n);

class AlwaysStarMerger : public vAST::Transformer {
 public:
  using vAST::Transformer::visit;
  virtual std::unique_ptr<vAST::Module> visit(
    std::unique_ptr<vAST::Module> node);
};

bool is_mantle_wire(CoreIR::Module* module);

bool isInlined(CoreIR::Module* module, bool _inline);

#endif
