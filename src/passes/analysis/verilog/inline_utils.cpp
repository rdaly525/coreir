#include "coreir/passes/analysis/verilog/inline_utils.hpp"

std::unique_ptr<vAST::Expression> UnaryOpReplacer::visit(
  std::unique_ptr<vAST::Expression> node) {
  if (auto ptr = dynamic_cast<vAST::Identifier*>(node.get())) {
    node.release();
    std::unique_ptr<vAST::Identifier> id(ptr);
    if (id->value == "in") { return std::move(this->in); }
    return vAST::Transformer::visit(std::move(id));
  }
  return vAST::Transformer::visit(std::move(node));
};

std::unique_ptr<vAST::Expression> BinaryOpReplacer::visit(
  std::unique_ptr<vAST::Expression> node) {
  if (auto ptr = dynamic_cast<vAST::Identifier*>(node.get())) {
    node.release();
    std::unique_ptr<vAST::Identifier> id(ptr);
    if (id->value == "in0") { return std::move(this->in0); }
    else if (id->value == "in1") {
      return std::move(this->in1);
    }
    return vAST::Transformer::visit(std::move(id));
  }
  return vAST::Transformer::visit(std::move(node));
};

std::unique_ptr<vAST::Expression> MuxReplacer::visit(
  std::unique_ptr<vAST::Expression> node) {
  if (auto ptr = dynamic_cast<vAST::Identifier*>(node.get())) {
    node.release();
    std::unique_ptr<vAST::Identifier> id(ptr);
    if (id->value == "in0") { return std::move(this->in0); }
    else if (id->value == "in1") {
      return std::move(this->in1);
    }
    else if (id->value == "sel") {
      return std::move(this->sel);
    }
    return vAST::Transformer::visit(std::move(id));
  }
  return vAST::Transformer::visit(std::move(node));
};

bool is_inlined(std::string primitive_type, std::string name) {
  return primitive_type == "binary" || primitive_type == "unary" ||
    primitive_type == "unaryReduce" || primitive_type == "binaryReduce" ||
    (primitive_type == "other" &&
     (name == "const" || name == "mux" || name == "slice"));
}

bool can_inline_binary_op(CoreIR::Module* module, bool _inline) {
  if (
    module->isGenerated() &&
    module->getGenerator()->getMetaData().count("verilog") > 0) {
    json verilog_json = module->getGenerator()->getMetaData()["verilog"];
    return module->getGenerator()->hasPrimitiveExpressionLambda() &&
      (verilog_json["primitive_type"] == "binary" ||
       verilog_json["primitive_type"] == "binaryReduce") &&
      _inline;
  }
  if (module->getMetaData().count("verilog") > 0) {
    json verilog_json = module->getMetaData()["verilog"];
    return module->hasPrimitiveExpressionLambda() &&
      (verilog_json["primitive_type"] == "binary" ||
       verilog_json["primitive_type"] == "binaryReduce") &&
      _inline;
  }
  return false;
}

std::unique_ptr<vAST::Expression> get_primitive_expr(
  CoreIR::Instance* instance) {
  CoreIR::Module* module = instance->getModuleRef();
  if (module->isGenerated()) {
    return module->getGenerator()->getPrimitiveExpressionLambda()();
  }
  return module->getPrimitiveExpressionLambda()();
}

std::unique_ptr<vAST::StructuralStatement> inline_binary_op(
  std::pair<std::string, CoreIR::Instance*> instance,
  std::unique_ptr<vAST::Connections> verilog_connections) {
  BinaryOpReplacer transformer(
    verilog_connections->at("in0"),
    verilog_connections->at("in1"));

  std::unique_ptr<vAST::Expression> primitive_expr = get_primitive_expr(
    instance.second);

  vAST::BinaryOp* binary_op = dynamic_cast<vAST::BinaryOp*>(
    primitive_expr.get());
  ASSERT(binary_op, "Expected binary_op for primitive expr");
  if (
    binary_op->op == vAST::BinOp::ADD || binary_op->op == vAST::BinOp::SUB ||
    binary_op->op == vAST::BinOp::MUL || binary_op->op == vAST::BinOp::DIV) {

    // Cast output so linters are happy (e.g. default verilog add
    // appends an extra bit)
    CoreIR::Value*
      width_value = instance.second->getModuleRef()->getGenArgs().at("width");
    auto width_int = CoreIR::dyn_cast<CoreIR::ConstInt>(width_value);
    ASSERT(width_int, "Expected ConstInt for width parameter");
    primitive_expr = std::make_unique<vAST::Cast>(
      width_int->get(),
      std::move(primitive_expr));
  }

  return std::make_unique<vAST::ContinuousAssign>(
    std::make_unique<vAST::Identifier>(instance.first + "_out"),
    transformer.visit(std::move(primitive_expr)));
}

bool can_inline_unary_op(CoreIR::Module* module, bool _inline) {
  if (
    module->isGenerated() &&
    module->getGenerator()->getMetaData().count("verilog") > 0) {
    json verilog_json = module->getGenerator()->getMetaData()["verilog"];
    return module->getGenerator()->hasPrimitiveExpressionLambda() &&
      (verilog_json["primitive_type"] == "unary" ||
       verilog_json["primitive_type"] == "unaryReduce") &&
      _inline;
  }
  if (module->getMetaData().count("verilog") > 0) {
    json verilog_json = module->getMetaData()["verilog"];
    return module->hasPrimitiveExpressionLambda() &&
      (verilog_json["primitive_type"] == "unary" ||
       verilog_json["primitive_type"] == "unaryReduce") &&
      _inline;
  }
  return false;
}

std::unique_ptr<vAST::StructuralStatement> inline_unary_op(
  std::pair<std::string, CoreIR::Instance*> instance,
  std::unique_ptr<vAST::Connections> verilog_connections,
  bool is_wire) {
  UnaryOpReplacer transformer(verilog_connections->at("in"));
  std::string wire_name = instance.first;
  if (!is_wire) { wire_name += "_out"; }
  return std::make_unique<vAST::ContinuousAssign>(
    std::make_unique<vAST::Identifier>(wire_name),
    transformer.visit(get_primitive_expr(instance.second)));
}

bool can_inline_const_op(CoreIR::Module* module, bool _inline) {
  if (
    module->isGenerated() &&
    module->getGenerator()->getMetaData().count("verilog") > 0) {
    json verilog_json = module->getGenerator()->getMetaData()["verilog"];
    return module->getGenerator()->hasPrimitiveExpressionLambda() &&
      verilog_json["primitive_type"] == "other" &&
      module->getName() == "const" && _inline;
  }
  if (module->getMetaData().count("verilog") > 0) {
    json verilog_json = module->getMetaData()["verilog"];
    return module->hasPrimitiveExpressionLambda() &&
      verilog_json["primitive_type"] == "other" &&
      module->getName() == "const" && _inline;
  }
  return false;
}

bool can_inline_mux_op(CoreIR::Module* module, bool _inline) {
  if (
    module->isGenerated() &&
    module->getGenerator()->getMetaData().count("verilog") > 0) {
    json verilog_json = module->getGenerator()->getMetaData()["verilog"];
    return module->getGenerator()->hasPrimitiveExpressionLambda() &&
      verilog_json["primitive_type"] == "other" && module->getName() == "mux" &&
      _inline;
  }
  if (module->getMetaData().count("verilog") > 0) {
    json verilog_json = module->getMetaData()["verilog"];
    return module->hasPrimitiveExpressionLambda() &&
      verilog_json["primitive_type"] == "other" && module->getName() == "mux" &&
      _inline;
  }
  return false;
}

std::unique_ptr<vAST::StructuralStatement> inline_mux_op(
  std::pair<std::string, CoreIR::Instance*> instance,
  std::unique_ptr<vAST::Connections> verilog_connections) {
  MuxReplacer transformer(
    verilog_connections->at("in0"),
    verilog_connections->at("in1"),
    verilog_connections->at("sel"));
  return std::make_unique<vAST::ContinuousAssign>(
    std::make_unique<vAST::Identifier>(instance.first + "_out"),
    transformer.visit(get_primitive_expr(instance.second)));
}

bool can_inline_slice_op(CoreIR::Module* module, bool _inline) {
  if (
    module->isGenerated() &&
    module->getGenerator()->getMetaData().count("verilog") > 0) {
    json verilog_json = module->getGenerator()->getMetaData()["verilog"];
    return module->getGenerator()->hasPrimitiveExpressionLambda() &&
      verilog_json["primitive_type"] == "other" &&
      module->getName() == "slice" && _inline;
  }
  return false;
}
