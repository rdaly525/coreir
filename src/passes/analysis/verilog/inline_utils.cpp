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

bool is_muxn(CoreIR::Module* module) {
  return module->isGenerated() && module->getGenerator()->getName() == "muxn" &&
    module->getGenerator()->getNamespace()->getName() == "commonlib";
}

std::unique_ptr<vAST::Always> make_muxn_if(
  std::unique_ptr<vAST::Connections> verilog_connections,
  int n) {
  std::vector<std::variant<
    std::unique_ptr<vAST::Identifier>,
    std::unique_ptr<vAST::PosEdge>,
    std::unique_ptr<vAST::NegEdge>,
    std::unique_ptr<vAST::Star>>>
    sensitivity_list;
  sensitivity_list.push_back(std::make_unique<vAST::Star>());

  std::unique_ptr<vAST::Expression> target = verilog_connections->at("out");
  auto ptr = dynamic_cast<vAST::Identifier*>(target.get());
  target.release();
  ASSERT(ptr, "Expected muxn output to be an identifier");

  std::unique_ptr<vAST::Identifier>
    target_id = std::unique_ptr<vAST::Identifier>(ptr);

  std::vector<std::unique_ptr<vAST::BehavioralStatement>> true_body;
  true_body.push_back(std::make_unique<vAST::BlockingAssign>(
    target_id->clone(),
    verilog_connections->at("in_data_0")));

  std::vector<std::unique_ptr<vAST::BehavioralStatement>> else_body;
  else_body.push_back(std::make_unique<vAST::BlockingAssign>(
    target_id->clone(),
    verilog_connections->at("in_data_" + std::to_string(n - 1))));

  std::unique_ptr<vAST::Expression> in_sel = verilog_connections->at("in_sel");

  std::vector<std::pair<
    std::unique_ptr<vAST::Expression>,
    std::vector<std::unique_ptr<vAST::BehavioralStatement>>>>
    else_ifs;

  for (int i = 1; i < n - 1; i++) {
    std::unique_ptr<vAST::Expression> cond = std::make_unique<vAST::BinaryOp>(
      in_sel->clone(),
      vAST::BinOp::EQ,
      vAST::make_num(std::to_string(i)));
    std::vector<std::unique_ptr<vAST::BehavioralStatement>> body;
    body.push_back(std::make_unique<vAST::BlockingAssign>(
      target_id->clone(),
      verilog_connections->at("in_data_" + std::to_string(i))));
    else_ifs.push_back({std::move(cond), std::move(body)});
  }

  std::vector<std::unique_ptr<vAST::BehavioralStatement>> body;
  body.push_back(std::make_unique<vAST::If>(
    std::make_unique<vAST::BinaryOp>(
      in_sel->clone(),
      vAST::BinOp::EQ,
      vAST::make_num("0")),
    std::move(true_body),
    std::move(else_ifs),
    std::move(else_body))

  );

  return std::make_unique<vAST::Always>(
    std::move(sensitivity_list),
    std::move(body));
}
