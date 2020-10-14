#pragma once

json generateMemoryVerilogInterface(bool with_ren) {
  json result = {
    "input clk",
    "input [width-1:0] wdata",
    "input [$clog2(depth)-1:0] waddr",
    "input wen",
    "output [width-1:0] rdata",
    "input [$clog2(depth)-1:0] raddr"};
  if (with_ren) { result.push_back("input ren"); }
  return result;
}

std::string generateMemoryVerilogBody(
  bool verilator_debug,
  bool with_ren,
  bool with_sync_read_param) {
  std::string verilog_str = "  reg [width-1:0] data [depth-1:0]";
  if (verilator_debug) { verilog_str += "/*verilator public*/"; }
  verilog_str += ";\n";
  verilog_str +=
    // verilator doesn't support 2d array parameter, so we pack it into a 1d
    // array
    "  generate if (has_init) begin\n"
    "    genvar j;\n"
    "    for (j = 0; j < depth; j = j + 1) begin\n"
    "      initial begin\n"
    "        data[j] = init[(j+1)*width-1:j*width];\n"
    "      end\n"
    "    end\n"
    "  end\n"
    "  endgenerate\n"
    ""
    "  always @(posedge clk) begin\n"
    "    if (wen) begin\n"
    "      data[waddr] <= wdata;\n"
    "    end\n"
    "  end\n"
    "";
  if (with_sync_read_param) {
    // coreir.mem
    ASSERT(!with_ren, "Cannot use ren with sync_read_param");
    verilog_str +=
      "  generate if (sync_read) begin\n"
      "  reg [width-1:0] rdata_reg;\n"
      "  always @(posedge clk) begin\n"
      "    rdata_reg <= data[raddr];\n"
      "  end\n"
      "  assign rdata = rdata_reg;\n"
      "  end else begin\n"
      "  assign rdata = data[raddr];\n"
      "  end\n"
      "  endgenerate\n";
  }
  else {
    // for memory.sync_read_mem
    verilog_str +=
      "  reg [width-1:0] rdata_reg;\n"
      "  always @(posedge clk) begin\n";
    if (with_ren) { verilog_str += "    if (ren) rdata_reg <= data[raddr];\n"; }
    else {
      verilog_str += "    rdata_reg <= data[raddr];\n";
    }
    verilog_str +=
      "  end\n"
      "  assign rdata = rdata_reg;\n";
  }
  return verilog_str;
}

void CoreIRLoadVerilog_memory(CoreIR::Context* c) {
  {
    // sync_read_mem
    json vjson;
    vjson["prefix"] = "coreir_";
    vjson["interface"] = generateMemoryVerilogInterface(true);
    vjson["parameters"] = {"has_init"};
    vjson["definition"] = generateMemoryVerilogBody(false, true, false);
    vjson["verilator_debug_definition"] = generateMemoryVerilogBody(
      true,
      true,
      false);
    CoreIR::Namespace* memory = c->getNamespace("memory");
    memory->getGenerator("sync_read_mem")->getMetaData()["verilog"] = vjson;
  }
}
