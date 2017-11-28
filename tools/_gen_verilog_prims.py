import math
import numpy as np


class vmodule:
  def __init__(self,name):
    self.name = name
    self.params = []
    self.ports = []

  def add_param(self,name,init=None):
    self.params.append([name,init])

  def add_input(self,name, width=None):
    self.ports.append(["input",name,width])
  
  def add_output(self,name, width=None):
    self.ports.append(["output",name,width])
  
  def add_body(self,body):
    self.body = body

  def to_string(self):
    assert len(self.ports) > 0
    assert self.body
    s = "module %s " % self.name
    if (len(self.params) > 0):
      ps = []
      for pa in self.params:
        p = "parameter " + pa[0]
        if (not pa[1] is None):
          p += "="+str(pa[1])
        ps.append(p)
      s += "#(%s) " % ",".join(ps)
    ports = []
    for port in self.ports:
      p = "  " + port[0]
      width = port[2]
      if (width is not None):
        if type(width) is str:
          p += " [%s-1:0]" % width
        elif type(width) is int:
          p += "[%s:0]" % str(width-1)
        else:
          assert(False)
      p += " " + port[1]
      ports.append(p)
    ports.sort()
    s += "(\n%s\n);\n" % ",\n".join(ports)
    s += self.body + "\n"
    s += "endmodule\n\n"
    return s

if __name__ == "__main__":
  
  
  
  ops = {
    "unary":{
      "not":"~in",
      "neg":"-in"
    },
    "unaryReduce":{
      "andr":"&in",
      "orr":"|in",
      "xorr":"^in"
    },
    "binary":{
      "and":"in0 & in1",
      "or":"in0 | in1",
      "xor":"in0 ^ in1",
      "dshl":"in0 << in1",
      "dlshr":"in0 >> in1",
      "dashr":"$signed(in0) >>> in1", #Could be buggy
      "add":"in0 + in1",
      "sub":"in0 - in1",
      "mul":"in0 * in1",
      "udiv":"in0 / in1",
      #"urem":"in0 % in1",
      "sdiv":"$signed(in0) / $signed(in1)", #Could be buggy
      #"srem":"$signed(in0) % $signed(in1)", 
      #"smod":"$signed(in0) % $signed(in1)", #TODO definitely wrong
    },
    "static_shift": {
        "lshr": "in >> SHIFTBITS",
        "shl": "in << SHIFTBITS",
        "ashr": "$signed(in) >>> SHIFTBITS"
    },
    "binaryReduce":{
      "eq":"in0 == in1",
      "slt":"$signed(in0) < $signed(in1)",
      "sgt":"$signed(in0) > $signed(in1)",
      "sle":"$signed(in0) <= $signed(in1)",
      "sge":"$signed(in0) >= $signed(in1)",
      "ult":"in0 < in1",
      "ugt":"in0 > in1",
      "ule":"in0 <= in1",
      "uge":"in0 >= in1"
    }
  }

  with open("coreir_prims.v","w") as f:
    
    for t in ["unary","unaryReduce","binary","static_shift","binaryReduce"]:
      f.write("//%s ops\n" % t)
      for op, exp in ops[t].iteritems():
        v = vmodule("coreir_"+op)
        v.add_param("width",16)
        if (t.find("unary")>=0):
          v.add_input("in","width")
        elif t == "static_shift":
          v.add_input("in","width")
          v.add_param("SHIFTBITS", 1)
        else:
          v.add_input("in0","width")
          v.add_input("in1","width")
        if (t.find("Reduce")>=0):
          v.add_output("out")
        else:
          v.add_output("out","width")
        v.add_body("  assign out = %s;" % exp)
        f.write(v.to_string())
    
    #Do the mux
    f.write("//ternary op\n")
    v = vmodule("coreir_mux")
    v.add_param("width",16)
    v.add_input("in0","width")
    v.add_input("in1","width")
    v.add_input("sel")
    v.add_output("out","width")
    v.add_body("  assign out = sel ? in1 : in0;")
    f.write(v.to_string())

    f.write("//1 bit ops\n")
    #Do the 1 bit versions
    for name,op in [("and","&"),("or","|"),("xor","^")]:
      v = vmodule("coreir_bit"+name)
      v.add_input("in0")
      v.add_input("in1")
      v.add_output("out")
      v.add_body("  assign out = in0 " + op + "in1;")
      f.write(v.to_string())

    v = vmodule("coreir_bitnot")
    v.add_input("in")
    v.add_output("out")
    v.add_body("  assign out = ~in;")
    f.write(v.to_string())
    
    v = vmodule("coreir_bitmux")
    v.add_input("in0")
    v.add_input("in1")
    v.add_input("sel")
    v.add_output("out")
    v.add_body("  assign out = sel ? in1 : in0;")
    f.write(v.to_string())



    #Do Slice
    f.write("//slice op\n")
    v = vmodule("coreir_slice")
    v.add_param("width",16)
    v.add_param("lo",0)
    v.add_param("hi",16)
    v.add_input("in","width")
    v.add_output("out","(hi-lo)")
    v.add_body("  assign out = in[hi-1:lo];")
    f.write(v.to_string())
    
    #Do concat
    f.write("//concat op\n")
    v = vmodule("coreir_concat")
    v.add_param("width0",16)
    v.add_param("width1",16)
    v.add_input("in0","width0")
    v.add_input("in1","width1")
    v.add_output("out","(width0+width1)")
    v.add_body("  assign out = {in0,in1};")
    f.write(v.to_string())

    #Do the Const
    f.write("//Const op\n")
    v = vmodule("coreir_const")
    v.add_param("width",16)
    v.add_param("value",0)
    v.add_output("out","width")
    v.add_body("  assign out = value;")
    f.write(v.to_string())
    
    #Do the Bit Const
    f.write("//Bit Const op\n")
    v = vmodule("coreir_bitconst")
    v.add_param("value",0)
    v.add_output("out")
    v.add_body("  assign out = value;")
    f.write(v.to_string())
    
    #Do the term
    f.write("//term op\n")
    v = vmodule("coreir_term")
    v.add_param("width",16)
    v.add_input("in","width")
    v.add_body("  ")
    f.write(v.to_string())
    
    #Do the bitterm
    f.write("//term op\n")
    v = vmodule("coreir_bitterm")
    v.add_input("in")
    v.add_body("  ")
    f.write(v.to_string())

    #Now do the registers
    #name is the regex: Reg_(P|N)R?C?E?
    #P=posedge clock,
    #N=negedge clock,
    #R=rst (asynchronous)
    #C=clr (sychronous)
    #E=en

    f.write("//Now all the register permutations\n")
    #posedge = bit 0
    #rst = bit 1
    #clr = bit 2
    #en = bit 3
    def rexpr(clr,en):
      expr = "in"
      if (clr):
        expr = "(clr ? init : in)"
      if (en):
        expr = "en ? %s : r" % expr
      return expr
    for i in range(16):
      posedge = (i>>0) & 1
      rst = (i>>1) & 1
      clr = (i>>2) & 1
      en = (i>>3) & 1
      if (rst and clr):
        continue
      body = "  reg [width-1:0] r;\n"
      body += "  always @(%s clk" % ("posedge" if posedge else "negedge")
      if (rst):
        body += ", negedge rst"
      body += ") begin\n"
      if (rst):
        body += "    if (!rst) r <= init;\n"
        body += "    else r <= %s;\n" % rexpr(clr,en)
      else:
        body += "    r <= %s;\n" % rexpr(clr,en)
      body += "  end\n"
      body += "  assign out = r;"
      name = "reg_" + ("P" if posedge else "N")
      if (rst):
        name += "R"
      if (clr):
        name += "C"
      if (en):
        name += "E"
      v = vmodule("coreir_"+name)
      v.add_param("width",16)
      #if (rst or clr):
      v.add_param("init",0)
      v.add_input("in","width")
      v.add_input("clk")
      v.add_output("out","width")
      if (rst):
        v.add_input("rst")
      if (clr):
        v.add_input("clr")
      if (en):
        v.add_input("en")

      v.add_body(body)
      f.write(v.to_string())
    
    #Now do the single bit versions
    for i in range(16):
      posedge = (i>>0) & 1
      rst = (i>>1) & 1
      clr = (i>>2) & 1
      en = (i>>3) & 1
      if (rst and clr):
        continue
      body = "  reg r;\n"
      body += "  always @(%s clk" % ("posedge" if posedge else "negedge")
      if (rst):
        body += ", negedge rst"
      body += ") begin\n"
      if (rst):
        body += "    if (!rst) r <= init;\n"
        body += "    else r <= %s;\n" % rexpr(clr,en)
      else:
        body += "    r <= %s;\n" % rexpr(clr,en)
      body += "  end\n"
      body += "  assign out = r;"
      name = "bitreg_" + ("P" if posedge else "N")
      if (rst):
        name += "R"
      if (clr):
        name += "C"
      if (en):
        name += "E"
      v = vmodule("coreir_"+name)
      #if (rst or clr):
      v.add_param("init",0)
      v.add_input("in")
      v.add_input("clk")
      v.add_output("out")
      if (rst):
        v.add_input("rst")
      if (clr):
        v.add_input("clr")
      if (en):
        v.add_input("en")

      v.add_body(body)
      f.write(v.to_string())
      
    #Now do the memory
    v = vmodule("coreir_mem")
    v.add_param("width",16)
    v.add_param("depth",1024)
    v.add_input("clk")
    v.add_input("wdata","width")
    v.add_input("waddr","$clog2(depth)")
    v.add_input("wen")
    v.add_output("rdata","width")
    v.add_input("raddr","$clog2(depth)")
    v.add_body("""
reg [width-1:0] data[depth-1:0];

always @(posedge clk) begin
  if (wen) begin
    data[waddr] <= wdata;
  end
end

assign rdata = data[raddr];

//Initialize to X
integer i;
initial begin
  outreg = {width{1'bx}};
  for (i=0; i<depth; i=i+1) begin
    data[i] = {width{1'bx}};
  end
end
""");
    f.write(v.to_string())

