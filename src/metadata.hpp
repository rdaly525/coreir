struct Metadata {
  MetadataKind kind;
  Metadata(MetadataKind kind) : kind(kind) {}
  bool isKind(MetadataKind k) {return k==kind;}
}

struct VerilogMetadata {
  string verilog;
  VerilogMetadata(string verilog) : verilog(verilog), Metadata(VERILOG) {}
}
