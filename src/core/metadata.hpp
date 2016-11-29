#ifndef METADATA_HPP_
#define METADATA_HPP_

class Metadata {
  string type;
  public :
    Metadata(string type) : type(type) {}

}

class SDF : public Metadata {
  
  public :
    SDF() : Metadata("SDF") {}

}

class Pipeline : public Metadata {

  public :
    Pipeline() : Metadata("Pipeline") {}
}


#endif // METADATA_HPP_
