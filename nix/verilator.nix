# Custom verilator package so we can use the pinned verilator version specified in
# sources.json

{ stdenv, perl, flex, bison, sources }:

stdenv.mkDerivation rec {
  name = "verilator";

  src = sources.verilator;

  enableParallelBuilding = true;
  buildInputs = [ perl flex bison ];

  meta = {
    description = "Fast and robust (System)Verilog simulator/compiler";
    homepage    = "https://www.veripool.org/wiki/verilator";
    license     = stdenv.lib.licenses.lgpl3;
    platforms   = stdenv.lib.platforms.unix;
  };
}
