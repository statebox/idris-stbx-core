{ stdenv, haskellPackages, texlive }:

stdenv.mkDerivation rec {
  name = "idris-statebox-core-doc-${version}";
  version = "dev";
  src = ./.;

  buildInputs = [
    haskellPackages.lhs2tex
    texlive.combined.scheme-full
  ];

  buildPhase = ''
    cd docs
    mkdir out
    lhs2TeX -o out/main.tex main.lidr
    cd out
    HOME="$PWD" pdflatex main.tex
  '';

  installPhase = ''
    mkdir -p $out/share/doc/idris-stbx-core
    cp main.pdf $out/share/doc/idris-stbx-core
  '';

  meta = {
    description = "Literate Idris glued open petrinet semantics";
    homepage = "https://statebox.org/";
  };
}
