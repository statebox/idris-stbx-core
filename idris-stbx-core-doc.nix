{ stdenv, pandoc, texlive }:

stdenv.mkDerivation rec {
  name = "idris-stbx-core-doc-${version}";
  version = "dev";
  src = ./.;

  buildInputs = [
    pandoc
    texlive.combined.scheme-full
  ];

  buildPhase = ''
    cd docs
    make
  '';

  installPhase = ''
    mkdir -p $out/share/doc/idris-stbx-core
    cp main.pdf main.html $out/share/doc/idris-stbx-core
  '';

  meta = {
    description = "Literate Idris glued open petrinet semantics";
    homepage = "https://statebox.org";
  };
}
