{ stdenv, pkgs, idrisPackages }:

idrisPackages.build-idris-package {
  name = "idris-stbx-core";
  version = "dev";
  src = ./.;
  doCheck = true;

  idrisDeps = with idrisPackages; [
    contrib
  ];

  meta = {
    description = "Literate Idris glued open petrinet semantics";
    homepage = "https://statebox.org/";
  };
}
