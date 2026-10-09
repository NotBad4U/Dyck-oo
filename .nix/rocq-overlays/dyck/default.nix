## Local package definition for this development.
## It is not in nixpkgs, so we describe it here; the coq-nix-toolbox
## overrides `version` with the local sources when building the main job.
## Doc: https://nixos.org/manual/nixpkgs/stable/#sec-language-coq

{
  lib,
  mkRocqDerivation,
  stdlib,
  version ? null,
}:

mkRocqDerivation {
  pname = "dyck";
  owner = "NotBad4U";

  inherit version;
  ## No release: the version is always the local sources.
  defaultVersion = null;

  propagatedBuildInputs = [
    stdlib
  ];

  meta = {
    description = "Infinite Dyck paths algebra for unbounded interval temporal logic";
  };
}
