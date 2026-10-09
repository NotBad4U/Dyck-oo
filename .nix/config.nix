{
  ## DO NOT CHANGE THIS
  format = "1.0.0";
  ## unless you made an automated or manual update
  ## to another supported format.

  ## The attribute to build from the local sources,
  ## using the overlay located in `.nix/rocq-overlays/dyck`.
  attribute = "dyck";

  ## Indicate the relative location of your _CoqProject
  coqproject = "_CoqProject";

  ## The toolbox already puts `coq-lsp` in the shell; this adds the language
  ## server the VsRocq editor extension talks to.
  buildInputs = [ "vsrocq-language-server" ];

  default-bundle = "9.2";

  ## Rocq 9.2 is the latest Rocq of the pinned nixpkgs (`.nix/nixpkgs.nix`).
  ## The development only needs Rocq and its standard library (`Stdlib`
  ## prefix), so only `rocqPackages` are pinned; `coq` is kept in step so
  ## that the editor servers pulled from `coqPackages` are not rebuilt from
  ## source.
  bundles."9.2" = {
    rocqPackages = {
      rocq-core.override.version = "9.2";
    };
    coqPackages.coq.override.version = "9.2";
  };

  ## Cachix caches to use in CI
  cachix.coq = {};
  cachix.coq-community = {};
}
