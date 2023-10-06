{
  description = "the flake for this project";

  inputs = {
    # Convenience functions for writing flakes
    flake-utils.url = "github:numtide/flake-utils";
    # nixpkgs
    nixpkgs.url = "github:NixOs/nixpkgs/nixpkgs-unstable";
  };


  outputs = {
    self,
    flake-utils,
    nixpkgs
  }:
    flake-utils .lib.eachDefaultSystem (system:
    let 
      pkgs = import nixpkgs { inherit system; };
      ocamlPackages = pkgs.ocamlPackages;
      lib = nixpkgs.lib;
      ocaml = ocamlPackages.ocaml;
      ocaml-syntax-shims = ocamlPackages.ocaml-syntax-shims;
      ppx_let = pkgs.ppx_let;
    in {

    devShell = pkgs.mkShell {
      buildInputs = with pkgs; [
        ocaml
        dune_3
        ocamlformat
      ]
        ++ (with ocamlPackages; [
          merlin
          containers
          containers-data
          mtime
          alcotest
          qcheck-alcotest
          oseq
          iter
          findlib
          zarith
          utop
      ])
      ++ ([
        self.packages.${system}.msat
      ]);
    };

    packages = {

      default = self.packages.${system}.msat;

      msat = ocamlPackages.buildDunePackage rec {

        # from https://gitlab.com/vbgl/nixtrapkgs
        pname = "msat";
        version = "0.9.1";

        src = pkgs.fetchFromGitHub {
          owner = "Gbury";
          repo = pname;
          rev = "v${version}";
          hash = "sha256-ER7ZUejW+Zy3l2HIoFDYbR8iaKMvLZWaeWrOAAYXjG4=";
        };

        propagatedBuildInputs = [
          ocamlPackages.iter
        ];

        preBuild = ''
          dune build msat.opam
        '';

        meta = {
          license = lib.licenses.apsl20;
          homepage = "https://gbury.github.io/mSAT/";
          description = "A modular sat/smt solver with proof output";
        };
      };
    };

  });

}
