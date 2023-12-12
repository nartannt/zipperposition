{
  inputs = {
    flake-utils.url = "github:numtide/flake-utils";
    nixpkgs.url = "github:NixOs/nixpkgs/nixpkgs-unstable";
  };


  outputs = { self, flake-utils, nixpkgs }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; };
        inherit (pkgs) ocamlPackages;
      in
      rec {
        packages = {
          # from https://gitlab.com/vbgl/nixtrapkgs
          msat = ocamlPackages.buildDunePackage rec {

            pname = "msat";
            version = "0.9.1";

            src = pkgs.fetchFromGitHub {
              owner = "Gbury";
              repo = pname;
              rev = "v${version}";
              hash = "sha256-ER7ZUejW+Zy3l2HIoFDYbR8iaKMvLZWaeWrOAAYXjG4=";
            };

            propagatedBuildInputs = [ ocamlPackages.iter ];

            meta = with pkgs.lib; {
              license = licenses.apsl20;
              homepage = "https://gbury.github.io/mSAT/";
              description = "A modular sat/smt solver with proof output";
            };
          };


          default = ocamlPackages.buildDunePackage {
            pname = "zipperposition";
            version = "2.1";

            duneVersion = "3";

            src = ./.;

            doCheck = true;
            checkInputs = with ocamlPackages; [ qcheck-alcotest ];

            buildInputs = with ocamlPackages; [
              containers
              containers-data
              iter
              menhirLib
              fileutils
              mtime
              oseq
              self.packages.${system}.msat
              zarith
            ];

            nativeBuildInputs = with ocamlPackages; [
              menhir
            ];

            # I believe buildDunePackage calls the wrong command for
            # multi-outputs dune projects. I know this is an anti-pattern, but
            # this works just fine.
            buildPhase = ''
              dune build --profile=release ''${enableParallelBuilding:+-j $NIX_BUILD_CORES}
            '';

            checkPhase = ''
              dune runtest --profile=release ''${enableParallelBuilding:+-j $NIX_BUILD_CORES}
            '';

            meta = with pkgs.lib; {
              description = ''
                An automatic theorem prover in OCaml for typed higher-order
                logic with equality and datatypes.
              '';
              longDescription = ''
                An automatic theorem prover in OCaml for typed higher-order
                logic with equality and datatypes, based on
                superposition+rewriting; and Logtk, a supporting library for
                manipulating terms, formulas, clauses, etc.
              '';
              homepage = "https://sneeuwballen.github.io/zipperposition/";
              license = licenses.bsd2;
            };
          };
        };

        devShells.default = pkgs.mkShell (with packages.default; {
          name = pname + "-dev";
          packages =
            buildInputs ++ nativeBuildInputs ++ 
            (with ocamlPackages; [ merlin ocaml-lsp ocamlformat utop ]);
          # TODO: only keep one of merlin and ocaml-lsp, preferably ocaml-lsp
        });
      });
}
