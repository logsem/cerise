# Adapted from https://gitlab.mpi-sws.org/lgaeher/refinedrust-dev/-/blob/main/flake.nix

{
  inputs = {
    flake-utils.url = "github:numtide/flake-utils";
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    self.submodules = true;
  };

  outputs = {
    self,
    flake-utils,
    nixpkgs,
  }:
    flake-utils.lib.eachDefaultSystem (system: let
      ocamlFlambda = _: prev: rec {
        # NOTE: Using OCaml 4.14 due to Rocq being slow with OCaml 5+
        # See: https://github.com/NixOS/nixpkgs/blob/nixos-25.05/pkgs/applications/science/logic/rocq-core/default.nix#L15
        ocamlPackages = prev.ocaml-ng.ocamlPackages_4_14.overrideScope (final: prev: {
          ocaml = prev.ocaml.override {
            flambdaSupport = true;
          };

          dune_3 = prev.dune_3.overrideAttrs rec {
            version = "3.21.0";

            src = pkgs.fetchurl {
              url = "https://github.com/ocaml/dune/releases/download/3.21.0/dune-3.21.0.tbz";
              hash = "sha256-521NiTaKCnACUZOur098W1QDHbo/Wb+dKvGXHcDs7d0=";
            };
          };

        });

        rocqPackages = prev.rocqPackages.overrideScope (_: prev: rec {
          dune = ocamlPackages.dune_3;

          mkRocqDerivation = args:
            prev.mkRocqDerivation ({
              preBuild = ''
            dune() { command dune $@ --display=short; }
          '';
            }
            // args);

          rocq-core = pkgs.rocq-core_9_1.override {
            inherit dune;
            customOCamlPackages = ocamlPackages;
          };
        });
      };

      overlays = [ocamlFlambda ];
      pkgs = import nixpkgs {inherit overlays system;};

      name = "cerise";
      version = "0.0.0";

      meta = with pkgs.lib; {
        description = "Cerise, Rocq mechanization of a capability machine and principles to reason about the interaction of known and unknown code";
        homepage = "https://github.com/logsem/cerise";
        license = licenses.bsd3;
      };

      ocaml = {
        pkgs = pkgs.ocamlPackages;
        version = pkgs.ocaml.version;
      };

      rocq = {
        pkgs = pkgs.rocqPackages;
        toolchain = [rocq.pkgs.rocq-core] ++ rocq.pkgs.rocq-core.nativeBuildInputs;

        version = rocq.pkgs.rocq-core.rocq-version;

        stdpp = {
          version = "1.13.0";
          sha256 = "sha256-kj8oBzarsLB4DDQ43yz4ViQbyzuISqext28wC2Fh3Sw=";
        };

        iris = {
          version = "4.5.0";
          sha256 = "sha256-oGqo+W1prLtAwRwo2U15VGhmrkDIPPE6uMbNrTa8iAQ=";
        };
      };

    in rec {
      packages = let
        mkDepRocqDerivation = pin: {
          pname,
          propagatedBuildInputs ? [rocq.pkgs.stdlib],
          owner ? "iris",
        }:
          rocq.pkgs.mkRocqDerivation {
            inherit pname propagatedBuildInputs owner;

            domain = "gitlab.mpi-sws.org";
            # NOTE: Remove `sed` line when Makefiles will be updated upstream
            preBuild = ''
              sed -i -e 's/"$(COQBIN)coq_makefile"/"$(COQBIN)rocq" makefile/g' Makefile
              patchShebangs coq-lint.sh
            '';

            release.${pin.version}.sha256 = "${pin.sha256}";
            version = pin.version;
          };
      in {
        theories = let
          # NOTE: Remove `equations` when available in Nix's `RocqPackages`
          equations = rocq.pkgs.mkRocqDerivation {
            pname = "equations";
            owner = "mattam82";
            repo = "Coq-Equations";
            opam-name = "rocq-equations";

            propagatedBuildInputs = [rocq.pkgs.stdlib ocaml.pkgs.ppx_optcomp];

            mlPlugin = true;
            useDune = true;

            version = "v1.3.1-9.1";
            release = {
              "v1.3.1-9.1".sha256 = "sha256-LtYbAR3jt+JbYcqP+m1n3AZhAWSMIeOZtmdSJwg7L1A=";
            };

            patchPhase = ''
                       sed -i -e 's/(lang dune 3.13)/(lang dune 3.21)/g' dune-project
                       sed -i -e 's/(using coq 0.8)/(using rocq 0.11)/g' dune-project
                       sed -i -e 's/coq-core/rocq-runtime/g' src/dune
                       sed -i -e 's/coq/rocq/g' examples/dune src/dune theories/dune theories/Prop/dune theories/Type/dune test-suite/dune
                       '';
          };

          stdpp = mkDepRocqDerivation rocq.stdpp {
            pname = "stdpp";
          };

          iris = mkDepRocqDerivation rocq.iris {
            pname = "iris";

            propagatedBuildInputs = [stdpp];
          };

          machine_utils = rocq.pkgs.mkRocqDerivation {
            pname = "machine_utils";
            opam-name = "machine_utils";
            src = ./machine_utils;

            propagatedBuildInputs = [iris pkgs.ocamlPackages.odoc];

            preBuild = "dune() { command dune $@ --display=short; }";
            useDune = true;
            version = "0.0.0";
          };

        in
          rocq.pkgs.mkRocqDerivation {
            inherit meta version;

            pname = name;
            opam-name = name;
            src = ./.;

            propagatedBuildInputs = [machine_utils equations];

            preBuild = "dune() { command dune $@ --display=short; }";
            useDune = true;
          };
        default = packages.theories;
      };

      devShells.default = pkgs.mkShell {
        inputsFrom = [packages.theories];
      };

    });
}
