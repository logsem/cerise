{
  inputs = {
    flake-utils.url = "github:numtide/flake-utils";
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
  };


  outputs = { self, flake-utils, nixpkgs }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; };
        inherit (pkgs) coqPackages;
      in
        rec {
          packages.default = coqPackages.mkCoqDerivation {
              pname = "cerise";
              version = "0.0.0";

              coq-version = "8.20";

              src = ./.;

              buildInputs = with coqPackages; [ equations iris stdpp ];

              meta = with pkgs.lib; {
                description = "Cerise, Coq mechanization of a capability machine and principles to reason about the interaction of known and unknown code";
                homepage = "https://github.com/logsem/cerise";
                license = licenses.bsd3;
              };
            };

            devShells.default = pkgs.mkShell (with packages.default; {
              name = pname + "-dev";
              packages = buildInputs ++ [ pkgs.coq coqPackages.coq-lsp ];
            });
          });
}
