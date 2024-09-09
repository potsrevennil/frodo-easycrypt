{
  description = "easycrypt-test";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-24.05";
    easycrypt-nightly = {
      url = "github:Easycrypt/easycrypt?ref=4d79300df74984f206b69dfc50cf628ef7e914c1";
      inputs.nixpkgs-lib.follows = "nixpkgs";
    };
    jasmin-nightly = {
      url = "github:jasmin-lang/jasmin/e4640e7dcdb01d1ba63617a5d78456e1209d699c";
      flake = false;
    };

    flake-parts = {
      url = "github:hercules-ci/flake-parts";
      inputs.nixpkgs-lib.follows = "nixpkgs";
    };
  };

  outputs = inputs@{ flake-parts, nixpkgs, easycrypt-nightly, jasmin-nightly, ... }:
    flake-parts.lib.mkFlake { inherit inputs; } {
      imports = [ ];
      systems = [ "x86_64-linux" "aarch64-linux" "aarch64-darwin" "x86_64-darwin" ];
      perSystem = { pkgs, system, ... }:
        let
          easycrypt = easycrypt-nightly.packages.${system};
          jasminc = pkgs.callPackage "${jasmin-nightly}/default.nix" { inherit pkgs; };
        in
        {
          # Per-system attributes can be defined here. The self' and inputs'
          # module parameters provide easy access to attributes of the same
          # system.

          # Equivalent to  inputs'.nixpkgs.legacyPackages.hello;
          _module.args.pkgs = import nixpkgs {
            inherit system;
            config.allowUnfree = true;
          };

          devShells.default = pkgs.mkShellNoCC {
            packages = builtins.attrValues {
              easycrypt = easycrypt.with_provers;
              jasminc = jasminc;

              inherit (pkgs)
                direnv
                nix-direnv

                why3;
            };

            shellHook = ''
              export PATH=$PWD/bin:$PATH
              easycrypt why3config
            '';
          };
        };
      flake = {
        # The usual flake attributes can be defined here, including system-
        # agnostic ones like nixosModule and system-enumerating ones, although
        # those are more easily expressed in perSystem.

      };
    };
}
