
{
  inputs = {
    nixpkgs.url = "nixos";
  };

  outputs = { self, nixpkgs, ... }:
    let
      pkgs = import nixpkgs { system = "x86_64-linux"; };
      shell = pkgs.mkShell {
        packages = builtins.attrValues {
          inherit (pkgs)
            bazel;
        };
      };
    in {
      devShell.x86_64-linux = shell;
    };
}
