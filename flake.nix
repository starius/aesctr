{
  description = "aesctr: Go's arm64 AES-CTR assembly, proved correct as machine code with LNSym";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-26.05";
    lean4-nix = {
      url = "github:lenianiva/lean4-nix";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    # The AArch64 model the proofs run the machine code in.
    lnsym = {
      url = "github:leanprover/LNSym/49f8a1d9e46f8dcfc345f4bc15d35b0ba845ff5c";
      flake = false;
    };
  };

  outputs =
    {
      self,
      nixpkgs,
      lean4-nix,
      lnsym,
    }:
    let
      systems = [
        "x86_64-linux"
        "aarch64-linux"
      ];
      forAllSystems = f: nixpkgs.lib.genAttrs systems (system: f nixpkgs.legacyPackages.${system});
    in
    {
      devShells = forAllSystems (
        pkgs:
        let
          # Lean v4.35.0 (the version LNSym is on), from lean4-nix's binary release.
          lean =
            (pkgs.callPackage "${lean4-nix}/lib/toolchain.nix" {
              clang = pkgs.llvmPackages_23.clang;
              lld = pkgs.llvmPackages_23.lld;
              llvmPackages = pkgs.llvmPackages_23;
            }).fetchBinaryLean
              (import "${lean4-nix}/manifests/v4.35.0.nix");
        in
        {
          default = pkgs.mkShell {
            packages = [
              lean.lean-all
              # Bootstraps the Go tree under test (make.bash) and builds the
              # benchmark harness.
              pkgs.go
              pkgs.qemu-user
              pkgs.llvmPackages_19.llvm # llvm-objdump, to cross-check disassembly
              pkgs.python3
              pkgs.git
            ];
            LNSYM_SRC = "${lnsym}";
          };
        }
      );

      formatter = forAllSystems (pkgs: pkgs.nixfmt-rfc-style or pkgs.nixfmt);
    };
}
