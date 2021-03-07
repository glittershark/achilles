with import (builtins.fetchTarball {
  url = "https://github.com/nixos/nixpkgs/archive/93a812bb9f9c398bd5b9636ab3674dcfe8cfb884.tar.gz";
  sha256 = "14zzsgnigd7vjbrpzm1s4qsknm73sci38ss00x96wamz6psaxyah";
}) {};

mkShell {
  buildInputs = [
    clang_11
    llvm_11.lib
    llvmPackages_11.bintools
    llvmPackages_11.clang
    llvmPackages_11.libclang.lib
    zlib
    ncurses
    libxml2
    libffi
    pkg-config
  ];

}
