#!/usr/bin/env bash

ver="4.12.0"
if [ "$#" -ne 0 ]; then
    ver="$1"
fi

opam switch remove diagrams-coq
opam switch create diagrams-coq $ver

zlib_path=$(pkg-config zlib --cflags)
zlib_path=${zlib_path#"-I"}
zlib_include=$(pkg-config zlib --libs | cut -d ' ' -f 1)
zlib_include=${zlib_include#"-L"}

gmp_path=$(pkg-config gmp --cflags)
gmp_path=${gmp_path#"-I"}
gmp_include=$(pkg-config gmp --libs | cut -d ' ' -f 1)
gmp_include=${gmp_include#"-L"}

LIBRARY_PATH="$zlib_include:$gmp_include" CPATH="$zlib_path:$gmp_path" opam install merlin zarith