#!/usr/bin/env bash

export FILES=(\
  Misc.v \
  Limits/Graph.v \
  Limits/ConeCat.v \
  Limits/Functor.v \
  Limits/Equalizer.v \
  Limits/Product.v \
  Limits/Pullback.v \
  Limits/Terminal.v \
  Limits/Extension.v \
  Slice/Misc.v \
  Slice/BaseChangeFunctor.v \
  Cartesian.v \
  Exponential.v \
  CartesianClosed.v \
)

echo $FILES
for f in ${FILES[@]}; do
  coqc -R . Categories -noinit -indices-matter $f
done

