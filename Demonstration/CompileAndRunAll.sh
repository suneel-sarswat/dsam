#!/bin/bash

ocamlc -c certified.mli 
ocamlc -o create certified.ml Print.ml Create.ml
./create

ocamlc -c certified.mli
ocamlc -o compare certified.ml Print.ml Compare.ml
./compare
