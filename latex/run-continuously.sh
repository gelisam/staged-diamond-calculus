#!/bin/bash
set -e

./run.sh
fswatcher --throttle 300 --path staged-diamond-type-theory.tex -- ./run.sh
