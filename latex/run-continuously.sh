#!/bin/bash
set -e

./run.sh
fswatcher --throttle 300 --path diamond-modal-type-theory.tex -- ./run.sh
