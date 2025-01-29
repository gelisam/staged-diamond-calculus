#!/bin/bash
set -e

./run.sh
fswatcher --throttle 300 --path staged-diamond-calculus.tex -- ./run.sh
