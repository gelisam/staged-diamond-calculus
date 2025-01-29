#!/bin/bash
set -e

clear
pdflatex -halt-on-error staged-diamond-calculus.tex
echo "success."
