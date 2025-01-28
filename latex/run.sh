#!/bin/bash
set -e

clear
pdflatex -halt-on-error staged-diamond-type-theory.tex
echo "success."
