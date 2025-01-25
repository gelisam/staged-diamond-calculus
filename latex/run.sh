#!/bin/bash
set -e

clear
pdflatex -halt-on-error diamond-modal-type-theory.tex
echo "success."
