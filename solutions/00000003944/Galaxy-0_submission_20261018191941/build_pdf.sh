#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
# Optional first argument: directory containing pdflatex.fmt on minimal TeX installs.
if [ "${1:-}" != "" ]; then
 export TEXFORMATS="$1:"
 export TEXINPUTS=/usr/share/texlive/texmf-dist/tex//:
 export TFMFONTS=/usr/share/texlive/texmf-dist/fonts/tfm//:
 export T1FONTS=/usr/share/texlive/texmf-dist/fonts/type1//:
 export TEXFONTMAPS=/usr/share/texlive/texmf-dist/fonts/map//:
 export TEXMFVAR="$(pwd)/.tex-cache"
fi
pdflatex -no-shell-escape -output-format=pdf -interaction=nonstopmode -halt-on-error main.tex
pdflatex -no-shell-escape -output-format=pdf -interaction=nonstopmode -halt-on-error main.tex
