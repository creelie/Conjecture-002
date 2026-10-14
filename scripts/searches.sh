#!/usr/bin/env bash
# searches.sh -- the exhaustive searches behind the remarks of Section 4; outputs go to data/search/.
#
#   usage: scripts/searches.sh quick [OUTDIR]    bipartite graphs up to 11 vertices, triangle-free graphs up
#                                      to 10, chain graphs and trees up to 14 (a few minutes)
#          scripts/searches.sh full [OUTDIR]     adds bipartite graphs on 12 vertices, triangle-free graphs on
#                                      11, chain graphs and trees on 15 and 16 (a few hours on one core)
#          scripts/searches.sh sharp [OUTDIR]    Theorem 1.4 with a SAT solver for every connected graph H
#                                      with at most 8 vertices (about two hours on one core; needs
#                                      python-sat)
#
# OUTDIR defaults to data/search.  Each output file lists the pairs (G, k) with beta_k(G) != SF_k(G) (graph6, both values, a largest
# minimal k-star-forming set as a bit mask) and ends with the number of graphs read.  Needs nauty
# (geng, gentreeg, copyg; Debian names them nauty-geng etc.) and a C compiler.
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
MODE="${1:-quick}"
OUT="${2:-$ROOT/data/search}"
B="$ROOT/build"
mkdir -p "$OUT" "$B"
cc -O2 -Wall -Wextra -Werror -o "$B/sfsearch" "$ROOT/verification/c/sfsearch.c"

nauty() { if command -v "nauty-$1" > /dev/null; then echo "nauty-$1"; else echo "$1"; fi; }
GENG="$(nauty geng)"; GENTREEG="$(nauty gentreeg)"; COPYG="$(nauty copyg)"

run() {  # run NAME KMIN KMAX, graphs on stdin
  local name=$1 kmin=$2 kmax=$3
  "$B/sfsearch" "$kmin" "$kmax" > "$OUT/$name.txt" 2> "$OUT/$name.count"
  cat "$OUT/$name.count" >> "$OUT/$name.txt"
  rm -f "$OUT/$name.count"
  printf '%-22s %s\n' "$name" "$(tail -n 1 "$OUT/$name.txt")"
}

if [ "$MODE" = sharp ]; then
  for n in 1 2 3 4 5 6 7 8; do
    "$GENG" -cq "$n" | python3 -I "$ROOT/verification/python/check_sharp_sat.py" > "$OUT/sharp-sat-$n.txt"
    printf '%-22s %s\n' "sharp-sat-$n" "$(tail -n 1 "$OUT/sharp-sat-$n.txt")"
  done
  exit 0
fi
if [ "$MODE" = quick ]; then
  BIP="4 5 6 7 8 9 10 11"; TF="4 5 6 7 8 9 10"; CH="$(seq 2 14)"; TR="$(seq 2 14)"
else
  BIP="12"; TF="11"; CH="15 16"; TR="15 16"
fi
for n in $BIP; do "$GENG" -bq "$n" | run "bipartite-$n" 2 7; done
for n in $TF; do "$GENG" -tq "$n" | run "trianglefree-$n" 3 3; done
for n in $CH; do python3 -I "$ROOT/scripts/chain_graphs.py" "$n" | run "chain-$n" 3 8; done
for n in $TR; do "$GENTREEG" -q "$n" | "$COPYG" -gq | run "tree-$n" 2 6; done
