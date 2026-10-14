#!/usr/bin/env bash
# run_all.sh -- every check outside Lean; outputs go to build/.
#   C:      sfcheck.c computes beta_k and SF_k of G_k exactly for 2 <= k <= 7 and checks that
#           S = V - {p, q1, q2} is a minimal k-star-forming set; the output must equal
#           data/family_values.txt
#   Python: check_definition.py recomputes beta_k and SF_k of G_3 and G_4 straight from
#           Definition 2.1 of Sahbi, and checks the 10-vertex example for k = 2 of
#           the-omega-institute/trureturing pull request 14727
#   C:      chainlemmas.c checks Lemmas 4.1-4.3 on every minimal k-star-forming set of every chain
#           graph with at most 12 vertices, 2 <= k <= 7; the output must equal data/chain_lemmas.txt
#   Search: the quick searches of scripts/searches.sh (bipartite graphs up to 11 vertices, triangle-free
#           graphs up to 10, chain graphs and trees up to 14) must reproduce data/search/
# Needs a C compiler, Python 3 and nauty.
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
B="$ROOT/build"
mkdir -p "$B"
cd "$ROOT"

echo "== C: the graphs G_k"
cc -O2 -Wall -Wextra -Werror -o "$B/sfcheck" verification/c/sfcheck.c
"$B/sfcheck" | tee "$B/family_values.txt"
diff "$B/family_values.txt" data/family_values.txt

echo "== C: the lemmas on chain graphs"
cc -O2 -Wall -Wextra -Werror -o "$B/chainlemmas" verification/c/chainlemmas.c
for k in 2 3 4 5 6 7; do "$B/chainlemmas" 12 "$k"; done | tee "$B/chain_lemmas.txt"
diff "$B/chain_lemmas.txt" data/chain_lemmas.txt

echo "== Python: Definition 2.1, G_3, G_4 and the k = 2 example"
python3 -I verification/python/check_definition.py | tee "$B/check_definition.txt"

echo "== exhaustive searches (quick part)"
scripts/searches.sh quick "$B/search" | tee "$B/searches.txt"
for f in "$B"/search/*.txt; do
  diff "$f" "data/search/$(basename "$f")"
done
echo "all checks passed"
