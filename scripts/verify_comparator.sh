#!/usr/bin/env bash
# Run leanprover/comparator on comparator configs (comparators/<Name>.json).
# Adapted from the CaffarelliKohnNirenberg verification script (Apache-2.0, PalomarTemplate).
# usage: scripts/verify_comparator.sh [Name ...]   (default: every config whose Solution file exists)
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
cache=${CDG_COMPARATOR_CACHE:-"$HOME/.cache/cdg-comparator"}
comparator_commit=32bd61da1d68fbaa310234964e9b820b03a0f82f   # toolchain v4.35.0-rc2
lean4export_commit=6cea97789dc088ea47fcea15692db85685aedac5  # toolchain v4.35.0-rc2
co() { [ -d "$2/.git" ] || git clone -q --filter=blob:none "$1" "$2"
       git -C "$2" fetch -q --depth 1 origin "$3"; git -C "$2" checkout -q --detach "$3"; }
mkdir -p "$cache"
co https://github.com/leanprover/comparator.git "$cache/comparator" "$comparator_commit"
co https://github.com/leanprover/lean4export.git "$cache/lean4export" "$lean4export_commit"
for t in comparator lean4export; do
  [ "$(tr -d '[:space:]' < "$cache/$t/lean-toolchain")" = "$(tr -d '[:space:]' < "$root/lean-toolchain")" ] \
    || { echo "error: $t toolchain differs from the project's" >&2; exit 1; }
  [ -x "$cache/$t/.lake/build/bin/$t" ] || (cd "$cache/$t" && LEAN_NUM_THREADS=3 nice -n 10 lake build "$t")
done
landrun=${COMPARATOR_LANDRUN:-$(command -v landrun || true)}; nanoda=${COMPARATOR_NANODA:-$(command -v nanoda_bin || true)}
[ -n "$landrun" ] && [ -x "$landrun" ] || { echo "error: landrun not found; install it (github.com/zouuup/landrun) or set COMPARATOR_LANDRUN" >&2; exit 1; }
[ -n "$nanoda" ] && [ -x "$nanoda" ] || { echo "error: nanoda_bin not found; build github.com/robsimmons/nanoda_lib (cargo build --release) or set COMPARATOR_NANODA" >&2; exit 1; }
cd "$root"
names=("$@")
if [ ${#names[@]} -eq 0 ]; then
  for c in comparators/*.json; do n=$(basename "$c" .json); [ -f "CoarseDeGiorgiAudit/Solution/$n.lean" ] && names+=("$n"); done
fi
status=0
for n in "${names[@]}"; do
  echo "=== comparator: $n"
  # Build the challenge and solution first under the caller's LEAN_NUM_THREADS: the comparator's own build
  # does not inherit it, so it must find nothing to rebuild.
  mods=$(python3 -c 'import json,sys; c=json.load(open(sys.argv[1])); print(c["challenge_module"], c["solution_module"])' "comparators/$n.json")
  LEAN_NUM_THREADS=${LEAN_NUM_THREADS:-1} nice -n 10 lake build $mods >/dev/null \
    || { echo "=== $n: FAIL (build)"; status=1; continue; }
  if COMPARATOR_LEAN4EXPORT="$cache/lean4export/.lake/build/bin/lean4export" COMPARATOR_NANODA="$nanoda" \
     COMPARATOR_LANDRUN="$landrun" LEAN_NUM_THREADS=${LEAN_NUM_THREADS:-2} \
     nice -n 10 lake env "$cache/comparator/.lake/build/bin/comparator" "comparators/$n.json"; then
    echo "=== $n: PASS"
  else echo "=== $n: FAIL"; status=1; fi
done
exit $status
