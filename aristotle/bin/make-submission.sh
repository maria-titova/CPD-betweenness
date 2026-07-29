#!/usr/bin/env bash
# make-submission.sh <call-dir>
#
# Build a SELF-CONTAINED Aristotle submission tree for one thin-B call:
#   = the whole `lean/` project (package CPDLinear) MINUS .lake,
#   + `SPECIFICATION.tex`  (a copy of tex/v5.tex — the authoritative writeup),
#   + `TASK.md`            (a copy of the call's prompt.md, so the prover can
#                           re-read its own instructions from inside the project).
#
# We ship the FULL Lean project, not a stripped subset: the thin-B targets sit
# on top of the proved single-valued machinery (BetweennessOrder, Restriction,
# Coalition...) and the prover needs to read it. Aristotle rebuilds against its
# own matched mathlib v4.28.0, so `.lake/` is excluded (~7GB, and the SDK would
# otherwise walk it — .lake is exempt from .gitignore filtering in the SDK).
set -euo pipefail

CALLDIR="${1:?usage: make-submission.sh <call-dir>}"
CALLDIR="$(cd "$CALLDIR" && pwd)"
ROOT="/projects/lean/CPD-betweenness"
DEST="$CALLDIR/submission"

[[ -f "$CALLDIR/prompt.md" ]] || { echo "missing $CALLDIR/prompt.md" >&2; exit 1; }

rm -rf "$DEST"; mkdir -p "$DEST"
rsync -a --exclude '.lake/' --exclude '.git/' "$ROOT/lean"/ "$DEST"/
cp "$ROOT/tex/v5.tex" "$DEST/SPECIFICATION.tex"
cp "$CALLDIR/prompt.md" "$DEST/TASK.md"

# Sanity: the submission must carry the targets and must NOT carry a build dir.
[[ -f "$DEST/CPDLinear/ThinB.lean" ]] || { echo "ThinB.lean missing from bundle" >&2; exit 1; }
[[ -d "$DEST/.lake" ]] && { echo ".lake leaked into bundle" >&2; exit 1; }

echo "$DEST"
echo "  files: $(find "$DEST" -type f | wc -l)   size: $(du -sh "$DEST" | cut -f1)"
echo "  sorry: $(grep -rc '\bsorry\b' "$DEST"/CPDLinear/*.lean | grep -v ':0$' | tr '\n' ' ')"
