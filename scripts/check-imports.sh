#!/usr/bin/env bash
# Enforce the dependency rules of CLAUDE.md on every module's import lines.
#
#   Understory/Core   imports Init, Std, Lean and Understory.Core only (no Mathlib)
#   Understory/**     never imports PoV or Test
#   PoV/**            imports Mathlib, Lean core and public Understory modules
#                     (a module is internal when its path contains `Internal`)
#   everything        never imports the frozen reference (Kindling, Demo, Scale)
#
# Usage: scripts/check-imports.sh && lake build
set -euo pipefail
cd "$(dirname "$0")/.."

fail=0
violation() { echo "import rule violated: $1: import $2 ($3)"; fail=1; }

imports() { sed -n 's/^\(public \)\?import \+\([A-Za-z0-9_.]\+\).*/\2/p' "$1"; }

while IFS= read -r f; do
  for m in $(imports "$f"); do
    case "$m" in Kindling|Kindling.*|Demo|Demo.*|Scale|Scale.*)
      violation "$f" "$m" "nothing imports reference/";; esac
    case "$f" in
      Understory/Core/*|Understory/Core.lean)
        case "$m" in Init|Init.*|Std|Std.*|Lean|Lean.*|Understory.Core|Understory.Core.*) ;;
          *) violation "$f" "$m" "Core imports Lean core only";; esac;;
    esac
    case "$f" in
      Understory/*|Understory.lean)
        case "$m" in PoV|PoV.*|Test|Test.*)
          violation "$f" "$m" "the library never imports its consumers";; esac;;
      PoV/*|PoV.lean)
        case "$m" in
          *Internal*) violation "$f" "$m" "PoV imports public modules only";;
          Understory|Understory.*|PoV|PoV.*|Mathlib|Mathlib.*|Init|Init.*|Std|Std.*|Lean|Lean.*) ;;
          *) violation "$f" "$m" "PoV imports Understory, Mathlib and Lean core only";; esac;;
    esac
  done
done < <(find Understory Understory.lean PoV PoV.lean Test Test.lean -name '*.lean' 2>/dev/null | sort)

[ "$fail" -eq 0 ] && echo "imports: all dependency rules hold"
exit "$fail"
