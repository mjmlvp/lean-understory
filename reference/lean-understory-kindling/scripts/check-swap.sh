#!/usr/bin/env bash
# The swap test: literally the same downstream files, two builds.
# Only Demo/Spec.lean (the interface module) and the expected test output differ.
set -euo pipefail
cd "$(dirname "$0")/.."
shared="Demo/Downstream.lean Demo/MathlibStyle.lean Demo/TwoImpls.lean Demo/Audit.lean"
before=$(sha256sum $shared)
for v in classical constructive; do
  cp "variants/$v/Spec.lean"  Demo/Spec.lean
  cp "variants/$v/Tests.lean" Demo/Tests.lean
  lake build > "build-$v.log" 2>&1 || { cat "build-$v.log"; exit 1; }
  echo "== variant $v: build and all #guard_msgs passed"
done
[ "$before" = "$(sha256sum $shared)" ] && echo "== downstream files unchanged, byte for byte"
echo "== the complete difference in the interface module:"
diff variants/classical/Spec.lean variants/constructive/Spec.lean || true
