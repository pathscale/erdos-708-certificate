#!/usr/bin/env zsh
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT_DIR"

WORK_DIR="$ROOT_DIR/.validation-scratch"
rm -rf "$WORK_DIR"
mkdir -p "$WORK_DIR"
trap 'rm -rf "$WORK_DIR"' EXIT

echo "=== [1/6] Checking SHA-256 manifest (SHA256SUMS.txt) ==="
grep -v " (raw)$" SHA256SUMS.txt | shasum -a 256 -c -

echo "=== [2/6] Decompressing certificate & checking raw SHA-256 ==="
zstd -dc data/erdos708-g6-cert.rec.zst > "$WORK_DIR/erdos708-g6-cert.rec"
ACTUAL_RAW_SHA="$(shasum -a 256 "$WORK_DIR/erdos708-g6-cert.rec" | awk '{print $1}')"
EXPECTED_RAW_SHA="65b22b54e7f3b652a20d1812ede4cd7664f12c5d230338fea9608acbd9792e68"
if [[ "$ACTUAL_RAW_SHA" != "$EXPECTED_RAW_SHA" ]]; then
  echo "FAIL: raw .rec SHA-256 mismatch ($ACTUAL_RAW_SHA != $EXPECTED_RAW_SHA)" >&2
  exit 1
fi
echo "Raw .rec SHA-256 verified: $ACTUAL_RAW_SHA"

echo "=== [3/6] Compiling & Running Zero-Dependency Standalone Rust Verifier ==="
rustc -O --edition 2021 scripts/check708_standalone.rs -o "$WORK_DIR/check708_standalone"
"$WORK_DIR/check708_standalone" --cert "$WORK_DIR/erdos708-g6-cert.rec" --timeout-secs 60 | tee "$WORK_DIR/check-rs.log"
grep -F "accept (rust-standalone) rows=3475 max_m=3481 leaves=15712 pruned=24628129260" "$WORK_DIR/check-rs.log"

echo "=== [4/6] Regenerating Prefix M=7..=150 from Scratch & Checking Exact Invariant Match ==="
"$WORK_DIR/check708_standalone" --prove 7 150 12 "$WORK_DIR/prefix-150.rec" --timeout-secs 60 > "$WORK_DIR/prove-150.log"
head -n 144 "$WORK_DIR/erdos708-g6-cert.rec" | cut -f1,2,4,5 > "$WORK_DIR/expected-150.cols"
cut -f1,2,4,5 "$WORK_DIR/prefix-150.rec" > "$WORK_DIR/actual-150.cols"
diff -u "$WORK_DIR/expected-150.cols" "$WORK_DIR/actual-150.cols"
echo "Prefix M=7..=150 regeneration invariant match (M, leaves, max_tau, status): OK"

echo "=== [5/6] Running Independent TypeScript/Bun BigInt Verifier ==="
bun scripts/check708-independent.ts "$WORK_DIR/erdos708-g6-cert.rec" "$WORK_DIR/check-ts.log"
grep -F "accept (ts-independent) rows=3475 max_m=3481 leaves=15712 pruned=24628129260" "$WORK_DIR/check-ts.log"

echo "=== [6/6] Running Negative Tamper / Soundness Checks ==="
sed 's/^M=437\(.*\)max_tau=[0-9]*/M=437\1max_tau=9/' \
  "$WORK_DIR/erdos708-g6-cert.rec" > "$WORK_DIR/tamper-tau9.rec"
if "$WORK_DIR/check708_standalone" --cert "$WORK_DIR/tamper-tau9.rec" >/dev/null 2>&1; then
  echo "FAIL: Rust checker accepted max_tau=9!" >&2
  exit 1
fi
if bun scripts/check708-independent.ts "$WORK_DIR/tamper-tau9.rec" >/dev/null 2>&1; then
  echo "FAIL: TS checker accepted max_tau=9!" >&2
  exit 1
fi
echo "Tamper A (max_tau=9 on M=437) -> REJECTED by both checkers (OK)"

grep -v "^M=500	" "$WORK_DIR/erdos708-g6-cert.rec" > "$WORK_DIR/tamper-gap.rec"
if "$WORK_DIR/check708_standalone" --cert "$WORK_DIR/tamper-gap.rec" >/dev/null 2>&1; then
  echo "FAIL: Rust checker accepted non-contiguous M gap!" >&2
  exit 1
fi
if bun scripts/check708-independent.ts "$WORK_DIR/tamper-gap.rec" >/dev/null 2>&1; then
  echo "FAIL: TS checker accepted non-contiguous M gap!" >&2
  exit 1
fi
echo "Tamper B (omitted row M=500) -> REJECTED by both checkers (OK)"

head -n 200 "$WORK_DIR/erdos708-g6-cert.rec" > "$WORK_DIR/tamper-trunc.rec"
if "$WORK_DIR/check708_standalone" --cert "$WORK_DIR/tamper-trunc.rec" >/dev/null 2>&1; then
  echo "FAIL: Rust checker accepted truncated certificate!" >&2
  exit 1
fi
if bun scripts/check708-independent.ts "$WORK_DIR/tamper-trunc.rec" >/dev/null 2>&1; then
  echo "FAIL: TS checker accepted truncated certificate!" >&2
  exit 1
fi
echo "Tamper C (truncated certificate max_m=206 < 3481) -> REJECTED by both checkers (OK)"

echo ""
echo "ALL POSITIVE AND NEGATIVE TAMPER CHECKS PASSED."
