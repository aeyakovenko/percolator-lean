#!/usr/bin/env bash
set -euo pipefail

if [ ! -f ../lean-svm/LeanSVM/CPI.lean ] || ! grep -q "def checkTokenOr2022Prog" ../lean-svm/LeanSVM/CPI.lean; then
  echo "ERROR: sibling ../lean-svm checkout is missing or outdated (requires LeanSVM.CPI.checkTokenOr2022Prog)." >&2
  echo "       Please update ../lean-svm to latest main and rebuild it first." >&2
  exit 1
fi

echo "=== 1. Build Lean 4 formal model, verify all kernel proofs (0 sorry, 0 axioms) ==="
lake build
lake build Percolator.EvilMatcher

echo "=== 2. Compile core Percolator + external Matcher, OracleAdapter, RewardModule & test-only EvilMatcher to Solana sBPF (.so) ==="
mkdir -p build
LEAN_PATH=../lean-svm/.lake/build/lib/lean:.lake/build/lib/lean \
  ../lean-svm/.lake/build/bin/lean-svm build Percolator.Program Percolator.Program.entrypoint -o build/percolator.so
LEAN_PATH=../lean-svm/.lake/build/lib/lean:.lake/build/lib/lean \
  ../lean-svm/.lake/build/bin/lean-svm build Percolator.Matcher Percolator.Matcher.entrypoint -o build/matcher.so
LEAN_PATH=../lean-svm/.lake/build/lib/lean:.lake/build/lib/lean \
  ../lean-svm/.lake/build/bin/lean-svm build Percolator.OracleAdapter Percolator.OracleAdapter.entrypoint -o build/oracle_adapter.so
LEAN_PATH=../lean-svm/.lake/build/lib/lean:.lake/build/lib/lean \
  ../lean-svm/.lake/build/bin/lean-svm build Percolator.RewardModule Percolator.RewardModule.entrypoint -o build/reward_module.so
LEAN_PATH=../lean-svm/.lake/build/lib/lean:.lake/build/lib/lean \
  ../lean-svm/.lake/build/bin/lean-svm build Percolator.HlpVault Percolator.HlpVault.entrypoint -o build/hlp_vault.so
LEAN_PATH=../lean-svm/.lake/build/lib/lean:.lake/build/lib/lean \
  ../lean-svm/.lake/build/bin/lean-svm build Percolator.EvilMatcher Percolator.EvilMatcher.entrypoint -o build/evil_matcher.so
LEAN_PATH=../lean-svm/.lake/build/lib/lean:.lake/build/lib/lean \
  ../lean-svm/.lake/build/bin/lean-svm build Percolator.LimitMatcher Percolator.LimitMatcher.entrypoint -o build/limit_matcher.so

echo "=== 3. Execute all 17 LiteSVM verification, boring exchange, 8-leg CU stress, reward buy-and-burn, adversarial PropAMM, flip, HLP vault & fuzz suites (sBPF v3 / Agave 4.x) ==="
cargo run --manifest-path svm-runner/Cargo.toml --release -- \
  build/percolator.so build/matcher.so build/oracle_adapter.so build/reward_module.so build/evil_matcher.so build/hlp_vault.so build/limit_matcher.so
