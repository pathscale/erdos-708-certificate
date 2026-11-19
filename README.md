# Erdős Problem #708 — Exact Small-$n$ Values ($g(4) = 5, g(5) = 6, g(6) = 8$) and Constructive Lower Bounds ($g(7) \ge 9, g(8) \ge 11$)

Standalone verification suite, finite certificate archive, and manuscript for Erdős Problem #708 (Erdős–Surányi 1959).

- **Zenodo Archive (This Repository & Finite Certificate):** `10.5281/zenodo.24366897` (`https://doi.org/10.5281/zenodo.24366897`)
- **Companion Asymptotic Manuscript & Suite:** `10.5281/zenodo.24342717` (`https://doi.org/10.5281/zenodo.24342717`)

## Contents

- `paper/erdos708-paper.pdf` (`paper/erdos708-paper.typ`, `paper/erdos708-paper.tex`, `paper/references.bib`): Manuscript proving $g(4) = 5$, $g(5) = 6$, $g(6) = 8$, $g(7) \ge 9$, $g(8) \ge 11$, the unrestricted Universal Cumulative-GCD Slot Theorem, and the bipartite spanning-forest bound $\tau(A, I) \le 2n - r - s + 1$.
- `data/erdos708-g6-cert.rec.zst`: Zstandard-compressed `3,475`-row certificate covering $7 \le M \le 3{,}481$ (`17,418` bytes compressed, SHA-256 `b6368979558724d0b7934a329419a34c610cb8e25e428cba9eb758842ae11b45`; `169,969` bytes raw `erdos708-g6-cert.rec`, SHA-256 `65b22b54e7f3b652a20d1812ede4cd7664f12c5d230338fea9608acbd9792e68`).
- `scripts/check708_standalone.rs`: Zero-dependency Rust 2021 verifier and parallel certificate generator:
  - `Part 1`: Verifies constructive lower-bound witnesses for $g(3) \ge 4$, $g(4) \ge 5$, $g(5) \ge 6$, $g(6) \ge 8$, $g(7) \ge 9$, and $g(8) \ge 11$.
  - `Part 2`: Independent small-$M$ universal-$x$ Chinese Remainder verification ($g(3) \le 4$, $g(4) \le 5$, $g(5) \le 6$).
  - `Part 3`: Validates all `3,475` contiguous rows of `erdos708-g6-cert.rec` ($7 \le M \le 3{,}481$), or regenerates the entire certificate byte-for-byte from scratch.
  - `Part 4`: Executes all analytic threshold and monotone smooth-bridge checks above $M = 3{,}481$ (`354` $\{2,3,5,7\}$-smooth $M \in [3482, 56124]$, smooth pairs up to $16{,}464$, smooth triples up to $576{,}240$, and Subcase 3b below $360{,}065$).
- `scripts/check708-independent.ts`: Independent TypeScript/Bun `BigInt` verifier checking all witnesses, certificate invariants, and closed-form threshold inequalities.
- `scripts/validate-all.sh`: End-to-end `SHA256SUMS.txt` verification, `.zst` decompression, Rust + Bun verification, prefix regeneration ($7 \le M \le 150$), and three negative tamper tests (`max_tau=9`, non-contiguous $M$ gap, and truncated certificate).

## Verification & Certificate Regeneration Commands

Run the full automated verification and tamper-rejection suite (`< 15s`):

```sh
./scripts/validate-all.sh
```

Compile and run the standalone Rust verifier directly (`rustc` 2021 edition, zero external crates):

```sh
zstd -dc data/erdos708-g6-cert.rec.zst > /tmp/erdos708-g6-cert.rec
rustc -O --edition 2021 scripts/check708_standalone.rs -o /tmp/check708_standalone
/tmp/check708_standalone --cert /tmp/erdos708-g6-cert.rec --timeout-secs 60
```

Regenerate the complete `3,475`-row certificate ($7 \le M \le 3{,}481$) from scratch on `12` threads (`~3` minutes):

```sh
/tmp/check708_standalone --prove 7 3481 12 /tmp/regenerated-g6-cert.rec
```

Run the independent TypeScript/Bun `BigInt` verifier:

```sh
bun scripts/check708-independent.ts /tmp/erdos708-g6-cert.rec
```
