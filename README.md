# Erdős Problem #1219 in Lean 4

A complete, machine-checked Lean 4 / Mathlib proof of the affirmative answer to
[Erdős problem #1219](https://www.erdosproblems.com/1219) (Erdős–Hajnal 1971, Problem 3, asked by
Erdős, Hajnal and Rado; solved by Shelah in 1975):

> Let `(n_k)` be an increasing sequence of integers such that `2^{ℵ_{n_k}}` is strictly increasing,
> and `2^{ℵ_{n_0}} > ℵ_ω`. Is it true that `Σ_k 2^{ℵ_{n_k}} → (ℵ_ω)²`?

Yes. The Lean statement (root-level `erdos_1219`, in `Challenge.lean` with `sorry` and in
`Solution.lean` with a proof) is

```lean
theorem erdos_1219 (n : ℕ → ℕ) (hn : StrictMono n)
    (hpow : StrictMono fun k => (2 : Cardinal.{u}) ^ ℵ_ (n k))
    (h0 : ℵ_ ω < (2 : Cardinal.{u}) ^ ℵ_ (n 0)) :
    Erdos1219.PartitionArrow (Cardinal.sum fun k => (2 : Cardinal.{u}) ^ ℵ_ (n k)) (ℵ_ ω)
```

where `Erdos1219.PartitionArrow κ α` is the binary partition relation `κ → (α)²₂` (every
`2`-colouring of the `2`-element subsets of a set of cardinality `κ` has a monochromatic subset
of cardinality `α`), the binary case of `Combinatorics.cardinalPartitionRel` of
google-deepmind/formal-conjectures. The proof depends only on the standard axioms `propext`,
`Classical.choice`, `Quot.sound`, and the Lean comparator (with the landrun sandbox and the
NanoDa kernel) accepts `Solution.lean` against `Challenge.lean`.

## Mathematics

The proof formalizes Shelah, *Notes on partition calculus* (Infinite and finite sets, Keszthely
1973, Colloq. Math. Soc. János Bolyai 10, North-Holland 1975, pp. 1257–1276; [Sh:40]), §1:
the Canonization Lemma 1.1 (specialized to two colours, pairs and `cf λ = ω`), Theorem 1.2 and
Corollary 1.3. See [docs/PROOF.md](docs/PROOF.md) for the complete informal proof that was
formalized. In outline, with `μ_k = ℵ_{n_k}`, `λ_k = (2^{μ_k})⁺` and `χ = Σ_k 2^{μ_k} = Σ_k λ_k`:

1. **Unbalanced Erdős–Rado** `(2^μ)⁺ → ((2^μ)⁺, μ⁺)²` (`Erdos1219/UnbalancedErdosRado.lean`),
   proved with a "critical ordinal" argument: either some ordinal `α` of cofinality `μ⁺` is *good*
   (a maximal `1`-homogeneous subset of its `1`-neighbourhood has size `≥ μ⁺`), or a
   closure-point/pigeonhole argument (replacing Fodor's lemma) yields a `0`-homogeneous set of
   size `(2^μ)⁺`.
2. Split a set of size `χ` into blocks `A_k` of size `λ_k`. If there is no homogeneous set of
   size `ℵ_ω`, then by (1) every subset of `A_k` of full size contains homogeneous sets of both
   colours of size `μ_k`.
3. **Canonization** (`Erdos1219/Canonization.lean`): in each block a *guide* `a*_k` is chosen
   outside the small set of points having a small type-class over some `≤ μ_k`-sized subset of the
   earlier blocks; the blocks `B_k = B_{k,0} ∪ B_{k,1}` (a `0`- and a `1`-homogeneous part of size
   `μ_k`) are then chosen inside the type-class of the guide over the earlier blocks, all with the
   same type over all guides. This makes the colour between `B_i` and `B_j` depend only on `(i, j)`.
4. **Ramsey on `ℕ`** (`Erdos1219/Ramsey.lean`, via a non-principal ultrafilter) gives an infinite
   set `I` of block indices and a colour `δ` with all cross colours equal to `δ`; then
   `⋃_{k ∈ I} B_{k,δ}` is `δ`-homogeneous of size `Σ_{k∈I} ℵ_{n_k} = ℵ_ω`, a contradiction.

## Layout

| file | content |
|---|---|
| `Erdos1219/Defs.lean` | `Homog`, `ofFinsetColouring`, `PartitionArrow` |
| `Erdos1219/CardinalLemmas.lean` | regular-cardinal pigeonhole, bounded subsets, `ℕ`-indexed sums, `ℵ_ω` |
| `Erdos1219/Ramsey.lean` | `ramsey_nat`: Ramsey's theorem for pairs on `ℕ` |
| `Erdos1219/UnbalancedErdosRado.lean` | `erdosRado_unbalanced`: `(2^μ)⁺ → ((2^μ)⁺, μ⁺)²` for both colours |
| `Erdos1219/Canonization.lean` | Shelah's canonization and `core` (symmetric colourings `V → V → Bool`) |
| `Erdos1219/Main.lean` | `Erdos1219.erdos_1219` for colourings of `2`-element finsets |
| `Challenge.lean` | comparator challenge: verbatim `PartitionArrow` + `erdos_1219` with `sorry` (Mathlib only) |
| `Solution.lean` | comparator solution: `erdos_1219` proved by delegation to the library |
| `comparator.json`, `comparator-ci.json` | comparator configurations (NanoDa on / off) |
| `AxiomAudit.lean` | `#print axioms` of the targets |
| `scripts/` | `sync_challenge.py --check`, comparator tool installation and runner |
| `docs/PROOF.md` | the informal proof that was formalized |
| `logs/` | recorded comparator and axiom-audit outputs |

## How to verify

Toolchain `leanprover/lean4:v4.35.0-rc3`, Mathlib `c55e6e786f49471c72fbddbec5415808896aec1e`.

```sh
python3 scripts/sync_challenge.py --check
lake exe cache get && lake build            # builds Erdos1219, Challenge (one sorry), Solution
lake env lean AxiomAudit.lean
bash scripts/install-comparator-tools.sh "$PWD/.tools"   # Linux with Landlock; Go bootstrapped
bash scripts/run-comparator.sh "$PWD" "$PWD/.tools" comparator-ci.json   # or comparator.json with nanoda_bin
```

Recorded result (2026-09-28 KST, Ubuntu x86_64; comparator `777e7f5`, lean4export at
`v4.35.0-rc3`, landrun 0.1.15, nanoda_lib `68d5ca9`), `logs/comparator-20260928.log`:

```
Running nanoda kernel on solution
Nanoda kernel accepts the solution
Running Lean default kernel on solution.
Lean default kernel accepts the solution
Your solution is okay!
```

and `logs/axiom-audit-20260928.log`:

```
'erdos_1219' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Faithfulness notes

* "Increasing sequence of integers `(n_k)`" is rendered as `n : ℕ → ℕ` with `StrictMono n`
  (indices of alephs are natural numbers). The two conditions are `hpow` and `h0`.
* `Σ_k 2^{ℵ_{n_k}}` is the cardinal sum `Cardinal.sum`; `→ (ℵ_ω)²` is the two-colour binary
  partition relation (the standard convention when the number of colours is omitted).
* Colourings are functions on `{s : Finset A // s.card = 2}` and the homogeneous set has
  cardinality exactly `ℵ_ω`, exactly as in formal-conjectures' `cardinalPartitionRel`.

## Credits and licence

* Mathematics: Saharon Shelah ([Sh:40], 1975). Problem: Erdős, Hajnal and Rado ([ErHa71]).
* Author of the formalization: Ji Ho Bae. The Lean code was written in Claude Code agent sessions
  (Anthropic Claude) under the author's direction; all proofs are checked by Lean's kernel and
  by the comparator.
* Tools: Mathlib; the Lean FRO comparator (scripts adapted from elliotglazer/erdos501, Apache-2.0);
  Thomas Bloom's erdosproblems.com.
* Licence: Apache-2.0 (see `LICENSE`).
