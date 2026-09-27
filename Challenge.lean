/-
Copyright (c) 2026 Ji Ho Bae. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Erdős Problem #1219 — comparator challenge (trusted statement)

This file is the *trusted* half of a comparator challenge
(https://github.com/leanprover/comparator), following the conventions of
elliotglazer/erdos501: it states, with `sorry`, exactly what `Solution.lean` proves.  It imports
**Mathlib only**.  The definition `Erdos1219.PartitionArrow` is copied verbatim from the
library's `Erdos1219/Defs.lean` (checked by `scripts/sync_challenge.py --check`).

## The problem (erdosproblems.com/1219; Erdős–Hajnal 1971, Problem 3, asked by Erdős, Hajnal and
Rado)

Let `(n_k)` be an increasing sequence of integers such that `2 ^ ℵ_{n_k}` is strictly increasing,
and `2 ^ ℵ_{n_0} > ℵ_ω`.  Is it true that `Σ_k 2 ^ ℵ_{n_k} → (ℵ_ω)²`?

The answer is yes (Shelah, *Notes on partition calculus*, 1975, §1).

## The target

`erdos_1219`: for every `n : ℕ → ℕ` which is strictly increasing, such that
`k ↦ 2 ^ ℵ_{n k}` is strictly increasing and `ℵ_ω < 2 ^ ℵ_{n 0}`, the partition relation
`Σ_k 2 ^ ℵ_{n k} → (ℵ_ω)²₂` holds: every `2`-colouring of the `2`-element subsets of a set of
cardinality `Σ_k 2 ^ ℵ_{n k}` has a monochromatic subset of cardinality `ℵ_ω`.

## Reading guide

* `Erdos1219.PartitionArrow κ α` is the binary partition relation `κ → (α)²₂`: for every type
  `A` with `#A = κ` and every colouring `col` of the `2`-element finsets of `A` by `Bool`, there
  are a colour `c` and a set `H` with `#H = α` all of whose `2`-element subsets have colour `c`.
  This is the binary case of `Combinatorics.cardinalPartitionRel` of google-deepmind/formal-conjectures.
* `ℵ_ o` is `Cardinal.aleph o` (so `ℵ_ 0 = ℵ₀`), `ω` is the first infinite ordinal, `2 ^ κ` is
  cardinal exponentiation, and `Cardinal.sum` is the cardinal sum of an `ℕ`-indexed family.
* The hypothesis `StrictMono n` says that `(n_k)` is an increasing sequence of natural numbers;
  the hypotheses `hpow` and `h0` are the two conditions of the problem.
-/
import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.Data.Finset.Card

open Cardinal Ordinal

universe u

namespace Erdos1219

/-- The classical binary partition relation `κ → (α)²₂` on colourings of `2`-element finsets,
in the style of `Combinatorics.cardinalPartitionRel` of formal-conjectures. -/
def PartitionArrow (κ α : Cardinal.{u}) : Prop :=
  ∀ (A : Type u), #A = κ →
    ∀ col : {s : Finset A // s.card = 2} → Bool,
      ∃ (c : Bool) (H : Set A), #H = α ∧
        ∀ (s : Finset A) (hs : s.card = 2), (↑s : Set A) ⊆ H → col ⟨s, hs⟩ = c

end Erdos1219

/-- **Erdős problem #1219.**  Let `(n_k)` be an increasing sequence of natural numbers such that
`2 ^ ℵ_{n_k}` is strictly increasing and `2 ^ ℵ_{n_0} > ℵ_ω`.  Then
`Σ_k 2 ^ ℵ_{n_k} → (ℵ_ω)²₂`. -/
theorem erdos_1219 (n : ℕ → ℕ) (hn : StrictMono n)
    (hpow : StrictMono fun k => (2 : Cardinal.{u}) ^ ℵ_ (n k))
    (h0 : ℵ_ ω < (2 : Cardinal.{u}) ^ ℵ_ (n 0)) :
    Erdos1219.PartitionArrow (Cardinal.sum fun k => (2 : Cardinal.{u}) ^ ℵ_ (n k)) (ℵ_ ω) := by
  sorry
