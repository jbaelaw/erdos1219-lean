/-
Copyright (c) 2026 Ji Ho Bae. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Erdős Problem #1219 — comparator solution

The untrusted half of the comparator challenge: the statement of `Challenge.lean`, repeated
verbatim, proved by delegation to the library (`Erdos1219.erdos_1219` in `Erdos1219/Main.lean`).
Only the statement is compared by the comparator; this file must not import `Challenge`.
The definition `Erdos1219.PartitionArrow` is the library's (`Erdos1219/Defs.lean`), of which
`Challenge.lean` contains a verbatim copy.
-/
import Erdos1219.Main

open Cardinal Ordinal

universe u

/-- **Erdős problem #1219.**  Let `(n_k)` be an increasing sequence of natural numbers such that
`2 ^ ℵ_{n_k}` is strictly increasing and `2 ^ ℵ_{n_0} > ℵ_ω`.  Then
`Σ_k 2 ^ ℵ_{n_k} → (ℵ_ω)²₂`. -/
theorem erdos_1219 (n : ℕ → ℕ) (hn : StrictMono n)
    (hpow : StrictMono fun k => (2 : Cardinal.{u}) ^ ℵ_ (n k))
    (h0 : ℵ_ ω < (2 : Cardinal.{u}) ^ ℵ_ (n 0)) :
    Erdos1219.PartitionArrow (Cardinal.sum fun k => (2 : Cardinal.{u}) ^ ℵ_ (n k)) (ℵ_ ω) :=
  Erdos1219.erdos_1219 n hn hpow h0
