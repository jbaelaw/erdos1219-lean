import Erdos1219.Canonization

/-!
# Erdős problem #1219: the statement on colourings of `2`-element finsets
-/

open Cardinal Ordinal

namespace Erdos1219

universe u

/-- **Erdős problem #1219** (Erdős–Hajnal–Rado; proved by Shelah).  Let `(n_k)` be an increasing
sequence of natural numbers such that `2 ^ ℵ_{n_k}` is strictly increasing and
`2 ^ ℵ_{n_0} > ℵ_ω`.  Then `Σ_k 2 ^ ℵ_{n_k} → (ℵ_ω)²₂`. -/
theorem erdos_1219 (n : ℕ → ℕ) (hn : StrictMono n)
    (hpow : StrictMono fun k => (2 : Cardinal.{u}) ^ ℵ_ (n k))
    (h0 : ℵ_ ω < (2 : Cardinal.{u}) ^ ℵ_ (n 0)) :
    PartitionArrow (Cardinal.sum fun k => (2 : Cardinal.{u}) ^ ℵ_ (n k)) (ℵ_ ω) := by
  intro A hA col
  obtain ⟨c, H, hH, hom⟩ :=
    core (ofFinsetColouring col) (ofFinsetColouring_symm col) n hn hpow h0 hA
  refine ⟨c, H, hH, ?_⟩
  intro s hs hsH
  classical
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.1 hs
  have hx : x ∈ H := hsH (by simp)
  have hy : y ∈ H := hsH (by simp)
  have := hom x hx y hy hxy
  rw [ofFinsetColouring_apply col hxy] at this
  exact this

end Erdos1219
