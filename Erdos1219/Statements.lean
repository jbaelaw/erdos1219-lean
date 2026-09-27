import Erdos1219.Defs

/-! Interface statements (proved in their own files). -/

open Cardinal Ordinal

namespace Erdos1219

universe u

/-- Ramsey's theorem for pairs on `ℕ`, in the form used here: for every colouring `g` of
ordered pairs `(p, q)` with `p < q`, there is an infinite (strictly increasing) subsequence on
which `g` is constant. -/
theorem ramsey_nat_stmt (g : ℕ → ℕ → Bool) :
    ∃ (m : ℕ → ℕ) (δ : Bool), StrictMono m ∧ ∀ p q, p < q → g (m p) (m q) = δ := by
  sorry

/-- The unbalanced Erdős–Rado theorem `(2^μ)⁺ → ((2^μ)⁺, μ⁺)²`, for both colours. -/
theorem erdosRado_unbalanced_stmt {V : Type u} (f : V → V → Bool) (hf : ∀ x y, f x y = f y x)
    (μ : Cardinal.{u}) (hμ : ℵ₀ ≤ μ) (C : Set V) (hC : #C = Order.succ (2 ^ μ)) (c : Bool) :
    (∃ H ⊆ C, #H = Order.succ (2 ^ μ) ∧ Homog f c H) ∨
      (∃ H ⊆ C, #H = Order.succ μ ∧ Homog f (!c) H) := by
  sorry

/-- The core theorem: the partition relation for symmetric pair colourings. -/
theorem core_stmt {V : Type u} (f : V → V → Bool) (hf : ∀ x y, f x y = f y x)
    (n : ℕ → ℕ) (hn : StrictMono n)
    (hpow : StrictMono fun k => (2 : Cardinal.{u}) ^ ℵ_ (n k))
    (h0 : ℵ_ ω < (2 : Cardinal.{u}) ^ ℵ_ (n 0))
    (hV : #V = Cardinal.sum fun k => (2 : Cardinal.{u}) ^ ℵ_ (n k)) :
    ∃ (c : Bool) (H : Set V), #H = ℵ_ ω ∧ Homog f c H := by
  sorry

end Erdos1219
