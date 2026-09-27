import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.Data.Finset.Card

/-!
# Erdős problem #1219 — basic definitions

Pair colourings are represented by (symmetric) functions `f : V → V → Bool`;
only the values on pairs of distinct points matter.
-/

open Cardinal

namespace Erdos1219

universe u

variable {V : Type u}

/-- `H` is `c`-homogeneous for the pair colouring `f`: all pairs of distinct points of `H`
receive colour `c`. -/
def Homog (f : V → V → Bool) (c : Bool) (H : Set V) : Prop :=
  ∀ x ∈ H, ∀ y ∈ H, x ≠ y → f x y = c

theorem Homog.mono {f : V → V → Bool} {c : Bool} {H H' : Set V} (h : Homog f c H)
    (hH : H' ⊆ H) : Homog f c H' :=
  fun x hx y hy hxy => h x (hH hx) y (hH hy) hxy

theorem Homog.empty (f : V → V → Bool) (c : Bool) : Homog f c ∅ := by
  intro x hx; simp at hx

theorem Homog.singleton (f : V → V → Bool) (c : Bool) (x : V) : Homog f c {x} := by
  intro a ha b hb hab
  simp only [Set.mem_singleton_iff] at ha hb
  exact absurd (ha.trans hb.symm) hab

/-- The pair colouring on ordered pairs of distinct points induced by a colouring of
`2`-element finsets (the diagonal is coloured `false`, which is irrelevant). -/
noncomputable def ofFinsetColouring (col : {s : Finset V // s.card = 2} → Bool) (x y : V) :
    Bool :=
  if h : x = y then false else col ⟨{x, y}, Finset.card_pair h⟩

theorem ofFinsetColouring_symm (col : {s : Finset V // s.card = 2} → Bool) (x y : V) :
    ofFinsetColouring col x y = ofFinsetColouring col y x := by
  unfold ofFinsetColouring
  by_cases h : x = y
  · subst h; simp
  · have h' : y ≠ x := fun e => h e.symm
    rw [dif_neg h, dif_neg h']
    congr 1
    exact Subtype.ext (Finset.pair_comm x y)

theorem ofFinsetColouring_apply (col : {s : Finset V // s.card = 2} → Bool) {x y : V}
    (h : x ≠ y) : ofFinsetColouring col x y = col ⟨{x, y}, Finset.card_pair h⟩ := by
  unfold ofFinsetColouring
  rw [dif_neg h]

/-- The classical binary partition relation `κ → (α)²₂` on colourings of `2`-element finsets,
in the style of `Combinatorics.cardinalPartitionRel` of formal-conjectures. -/
def PartitionArrow (κ α : Cardinal.{u}) : Prop :=
  ∀ (A : Type u), #A = κ →
    ∀ col : {s : Finset A // s.card = 2} → Bool,
      ∃ (c : Bool) (H : Set A), #H = α ∧
        ∀ (s : Finset A) (hs : s.card = 2), (↑s : Set A) ⊆ H → col ⟨s, hs⟩ = c

end Erdos1219
