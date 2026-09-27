import Erdos1219.Defs
import Mathlib.Order.Filter.Ultrafilter.Basic

/-!
# Ramsey's theorem for pairs on `ℕ`

We prove the infinite Ramsey theorem for pairs (two colours) on `ℕ` via a non-principal
ultrafilter (`Filter.hyperfilter ℕ`).

Sketch: let `U` be the hyperfilter on `ℕ`.  For each `i` pick the colour `c i` such that
`{j | i < j ∧ g i j = c i} ∈ U`; then pick the colour `δ` with `{i | c i = δ} ∈ U`.
We build a decreasing sequence of sets `S₀ ⊇ S₁ ⊇ …`, all in `U`, all contained in
`{i | c i = δ}`, together with elements `m p ∈ S p`, by
`S (p+1) := S p ∩ {j | m p < j ∧ g (m p) j = δ}`.  Since `m q ∈ S q ⊆ S (p+1)` for `p < q`,
the sequence `m` is strictly increasing and `δ`-homogeneous.
-/

open Cardinal

namespace Erdos1219

/-- Ramsey's theorem for pairs on `ℕ`: for every colouring `g` of ordered pairs `(p, q)` with
`p < q` (only those values matter), there is a strictly increasing sequence `m` and a colour `δ`
with `g (m p) (m q) = δ` whenever `p < q`. -/
theorem ramsey_nat (g : ℕ → ℕ → Bool) :
    ∃ (m : ℕ → ℕ) (δ : Bool), StrictMono m ∧ ∀ p q, p < q → g (m p) (m q) = δ := by
  classical
  -- the non-principal ultrafilter on `ℕ`
  let U : Ultrafilter ℕ := Filter.hyperfilter ℕ
  -- every final segment `{j | i < j}` belongs to `U`
  have hgt : ∀ i : ℕ, {j | i < j} ∈ U := fun i =>
    Ultrafilter.mem_coe.mp (Nat.hyperfilter_le_atTop (Filter.eventually_gt_atTop i))
  -- for each `i` choose the colour `c i` of `U`-almost all `j > i`
  have hc : ∀ i : ℕ, ∃ c : Bool, {j | i < j ∧ g i j = c} ∈ U := by
    intro i
    rcases Ultrafilter.mem_or_compl_mem U {j | g i j = true} with h | h
    · refine ⟨true, ?_⟩
      exact Ultrafilter.mem_coe.mp
        (Filter.inter_mem (Ultrafilter.mem_coe.mpr (hgt i)) (Ultrafilter.mem_coe.mpr h))
    · refine ⟨false, ?_⟩
      have h' : {j | g i j = false} ∈ U := by
        refine Ultrafilter.mem_coe.mp
          (Filter.mem_of_superset (Ultrafilter.mem_coe.mpr h) ?_)
        intro j hj
        simpa using hj
      exact Ultrafilter.mem_coe.mp
        (Filter.inter_mem (Ultrafilter.mem_coe.mpr (hgt i)) (Ultrafilter.mem_coe.mpr h'))
  choose c hc using hc
  -- choose the colour `δ` taken by `U`-almost all `i`
  have hδ : ∃ δ : Bool, {i | c i = δ} ∈ U := by
    rcases Ultrafilter.mem_or_compl_mem U {i | c i = true} with h | h
    · exact ⟨true, h⟩
    · refine ⟨false, ?_⟩
      refine Ultrafilter.mem_coe.mp
        (Filter.mem_of_superset (Ultrafilter.mem_coe.mpr h) ?_)
      intro i hi
      simpa using hi
  obtain ⟨δ, hδ⟩ := hδ
  have key : ∀ i, c i = δ → {j | i < j ∧ g i j = δ} ∈ U := by
    intro i hi
    rw [← hi]
    exact hc i
  -- the type of "good" sets: members of `U` contained in `{i | c i = δ}`
  let T := {S : Set ℕ // S ∈ U ∧ S ⊆ {i | c i = δ}}
  have pick : ∀ S : T, ∃ x, x ∈ S.1 := fun S => Ultrafilter.nonempty_of_mem S.2.1
  choose x hx using pick
  -- one step of the construction
  let step : T → T := fun S =>
    ⟨S.1 ∩ {j | x S < j ∧ g (x S) j = δ},
      Ultrafilter.mem_coe.mp
        (Filter.inter_mem (Ultrafilter.mem_coe.mpr S.2.1)
          (Ultrafilter.mem_coe.mpr (key (x S) (S.2.2 (hx S))))),
      fun j hj => S.2.2 hj.1⟩
  let S0 : T := ⟨{i | c i = δ}, hδ, subset_rfl⟩
  let seq : ℕ → T := fun n => Nat.rec S0 (fun _ S => step S) n
  have seq_succ : ∀ n, seq (n + 1) = step (seq n) := fun _ => rfl
  -- the sets are decreasing
  have anti : ∀ p q, p ≤ q → (seq q).1 ⊆ (seq p).1 := by
    intro p q hpq
    induction hpq with
    | refl => exact subset_rfl
    | step _ ih =>
      intro j hj
      apply ih
      rw [seq_succ] at hj
      exact hj.1
  have main : ∀ p q, p < q → x (seq p) < x (seq q) ∧ g (x (seq p)) (x (seq q)) = δ := by
    intro p q hpq
    have h1 : x (seq q) ∈ (seq (p + 1)).1 := anti (p + 1) q hpq (hx (seq q))
    rw [seq_succ] at h1
    exact h1.2
  refine ⟨fun p => x (seq p), δ, ?_, ?_⟩
  · exact strictMono_nat_of_lt_succ fun p => (main p (p + 1) (Nat.lt_succ_self p)).1
  · intro p q hpq
    exact (main p q hpq).2

end Erdos1219

