import Erdos1219.Defs

/-!
# Cardinal arithmetic lemmas for Erdős #1219

Small facts about regular cardinals, bounded subsets, `ℕ`-indexed sums and `ℵ_ω`.
-/

open Cardinal Ordinal Function

namespace Erdos1219

universe u

/-- A union of fewer than `c` sets, each of cardinality `< c`, has cardinality `< c` when `c`
is regular. -/
theorem mk_iUnion_lt_of_isRegular {V ι : Type u} {c : Cardinal.{u}} (hc : c.IsRegular)
    (hι : #ι < c) (t : ι → Set V) (ht : ∀ i, #(t i) < c) : #(⋃ i, t i) < c :=
  mk_iUnion_le_sum_mk.trans_lt (sum_lt_of_isRegular hc hι ht)

/-- Pigeonhole for regular cardinals: a set of regular cardinality `c` mapped into a type of
cardinality `< c` has a fibre of cardinality `c`. -/
theorem exists_fiber_eq_of_isRegular {V T : Type u} {c : Cardinal.{u}} (hc : c.IsRegular)
    (s : Set V) (hs : #s = c) (φ : V → T) (hT : #T < c) :
    ∃ t, #(s ∩ φ ⁻¹' {t} : Set V) = c := by
  by_contra h
  have hlt : ∀ t, #(s ∩ φ ⁻¹' {t} : Set V) < c := fun t =>
    lt_of_le_of_ne ((mk_le_mk_of_subset Set.inter_subset_left).trans_eq hs)
      (fun ht => h ⟨t, ht⟩)
  have hsub : s ⊆ ⋃ t, s ∩ φ ⁻¹' {t} := fun v hv => Set.mem_iUnion.2 ⟨φ v, hv, rfl⟩
  exact absurd ((mk_le_mk_of_subset hsub).trans_lt (mk_iUnion_lt_of_isRegular hc hT _ hlt))
    (by rw [hs]; exact lt_irrefl c)

theorem two_pow_pow_self {μ : Cardinal.{u}} (hμ : ℵ₀ ≤ μ) :
    ((2 : Cardinal.{u}) ^ μ) ^ μ = 2 ^ μ := by
  rw [← power_mul, mul_eq_self hμ]

theorem le_two_pow_self {μ : Cardinal.{u}} : μ ≤ 2 ^ μ := (cantor μ).le

theorem aleph0_le_two_pow {μ : Cardinal.{u}} (hμ : ℵ₀ ≤ μ) : ℵ₀ ≤ 2 ^ μ :=
  hμ.trans le_two_pow_self

/-- The subsets of `U` of cardinality `≤ μ`, when `#U ≤ 2 ^ μ`: there are at most `2 ^ μ`. -/
theorem mk_bounded_subsets_le {V : Type u} (U : Set V) {μ : Cardinal.{u}} (hμ : ℵ₀ ≤ μ)
    (hU : #U ≤ 2 ^ μ) : #{B : Set V // B ⊆ U ∧ #B ≤ μ} ≤ 2 ^ μ := by
  have key : #{B : Set V // B ⊆ U ∧ #B ≤ μ} ≤ #{t : Set (↥U) // #t ≤ μ} := by
    refine mk_le_of_injective (f := fun B => ⟨Subtype.val ⁻¹' B.1, ?_⟩) ?_
    · rw [mk_preimage_of_injective_of_subset_range _ _ Subtype.val_injective
        (by simpa using B.2.1)]
      exact B.2.2
    · rintro ⟨B, hB⟩ ⟨B', hB'⟩ h
      simp only [Subtype.mk.injEq] at h
      have h1 : ((↑) : ↥U → V) '' (((↑) : ↥U → V) ⁻¹' B) = B :=
        Set.image_preimage_eq_of_subset (by simpa using hB.1)
      have h2 : ((↑) : ↥U → V) '' (((↑) : ↥U → V) ⁻¹' B') = B' :=
        Set.image_preimage_eq_of_subset (by simpa using hB'.1)
      rw [Subtype.mk.injEq]
      calc B = ((↑) : ↥U → V) '' (((↑) : ↥U → V) ⁻¹' B) := h1.symm
        _ = ((↑) : ↥U → V) '' (((↑) : ↥U → V) ⁻¹' B') := by rw [h]
        _ = B' := h2
  refine key.trans ((mk_bounded_set_le (↥U) μ).trans ?_)
  have hmax : max #U ℵ₀ ≤ 2 ^ μ := max_le hU (aleph0_le_two_pow hμ)
  exact (power_le_power_right hmax).trans (two_pow_pow_self hμ).le

/-- The shift of an `ℕ`-indexed family has a smaller sum. -/
theorem sum_shift_le (a : ℕ → Cardinal.{u}) :
    Cardinal.sum (fun k => a (k + 1)) ≤ Cardinal.sum a := by
  show #(Σ k : ℕ, (a (k + 1)).out) ≤ #(Σ k : ℕ, (a k).out)
  refine mk_le_of_injective
    (f := fun p : (Σ k : ℕ, (a (k + 1)).out) => (⟨p.1 + 1, p.2⟩ : Σ k : ℕ, (a k).out)) ?_
  rintro ⟨k, x⟩ ⟨k', x'⟩ h
  simp only [Sigma.mk.injEq, add_left_inj] at h
  obtain ⟨rfl, h2⟩ := h
  rw [heq_iff_eq] at h2
  subst h2
  rfl

/-- Two interlaced `ℕ`-indexed families have the same sum. -/
theorem sum_eq_of_interlaced (a b : ℕ → Cardinal.{u}) (h1 : ∀ k, a k ≤ b k)
    (h2 : ∀ k, b k ≤ a (k + 1)) : Cardinal.sum a = Cardinal.sum b :=
  le_antisymm (sum_le_sum _ _ h1) ((sum_le_sum _ _ h2).trans (sum_shift_le a))

theorem aleph_nat_le_aleph_omega (N : ℕ) : ℵ_ (N : Ordinal.{u}) ≤ ℵ_ ω :=
  aleph_le_aleph.2 (natCast_lt_omega0 N).le

theorem aleph_omega_le_of_forall_nat {c : Cardinal.{u}}
    (h : ∀ N : ℕ, ℵ_ (N : Ordinal.{u}) ≤ c) : ℵ_ ω ≤ c := by
  rw [aleph_limit isSuccLimit_omega0]
  refine ciSup_le' fun a => ?_
  obtain ⟨N, hN⟩ := lt_omega0.1 a.2
  have : (a : Ordinal.{u}) = N := hN
  rw [this]
  exact h N

/-- The cardinality of a disjoint `ℕ`-indexed union is the sum of the cardinalities. -/
theorem mk_iUnion_nat_eq_sum {V : Type u} (t : ℕ → Set V) (h : Pairwise (Disjoint on t)) :
    #(⋃ p, t p) = Cardinal.sum fun p => #(t p) := by
  have := mk_iUnion_eq_sum_mk_lift h
  simpa using this

/-- A countable sum of alephs with unbounded indices below `ω` is `ℵ_ω`. -/
theorem sum_aleph_eq_aleph_omega (e : ℕ → ℕ) (he : ∀ N, N ≤ e N) :
    Cardinal.sum (fun p => ℵ_ (e p : Ordinal.{u})) = ℵ_ ω := by
  apply le_antisymm
  · calc Cardinal.sum (fun p => ℵ_ (e p : Ordinal.{u}))
        ≤ Cardinal.sum (fun _ : ℕ => (ℵ_ ω : Cardinal.{u})) :=
          sum_le_sum _ _ fun p => aleph_nat_le_aleph_omega (e p)
      _ = ℵ_ ω := by
          rw [sum_const]
          simp only [mk_nat, Cardinal.lift_aleph0, Cardinal.lift_id']
          exact mul_eq_right (aleph0_le_aleph ω) (aleph0_le_aleph ω) aleph0_ne_zero
  · refine aleph_omega_le_of_forall_nat fun N => ?_
    calc ℵ_ (N : Ordinal.{u}) ≤ ℵ_ (e N : Ordinal.{u}) := aleph_le_aleph.2 (by exact_mod_cast he N)
      _ ≤ _ := le_sum _ N

theorem nonempty_of_mk_eq {V : Type u} {s : Set V} {c : Cardinal.{u}} (hs : #s = c)
    (hc : ℵ₀ ≤ c) : s.Nonempty := by
  have : Nonempty s := mk_ne_zero_iff.1 (by rw [hs]; exact (aleph0_pos.trans_le hc).ne')
  exact Set.nonempty_coe_sort.1 this

end Erdos1219
