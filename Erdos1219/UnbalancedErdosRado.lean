import Erdos1219.Defs
import Mathlib.SetTheory.Cardinal.Pigeonhole

/-!
# The unbalanced Erdős–Rado theorem `(2^μ)⁺ → ((2^μ)⁺, μ⁺)²`

We prove: for every symmetric colouring `f : V → V → Bool`, every infinite cardinal `μ` and
every set `C` of cardinality `(2^μ)⁺`, either `C` contains a `c`-homogeneous set of size
`(2^μ)⁺` or a `!c`-homogeneous set of size `μ⁺`.

The proof is carried out on a well-ordered type `W` of regular cardinality `θ = (2^μ)⁺` whose
order type is the initial ordinal `θ.ord` (concretely `θ.ord.ToType`), and then transported.
-/

open Cardinal Ordinal Set

namespace Erdos1219

universe u

/-! ### Boundedness in well-orders of regular cardinality -/

section WellOrder

variable {X : Type u} [LinearOrder X] [WellFoundedLT X]

/-- In a well-order of regular cardinality `#X` whose order type is the initial ordinal
`(#X).ord`, every subset of cardinality `< #X` is strictly bounded. -/
theorem exists_forall_lt_of_mk_lt (hreg : Cardinal.IsRegular #X) (hX : ord #X = typeLT X)
    {s : Set X} (hs : #s < #X) : ∃ x, ∀ y ∈ s, y < x := by
  rw [← not_isCofinal_iff]
  intro hcof
  have h1 : Order.cof X = #X := by
    rw [← Ordinal.cof_type, ← hX, hreg.cof_ord]
  have h2 := Order.cof_le hcof
  rw [h1] at h2
  exact h2.not_gt hs

theorem exists_gt_of_regular (hreg : Cardinal.IsRegular #X) (hX : ord #X = typeLT X) (x : X) :
    ∃ y, x < y := by
  obtain ⟨y, hy⟩ := exists_forall_lt_of_mk_lt hreg hX (s := {x})
    (by rw [mk_singleton]; exact one_lt_aleph0.trans_le hreg.aleph0_le)
  exact ⟨y, hy x (mem_singleton x)⟩

/-- Well-founded recursion: a sequence `β` indexed by a well-order `I` such that `β ξ` lies
above `h (β η)` for all `η < ξ`, provided all relevant sets are bounded. -/
theorem exists_seq {I W : Type u} [LinearOrder I] [WellFoundedLT I] [LinearOrder W]
    [WellFoundedLT W] {κ : Cardinal.{u}}
    (hb : ∀ s : Set W, #s < κ → ∃ x, ∀ y ∈ s, y < x) (hI : ∀ ξ : I, #(Iio ξ) < κ)
    (h : W → W) : ∃ β : I → W, ∀ ξ η, η < ξ → h (β η) < β ξ := by
  let F : (ξ : I) → ((η : I) → η < ξ → W) → W := fun ξ IH =>
    Classical.choose (hb (range fun η : Iio ξ => h (IH η η.2)) (mk_range_le.trans_lt (hI ξ)))
  refine ⟨WellFounded.fix wellFounded_lt F, fun ξ η hη => ?_⟩
  rw [WellFounded.fix_eq wellFounded_lt F ξ]
  exact Classical.choose_spec
    (hb (range fun η : Iio ξ => h (WellFounded.fix wellFounded_lt F η))
      (mk_range_le.trans_lt (hI ξ))) _ ⟨⟨η, hη⟩, rfl⟩

end WellOrder

/-! ### The combinatorial core -/

section Main

variable {W : Type u} [LinearOrder W] [WellFoundedLT W]

/-- The `!c`-neighbours of `α` lying below `α`. -/
def nbr (f : W → W → Bool) (c : Bool) (α : W) : Set W := {γ | γ < α ∧ f γ α = !c}

/-- The points joined by colour `!c` to every element of `Z`. -/
def common (f : W → W → Bool) (c : Bool) (Z : Set W) : Set W := {γ | ∀ z ∈ Z, f z γ = !c}

/-- Points of cofinality `> μ`: every subset of the initial segment of size `≤ μ` is bounded
strictly below the point. -/
def bigCof (μ : Cardinal.{u}) : Set W :=
  {α | ∀ Z : Set W, Z ⊆ Iio α → #Z ≤ μ → ∃ β < α, Z ⊆ Iio β}

/-- `α` is *good*: it has big cofinality, and every small `!c`-homogeneous `Z ⊆ nbr f c α`
bounded by some `β < α` admits a `!c`-neighbour of `α` above `β` joined to all of `Z`. -/
def IsGood (f : W → W → Bool) (c : Bool) (μ : Cardinal.{u}) (α : W) : Prop :=
  α ∈ bigCof μ ∧ ∀ Z ⊆ nbr f c α, Homog f (!c) Z → #Z ≤ μ →
    ∀ β < α, Z ⊆ Iio β → ∃ γ ∈ nbr f c α ∩ common f c Z, β ≤ γ

omit [LinearOrder W] [WellFoundedLT W] in
theorem homog_sUnion_of_chain {f : W → W → Bool} {c : Bool} {ch : Set (Set W)}
    (hch : IsChain (· ⊆ ·) ch) (hh : ∀ Z ∈ ch, Homog f c Z) : Homog f c (⋃₀ ch) := by
  intro x hx y hy hxy
  obtain ⟨Z₁, hZ₁, hx⟩ := mem_sUnion.1 hx
  obtain ⟨Z₂, hZ₂, hy⟩ := mem_sUnion.1 hy
  rcases hch.total hZ₁ hZ₂ with h | h
  · exact hh Z₂ hZ₂ x (h hx) y hy hxy
  · exact hh Z₁ hZ₁ x hx y (h hy) hxy

omit [LinearOrder W] [WellFoundedLT W] in
theorem exists_maximal_homog (f : W → W → Bool) (c : Bool) (A : Set W) :
    ∃ Z, Maximal (· ∈ {Z : Set W | Z ⊆ A ∧ Homog f c Z}) Z := by
  have hchain : ∀ ch ⊆ {Z : Set W | Z ⊆ A ∧ Homog f c Z}, IsChain (· ⊆ ·) ch → ch.Nonempty →
      ∃ ub ∈ {Z : Set W | Z ⊆ A ∧ Homog f c Z}, ∀ s ∈ ch, s ⊆ ub := by
    intro ch hch hchain _
    exact ⟨⋃₀ ch, ⟨sUnion_subset fun Z hZ => (hch hZ).1,
      homog_sUnion_of_chain hchain fun Z hZ => (hch hZ).2⟩, fun Z hZ => subset_sUnion_of_mem hZ⟩
  obtain ⟨Z, -, hZ⟩ := zorn_subset_nonempty {Z : Set W | Z ⊆ A ∧ Homog f c Z} hchain ∅
    ⟨empty_subset _, Homog.empty f c⟩
  exact ⟨Z, hZ⟩

omit [WellFoundedLT W] in
/-- Case 1: a good point yields a `!c`-homogeneous set of size `μ⁺`. -/
theorem good_case {f : W → W → Bool} (hf : ∀ x y, f x y = f y x) {c : Bool}
    {μ : Cardinal.{u}} {α : W} (hgood : IsGood f c μ α) :
    ∃ H : Set W, #H = Order.succ μ ∧ Homog f (!c) H := by
  obtain ⟨Z, hZ⟩ := exists_maximal_homog f (!c) (nbr f c α)
  obtain ⟨hZA, hZh⟩ := hZ.1
  have hlt : μ < #Z := by
    by_contra hle
    rw [not_lt] at hle
    obtain ⟨β, hβα, hZβ⟩ := hgood.1 Z (fun z hz => (hZA hz).1) hle
    obtain ⟨γ, ⟨hγA, hγD⟩, hβγ⟩ := hgood.2 Z hZA hZh hle β hβα hZβ
    have hins : insert γ Z ∈ {Z : Set W | Z ⊆ nbr f c α ∧ Homog f (!c) Z} := by
      refine ⟨insert_subset hγA hZA, ?_⟩
      intro x hx y hy hxy
      rcases mem_insert_iff.1 hx with hxγ | hxZ <;> rcases mem_insert_iff.1 hy with hyγ | hyZ
      · exact absurd (hxγ.trans hyγ.symm) hxy
      · rw [hxγ, hf]; exact hγD y hyZ
      · rw [hyγ]; exact hγD x hxZ
      · exact hZh x hxZ y hyZ hxy
    have heq := hZ.eq_of_subset hins (subset_insert γ Z)
    have hγZ : γ ∈ Z := heq ▸ mem_insert γ Z
    exact absurd (hZβ hγZ) (not_lt.2 hβγ)
  obtain ⟨H, hHZ, hH⟩ := le_mk_iff_exists_subset.1 (Order.succ_le_of_lt hlt)
  exact ⟨H, hH, hZh.mono hHZ⟩

omit [WellFoundedLT W] in
theorem not_good_unfold {f : W → W → Bool} {c : Bool} {μ : Cardinal.{u}} {α : W}
    (hα : α ∈ bigCof μ) (hno : ¬ IsGood f c μ α) :
    ∃ (Z : Set W) (β : W), Z ⊆ nbr f c α ∧ Homog f (!c) Z ∧ #Z ≤ μ ∧ β < α ∧ Z ⊆ Iio β ∧
      nbr f c α ∩ common f c Z ⊆ Iio β := by
  unfold IsGood at hno
  push Not at hno
  obtain ⟨Z, hZA, hZh, hZμ, β, hβα, hZβ, hγ⟩ := hno hα
  exact ⟨Z, β, hZA, hZh, hZμ, hβα, hZβ, fun γ hγ' => hγ γ hγ'⟩

/-- Claim A (closure-point argument): if `δ` regresses on the points of big cofinality, then
some fibre of `δ` on those points has full cardinality. -/
theorem exists_large_fibre {μ : Cardinal.{u}} (hμ : ℵ₀ ≤ μ)
    (hW : #W = Order.succ (2 ^ μ)) (hord : ord #W = typeLT W)
    (δ : W → W) (hδ : ∀ α ∈ bigCof μ, δ α < α) :
    ∃ δ₀, #W ≤ #{α | α ∈ bigCof μ ∧ δ α = δ₀} := by
  have h2μ : ℵ₀ ≤ 2 ^ μ := hμ.trans (cantor μ).le
  have hreg : Cardinal.IsRegular #W := by rw [hW]; exact isRegular_succ h2μ
  have hℵW : ℵ₀ ≤ #W := hreg.aleph0_le
  by_contra hcon
  push Not at hcon
  -- strict bounds for the (small) fibres
  choose g hg using fun δ₀ => exists_forall_lt_of_mk_lt hreg hord (hcon δ₀)
  -- the closure step `h`
  have hstep : ∀ x : W, #(insert x (g '' Iic x) : Set W) < #W := by
    intro x
    calc #(insert x (g '' Iic x) : Set W) ≤ #(g '' Iic x) + 1 := mk_insert_le
      _ ≤ #(Iic x) + 1 := add_le_add mk_image_le le_rfl
      _ < #W := add_lt_of_lt hℵW (mk_Iic_lt x hord hℵW) (one_lt_aleph0.trans_le hℵW)
  choose h hh using fun x => exists_forall_lt_of_mk_lt hreg hord (hstep x)
  have hxh : ∀ x, x < h x := fun x => hh x x (mem_insert x _)
  have hgh : ∀ x δ', δ' ≤ x → g δ' < h x := fun x δ' hδ' =>
    hh x (g δ') (mem_insert_of_mem x (mem_image_of_mem g hδ'))
  -- the index well-order `I` of cardinality `μ⁺`
  have hI : #((Order.succ μ).ord.ToType) = Order.succ μ := mk_ord_toType _
  have hordI : ord #((Order.succ μ).ord.ToType) = typeLT ((Order.succ μ).ord.ToType) := by
    rw [hI, type_toType]
  have hregI : Cardinal.IsRegular #((Order.succ μ).ord.ToType) := by
    rw [hI]; exact isRegular_succ hμ
  have hμI : μ < #((Order.succ μ).ord.ToType) := by rw [hI]; exact Order.lt_succ μ
  have hIW : #((Order.succ μ).ord.ToType) < #W := by
    rw [hI, hW]
    exact (Order.succ_le_of_lt (cantor μ)).trans_lt (Order.lt_succ _)
  obtain ⟨β, hβ⟩ := exists_seq (I := (Order.succ μ).ord.ToType) (κ := #W)
    (fun s hs => exists_forall_lt_of_mk_lt hreg hord hs)
    (fun ξ => (mk_Iio_lt ξ hordI).trans hIW) h
  have hβmono : ∀ ξ η : (Order.succ μ).ord.ToType, η < ξ → β η < β ξ :=
    fun ξ η hη => (hxh _).trans (hβ ξ η hη)
  -- the least strict upper bound `α₀` of the range of `β`
  have hT : {x : W | ∀ ξ, β ξ < x}.Nonempty := by
    obtain ⟨x, hx⟩ := exists_forall_lt_of_mk_lt hreg hord (s := range β)
      (mk_range_le.trans_lt hIW)
    exact ⟨x, fun ξ => hx _ (mem_range_self ξ)⟩
  obtain ⟨α₀, hα₀T, hbelow⟩ : ∃ α₀ : W, (∀ ξ, β ξ < α₀) ∧ ∀ y, y < α₀ → ∃ ξ, y ≤ β ξ := by
    refine ⟨(wellFounded_lt (α := W)).min _ hT, (wellFounded_lt (α := W)).min_mem _ hT, ?_⟩
    intro y hy
    by_contra hcon'
    push Not at hcon'
    exact (wellFounded_lt (α := W)).not_lt_min {x : W | ∀ ξ, β ξ < x} (x := y) hcon' hy
  -- `α₀` has big cofinality
  have hα₀S : α₀ ∈ bigCof μ := by
    intro Z hZ hZμ
    choose ξ hξ using fun z : Z => hbelow z (hZ z.2)
    obtain ⟨ξ', hξ'⟩ := exists_forall_lt_of_mk_lt hregI hordI (s := range ξ)
      (mk_range_le.trans_lt (hZμ.trans_lt hμI))
    refine ⟨β ξ', hα₀T ξ', fun z hz => ?_⟩
    exact (hξ ⟨z, hz⟩).trans_lt (hβmono _ _ (hξ' _ (mem_range_self _)))
  -- but `α₀` lies in the fibre of `δ α₀`, which is bounded below `α₀`
  have h1 : α₀ < g (δ α₀) := hg (δ α₀) α₀ ⟨hα₀S, rfl⟩
  obtain ⟨ξ, hξ⟩ := hbelow _ (hδ α₀ hα₀S)
  obtain ⟨ξ', hξξ'⟩ := exists_gt_of_regular hregI hordI ξ
  have h2 : g (δ α₀) < β ξ' := (hgh _ _ hξ).trans (hβ ξ' ξ hξξ')
  exact lt_irrefl α₀ (h1.trans (h2.trans (hα₀T ξ')))

/-- Case 2: if no point is good, there is a `c`-homogeneous set of full cardinality. -/
theorem no_good_case {f : W → W → Bool} (hf : ∀ x y, f x y = f y x) {c : Bool}
    {μ : Cardinal.{u}} (hμ : ℵ₀ ≤ μ) (hW : #W = Order.succ (2 ^ μ)) (hord : ord #W = typeLT W)
    (hno : ∀ α, ¬ IsGood f c μ α) : ∃ H : Set W, #H = #W ∧ Homog f c H := by
  have h2μ : ℵ₀ ≤ 2 ^ μ := hμ.trans (cantor μ).le
  have hreg : Cardinal.IsRegular #W := by rw [hW]; exact isRegular_succ h2μ
  have hℵW : ℵ₀ ≤ #W := hreg.aleph0_le
  have hchoice : ∀ α : W, ∃ (Z : Set W) (δ : W), α ∈ bigCof μ →
      (Z ⊆ nbr f c α ∧ Homog f (!c) Z ∧ #Z ≤ μ ∧ δ < α ∧ Z ⊆ Iio δ ∧
        nbr f c α ∩ common f c Z ⊆ Iio δ) := by
    intro α
    by_cases hα : α ∈ bigCof μ
    · obtain ⟨Z, δ, hZδ⟩ := not_good_unfold hα (hno α)
      exact ⟨Z, δ, fun _ => hZδ⟩
    · exact ⟨∅, α, fun h => absurd h hα⟩
  choose Z δ hZδ using hchoice
  obtain ⟨δ₀, hδ₀⟩ := exists_large_fibre hμ hW hord δ fun α hα => (hZδ α hα).2.2.2.1
  -- Claim B: pigeonhole on the map `α ↦ Z α`
  have hTcard : #{t : Set W // t ⊆ Iio δ₀ ∧ #t ≤ μ} < (#W).ord.cof := by
    rw [hreg.cof_ord]
    refine (mk_bounded_subset_le (Iio δ₀) μ).trans_lt ?_
    have hIio : #(Iio δ₀) ≤ 2 ^ μ := by
      rw [← Order.lt_succ_iff, ← hW]
      exact mk_Iio_lt δ₀ hord
    calc max #(Iio δ₀) ℵ₀ ^ μ ≤ (2 ^ μ) ^ μ := power_le_power_right (max_le hIio h2μ)
      _ = 2 ^ μ := by rw [← power_mul, mul_eq_self hμ]
      _ < #W := by rw [hW]; exact Order.lt_succ _
  let φ : {α | α ∈ bigCof μ ∧ δ α = δ₀} → {t : Set W // t ⊆ Iio δ₀ ∧ #t ≤ μ} := fun α =>
    ⟨Z α, by
      have h := hZδ α.1 α.2.1
      refine ⟨h.2.2.2.2.1.trans ?_, h.2.2.1⟩
      rw [α.2.2]⟩
  obtain ⟨Z₀, t, htF, htcard, hφ⟩ := infinite_pigeonhole_set φ #W hδ₀ hℵW hTcard
  have htZ : ∀ x ∈ t, Z x = Z₀.1 := fun x hx => congrArg Subtype.val (hφ hx)
  have htW : #t = #W := le_antisymm (mk_set_le t) htcard
  -- Claim C: remove the points `≤ δ₀`
  refine ⟨t \ Iic δ₀, ?_, ?_⟩
  · have h1 : t.Infinite := infinite_coe_iff.1 (infinite_iff.2 (hℵW.trans htcard))
    have h2 : #(Iic δ₀) < #t := by rw [htW]; exact mk_Iic_lt δ₀ hord hℵW
    rw [mk_sdiff_eq_left h1 h2, htW]
  · have hbool : ∀ b d : Bool, ¬ b = d → b = !d := by decide
    have key : ∀ a ∈ t \ Iic δ₀, ∀ a' ∈ t \ Iic δ₀, a < a' → f a a' = c := by
      intro a ha a' ha' hlt
      have haF := htF ha.1
      have ha'F := htF ha'.1
      have hZa := hZδ a haF.1
      have hZa' := hZδ a' ha'F.1
      have haD : a ∈ common f c (Z a') := by
        intro z hz
        rw [htZ a' ha'.1, ← htZ a ha.1] at hz
        exact (hZa.1 hz).2
      by_contra hne
      have hmem : a ∈ nbr f c a' ∩ common f c (Z a') := ⟨⟨hlt, hbool _ _ hne⟩, haD⟩
      have hlt' := hZa'.2.2.2.2.2 hmem
      rw [ha'F.2] at hlt'
      exact ha.2 (le_of_lt hlt')
    intro a ha a' ha' hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact key a ha a' ha' h
    · rw [hf]; exact key a' ha' a ha h

/-- The theorem on a well-ordered type of cardinality `(2^μ)⁺` and order type `(2^μ)⁺.ord`. -/
theorem erdosRado_unbalanced_wo {f : W → W → Bool} (hf : ∀ x y, f x y = f y x)
    {μ : Cardinal.{u}} (hμ : ℵ₀ ≤ μ) (hW : #W = Order.succ (2 ^ μ)) (hord : ord #W = typeLT W)
    (c : Bool) :
    (∃ H : Set W, #H = Order.succ (2 ^ μ) ∧ Homog f c H) ∨
      (∃ H : Set W, #H = Order.succ μ ∧ Homog f (!c) H) := by
  by_cases hg : ∃ α, IsGood f c μ α
  · obtain ⟨α, hα⟩ := hg
    exact Or.inr (good_case hf hα)
  · push Not at hg
    obtain ⟨H, hH, hHc⟩ := no_good_case hf hμ hW hord hg
    exact Or.inl ⟨H, hH.trans hW, hHc⟩

end Main

/-! ### The theorem on an arbitrary type -/

/-- The unbalanced Erdős–Rado theorem `(2^μ)⁺ → ((2^μ)⁺, μ⁺)²`, stated for both colours `c`. -/
theorem erdosRado_unbalanced {V : Type u} (f : V → V → Bool) (hf : ∀ x y, f x y = f y x)
    (μ : Cardinal.{u}) (hμ : ℵ₀ ≤ μ) (C : Set V) (hC : #C = Order.succ (2 ^ μ)) (c : Bool) :
    (∃ H ⊆ C, #H = Order.succ (2 ^ μ) ∧ Homog f c H) ∨
      (∃ H ⊆ C, #H = Order.succ μ ∧ Homog f (!c) H) := by
  have hW : #((Order.succ (2 ^ μ : Cardinal.{u})).ord.ToType) = Order.succ (2 ^ μ) :=
    mk_ord_toType _
  have hord : ord #((Order.succ (2 ^ μ : Cardinal.{u})).ord.ToType) =
      typeLT ((Order.succ (2 ^ μ : Cardinal.{u})).ord.ToType) := by
    rw [hW, type_toType]
  obtain ⟨e⟩ : Nonempty (C ≃ (Order.succ (2 ^ μ : Cardinal.{u})).ord.ToType) :=
    Cardinal.eq.1 (hC.trans hW.symm)
  let g : (Order.succ (2 ^ μ : Cardinal.{u})).ord.ToType → V := fun x => (e.symm x : V)
  have hg : Function.Injective g := fun x y hxy =>
    e.symm.injective (Subtype.val_injective hxy)
  have hf' : ∀ x y, f (g x) (g y) = f (g y) (g x) := fun x y => hf _ _
  have transport : ∀ (d : Bool) (H : Set ((Order.succ (2 ^ μ : Cardinal.{u})).ord.ToType)),
      Homog (fun x y => f (g x) (g y)) d H →
        g '' H ⊆ C ∧ #(g '' H) = #H ∧ Homog f d (g '' H) := by
    intro d H hH
    refine ⟨?_, mk_image_eq hg, ?_⟩
    · rintro _ ⟨x, -, rfl⟩
      exact (e.symm x).2
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy
      exact hH x hx y hy fun h => hxy (congrArg g h)
  rcases erdosRado_unbalanced_wo hf' hμ hW hord c with ⟨H, hH, hHc⟩ | ⟨H, hH, hHc⟩
  · obtain ⟨h1, h2, h3⟩ := transport c H hHc
    exact Or.inl ⟨g '' H, h1, h2.trans hH, h3⟩
  · obtain ⟨h1, h2, h3⟩ := transport (!c) H hHc
    exact Or.inr ⟨g '' H, h1, h2.trans hH, h3⟩

end Erdos1219

#print axioms Erdos1219.erdosRado_unbalanced
