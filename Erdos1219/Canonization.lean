import Erdos1219.Defs
import Erdos1219.CardinalLemmas
import Erdos1219.Ramsey
import Erdos1219.UnbalancedErdosRado

/-!
# The canonization argument (Shelah, Notes on partition calculus, §1)

We formalize the proof of Shelah's Theorem 1.2 (special case: `λ = ℵ_ω`), following the
Canonization Lemma 1.1 of that paper.  See `docs/PROOF.md` for the mathematical proof.

The colouring is a symmetric `f : V → V → Bool`, the vertex set `V` is (essentially) the disjoint
union of blocks `A k` with `#(A k) = lam k := (2 ^ ℵ_{n k})⁺`.  Assuming that there is no
homogeneous set of size `ℵ_ω` at all (`hno`), every block contains, inside every subset of full
size, homogeneous sets of both colours of size `μ k := ℵ_{n k}` (unbalanced Erdős–Rado).  A
"guide" `guide k ∈ A k` avoiding the small set `bad k` is chosen in each block; then blocks
`B k = (B k).1 ∪ (B k).2` (a `false`-homogeneous and a `true`-homogeneous part, each of size
`μ k`) are chosen inductively inside the class of the guide over the earlier blocks, all with the
same type over the guides.  This makes the colouring canonical across blocks, so that Ramsey's
theorem on `ℕ` produces the required homogeneous set of size `ℵ_ω`, a contradiction.
-/

open Cardinal Ordinal Function

namespace Erdos1219

universe u

/-- The data of the argument: a symmetric colouring on `V`, the sequence `n`, blocks `A k` of
size `(2 ^ ℵ_{n k})⁺`, and the assumption that there is no homogeneous set of size `ℵ_ω`. -/
structure Ctx (V : Type u) where
  f : V → V → Bool
  hf : ∀ x y, f x y = f y x
  n : ℕ → ℕ
  hn : StrictMono n
  hpow : StrictMono fun k => (2 : Cardinal.{u}) ^ ℵ_ (n k)
  h0 : ℵ_ ω < (2 : Cardinal.{u}) ^ ℵ_ (n 0)
  A : ℕ → Set V
  hA : ∀ k, #(A k) = Order.succ ((2 : Cardinal.{u}) ^ ℵ_ (n k))
  hdisj : ∀ i j, i ≠ j → Disjoint (A i) (A j)
  hno : ∀ (c : Bool) (H : Set V), Homog f c H → #H ≠ ℵ_ ω

namespace Ctx

variable {V : Type u} (S : Ctx V)

/-! ### Cardinal bookkeeping -/

/-- `μ k = ℵ_{n k}`. -/
noncomputable def μ (k : ℕ) : Cardinal.{u} := ℵ_ (S.n k : Ordinal.{u})

/-- `lam k = (2 ^ μ k)⁺`, the size of the `k`-th block. -/
noncomputable def lam (k : ℕ) : Cardinal.{u} := Order.succ (2 ^ S.μ k)

theorem mk_A (k : ℕ) : #(S.A k) = S.lam k := S.hA k

theorem aleph0_le_μ (k : ℕ) : ℵ₀ ≤ S.μ k := aleph0_le_aleph _

theorem μ_mono {i k : ℕ} (h : i ≤ k) : S.μ i ≤ S.μ k :=
  aleph_le_aleph.2 (by exact_mod_cast S.hn.monotone h)

theorem two_pow_μ_lt {i k : ℕ} (h : i < k) : (2 : Cardinal.{u}) ^ S.μ i < 2 ^ S.μ k := S.hpow h

theorem two_pow_μ_le {i k : ℕ} (h : i ≤ k) : (2 : Cardinal.{u}) ^ S.μ i ≤ 2 ^ S.μ k :=
  S.hpow.monotone h

theorem aleph0_le_two_pow_μ (k : ℕ) : ℵ₀ ≤ (2 : Cardinal.{u}) ^ S.μ k :=
  aleph0_le_two_pow (S.aleph0_le_μ k)

theorem lam_isRegular (k : ℕ) : (S.lam k).IsRegular := isRegular_succ (S.aleph0_le_two_pow_μ k)

theorem two_pow_lt_lam (k : ℕ) : (2 : Cardinal.{u}) ^ S.μ k < S.lam k := Order.lt_succ _

theorem lam_le_two_pow_succ (k : ℕ) : S.lam k ≤ 2 ^ S.μ (k + 1) :=
  Order.succ_le_of_lt (S.two_pow_μ_lt (Nat.lt_succ_self k))

theorem aleph_omega_lt_two_pow (k : ℕ) : ℵ_ ω < (2 : Cardinal.{u}) ^ S.μ k :=
  S.h0.trans_le (S.two_pow_μ_le (Nat.zero_le k))

theorem aleph_omega_lt_lam (k : ℕ) : ℵ_ ω < S.lam k :=
  (S.aleph_omega_lt_two_pow k).trans (S.two_pow_lt_lam k)

theorem μ_lt_lam (k : ℕ) : S.μ k < S.lam k :=
  le_two_pow_self.trans_lt (S.two_pow_lt_lam k)

theorem two_pow_aleph0_lt_lam (k : ℕ) : (2 : Cardinal.{u}) ^ ℵ₀ < S.lam k :=
  (power_le_power_left two_ne_zero (S.aleph0_le_μ k)).trans_lt (S.two_pow_lt_lam k)

/-! ### Homogeneous sets of both colours inside every large subset of a block -/

/-- There is no homogeneous set of size `lam k` (it would contain one of size `ℵ_ω`). -/
theorem noBig (k : ℕ) (c : Bool) (H : Set V) (hH : Homog S.f c H) : #H ≠ S.lam k := by
  intro hHk
  obtain ⟨H', hH'sub, hH'⟩ :=
    le_mk_iff_exists_subset.1 ((S.aleph_omega_lt_lam k).le.trans_eq hHk.symm)
  exact S.hno c H' (hH.mono hH'sub) hH'

/-- Every subset of full size of a block contains homogeneous sets of both colours of size
`μ k` (unbalanced Erdős–Rado). -/
theorem exists_homog_two (k : ℕ) (C : Set V) (hC : #C = S.lam k) :
    ∃ B0 B1 : Set V, B0 ⊆ C ∧ B1 ⊆ C ∧ #B0 = S.μ k ∧ #B1 = S.μ k ∧
      Homog S.f false B0 ∧ Homog S.f true B1 := by
  have h0 := erdosRado_unbalanced S.f S.hf (S.μ k) (S.aleph0_le_μ k) C hC true
  have h1 := erdosRado_unbalanced S.f S.hf (S.μ k) (S.aleph0_le_μ k) C hC false
  rcases h0 with ⟨H, -, hH, hom⟩ | ⟨H0, hH0C, hH0, hom0⟩
  · exact absurd hH (S.noBig k true H hom)
  rcases h1 with ⟨H, -, hH, hom⟩ | ⟨H1, hH1C, hH1, hom1⟩
  · exact absurd hH (S.noBig k false H hom)
  obtain ⟨B0, hB0, hB0c⟩ :=
    le_mk_iff_exists_subset.1 ((Order.le_succ (S.μ k)).trans_eq hH0.symm)
  obtain ⟨B1, hB1, hB1c⟩ :=
    le_mk_iff_exists_subset.1 ((Order.le_succ (S.μ k)).trans_eq hH1.symm)
  exact ⟨B0, B1, hB0.trans hH0C, hB1.trans hH1C, hB0c, hB1c, hom0.mono hB0, hom1.mono hB1⟩

/-! ### The union of the earlier blocks -/

/-- `U k = A 0 ∪ ... ∪ A (k-1)`. -/
noncomputable def U (S : Ctx V) : ℕ → Set V
  | 0 => ∅
  | k + 1 => U S k ∪ S.A k

theorem mem_U {v : V} {k : ℕ} : v ∈ S.U k ↔ ∃ i, i < k ∧ v ∈ S.A i := by
  induction k with
  | zero => simp [U]
  | succ k ih =>
    simp only [U, Set.mem_union, ih]
    constructor
    · rintro (⟨i, hi, hv⟩ | hv)
      · exact ⟨i, Nat.lt_succ_of_lt hi, hv⟩
      · exact ⟨k, Nat.lt_succ_self k, hv⟩
    · rintro ⟨i, hi, hv⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact Or.inl ⟨i, hi, hv⟩
      · exact Or.inr hv

theorem A_subset_U {i k : ℕ} (h : i < k) : S.A i ⊆ S.U k := fun _ hv => S.mem_U.2 ⟨i, h, hv⟩

theorem mk_U_le (k : ℕ) : #(S.U k) ≤ 2 ^ S.μ k := by
  induction k with
  | zero => simp [U]
  | succ k ih =>
    calc #(S.U (k + 1)) = #(S.U k ∪ S.A k : Set V) := by rw [U]
      _ ≤ #(S.U k) + #(S.A k) := mk_union_le _ _
      _ ≤ 2 ^ S.μ (k + 1) + 2 ^ S.μ (k + 1) :=
          add_le_add (ih.trans (S.two_pow_μ_le (Nat.le_succ k)))
            (by rw [S.mk_A]; exact S.lam_le_two_pow_succ k)
      _ = 2 ^ S.μ (k + 1) := add_eq_self (S.aleph0_le_two_pow_μ _)

/-! ### Classes, bad points and guides -/

/-- The class of `a` over `B` inside the block `A k`: the points of `A k` with the same
colours towards `B` as `a`. -/
def cls (k : ℕ) (a : V) (B : Set V) : Set V := {a' ∈ S.A k | ∀ b ∈ B, S.f a' b = S.f a b}

theorem cls_subset_A (k : ℕ) (a : V) (B : Set V) : S.cls k a B ⊆ S.A k := fun _ h => h.1

/-- The bad points of `A k`: those having a small class over some small subset of `U k`. -/
def bad (k : ℕ) : Set V :=
  {a ∈ S.A k | ∃ B : Set V, B ⊆ S.U k ∧ #B ≤ S.μ k ∧ #(S.cls k a B) < S.lam k}

/-- The type of `a` over `B`. -/
def tp (a : V) (B : Set V) : Set (↥B) := {b | S.f a b = true}

theorem cls_eq_fib (k : ℕ) (a : V) (B : Set V) :
    S.cls k a B = {a' ∈ S.A k | S.tp a' B = S.tp a B} := by
  ext a'
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    ext b
    show S.f a' b = true ↔ S.f a b = true
    rw [h2 b b.2]
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun b hb => ?_⟩
    have := Set.ext_iff.1 h2 ⟨b, hb⟩
    exact Bool.eq_iff_iff.2 this

theorem mk_small_lt (k : ℕ) (B : Set V) (hB : #B ≤ S.μ k) :
    #({a ∈ S.A k | #(S.cls k a B) < S.lam k} : Set V) < S.lam k := by
  have hsub : {a ∈ S.A k | #(S.cls k a B) < S.lam k} ⊆
      ⋃ (t : {t : Set (↥B) // #({a ∈ S.A k | S.tp a B = t} : Set V) < S.lam k}),
        {a ∈ S.A k | S.tp a B = t.1} := by
    rintro a ⟨ha, hlt⟩
    rw [S.cls_eq_fib] at hlt
    exact Set.mem_iUnion.2 ⟨⟨S.tp a B, hlt⟩, ha, rfl⟩
  refine (mk_le_mk_of_subset hsub).trans_lt
    (mk_iUnion_lt_of_isRegular (S.lam_isRegular k) ?_ _ fun t => t.2)
  calc #{t : Set (↥B) // #({a ∈ S.A k | S.tp a B = t} : Set V) < S.lam k}
      ≤ #(Set (↥B)) := mk_subtype_le _
    _ = 2 ^ #B := mk_set
    _ ≤ 2 ^ S.μ k := power_le_power_left two_ne_zero hB
    _ < S.lam k := S.two_pow_lt_lam k

theorem mk_bad_lt (k : ℕ) : #(S.bad k) < S.lam k := by
  have hsub : S.bad k ⊆ ⋃ (B : {B : Set V // B ⊆ S.U k ∧ #B ≤ S.μ k}),
      {a ∈ S.A k | #(S.cls k a B.1) < S.lam k} := by
    rintro a ⟨ha, B, hBU, hBμ, hlt⟩
    exact Set.mem_iUnion.2 ⟨⟨B, hBU, hBμ⟩, ha, hlt⟩
  refine (mk_le_mk_of_subset hsub).trans_lt
    (mk_iUnion_lt_of_isRegular (S.lam_isRegular k) ?_ _ fun B => S.mk_small_lt k B.1 B.2.2)
  exact (mk_bounded_subsets_le (S.U k) (S.aleph0_le_μ k) (S.mk_U_le k)).trans_lt
    (S.two_pow_lt_lam k)

theorem exists_guide (k : ℕ) : ∃ a, a ∈ S.A k ∧ a ∉ S.bad k := by
  by_contra h
  have hsub : S.A k ⊆ S.bad k := fun a ha => by
    by_contra hb
    exact h ⟨a, ha, hb⟩
  have := (mk_le_mk_of_subset hsub).trans_lt (S.mk_bad_lt k)
  rw [S.mk_A] at this
  exact lt_irrefl _ this

/-- The guide of block `k`: a point of `A k` that is not bad. -/
noncomputable def guide (k : ℕ) : V := (S.exists_guide k).choose

theorem guide_mem (k : ℕ) : S.guide k ∈ S.A k := (S.exists_guide k).choose_spec.1

theorem guide_not_bad (k : ℕ) : S.guide k ∉ S.bad k := (S.exists_guide k).choose_spec.2

theorem mk_cls_guide (k : ℕ) (B : Set V) (hBU : B ⊆ S.U k) (hBμ : #B ≤ S.μ k) :
    #(S.cls k (S.guide k) B) = S.lam k := by
  apply le_antisymm
  · exact (mk_le_mk_of_subset (S.cls_subset_A k _ B)).trans_eq (S.mk_A k)
  · by_contra h
    exact S.guide_not_bad k ⟨S.guide_mem k, B, hBU, hBμ, lt_of_not_ge h⟩

/-! ### The blocks -/

/-- The basic requirement on the `k`-th pair of blocks: both parts lie in `A k` and the union
has size at most `μ k`. -/
structure Basic (k : ℕ) (p : Set V × Set V) : Prop where
  sub : p.1 ∪ p.2 ⊆ S.A k
  mk_le : #(p.1 ∪ p.2 : Set V) ≤ S.μ k

/-- The union of the earlier blocks `prev i` (`i < k`). -/
noncomputable def prevU (S : Ctx V) : (k : ℕ) → (∀ i, i < k → Set V × Set V) → Set V
  | 0, _ => ∅
  | k + 1, prev =>
      prevU S k (fun i h => prev i (Nat.lt_succ_of_lt h)) ∪
        ((prev k (Nat.lt_succ_self k)).1 ∪ (prev k (Nat.lt_succ_self k)).2)

theorem mem_prevU {k : ℕ} {prev : ∀ i, i < k → Set V × Set V} {v : V} :
    v ∈ S.prevU k prev ↔ ∃ i, ∃ h : i < k, v ∈ (prev i h).1 ∪ (prev i h).2 := by
  induction k with
  | zero => simp [prevU]
  | succ k ih =>
    simp only [prevU, Set.mem_union, ih]
    constructor
    · rintro (⟨i, hi, hv⟩ | hv)
      · exact ⟨i, Nat.lt_succ_of_lt hi, hv⟩
      · exact ⟨k, Nat.lt_succ_self k, hv⟩
    · rintro ⟨i, hi, hv⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi' | rfl
      · exact Or.inl ⟨i, hi', hv⟩
      · exact Or.inr hv

theorem mk_prevU_le {k : ℕ} {prev : ∀ i, i < k → Set V × Set V}
    (hprev : ∀ i h, S.Basic i (prev i h)) : #(S.prevU k prev) ≤ S.μ k := by
  induction k with
  | zero => simp [prevU]
  | succ k ih =>
    calc #(S.prevU (k + 1) prev)
        ≤ #(S.prevU k (fun i h => prev i (Nat.lt_succ_of_lt h))) +
            #((prev k (Nat.lt_succ_self k)).1 ∪ (prev k (Nat.lt_succ_self k)).2 : Set V) :=
          mk_union_le _ _
      _ ≤ S.μ (k + 1) + S.μ (k + 1) :=
          add_le_add ((ih (fun i h => hprev i _)).trans (S.μ_mono (Nat.le_succ k)))
            ((hprev k _).mk_le.trans (S.μ_mono (Nat.le_succ k)))
      _ = S.μ (k + 1) := add_eq_self (S.aleph0_le_μ _)

theorem prevU_subset_U {k : ℕ} {prev : ∀ i, i < k → Set V × Set V}
    (hprev : ∀ i h, S.Basic i (prev i h)) : S.prevU k prev ⊆ S.U k := by
  intro v hv
  obtain ⟨i, hi, hvi⟩ := S.mem_prevU.1 hv
  exact S.A_subset_U hi ((hprev i hi).sub hvi)

/-- The properties of the `k`-th pair of blocks, relative to the earlier ones. -/
structure Good (k : ℕ) (prev : ∀ i, i < k → Set V × Set V) (p : Set V × Set V) : Prop where
  sub1 : p.1 ⊆ S.A k
  sub2 : p.2 ⊆ S.A k
  mk1 : #p.1 = S.μ k
  mk2 : #p.2 = S.μ k
  hom1 : Homog S.f false p.1
  hom2 : Homog S.f true p.2
  cls : ∀ a ∈ p.1 ∪ p.2, ∀ b ∈ S.prevU k prev, S.f a b = S.f (S.guide k) b
  same : ∀ a ∈ p.1 ∪ p.2, ∀ a' ∈ p.1 ∪ p.2, ∀ j, S.f a (S.guide j) = S.f a' (S.guide j)

/-- The type of a point over the guides. -/
def gtp (a : V) : Set (ULift.{u} ℕ) := {j | S.f a (S.guide j.down) = true}

theorem mk_set_uLift_nat_lt_lam (k : ℕ) : #(Set (ULift.{u} ℕ)) < S.lam k := by
  rw [mk_set, mk_uLift, mk_nat, Cardinal.lift_aleph0]
  exact S.two_pow_aleph0_lt_lam k

theorem exists_blocks (k : ℕ) (prev : ∀ i, i < k → Set V × Set V)
    (hprev : ∀ i h, S.Basic i (prev i h)) : ∃ p, S.Good k prev p ∧ S.Basic k p := by
  have hB1c : #(S.cls k (S.guide k) (S.prevU k prev)) = S.lam k :=
    S.mk_cls_guide k _ (S.prevU_subset_U hprev) (S.mk_prevU_le hprev)
  obtain ⟨t, ht⟩ := exists_fiber_eq_of_isRegular (S.lam_isRegular k) _ hB1c S.gtp
    (S.mk_set_uLift_nat_lt_lam k)
  obtain ⟨B0, B1, hB0, hB1, hB0c, hB1c, hom0, hom1⟩ := S.exists_homog_two k _ ht
  have hB0A : B0 ⊆ S.A k := fun a ha => (hB0 ha).1.1
  have hB1A : B1 ⊆ S.A k := fun a ha => (hB1 ha).1.1
  have hcls : ∀ a ∈ B0 ∪ B1, a ∈ S.cls k (S.guide k) (S.prevU k prev) := by
    rintro a (ha | ha)
    · exact (hB0 ha).1
    · exact (hB1 ha).1
  have htp : ∀ a ∈ B0 ∪ B1, S.gtp a = t := by
    rintro a (ha | ha)
    · exact (hB0 ha).2
    · exact (hB1 ha).2
  refine ⟨(B0, B1), ⟨hB0A, hB1A, hB0c, hB1c, hom0, hom1, ?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro a ha b hb
    exact (hcls a ha).2 b hb
  · intro a ha a' ha' j
    have h := (htp a ha).trans (htp a' ha').symm
    have h' : S.f a (S.guide j) = true ↔ S.f a' (S.guide j) = true := Set.ext_iff.1 h ⟨j⟩
    exact Bool.eq_iff_iff.2 h'
  · exact Set.union_subset hB0A hB1A
  · calc #(B0 ∪ B1 : Set V) ≤ #B0 + #B1 := mk_union_le _ _
      _ = S.μ k + S.μ k := by rw [hB0c, hB1c]
      _ = S.μ k := add_eq_self (S.aleph0_le_μ k)

/-- The blocks, defined by strong recursion. -/
noncomputable def blocks (S : Ctx V) : (k : ℕ) → {p : Set V × Set V // S.Basic k p}
  | k =>
    ⟨(S.exists_blocks k (fun i _ => (blocks S i).1) (fun i _ => (blocks S i).2)).choose,
      (S.exists_blocks k (fun i _ => (blocks S i).1) (fun i _ => (blocks S i).2)).choose_spec.2⟩
termination_by k => k

/-- The `k`-th pair of blocks. -/
noncomputable def B (k : ℕ) : Set V × Set V := (S.blocks k).1

theorem B_basic (k : ℕ) : S.Basic k (S.B k) := (S.blocks k).2

theorem blocks_good (k : ℕ) : S.Good k (fun i _ => S.B i) (S.B k) := by
  unfold B
  rw [blocks]
  exact (S.exists_blocks k (fun i _ => (S.blocks i).1)
    (fun i _ => (S.blocks i).2)).choose_spec.1

/-- The union of the two parts of the `k`-th block. -/
noncomputable def Bu (k : ℕ) : Set V := (S.B k).1 ∪ (S.B k).2

theorem Bu_subset_A (k : ℕ) : S.Bu k ⊆ S.A k := (S.B_basic k).sub

theorem mem_prevU_B {i j : ℕ} (hij : i < j) {a : V} (ha : a ∈ S.Bu i) :
    a ∈ S.prevU j (fun i _ => S.B i) :=
  S.mem_prevU.2 ⟨i, hij, ha⟩

/-! ### Canonicity -/

theorem canonical {i j : ℕ} (hij : i < j) {a a' b : V} (ha : a ∈ S.Bu i) (ha' : a' ∈ S.Bu i)
    (hb : b ∈ S.Bu j) : S.f a b = S.f a' b := by
  have hj := (S.blocks_good j).cls
  have hi := (S.blocks_good i).same
  calc S.f a b = S.f b a := S.hf a b
    _ = S.f (S.guide j) a := hj b hb a (S.mem_prevU_B hij ha)
    _ = S.f a (S.guide j) := S.hf _ _
    _ = S.f a' (S.guide j) := hi a ha a' ha' j
    _ = S.f (S.guide j) a' := S.hf _ _
    _ = S.f b a' := (hj b hb a' (S.mem_prevU_B hij ha')).symm
    _ = S.f a' b := S.hf _ _

/-- A chosen point of the `false`-part of the `i`-th block. -/
noncomputable def pick (i : ℕ) : V :=
  (nonempty_of_mk_eq (S.blocks_good i).mk1 (S.aleph0_le_μ i)).choose

theorem pick_mem (i : ℕ) : S.pick i ∈ S.Bu i :=
  Or.inl (nonempty_of_mk_eq (S.blocks_good i).mk1 (S.aleph0_le_μ i)).choose_spec

/-- The colour between the `i`-th and `j`-th blocks (`i < j`). -/
noncomputable def g (i j : ℕ) : Bool := S.f (S.pick i) (S.guide j)

theorem cross {i j : ℕ} (hij : i < j) {a b : V} (ha : a ∈ S.Bu i) (hb : b ∈ S.Bu j) :
    S.f a b = S.g i j := by
  have hj := (S.blocks_good j).cls
  calc S.f a b = S.f (S.pick i) b := S.canonical hij ha (S.pick_mem i) hb
    _ = S.f b (S.pick i) := S.hf _ _
    _ = S.f (S.guide j) (S.pick i) := hj b hb _ (S.mem_prevU_B hij (S.pick_mem i))
    _ = S.f (S.pick i) (S.guide j) := S.hf _ _

/-! ### The homogeneous set -/

/-- The `δ`-homogeneous part of the `k`-th block. -/
noncomputable def part (δ : Bool) (k : ℕ) : Set V := bif δ then (S.B k).2 else (S.B k).1

theorem part_subset_Bu (δ : Bool) (k : ℕ) : S.part δ k ⊆ S.Bu k := by
  cases δ
  · exact fun a ha => Or.inl ha
  · exact fun a ha => Or.inr ha

theorem part_homog (δ : Bool) (k : ℕ) : Homog S.f δ (S.part δ k) := by
  cases δ
  · exact (S.blocks_good k).hom1
  · exact (S.blocks_good k).hom2

theorem mk_part (δ : Bool) (k : ℕ) : #(S.part δ k) = S.μ k := by
  cases δ
  · exact (S.blocks_good k).mk1
  · exact (S.blocks_good k).mk2

theorem exists_homog : ∃ (c : Bool) (H : Set V), #H = ℵ_ ω ∧ Homog S.f c H := by
  obtain ⟨m, δ, hm, hδ⟩ := ramsey_nat S.g
  refine ⟨δ, ⋃ p, S.part δ (m p), ?_, ?_⟩
  · have hdisj' : Pairwise (Disjoint on fun p => S.part δ (m p)) := by
      intro p q hpq
      exact Set.disjoint_of_subset (S.part_subset_Bu δ (m p)) (S.part_subset_Bu δ (m q))
        ((S.hdisj _ _ (hm.injective.ne hpq)).mono (S.Bu_subset_A _) (S.Bu_subset_A _))
    rw [mk_iUnion_nat_eq_sum _ hdisj']
    simp only [S.mk_part]
    exact sum_aleph_eq_aleph_omega (fun p => S.n (m p))
      (fun N => (hm.id_le N).trans (S.hn.id_le _))
  · intro x hx y hy hxy
    obtain ⟨p, hxp⟩ := Set.mem_iUnion.1 hx
    obtain ⟨q, hyq⟩ := Set.mem_iUnion.1 hy
    rcases lt_trichotomy p q with h | rfl | h
    · rw [S.cross (hm h) (S.part_subset_Bu _ _ hxp) (S.part_subset_Bu _ _ hyq)]
      exact hδ p q h
    · exact S.part_homog δ (m p) x hxp y hyq hxy
    · rw [S.hf, S.cross (hm h) (S.part_subset_Bu _ _ hyq) (S.part_subset_Bu _ _ hxp)]
      exact hδ q p h

end Ctx

/-! ### The core theorem -/

/-- The core theorem: for a symmetric pair colouring of a set of size `Σ_k 2^{ℵ_{n_k}}`, there
is a homogeneous set of size `ℵ_ω`. -/
theorem core {V : Type u} (f : V → V → Bool) (hf : ∀ x y, f x y = f y x)
    (n : ℕ → ℕ) (hn : StrictMono n)
    (hpow : StrictMono fun k => (2 : Cardinal.{u}) ^ ℵ_ (n k))
    (h0 : ℵ_ ω < (2 : Cardinal.{u}) ^ ℵ_ (n 0))
    (hV : #V = Cardinal.sum fun k => (2 : Cardinal.{u}) ^ ℵ_ (n k)) :
    ∃ (c : Bool) (H : Set V), #H = ℵ_ ω ∧ Homog f c H := by
  by_contra hno
  have hsum : #V = #(Σ k : ℕ, (Order.succ ((2 : Cardinal.{u}) ^ ℵ_ (n k))).out) := by
    rw [hV]
    exact sum_eq_of_interlaced _ _ (fun k => Order.le_succ _)
      (fun k => Order.succ_le_of_lt (hpow (Nat.lt_succ_self k)))
  obtain ⟨e⟩ := Cardinal.eq.1 hsum
  let A : ℕ → Set V := fun k => e.symm '' Set.range (Sigma.mk k)
  have hA : ∀ k, #(A k) = Order.succ ((2 : Cardinal.{u}) ^ ℵ_ (n k)) := by
    intro k
    simp only [A]
    rw [mk_image_eq e.symm.injective, mk_range_eq _ sigma_mk_injective, mk_out]
  have hdisj : ∀ i j, i ≠ j → Disjoint (A i) (A j) := by
    intro i j hij
    simp only [A]
    rw [Set.disjoint_image_iff e.symm.injective]
    rw [Set.disjoint_left]
    rintro _ ⟨a, rfl⟩ ⟨b, hb⟩
    exact hij (Sigma.mk.inj_iff.1 hb).1.symm
  have hno' : ∀ (c : Bool) (H : Set V), Homog f c H → #H ≠ ℵ_ ω :=
    fun c H hH hc => hno ⟨c, H, hc, hH⟩
  let S : Ctx V := ⟨f, hf, n, hn, hpow, h0, A, hA, hdisj, hno'⟩
  obtain ⟨c, H, h1, h2⟩ := S.exists_homog
  exact hno ⟨c, H, h1, h2⟩

end Erdos1219
