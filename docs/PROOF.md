# Erdős problem #1219 — the proof being formalized

Source: S. Shelah, *Notes on partition calculus*, Infinite and finite sets
(Keszthely 1973), Colloq. Math. Soc. János Bolyai 10, North-Holland 1975,
pp. 1257–1276 ([Sh:40], https://shelah.logic.at/files/95045/40.pdf), §1:
Canonization Lemma 1.1, Theorem 1.2, Corollary 1.3.

## Statement (erdosproblems.com/1219)

Let (n_k) be an increasing sequence of integers such that 2^{ℵ_{n_k}} is
strictly increasing and 2^{ℵ_{n_0}} > ℵ_ω. Then Σ_k 2^{ℵ_{n_k}} → (ℵ_ω)²
(two colours).

## Notation

* μ(k) := ℵ_{n_k}. Then ℵ₀ ≤ μ(k) ≤ μ(k+1), and 2^{μ(k)} < 2^{μ(k+1)}.
* λ_k := (2^{μ(k)})⁺ (successor cardinal). λ_k is regular, 2^{μ(k)} < λ_k ≤ 2^{μ(k+1)},
  and λ_k > ℵ_ω because 2^{μ(k)} ≥ 2^{μ(0)} > ℵ_ω.
* χ := Σ_k 2^{μ(k)} = sup_k 2^{μ(k)} = sup_k λ_k = Σ_k λ_k.
* A colouring is a symmetric f : V × V → 2 on a set V with |V| = χ; only pairs of
  distinct points matter. H ⊆ V is c-homogeneous if f(x,y) = c for all distinct x, y ∈ H.
* For x ∈ V and a set B, the *type* of x over B is the function b ↦ f(x,b) on B.

## Tool 1: Ramsey for ω

For every g : ℕ × ℕ → 2 there are an infinite I ⊆ ℕ and δ with g(i,j) = δ for all
i < j in I. (Proof with a non-principal ultrafilter U on ℕ: let c(i) := the δ such
that {j > i : g(i,j) = δ} ∈ U; some δ has {i : c(i) = δ} ∈ U; choose
i_0 < i_1 < ... inside that set with g(i_p, i_q) = δ, which is possible because at
each step the admissible set is a finite intersection of members of U.)

## Tool 2: unbalanced Erdős–Rado, (2^μ)⁺ → ((2^μ)⁺, μ⁺)²

Let θ := (2^μ)⁺, f a colouring of θ (identified with the ordinals below θ).
Then either there is a 1-homogeneous set of size μ⁺, or a 0-homogeneous set of size θ.

Proof. For α < θ put E_α := {γ < α : f(γ,α) = 1}, and for Z ⊆ θ put
D_Z := {γ : f(z,γ) = 1 for all z ∈ Z}. Let S := {α < θ : cf α = μ⁺}
(equivalently: every subset of α of size ≤ μ is bounded in α).
Call α ∈ S *good* if for every 1-homogeneous Z ⊆ E_α with |Z| ≤ μ there is
γ ∈ E_α ∩ D_Z with γ > sup Z.

* If some α is good, build Z_ξ (ξ < μ⁺), increasing, 1-homogeneous, |Z_ξ| ≤ μ,
  Z_ξ ⊆ E_α: Z_0 = ∅, Z_{ξ+1} = Z_ξ ∪ {γ_ξ} with γ_ξ ∈ E_α ∩ D_{Z_ξ}, γ_ξ > sup Z_ξ,
  unions at limits. The γ_ξ are strictly increasing, so ∪ Z_ξ is 1-homogeneous of
  size μ⁺.
* Otherwise every α ∈ S is bad: there is a 1-homogeneous Z_α ⊆ E_α, |Z_α| ≤ μ, such
  that E_α ∩ D_{Z_α} ⊆ sup Z_α + 1 =: δ_α < α (bounded since |Z_α| ≤ μ < cf α).
  Fodor (or the elementary "closure point" argument below): there is δ_0 such that
  F := {α ∈ S : δ_α = δ_0} has size θ. Since |[δ_0]^{≤μ}| ≤ (2^μ)^μ = 2^μ < θ,
  some Z has F_Z := {α ∈ F : Z_α = Z} of size θ. For α < α' in F_Z with α > δ_0:
  Z ⊆ E_α gives α ∈ D_Z, and α ≥ δ_0, so α ∉ E_{α'} (as E_{α'} ∩ D_Z ⊆ δ_0), i.e.
  f(α,α') = 0. So F_Z \ (δ_0+1) is 0-homogeneous of size θ.

  Closure-point argument replacing Fodor: if every fibre {α ∈ S : δ_α = δ} had size
  < θ, let g(δ) := sup of that fibre + 1 < θ, let β_0 < β_1 < ... (ξ < μ⁺) be
  increasing with β_{ξ+1} > g(δ) for all δ ≤ β_ξ, α := sup β_ξ; then cf α = μ⁺, so
  α ∈ S, δ_α < α gives δ_α < β_ξ for some ξ and then α ≤ g(δ_α) < β_{ξ+1} < α.

By symmetry (swap colours) also: either a 0-homogeneous set of size μ⁺ or a
1-homogeneous set of size θ.

## Tool 3: the canonization (Shelah 1.1 specialized) and the theorem (Shelah 1.2)

Write V = ⊔_k A_k with |A_k| = λ_k (possible since Σ_k λ_k = χ). If some A_k contains a
homogeneous set of size ≥ ℵ_ω we are done. Otherwise, by Tool 2 (both versions) applied
inside any C ⊆ A_k with |C| = λ_k: C contains no homogeneous set of size λ_k (> ℵ_ω), so C
contains a 0-homogeneous set and a 1-homogeneous set, each of size μ(k)⁺ ≥ μ(k).

Guides. For k ∈ ℕ let U_k := ∪_{i<k} A_i (|U_k| ≤ 2^{μ(k)}). For a ∈ A_k and B ⊆ U_k let
cl(a,B) := {a' ∈ A_k : f(a',b) = f(a,b) for all b ∈ B}. Let
C_k := {a ∈ A_k : ∃ B ⊆ U_k, |B| ≤ μ(k), |cl(a,B)| < λ_k}.
Counting: the number of B's is ≤ (2^{μ(k)})^{μ(k)} = 2^{μ(k)}; for a fixed B the sets
cl(a,B) are the fibres of a ↦ (type of a over B), at most 2^{|B|} ≤ 2^{μ(k)} of them, and
the union of the small fibres has size < λ_k (λ_k regular). Hence |C_k| < λ_k and we may
pick a guide a*_k ∈ A_k \ C_k.

Blocks. Inductively on k choose B_k ⊆ A_k with |B_k| ≤ μ(k) (in fact B_k = B_{k,0} ∪ B_{k,1},
|B_{k,c}| = μ(k), B_{k,c} c-homogeneous):
1. B¹_k := cl(a*_k, ∪_{i<k} B_i) has size λ_k (the set ∪_{i<k} B_i is an admissible B, and
   a*_k ∉ C_k).
2. The map a ↦ (i ↦ f(a, a*_i)) from B¹_k to (ℕ → 2) has ≤ 2^{ℵ₀} ≤ 2^{μ(k)} < λ_k values, so
   some fibre B²_k ⊆ B¹_k has size λ_k.
3. Inside B²_k choose B_{k,0} (0-homogeneous) and B_{k,1} (1-homogeneous) of size μ(k), and
   put B_k := B_{k,0} ∪ B_{k,1}.

Canonicity. For i < j, a, a' ∈ B_i, b ∈ B_j:
f(a,b) = f(a,a*_j)   (b ∈ B¹_j and a ∈ ∪_{i'<j} B_{i'})
       = f(a',a*_j)  (a, a' ∈ B²_i)
       = f(a',b).
So g(i,j) := f(a,b) is well defined (independent of a ∈ B_i, b ∈ B_j).

Finish. By Tool 1 there are an infinite I ⊆ ℕ and δ with g(i,j) = δ for i < j in I.
H := ∪_{k∈I} B_{k,δ} is δ-homogeneous (inside a block by choice of B_{k,δ}, across blocks by
canonicity), and |H| = Σ_{k∈I} μ(k) = sup_{k∈I} ℵ_{n_k} = ℵ_ω because (n_k) is strictly
increasing and I is infinite.

## Cardinal arithmetic used

* λ_k = succ(2^{μ(k)}) is regular; λ_k ≤ 2^{μ(k+1)}; sup λ_k = sup 2^{μ(k)} = χ; Σ λ_k = χ.
* (2^μ)^μ = 2^μ; |U_k|^{μ(k)} ≤ 2^{μ(k)}; #(B → 2) = 2^{|B|}; 2^{ℵ₀} ≤ 2^{μ(k)}.
* A union of < λ sets each of size < λ has size < λ for λ regular (`Cardinal.sum_lt_of_isRegular`).
* A subset of (μ⁺).ord of size ≤ μ is bounded (`Cardinal.isRegular_succ`, `Ordinal.iSup_lt_ord_lift_of_isRegular`).
* ℵ_ω = sup_n ℵ_n; a countable sum of cardinals with unbounded terms below ℵ_ω is ℵ_ω.
