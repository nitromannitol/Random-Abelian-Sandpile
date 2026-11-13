import RandomSandpile.Defs.Mu
import RandomSandpile.Draft.Section5

/-!
# The discrete concave envelope

Shared infrastructure on the concave envelope
`Γ_w(x) = inf_{p ∈ ℝ^d} max_{y ∈ Ā} (w(y) + p · (x - y))` (`concaveEnvelopeOn A w`) of a function
`w : ℤ^d → ℝ` over the discrete closure `Ā` of a finite set `A ⊂ ℤ^d`.

The results are first proved for the envelope `concaveEnvelopeOver S w` over an arbitrary finite
set of sites `S` (so that `concaveEnvelopeOn A w = concaveEnvelopeOver (dClosure A) w`), writing
`conv S` for `convexHull ℝ (toE '' S)`:

* `concaveOn_concaveEnvelopeOver`: `Γ_w` is concave on `conv S`;
* `le_concaveEnvelopeOver`: `Γ_w ≥ w` on `S`;
* `isLUB_concaveEnvelopeOver`: on `conv S`, `Γ_w(x)` is the supremum of `∑ λ_i w(x_i)` over all
  convex combinations `x = ∑ λ_i x_i` of points `x_i ∈ S` (the dual description of the envelope; the
  proof separates a point from the compact convex hull of the graph of `w` in `ℝ^d × ℝ`);
* `concaveEnvelopeOver_le_of_concaveOn`: `Γ_w` is the least concave function on `conv S` lying above
  `w` on `S`.

For `A` finite (`concaveEnvelopeOn`):

* `concaveEnvelopeOn_eq_iff_supGrad_nonempty`: for `x ∈ A`, `Γ_w(x) = w(x)` iff the supergradient
  set `∂⁺(w, x, A)` is nonempty (the contact set characterization);
* `supGrad_eq_supGradR_concaveEnvelopeOn`: at a contact point `x ∈ Ā`,
  `∂⁺(w, x, A) = ∂⁺(Γ_w, x)` with the supergradient of `Γ_w` tested on `conv Ā`.

Wrappers for the cube (`concaveEnvelope w n` over `Q̄_n`, hull `cubeHullClosure d n`):
`concaveOn_concaveEnvelope`, `le_concaveEnvelope`, `concaveEnvelope_le_of_concaveOn`,
`concaveEnvelope_eq_iff_supGrad_nonempty`, `supGrad_eq_supGradR_concaveEnvelope`.

The Carathéodory representation (Proposition 5.1):

* `isLUB_concaveEnvelopeOver_fin`: the supremum may be taken over combinations of `d + 1` points
  (an exchange argument on the linear dependences of the vectors `(x_i, 1) ∈ ℝ^d × ℝ`);
* `concaveEnvelopeOver_eq_of_eq_sum`: if `Γ_w(x) = ∑ λ_i w(x_i)` then `Γ_w(x_i) = w(x_i)` for
  `λ_i > 0`;
* `exists_affine_of_concaveEnvelopeOver_eq_sum`: and `Γ_w` is affine on `conv {x_i : λ_i > 0}`;
* `concaveEnvelopeRep : ConcaveEnvelopeRepStmt`.

The functions `affineMajorant S w p` (the least affine function of slope `p` lying above `w` on
`S`) are the objects over which the infimum defining `Γ_w` is taken.
-/

open Filter Topology LatticeProb

namespace RandomSandpile

variable {d : ℕ}

section General

variable (S : Set (Site d)) (w : Site d → ℝ)

/-- The least affine function of slope `p` lying above `w` on `S`, evaluated at `x`:
`max_{y ∈ S} (w(y) + p · (x - y))`. -/
noncomputable def affineMajorant (p x : Rd d) : ℝ :=
  ⨆ y : S, (w y + inner ℝ p (x - toE (y : Site d)))

/-- The concave envelope of `w` over the set of sites `S` (no discrete closure is taken):
`inf_{p ∈ ℝ^d} max_{y ∈ S} (w(y) + p · (x - y))`. With `S = Ā` this is `concaveEnvelopeOn A w`. -/
noncomputable def concaveEnvelopeOver (x : Rd d) : ℝ :=
  ⨅ p : Rd d, affineMajorant S w p x

/-- The values `∑ λ_i w(x_i)` of the convex combinations `x = ∑ λ_i x_i` of points `x_i ∈ S`,
indexed by an arbitrary finite type. -/
def convexCombValues (x : Rd d) : Set ℝ :=
  {t | ∃ (ι : Type) (_ : Fintype ι) (lam : ι → ℝ) (z : ι → Site d), (∀ i, z i ∈ S) ∧
    (∀ i, 0 ≤ lam i) ∧ ∑ i, lam i = 1 ∧ ∑ i, lam i • toE (z i) = x ∧ t = ∑ i, lam i * w (z i)}

end General

theorem concaveEnvelopeOn_eq_concaveEnvelopeOver (A : Set (Site d)) (w : Site d → ℝ) :
    concaveEnvelopeOn A w = concaveEnvelopeOver (dClosure A) w := rfl

variable {S : Set (Site d)} {w : Site d → ℝ}

theorem bddAbove_range_affine (hS : S.Finite) (p x : Rd d) :
    BddAbove (Set.range fun y : S => w y + inner ℝ p (x - toE (y : Site d))) := by
  have := hS.to_subtype
  exact (Set.finite_range _).bddAbove

theorem le_affineMajorant (hS : S.Finite) (p x : Rd d) {y : Site d} (hy : y ∈ S) :
    w y + inner ℝ p (x - toE y) ≤ affineMajorant S w p x :=
  le_ciSup (f := fun y : S => w y + inner ℝ p (x - toE (y : Site d)))
    (bddAbove_range_affine hS p x) ⟨y, hy⟩

theorem affineMajorant_le (hne : S.Nonempty) {p x : Rd d} {c : ℝ}
    (h : ∀ y ∈ S, w y + inner ℝ p (x - toE y) ≤ c) : affineMajorant S w p x ≤ c := by
  have := hne.to_subtype
  exact ciSup_le fun y => h y y.2

/-- `affineMajorant S w p` is affine of slope `p`. -/
theorem affineMajorant_eq_add (hS : S.Finite) (hne : S.Nonempty) (p x z : Rd d) :
    affineMajorant S w p x = inner ℝ p (x - z) + affineMajorant S w p z := by
  have e : ∀ y : Site d, inner ℝ p (x - toE y) = inner ℝ p (x - z) + inner ℝ p (z - toE y) := by
    intro y
    rw [← inner_add_right]
    congr 1
    abel
  apply le_antisymm
  · refine affineMajorant_le hne fun y hy => ?_
    have := le_affineMajorant (w := w) hS p z hy
    rw [e y]
    linarith
  · rw [← le_sub_iff_add_le']
    refine affineMajorant_le hne fun y hy => ?_
    have := le_affineMajorant (w := w) hS p x hy
    rw [e y] at this
    linarith

/-- Every convex combination `∑ λ_i w(x_i)` with `∑ λ_i x_i = x` lies below
`affineMajorant S w p x`. -/
theorem sum_le_affineMajorant (hS : S.Finite) (p : Rd d) {ι : Type*} [Fintype ι] {lam : ι → ℝ}
    {z : ι → Site d} (hz : ∀ i, z i ∈ S) (h0 : ∀ i, 0 ≤ lam i) (h1 : ∑ i, lam i = 1) {x : Rd d}
    (hx : ∑ i, lam i • toE (z i) = x) : ∑ i, lam i * w (z i) ≤ affineMajorant S w p x := by
  have key : ∑ i, lam i * inner ℝ p (x - toE (z i)) = 0 := by
    have hv : ∑ i, lam i • (x - toE (z i)) = 0 := by
      simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, h1, one_smul, hx, sub_self]
    have : ∑ i, lam i * inner ℝ p (x - toE (z i)) = inner ℝ p (∑ i, lam i • (x - toE (z i))) := by
      rw [inner_sum]
      simp only [real_inner_smul_right]
    rw [this, hv, inner_zero_right]
  calc ∑ i, lam i * w (z i) = ∑ i, lam i * (w (z i) + inner ℝ p (x - toE (z i))) := by
        simp only [mul_add, Finset.sum_add_distrib, key, add_zero]
    _ ≤ ∑ i, lam i * affineMajorant S w p x :=
        Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left (le_affineMajorant hS p x (hz i)) (h0 i)
    _ = affineMajorant S w p x := by rw [← Finset.sum_mul, h1, one_mul]

/-- A point of `conv S` is a convex combination of points of `S`. -/
theorem exists_comb_of_mem_convexHull {x : Rd d} (hx : x ∈ convexHull ℝ (toE '' S)) :
    ∃ (ι : Type) (_ : Fintype ι) (lam : ι → ℝ) (z : ι → Site d), (∀ i, z i ∈ S) ∧
      (∀ i, 0 ≤ lam i) ∧ ∑ i, lam i = 1 ∧ ∑ i, lam i • toE (z i) = x := by
  obtain ⟨ι, hι, lam, v, h0, h1, hv, hx⟩ := mem_convexHull_iff_exists_fintype.1 hx
  choose z hzS hz using hv
  refine ⟨ι, hι, lam, z, hzS, h0, h1, ?_⟩
  simpa only [hz] using hx

theorem nonempty_of_mem_convexHull {x : Rd d} (hx : x ∈ convexHull ℝ (toE '' S)) :
    S.Nonempty :=
  Set.image_nonempty.1 (convexHull_nonempty_iff.1 ⟨x, hx⟩)

theorem bddBelow_range_affineMajorant (hS : S.Finite) {x : Rd d}
    (hx : x ∈ convexHull ℝ (toE '' S)) : BddBelow (Set.range fun p => affineMajorant S w p x) := by
  obtain ⟨ι, _, lam, z, hz, h0, h1, hxz⟩ := exists_comb_of_mem_convexHull hx
  exact ⟨∑ i, lam i * w (z i), by
    rintro _ ⟨p, rfl⟩
    exact sum_le_affineMajorant hS p hz h0 h1 hxz⟩

theorem concaveEnvelopeOver_le_affineMajorant (hS : S.Finite) {x : Rd d}
    (hx : x ∈ convexHull ℝ (toE '' S)) (p : Rd d) :
    concaveEnvelopeOver S w x ≤ affineMajorant S w p x :=
  ciInf_le (bddBelow_range_affineMajorant hS hx) p

/-- `Γ_w` lies above every convex combination `∑ λ_i w(x_i)` with `∑ λ_i x_i = x`. -/
theorem sum_le_concaveEnvelopeOver (hS : S.Finite) {ι : Type*} [Fintype ι] {lam : ι → ℝ}
    {z : ι → Site d} (hz : ∀ i, z i ∈ S) (h0 : ∀ i, 0 ≤ lam i) (h1 : ∑ i, lam i = 1) {x : Rd d}
    (hx : ∑ i, lam i • toE (z i) = x) : ∑ i, lam i * w (z i) ≤ concaveEnvelopeOver S w x :=
  le_ciInf fun p => sum_le_affineMajorant hS p hz h0 h1 hx

/-- `Γ_w ≥ w` on `S`. -/
theorem le_concaveEnvelopeOver (hS : S.Finite) {y : Site d} (hy : y ∈ S) :
    w y ≤ concaveEnvelopeOver S w (toE y) := by
  have := sum_le_concaveEnvelopeOver (w := w) hS (ι := Unit) (lam := fun _ => 1)
    (z := fun _ => y) (fun _ => hy) (fun _ => zero_le_one) (by simp) (x := toE y) (by simp)
  simpa using this

/-- `Γ_w` is concave on `conv S`. -/
theorem concaveOn_concaveEnvelopeOver (hS : S.Finite) :
    ConcaveOn ℝ (convexHull ℝ (toE '' S)) (concaveEnvelopeOver S w) := by
  refine ⟨convex_convexHull ℝ _, fun x hx y hy a b ha hb hab => ?_⟩
  have hne := nonempty_of_mem_convexHull hx
  refine le_ciInf fun p => ?_
  set z := a • x + b • y
  have h1 := concaveEnvelopeOver_le_affineMajorant (w := w) hS hx p
  have h2 := concaveEnvelopeOver_le_affineMajorant (w := w) hS hy p
  have e1 := affineMajorant_eq_add (w := w) hS hne p x z
  have e2 := affineMajorant_eq_add (w := w) hS hne p y z
  have e3 : a * inner ℝ p (x - z) + b * inner ℝ p (y - z) = 0 := by
    rw [← real_inner_smul_right, ← real_inner_smul_right, ← inner_add_right]
    have : a • (x - z) + b • (y - z) = 0 := by
      obtain rfl : b = 1 - a := by linarith
      simp only [z]
      module
    rw [this, inner_zero_right]
  simp only [smul_eq_mul]
  calc a * concaveEnvelopeOver S w x + b * concaveEnvelopeOver S w y
      ≤ a * affineMajorant S w p x + b * affineMajorant S w p y :=
        add_le_add (mul_le_mul_of_nonneg_left h1 ha) (mul_le_mul_of_nonneg_left h2 hb)
    _ = affineMajorant S w p z := by
        rw [e1, e2]
        linear_combination e3 + affineMajorant S w p z * hab

/-- The key duality step: on `conv S`, `Γ_w(x)` lies below every upper bound of the values of the
convex combinations of `w` at `x`. Proof: if `t < Γ_w(x)`, separate `(x, t')`, `t < t' < Γ_w(x)`,
from the compact convex hull of the graph `{(y, w(y)) : y ∈ S}` in `ℝ^d × ℝ`; the separating
functional has a nonzero vertical component and yields a slope `p` with `max_S (w + p · (x - ·))
≤ t'`. -/
theorem concaveEnvelopeOver_le_of_mem_upperBounds (hS : S.Finite) {x : Rd d}
    (hx : x ∈ convexHull ℝ (toE '' S)) {t : ℝ} (ht : t ∈ upperBounds (convexCombValues S w x)) :
    concaveEnvelopeOver S w x ≤ t := by
  by_contra hlt
  rw [not_le] at hlt
  set t' := (t + concaveEnvelopeOver S w x) / 2 with ht'
  have htt' : t < t' := by rw [ht']; linarith
  have ht'Γ : t' < concaveEnvelopeOver S w x := by rw [ht']; linarith
  have hne := nonempty_of_mem_convexHull hx
  set Q : Set (Rd d × ℝ) := (fun y : Site d => (toE y, w y)) '' S with hQ
  have hQfin : Q.Finite := hS.image _
  -- `(x, t')` lies outside the convex hull of the graph of `w` over `S`
  have hq : ((x, t') : Rd d × ℝ) ∉ convexHull ℝ Q := by
    intro hq
    obtain ⟨ι, _, μ, v, hμ0, hμ1, hvQ, hv⟩ := mem_convexHull_iff_exists_fintype.1 hq
    choose z hzS hzv using hvQ
    have h1 : ∑ i, μ i • toE (z i) = x := by
      have := congrArg Prod.fst hv
      simpa [Prod.fst_sum, ← hzv] using this
    have h2 : ∑ i, μ i * w (z i) = t' := by
      have := congrArg Prod.snd hv
      simpa [Prod.snd_sum, ← hzv] using this
    have := ht ⟨ι, inferInstance, μ, z, hzS, hμ0, hμ1, h1, rfl⟩
    linarith
  obtain ⟨f, u, hfq, hfK⟩ := geometric_hahn_banach_point_closed (convex_convexHull ℝ Q)
    (hQfin.isClosed_convexHull ℝ) hq
  set fa : StrongDual ℝ (Rd d) := f.comp (ContinuousLinearMap.inl ℝ (Rd d) ℝ) with hfa
  set α : ℝ := f ((0 : Rd d), (1 : ℝ)) with hα
  have hf : ∀ (v : Rd d) (τ : ℝ), f (v, τ) = fa v + τ * α := by
    intro v τ
    have : ((v, τ) : Rd d × ℝ) = (v, 0) + τ • ((0 : Rd d), (1 : ℝ)) := by
      ext <;> simp
    rw [this, map_add, map_smul, smul_eq_mul]
    simp [hfa, hα]
  have hgraph : ∀ y ∈ S, ((toE y, w y) : Rd d × ℝ) ∈ convexHull ℝ Q :=
    fun y hy => subset_convexHull ℝ Q ⟨y, hy, rfl⟩
  -- the vertical component of the separating functional is negative
  have hαneg : α < 0 := by
    obtain ⟨ι, _, lam, z, hz, h0, h1, hxz⟩ := exists_comb_of_mem_convexHull hx
    have hmem : ((x, ∑ i, lam i * w (z i)) : Rd d × ℝ) ∈ convexHull ℝ Q := by
      have hsum : ∑ i, lam i • ((toE (z i), w (z i)) : Rd d × ℝ) = (x, ∑ i, lam i * w (z i)) := by
        refine Prod.ext ?_ ?_
        · simpa [Prod.fst_sum] using hxz
        · simp [Prod.snd_sum]
      rw [← hsum]
      exact (convex_convexHull ℝ Q).sum_mem (fun i _ => h0 i) h1 fun i _ => hgraph _ (hz i)
    have hle := ht ⟨ι, inferInstance, lam, z, hz, h0, h1, hxz, rfl⟩
    have h3 := hfK _ hmem
    rw [hf] at h3 hfq
    by_contra hα0
    rw [not_lt] at hα0
    nlinarith
  -- the slope `p` read off from the horizontal component
  set p : Rd d := (-α)⁻¹ • (InnerProductSpace.toDual ℝ (Rd d)).symm fa with hp
  have hpv : ∀ v : Rd d, inner ℝ p v = (-α)⁻¹ * fa v := by
    intro v
    rw [hp, real_inner_smul_left, InnerProductSpace.toDual_symm_apply]
  have hmaj : affineMajorant S w p x ≤ t' := by
    refine affineMajorant_le hne fun y hy => ?_
    have h3 := hfK _ (hgraph y hy)
    rw [hf] at h3 hfq
    have hβ : 0 < -α := neg_pos.2 hαneg
    rw [hpv, map_sub]
    have : (-α)⁻¹ * (fa x - fa (toE y)) ≤ t' - w y := by
      rw [inv_mul_le_iff₀ hβ]
      nlinarith
    linarith
  have := concaveEnvelopeOver_le_affineMajorant (w := w) hS hx p
  linarith

/-- On `conv S`, `Γ_w(x)` is the supremum of the values `∑ λ_i w(x_i)` over all convex
combinations `x = ∑ λ_i x_i` of points `x_i ∈ S` (without the bound `d + 1` on the
number of points). -/
theorem isLUB_concaveEnvelopeOver (hS : S.Finite) {x : Rd d}
    (hx : x ∈ convexHull ℝ (toE '' S)) :
    IsLUB (convexCombValues S w x) (concaveEnvelopeOver S w x) := by
  refine ⟨?_, fun t ht => concaveEnvelopeOver_le_of_mem_upperBounds hS hx ht⟩
  rintro _ ⟨ι, _, lam, z, hz, h0, h1, hxz, rfl⟩
  exact sum_le_concaveEnvelopeOver hS hz h0 h1 hxz

/-- `Γ_w` is the least concave function on `conv S` lying above `w` on `S`. -/
theorem concaveEnvelopeOver_le_of_concaveOn (hS : S.Finite) {f : Rd d → ℝ}
    (hf : ConcaveOn ℝ (convexHull ℝ (toE '' S)) f) (hfw : ∀ y ∈ S, w y ≤ f (toE y)) {x : Rd d}
    (hx : x ∈ convexHull ℝ (toE '' S)) : concaveEnvelopeOver S w x ≤ f x := by
  refine (isLUB_concaveEnvelopeOver hS hx).2 ?_
  rintro _ ⟨ι, _, lam, z, hz, h0, h1, rfl, rfl⟩
  calc ∑ i, lam i * w (z i) ≤ ∑ i, lam i • f (toE (z i)) :=
        Finset.sum_le_sum fun i _ => by
          rw [smul_eq_mul]
          exact mul_le_mul_of_nonneg_left (hfw _ (hz i)) (h0 i)
    _ ≤ f (∑ i, lam i • toE (z i)) :=
        hf.le_map_sum (fun i _ => h0 i) h1 fun i _ => subset_convexHull ℝ _ ⟨z i, hz i, rfl⟩

/-! ### The envelope over the discrete closure of a finite set -/

section Closure

variable {A : Set (Site d)}

theorem mem_dClosure_of_mem {x : Site d} (hx : x ∈ A) : x ∈ dClosure A := by
  rw [dClosure_eq]
  exact Or.inl hx

theorem mem_dClosure_of_adj {x y : Site d} (hx : x ∈ A) (hxy : Adj y x) : y ∈ dClosure A := by
  rw [dClosure_eq]
  by_cases hy : y ∈ A
  · exact Or.inl hy
  · exact Or.inr (mem_bdry.2 ⟨hy, x, hx, hxy⟩)

theorem adj_add_unit (x : Site d) (i : Fin d) : Adj (x + unit i) x := ⟨i, Or.inr rfl⟩

theorem adj_sub_unit (x : Site d) (i : Fin d) : Adj (x - unit i) x :=
  ⟨i, Or.inl (sub_add_cancel x (unit i)).symm⟩

/-- The discrete closure of a finite set is finite. -/
theorem dClosure_finite (hA : A.Finite) : (dClosure A).Finite := by
  rw [dClosure_eq]
  refine hA.union ((hA.biUnion fun x _ => (nbrFinset x).finite_toSet).subset ?_)
  intro y hy
  obtain ⟨-, x, hx, i, h | h⟩ := mem_bdry.1 hy
  · refine Set.mem_biUnion hx ?_
    subst h
    exact Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, by simp⟩)
  · refine Set.mem_biUnion hx ?_
    subst h
    exact Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, by simp⟩)

/-- The discrete cube `Q_r` is finite. -/
theorem cubeZ0_finite (r : ℝ) : (cubeZ0 r : Set (Site d)).Finite := by
  refine (Set.Finite.pi (t := fun _ : Fin d => Set.Icc (-⌈r⌉) ⌈r⌉)
    fun _ => Set.finite_Icc _ _).subset ?_
  intro y hy i _
  have h := hy i
  simp only [Pi.zero_apply, sub_zero] at h
  have hr : r ≤ (⌈r⌉ : ℝ) := Int.le_ceil r
  rw [abs_lt] at h
  constructor
  · have : ((-⌈r⌉ : ℤ) : ℝ) ≤ (y i : ℝ) := by push_cast; linarith
    exact_mod_cast this
  · have : (y i : ℝ) ≤ ((⌈r⌉ : ℤ) : ℝ) := by linarith
    exact_mod_cast this

theorem inner_toE_sub_toE_add_unit (p : Rd d) (x : Site d) (i : Fin d) :
    inner ℝ p (toE x - toE (x + unit i)) = -p i := by
  have : toE x - toE (x + unit i) = -EuclideanSpace.single i (1 : ℝ) := by
    ext j
    by_cases h : j = i
    · subst h
      simp [unit]
    · simp [unit, h]
  rw [this, inner_neg_right, EuclideanSpace.inner_single_right]
  simp

theorem inner_toE_sub_toE_sub_unit (p : Rd d) (x : Site d) (i : Fin d) :
    inner ℝ p (toE x - toE (x - unit i)) = p i := by
  have : toE x - toE (x - unit i) = EuclideanSpace.single i (1 : ℝ) := by
    ext j
    by_cases h : j = i
    · subst h
      simp [unit]
    · simp [unit, h]
  rw [this, EuclideanSpace.inner_single_right]
  simp

theorem toE_mem_convexHull_dClosure {x : Site d} (hx : x ∈ dClosure A) :
    toE x ∈ convexHull ℝ (toE '' dClosure A) :=
  subset_convexHull ℝ _ ⟨x, hx, rfl⟩

/-- `Γ_w` is concave on `conv Ā`. -/
theorem concaveOn_concaveEnvelopeOn (hA : A.Finite) :
    ConcaveOn ℝ (convexHull ℝ (toE '' dClosure A)) (concaveEnvelopeOn A w) :=
  concaveOn_concaveEnvelopeOver (dClosure_finite hA)

/-- `Γ_w ≥ w` on `Ā`. -/
theorem le_concaveEnvelopeOn (hA : A.Finite) {y : Site d} (hy : y ∈ dClosure A) :
    w y ≤ concaveEnvelopeOn A w (toE y) :=
  le_concaveEnvelopeOver (dClosure_finite hA) hy

/-- `Γ_w` is the least concave function on `conv Ā` lying above `w` on `Ā`. -/
theorem concaveEnvelopeOn_le_of_concaveOn (hA : A.Finite) {f : Rd d → ℝ}
    (hf : ConcaveOn ℝ (convexHull ℝ (toE '' dClosure A)) f) (hfw : ∀ y ∈ dClosure A, w y ≤ f (toE y))
    {x : Rd d} (hx : x ∈ convexHull ℝ (toE '' dClosure A)) : concaveEnvelopeOn A w x ≤ f x :=
  concaveEnvelopeOver_le_of_concaveOn (dClosure_finite hA) hf hfw hx

/-- On `conv Ā`, `Γ_w(x)` is the supremum of `∑ λ_i w(x_i)` over the convex combinations
`x = ∑ λ_i x_i` of points of `Ā`. -/
theorem isLUB_concaveEnvelopeOn (hA : A.Finite) {x : Rd d}
    (hx : x ∈ convexHull ℝ (toE '' dClosure A)) :
    IsLUB (convexCombValues (dClosure A) w x) (concaveEnvelopeOn A w x) :=
  isLUB_concaveEnvelopeOver (dClosure_finite hA) hx

/-- For `p ∈ ∂⁺(w, x, A)`, the affine function `w(x) + p · (z - x)` lies above `Γ_w` on
`conv Ā`. -/
theorem concaveEnvelopeOn_le_of_mem_supGrad (hA : A.Finite) {x : Site d} (hx : x ∈ dClosure A)
    {p : Rd d} (hp : p ∈ supGrad w x A) {z : Rd d} (hz : z ∈ convexHull ℝ (toE '' dClosure A)) :
    concaveEnvelopeOn A w z ≤ w x + inner ℝ p (z - toE x) := by
  rw [concaveEnvelopeOn_eq_concaveEnvelopeOver]
  refine (concaveEnvelopeOver_le_affineMajorant (dClosure_finite hA) hz p).trans
    (affineMajorant_le ⟨x, hx⟩ fun y hy => ?_)
  have h1 : w y ≤ w x + inner ℝ p (toE y - toE x) := hp y hy
  have e : inner ℝ p (z - toE y) = inner ℝ p (z - toE x) - inner ℝ p (toE y - toE x) := by
    rw [← inner_sub_right]
    congr 1
    abel
  rw [e]
  linarith

/-- A point `x ∈ Ā` with a nonempty supergradient set `∂⁺(w, x, A)` is a contact point:
`Γ_w(x) = w(x)`. -/
theorem concaveEnvelopeOn_eq_of_mem_supGrad (hA : A.Finite) {x : Site d} (hx : x ∈ dClosure A)
    {p : Rd d} (hp : p ∈ supGrad w x A) : concaveEnvelopeOn A w (toE x) = w x := by
  apply le_antisymm
  · simpa using concaveEnvelopeOn_le_of_mem_supGrad hA hx hp (toE_mem_convexHull_dClosure hx)
  · exact le_concaveEnvelopeOn hA hx

/-- At a contact point `x ∈ A` (`Γ_w(x) = w(x)`), the supergradient set `∂⁺(w, x, A)` is
nonempty. The infimum over slopes defining `Γ_w(x)` is attained: as the `2d` neighbours of `x` lie
in `Ā`, the slopes of near-minimizers are bounded, and a limit of a subsequence is a minimizer. -/
theorem supGrad_nonempty_of_concaveEnvelopeOn_eq (hA : A.Finite) {x : Site d} (hx : x ∈ A)
    (hΓ : concaveEnvelopeOn A w (toE x) = w x) : (supGrad w x A).Nonempty := by
  have hS := dClosure_finite hA
  have hlt : ∀ n : ℕ, ∃ p : Rd d,
      affineMajorant (dClosure A) w p (toE x) < w x + 1 / ((n : ℝ) + 1) := by
    intro n
    refine exists_lt_of_ciInf_lt ?_
    change concaveEnvelopeOn A w (toE x) < _
    rw [hΓ]
    have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  choose P hP using hlt
  have hPi : ∀ n i, |P n i| ≤ max (w x + 1 - w (x - unit i)) (w x + 1 - w (x + unit i)) := by
    intro n i
    have h1n : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have hplus := le_affineMajorant (w := w) hS (P n) (toE x)
      (mem_dClosure_of_adj hx (adj_add_unit x i))
    have hminus := le_affineMajorant (w := w) hS (P n) (toE x)
      (mem_dClosure_of_adj hx (adj_sub_unit x i))
    rw [inner_toE_sub_toE_add_unit] at hplus
    rw [inner_toE_sub_toE_sub_unit] at hminus
    have h := hP n
    have hl := le_max_left (w x + 1 - w (x - unit i)) (w x + 1 - w (x + unit i))
    have hr := le_max_right (w x + 1 - w (x - unit i)) (w x + 1 - w (x + unit i))
    rw [abs_le]
    constructor <;> linarith
  set R : ℝ := ∑ i, (max (w x + 1 - w (x - unit i)) (w x + 1 - w (x + unit i))) ^ 2 + 1 with hR
  have hPn : ∀ n, P n ∈ Metric.closedBall (0 : Rd d) R := by
    intro n
    rw [mem_closedBall_zero_iff]
    have hsq : ‖P n‖ ^ 2 ≤ R - 1 := by
      rw [EuclideanSpace.norm_sq_eq, hR, add_sub_cancel_right]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [Real.norm_eq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hPi n i) 2
    nlinarith [sq_nonneg (‖P n‖ - 1), sq_nonneg ‖P n‖]
  obtain ⟨p, -, φ, hφ, hlim⟩ := tendsto_subseq_of_bounded Metric.isBounded_closedBall hPn
  refine ⟨p, fun y hy => ?_⟩
  have hcont : Tendsto (fun k => w y + inner ℝ ((P ∘ φ) k) (toE x - toE y)) atTop
      (𝓝 (w y + inner ℝ p (toE x - toE y))) :=
    tendsto_const_nhds.add (hlim.inner tendsto_const_nhds)
  have hr : Tendsto (fun k => w x + 1 / ((φ k : ℝ) + 1)) atTop (𝓝 (w x + 0)) :=
    tendsto_const_nhds.add
      ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hφ.tendsto_atTop)
  have hle : w y + inner ℝ p (toE x - toE y) ≤ w x + 0 :=
    le_of_tendsto_of_tendsto' hcont hr fun k =>
      (le_affineMajorant hS (P (φ k)) (toE x) hy).trans (hP (φ k)).le
  have e : inner ℝ p (toE y - toE x) = -inner ℝ p (toE x - toE y) := by
    rw [← inner_neg_right, neg_sub]
  show w y ≤ w x + inner ℝ p (toE y - toE x)
  rw [e]
  linarith

/-- Contact set characterization: for `x ∈ A`, `Γ_w(x) = w(x)` iff `∂⁺(w, x, A) ≠ ∅`. -/
theorem concaveEnvelopeOn_eq_iff_supGrad_nonempty (hA : A.Finite) {x : Site d} (hx : x ∈ A) :
    concaveEnvelopeOn A w (toE x) = w x ↔ (supGrad w x A).Nonempty :=
  ⟨supGrad_nonempty_of_concaveEnvelopeOn_eq hA hx, fun ⟨_, hp⟩ =>
    concaveEnvelopeOn_eq_of_mem_supGrad hA (mem_dClosure_of_mem hx) hp⟩

/-- At a contact point `x ∈ Ā` (`Γ_w(x) = w(x)`), the supergradient set of `w` equals the
supergradient set of `Γ_w`, tested on `conv Ā`: `∂⁺(w, x, A) = ∂⁺(Γ_w, x)`. -/
theorem supGrad_eq_supGradR_concaveEnvelopeOn (hA : A.Finite) {x : Site d}
    (hx : x ∈ dClosure A) (hΓ : concaveEnvelopeOn A w (toE x) = w x) :
    supGrad w x A =
      supGradR (concaveEnvelopeOn A w) (toE x) (convexHull ℝ (toE '' dClosure A)) := by
  ext p
  constructor
  · intro hp z hz
    rw [hΓ]
    exact concaveEnvelopeOn_le_of_mem_supGrad hA hx hp hz
  · intro hp y hy
    have h1 := le_concaveEnvelopeOn (w := w) hA hy
    have h2 := hp (toE y) (toE_mem_convexHull_dClosure hy)
    rw [hΓ] at h2
    exact h1.trans h2

end Closure

/-! ### The envelope `Γ_w` over the cube `Q̄_n` -/

section Cube

variable {n : ℕ}

theorem dClosure_cubeZ0_finite (n : ℕ) : (dClosure (cubeZ0 (n : ℝ)) : Set (Site d)).Finite :=
  dClosure_finite (cubeZ0_finite _)

/-- `Γ_w` is concave on `𝒬̄_n`. -/
theorem concaveOn_concaveEnvelope (w : Site d → ℝ) (n : ℕ) :
    ConcaveOn ℝ (cubeHullClosure d n) (concaveEnvelope w n) :=
  concaveOn_concaveEnvelopeOn (cubeZ0_finite _)

/-- `Γ_w ≥ w` on `Q̄_n`. -/
theorem le_concaveEnvelope {y : Site d} (hy : y ∈ dClosure (cubeZ0 (n : ℝ))) :
    w y ≤ concaveEnvelope w n (toE y) :=
  le_concaveEnvelopeOn (cubeZ0_finite _) hy

/-- `Γ_w` is the least concave function on `𝒬̄_n` lying above `w` on `Q̄_n`. -/
theorem concaveEnvelope_le_of_concaveOn {f : Rd d → ℝ} (hf : ConcaveOn ℝ (cubeHullClosure d n) f)
    (hfw : ∀ y ∈ dClosure (cubeZ0 (n : ℝ)), w y ≤ f (toE y)) {x : Rd d}
    (hx : x ∈ cubeHullClosure d n) : concaveEnvelope w n x ≤ f x :=
  concaveEnvelopeOn_le_of_concaveOn (cubeZ0_finite _) hf hfw hx

/-- Contact set characterization on `Q_n`: `Γ_w(x) = w(x)` iff `∂⁺(w, x, Q_n) ≠ ∅`. -/
theorem concaveEnvelope_eq_iff_supGrad_nonempty {x : Site d} (hx : x ∈ cubeZ0 (n : ℝ)) :
    concaveEnvelope w n (toE x) = w x ↔ (supGrad w x (cubeZ0 (n : ℝ))).Nonempty :=
  concaveEnvelopeOn_eq_iff_supGrad_nonempty (cubeZ0_finite _) hx

/-- At a contact point `x ∈ Q̄_n`, `∂⁺(w, x, Q_n) = ∂⁺(Γ_w, x)`, the supergradient of `Γ_w`
being tested on `𝒬̄_n`. -/
theorem supGrad_eq_supGradR_concaveEnvelope {x : Site d} (hx : x ∈ dClosure (cubeZ0 (n : ℝ)))
    (hΓ : concaveEnvelope w n (toE x) = w x) :
    supGrad w x (cubeZ0 (n : ℝ)) = supGradR (concaveEnvelope w n) (toE x) (cubeHullClosure d n) :=
  supGrad_eq_supGradR_concaveEnvelopeOn (cubeZ0_finite _) hx hΓ

end Cube

/-! ### The Carathéodory representation (Proposition 5.1) -/

section Representation

/-- Exchange step: a convex combination of `m + 1 > d + 1` points of `S` can be replaced by a
convex combination of `m` of these points with the same barycenter and a value of `∑ λ_i w(x_i)`
at least as large. The vectors `(x_i, 1) ∈ ℝ^d × ℝ` are linearly dependent; moving the weights
along a dependence `μ` with `∑ μ_i w(x_i) ≥ 0` until one weight vanishes does not decrease the
value. -/
theorem exists_comb_fin_of_lt {m : ℕ} (hm : d < m) {lam : Fin (m + 1) → ℝ}
    {z : Fin (m + 1) → Site d} (hz : ∀ i, z i ∈ S) (h0 : ∀ i, 0 ≤ lam i) (h1 : ∑ i, lam i = 1) :
    ∃ (lam' : Fin m → ℝ) (z' : Fin m → Site d), (∀ j, z' j ∈ S) ∧ (∀ j, 0 ≤ lam' j) ∧
      ∑ j, lam' j = 1 ∧ ∑ j, lam' j • toE (z' j) = ∑ i, lam i • toE (z i) ∧
      ∑ i, lam i * w (z i) ≤ ∑ j, lam' j * w (z' j) := by
  classical
  have hdep : ¬LinearIndependent ℝ (fun i => ((toE (z i), (1 : ℝ)) : Rd d × ℝ)) := by
    intro hli
    have := hli.fintype_card_le_finrank
    rw [Fintype.card_fin, Module.finrank_prod, finrank_euclideanSpace, Fintype.card_fin,
      Module.finrank_self] at this
    omega
  obtain ⟨g, hg, i₁, hi₁⟩ := Fintype.not_linearIndependent_iff.1 hdep
  have hgx : ∑ i, g i • toE (z i) = 0 := by
    simpa [Prod.fst_sum] using congrArg Prod.fst hg
  have hg1 : ∑ i, g i = 0 := by
    simpa [Prod.snd_sum] using congrArg Prod.snd hg
  obtain ⟨μ, hμx, hμ1, ⟨i₂, hi₂⟩, hμw⟩ : ∃ μ : Fin (m + 1) → ℝ, ∑ i, μ i • toE (z i) = 0 ∧
      ∑ i, μ i = 0 ∧ (∃ i, μ i ≠ 0) ∧ 0 ≤ ∑ i, μ i * w (z i) := by
    rcases le_total 0 (∑ i, g i * w (z i)) with h | h
    · exact ⟨g, hgx, hg1, ⟨i₁, hi₁⟩, h⟩
    · refine ⟨-g, ?_, ?_, ⟨i₁, by simpa using hi₁⟩, ?_⟩
      · simp [neg_smul, Finset.sum_neg_distrib, hgx]
      · simp [Finset.sum_neg_distrib, hg1]
      · simp only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
        linarith
  have hneg : ∃ i, μ i < 0 := by
    by_contra hcon
    simp only [not_exists, not_lt] at hcon
    exact hi₂ ((Finset.sum_eq_zero_iff_of_nonneg fun j _ => hcon j).1 hμ1 i₂ (Finset.mem_univ _))
  obtain ⟨i₀, hi₀N, hmin⟩ := (Finset.univ.filter fun i => μ i < 0).exists_min_image
    (fun i => lam i / -μ i) (let ⟨i, hi⟩ := hneg; ⟨i, by simp [hi]⟩)
  have hi₀ : μ i₀ < 0 := (Finset.mem_filter.1 hi₀N).2
  set t := lam i₀ / -μ i₀ with ht
  have ht0 : 0 ≤ t := div_nonneg (h0 i₀) (neg_nonneg.2 hi₀.le)
  set lam₁ : Fin (m + 1) → ℝ := fun i => lam i + t * μ i with hlam₁
  have hlam₁0 : ∀ i, 0 ≤ lam₁ i := by
    intro i
    by_cases hi : μ i < 0
    · have h := hmin i (Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩)
      rw [le_div_iff₀ (neg_pos.2 hi)] at h
      simp only [hlam₁]
      linarith
    · simp only [hlam₁]
      nlinarith [h0 i, not_lt.1 hi]
  have hlam₁i₀ : lam₁ i₀ = 0 := by
    simp only [hlam₁, ht]
    rw [div_neg, neg_mul, div_mul_cancel₀ _ hi₀.ne]
    ring
  refine ⟨fun j => lam₁ (i₀.succAbove j), fun j => z (i₀.succAbove j), fun j => hz _,
    fun j => hlam₁0 _, ?_, ?_, ?_⟩
  · have h := Fin.sum_univ_succAbove lam₁ i₀
    rw [hlam₁i₀, zero_add] at h
    dsimp only
    rw [← h]
    simp only [hlam₁, Finset.sum_add_distrib, ← Finset.mul_sum, hμ1, h1, mul_zero, add_zero]
  · have h := Fin.sum_univ_succAbove (fun i => lam₁ i • toE (z i)) i₀
    simp only [hlam₁i₀, zero_smul, zero_add] at h
    dsimp only
    rw [← h]
    simp only [hlam₁, add_smul, Finset.sum_add_distrib, mul_smul, ← Finset.smul_sum, hμx,
      smul_zero, add_zero]
  · have h := Fin.sum_univ_succAbove (fun i => lam₁ i * w (z i)) i₀
    simp only [hlam₁i₀, zero_mul, zero_add] at h
    dsimp only
    rw [← h]
    simp only [hlam₁, add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
    nlinarith [mul_nonneg ht0 hμw]

/-- Iterated exchange: a convex combination of points of `S` indexed by `Fin m` can be replaced by
one indexed by `Fin N`, `N ≤ d + 1`, with the same barycenter and a value at least as large. -/
theorem exists_comb_fin_le (m : ℕ) : ∀ (lam : Fin m → ℝ) (z : Fin m → Site d),
    (∀ i, z i ∈ S) → (∀ i, 0 ≤ lam i) → ∑ i, lam i = 1 →
    ∃ (N : ℕ) (lam' : Fin N → ℝ) (z' : Fin N → Site d), N ≤ d + 1 ∧ (∀ j, z' j ∈ S) ∧
      (∀ j, 0 ≤ lam' j) ∧ ∑ j, lam' j = 1 ∧ ∑ j, lam' j • toE (z' j) = ∑ i, lam i • toE (z i) ∧
      ∑ i, lam i * w (z i) ≤ ∑ j, lam' j * w (z' j) := by
  induction m with
  | zero =>
    intro lam z hz h0 h1
    exact ⟨0, lam, z, Nat.zero_le _, hz, h0, h1, rfl, le_rfl⟩
  | succ m ih =>
    intro lam z hz h0 h1
    by_cases hm : m + 1 ≤ d + 1
    · exact ⟨m + 1, lam, z, hm, hz, h0, h1, rfl, le_rfl⟩
    · obtain ⟨lam', z', hz', h0', h1', hx', hw'⟩ :=
        exists_comb_fin_of_lt (w := w) (by omega) hz h0 h1
      obtain ⟨N, lam'', z'', hN, hz'', h0'', h1'', hx'', hw''⟩ := ih lam' z' hz' h0' h1'
      exact ⟨N, lam'', z'', hN, hz'', h0'', h1'', hx''.trans hx', hw'.trans hw''⟩

/-- Padding a convex combination indexed by `Fin N` with zero weights to one indexed by `Fin K`,
`N ≤ K`. -/
theorem exists_comb_fin_pad {N : ℕ} {y₀ : Site d} (hy₀ : y₀ ∈ S) (lam : Fin N → ℝ)
    (z : Fin N → Site d) (hz : ∀ i, z i ∈ S) (h0 : ∀ i, 0 ≤ lam i) (h1 : ∑ i, lam i = 1)
    (K : ℕ) (hK : N ≤ K) :
    ∃ (lam' : Fin K → ℝ) (z' : Fin K → Site d), (∀ j, z' j ∈ S) ∧ (∀ j, 0 ≤ lam' j) ∧
      ∑ j, lam' j = 1 ∧ ∑ j, lam' j • toE (z' j) = ∑ i, lam i • toE (z i) ∧
      ∑ j, lam' j * w (z' j) = ∑ i, lam i * w (z i) := by
  induction K, hK using Nat.le_induction with
  | base => exact ⟨lam, z, hz, h0, h1, rfl, rfl⟩
  | succ K _ ih =>
    obtain ⟨lam', z', hz', h0', h1', hx', hw'⟩ := ih
    refine ⟨Fin.cons 0 lam', Fin.cons y₀ z', fun j => ?_, fun j => ?_, ?_, ?_, ?_⟩
    · cases j using Fin.cases <;> simp [hy₀, hz']
    · cases j using Fin.cases <;> simp [h0']
    · simp [Fin.sum_univ_succ, h1']
    · simp [Fin.sum_univ_succ, hx']
    · simp [Fin.sum_univ_succ, hw']

/-- Every convex combination of points of `S` can be replaced by one with exactly `d + 1` (possibly
repeated, possibly zero-weight) points, with the same barycenter and a value at least as large. -/
theorem exists_comb_fin_succ {ι : Type*} [Fintype ι] {lam : ι → ℝ} {z : ι → Site d}
    (hz : ∀ i, z i ∈ S) (h0 : ∀ i, 0 ≤ lam i) (h1 : ∑ i, lam i = 1) :
    ∃ (lam' : Fin (d + 1) → ℝ) (z' : Fin (d + 1) → Site d), (∀ j, z' j ∈ S) ∧
      (∀ j, 0 ≤ lam' j) ∧ ∑ j, lam' j = 1 ∧
      ∑ j, lam' j • toE (z' j) = ∑ i, lam i • toE (z i) ∧
      ∑ i, lam i * w (z i) ≤ ∑ j, lam' j * w (z' j) := by
  obtain ⟨i₀⟩ : Nonempty ι := by
    rcases isEmpty_or_nonempty ι with h | h
    · simp at h1
    · exact h
  set e := Fintype.equivFin ι
  obtain ⟨N, lam', z', hN, hz', h0', h1', hx', hw'⟩ := exists_comb_fin_le (w := w)
    (Fintype.card ι) (lam ∘ e.symm) (z ∘ e.symm) (fun i => hz _) (fun i => h0 _)
    (by rw [← h1]; exact e.symm.sum_comp lam)
  obtain ⟨lam'', z'', hz'', h0'', h1'', hx'', hw''⟩ :=
    exists_comb_fin_pad (w := w) (hz i₀) lam' z' hz' h0' h1' (d + 1) hN
  refine ⟨lam'', z'', hz'', h0'', h1'', ?_, ?_⟩
  · rw [hx'', hx']
    exact e.symm.sum_comp (fun i => lam i • toE (z i))
  · rw [hw'']
    exact le_trans (e.symm.sum_comp (fun i => lam i * w (z i))).ge hw'

/-- Proposition 5.1, first part: on `conv S`, `Γ_w(x)` is the supremum of
`∑_{i=1}^{d+1} λ_i w(x_i)` over `x_i ∈ S`, `λ_i ∈ [0, 1]`, `∑ λ_i = 1`, `∑ λ_i x_i = x`. -/
theorem isLUB_concaveEnvelopeOver_fin (hS : S.Finite) {x : Rd d}
    (hx : x ∈ convexHull ℝ (toE '' S)) :
    IsLUB {s : ℝ | ∃ (lam : Fin (d + 1) → ℝ) (xs : Fin (d + 1) → Site d),
        (∀ i, xs i ∈ S) ∧ (∀ i, 0 ≤ lam i ∧ lam i ≤ 1) ∧
        ∑ i, lam i = 1 ∧ ∑ i, lam i • toE (xs i) = x ∧ s = ∑ i, lam i * w (xs i)}
      (concaveEnvelopeOver S w x) := by
  refine ⟨?_, fun t ht => concaveEnvelopeOver_le_of_mem_upperBounds hS hx ?_⟩
  · rintro _ ⟨lam, xs, hxs, h01, h1, hxx, rfl⟩
    exact sum_le_concaveEnvelopeOver hS hxs (fun i => (h01 i).1) h1 hxx
  · rintro _ ⟨ι, _, lam, z, hz, h0, h1, hxz, rfl⟩
    obtain ⟨lam', xs, hxs, h0', h1', hx', hw'⟩ := exists_comb_fin_succ (w := w) hz h0 h1
    refine hw'.trans (ht ⟨lam', xs, hxs, fun i => ⟨h0' i, ?_⟩, h1', hx'.trans hxz, rfl⟩)
    rw [← h1']
    exact Finset.single_le_sum (fun j _ => h0' j) (Finset.mem_univ i)

/-- Proposition 5.1, second part, contact points: if
`Γ_w(x) = ∑ λ_i w(x_i)` for a convex combination `x = ∑ λ_i x_i` of points of `S`, then
`Γ_w(x_i) = w(x_i)` for every `i` with `λ_i > 0`. -/
theorem concaveEnvelopeOver_eq_of_eq_sum (hS : S.Finite) {ι : Type*} [Fintype ι] {lam : ι → ℝ}
    {xs : ι → Site d} (hxs : ∀ i, xs i ∈ S) (h0 : ∀ i, 0 ≤ lam i) (h1 : ∑ i, lam i = 1)
    {x : Rd d} (hx : ∑ i, lam i • toE (xs i) = x)
    (hΓ : concaveEnvelopeOver S w x = ∑ i, lam i * w (xs i)) {i : ι} (hi : 0 < lam i) :
    concaveEnvelopeOver S w (toE (xs i)) = w (xs i) := by
  have hJ := (concaveOn_concaveEnvelopeOver (w := w) hS).le_map_sum (t := Finset.univ)
    (fun i _ => h0 i) h1 fun i _ => subset_convexHull ℝ _ ⟨xs i, hxs i, rfl⟩
  rw [hx, hΓ] at hJ
  simp only [smul_eq_mul] at hJ
  have hterm : ∀ j, 0 ≤ lam j * (concaveEnvelopeOver S w (toE (xs j)) - w (xs j)) :=
    fun j => mul_nonneg (h0 j) (sub_nonneg.2 (le_concaveEnvelopeOver hS (hxs j)))
  have hsum0 : ∑ j, lam j * (concaveEnvelopeOver S w (toE (xs j)) - w (xs j)) = 0 := by
    refine le_antisymm ?_ (Finset.sum_nonneg fun j _ => hterm j)
    simp only [mul_sub, Finset.sum_sub_distrib]
    linarith
  have h := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => hterm j).1 hsum0 i (Finset.mem_univ _)
  rcases mul_eq_zero.1 h with h | h
  · exact absurd h hi.ne'
  · linarith

/-- A linear map `V` whose kernel contains that of `T` factors through `T`. -/
theorem exists_linearMap_comp_eq_of_ker_le {U E : Type*} [AddCommGroup U] [Module ℝ U]
    [AddCommGroup E] [Module ℝ E] (T : U →ₗ[ℝ] E) (V : U →ₗ[ℝ] ℝ)
    (h : LinearMap.ker T ≤ LinearMap.ker V) : ∃ φ : E →ₗ[ℝ] ℝ, ∀ u, φ (T u) = V u := by
  obtain ⟨g, hg⟩ := LinearMap.exists_extend
    (((LinearMap.ker T).liftQ V h).comp T.quotKerEquivRange.symm.toLinearMap)
  refine ⟨g, fun u => ?_⟩
  have := LinearMap.congr_fun hg ⟨T u, LinearMap.mem_range_self T u⟩
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearEquiv.coe_coe,
    LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply,
    Submodule.liftQ_apply] at this
  exact this

/-- A point of the convex hull of `{f i : q i}` is a convex combination `∑ ν_i f(i)` with weights
supported on `{i : q i}`. -/
theorem exists_weights_of_mem_convexHull {ι : Type*} [Fintype ι] {q : ι → Prop}
    {f : ι → Rd d} {y : Rd d} (hy : y ∈ convexHull ℝ {z : Rd d | ∃ i, q i ∧ z = f i}) :
    ∃ ν : ι → ℝ, (∀ i, 0 ≤ ν i) ∧ (∀ i, ¬q i → ν i = 0) ∧ ∑ i, ν i = 1 ∧
      ∑ i, ν i • f i = y := by
  classical
  obtain ⟨κ, _, μ, v, hμ0, hμ1, hv, hy⟩ := mem_convexHull_iff_exists_fintype.1 hy
  simp only [Set.mem_ofPred_eq] at hv
  choose idx hq hidx using hv
  refine ⟨fun i => ∑ k, if idx k = i then μ k else 0, fun i => ?_, fun i hi => ?_, ?_, ?_⟩
  · exact Finset.sum_nonneg fun k _ => by split_ifs <;> simp [hμ0 k]
  · refine Finset.sum_eq_zero fun k _ => ?_
    rw [ite_eq_right]
    rintro rfl
    exact hi (hq k)
  · rw [Finset.sum_comm]
    simp [hμ1]
  · simp only [Finset.sum_smul]
    rw [Finset.sum_comm]
    simp [ite_smul, ← hidx, hy]

/-- Proposition 5.1, second part, linearity: if `Γ_w(x) = ∑ λ_i w(x_i)` for a convex
combination `x = ∑ λ_i x_i` of points of `S`, then `Γ_w` is affine on
`conv {x_i : λ_i > 0}`. Proof: for `y = ∑ ν_i x_i` in this hull, `x = s y + ∑ (λ_i - s ν_i) x_i`
for small `s > 0`, and concavity forces `Γ_w(y) = ∑ ν_i w(x_i)`; maximality of `∑ λ_i w(x_i)`
makes `ν ↦ ∑ ν_i w(x_i)` vanish on the affine dependences of the `x_i`, so it is the restriction of
an affine function of `y`. -/
theorem exists_affine_of_concaveEnvelopeOver_eq_sum (hS : S.Finite) {ι : Type*} [Fintype ι]
    {lam : ι → ℝ} {xs : ι → Site d} (hxs : ∀ i, xs i ∈ S) (h0 : ∀ i, 0 ≤ lam i)
    (h1 : ∑ i, lam i = 1) {x : Rd d} (hx : ∑ i, lam i • toE (xs i) = x)
    (hΓ : concaveEnvelopeOver S w x = ∑ i, lam i * w (xs i)) :
    ∃ (p : Rd d) (c : ℝ), ∀ y ∈ convexHull ℝ {z : Rd d | ∃ i, 0 < lam i ∧ z = toE (xs i)},
      concaveEnvelopeOver S w y = c + inner ℝ p y := by
  classical
  obtain ⟨i₀⟩ : Nonempty ι := by
    rcases isEmpty_or_nonempty ι with h | h
    · simp at h1
    · exact h
  -- the smallest positive weight
  set m₀ := Finset.univ.inf' ⟨i₀, Finset.mem_univ _⟩
    (fun i => if 0 < lam i then lam i else 1) with hm₀
  have hm₀pos : 0 < m₀ := by
    rw [hm₀]
    refine (Finset.lt_inf'_iff _).2 fun i _ => ?_
    split_ifs with h
    · exact h
    · exact one_pos
  have hm₀le : ∀ i, 0 < lam i → m₀ ≤ lam i := by
    intro i hi
    have := Finset.inf'_le (fun i => if 0 < lam i then lam i else 1) (Finset.mem_univ i)
    rw [ite_eq_left hi] at this
    exact this
  have hlam0 : ∀ i, ¬0 < lam i → lam i = 0 := fun i hi => le_antisymm (not_lt.1 hi) (h0 i)
  -- `ν ↦ ∑ ν_i w(x_i)` vanishes on the affine dependences supported on `{λ > 0}`
  have hcons : ∀ α : ι → ℝ, (∀ i, ¬0 < lam i → α i = 0) → ∑ i, α i • toE (xs i) = 0 →
      ∑ i, α i = 0 → ∑ i, α i * w (xs i) = 0 := by
    intro α hα hαx hα1
    have hApos : 0 < ∑ i, |α i| + 1 := by positivity
    set σ := m₀ / (∑ i, |α i| + 1) with hσ
    have hσpos : 0 < σ := div_pos hm₀pos hApos
    have hσα : ∀ i, σ * |α i| ≤ m₀ := by
      intro i
      have : |α i| ≤ ∑ i, |α i| + 1 := by
        have := Finset.single_le_sum (fun j _ => abs_nonneg (α j)) (Finset.mem_univ i)
        linarith
      calc σ * |α i| ≤ σ * (∑ i, |α i| + 1) := mul_le_mul_of_nonneg_left this hσpos.le
        _ = m₀ := div_mul_cancel₀ _ hApos.ne'
    have key : ∀ ε : ℝ, (ε = σ ∨ ε = -σ) → ε * ∑ i, α i * w (xs i) ≤ 0 := by
      intro ε hε
      have hε' : ∀ i, |ε * α i| ≤ m₀ := by
        intro i
        rw [abs_mul]
        have : |ε| = σ := by rcases hε with rfl | rfl <;> simp [abs_of_pos hσpos]
        rw [this]
        exact hσα i
      have hnn : ∀ i, 0 ≤ lam i + ε * α i := by
        intro i
        by_cases hi : 0 < lam i
        · have := hm₀le i hi
          have := neg_abs_le (ε * α i)
          linarith [hε' i]
        · rw [hα i hi, hlam0 i hi]
          simp
      have hle := sum_le_concaveEnvelopeOver (w := w) hS hxs hnn
        (by simp [Finset.sum_add_distrib, ← Finset.mul_sum, h1, hα1]) (x := x)
        (by simp [add_smul, Finset.sum_add_distrib, mul_smul, ← Finset.smul_sum, hαx, hx])
      rw [hΓ] at hle
      simp only [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum] at hle
      linarith
    have k1 := key σ (Or.inl rfl)
    have k2 := key (-σ) (Or.inr rfl)
    have e1 : ∑ i, α i * w (xs i) ≤ 0 := by
      by_contra hc
      rw [not_le] at hc
      nlinarith
    have e2 : 0 ≤ ∑ i, α i * w (xs i) := by
      by_contra hc
      rw [not_le] at hc
      nlinarith
    linarith
  -- linear algebra: `ν ↦ ∑ ν_i w(x_i)` factors through `ν ↦ (∑ ν_i x_i, ∑ ν_i)`
  let P : Submodule ℝ (ι → ℝ) :=
    { carrier := {α | ∀ i, ¬0 < lam i → α i = 0}
      add_mem' := by
        intro a b ha hb i hi
        simp [ha i hi, hb i hi]
      zero_mem' := by
        intro i _
        rfl
      smul_mem' := by
        intro c a ha i hi
        simp [ha i hi] }
  let T : P →ₗ[ℝ] Rd d × ℝ :=
    (Fintype.linearCombination ℝ fun i => ((toE (xs i), (1 : ℝ)) : Rd d × ℝ)).comp P.subtype
  let V : P →ₗ[ℝ] ℝ := (Fintype.linearCombination ℝ fun i => w (xs i)).comp P.subtype
  have hker : LinearMap.ker T ≤ LinearMap.ker V := by
    intro α hα
    rw [LinearMap.mem_ker] at hα ⊢
    simp only [T, V, LinearMap.comp_apply, Submodule.subtype_apply,
      Fintype.linearCombination_apply] at hα ⊢
    have hx0 : ∑ i, (α : ι → ℝ) i • toE (xs i) = 0 := by
      simpa [Prod.fst_sum] using congrArg Prod.fst hα
    have h10 : ∑ i, (α : ι → ℝ) i = 0 := by
      simpa [Prod.snd_sum] using congrArg Prod.snd hα
    simpa [smul_eq_mul] using hcons α α.2 hx0 h10
  obtain ⟨φ, hφ⟩ := exists_linearMap_comp_eq_of_ker_le T V hker
  let φa : Rd d →ₗ[ℝ] ℝ := φ.comp (LinearMap.inl ℝ (Rd d) ℝ)
  refine ⟨(InnerProductSpace.toDual ℝ (Rd d)).symm (LinearMap.toContinuousLinearMap φa),
    φ ((0 : Rd d), (1 : ℝ)), fun y hy => ?_⟩
  rw [InnerProductSpace.toDual_symm_apply, LinearMap.coe_toContinuousLinearMap']
  obtain ⟨ν, hν0, hνq, hν1, hνy⟩ := exists_weights_of_mem_convexHull hy
  have hφν : φ (y, 1) = ∑ i, ν i * w (xs i) := by
    have := hφ ⟨ν, hνq⟩
    simp only [T, V, LinearMap.comp_apply, Submodule.subtype_apply,
      Fintype.linearCombination_apply, smul_eq_mul] at this
    have e : ∑ i, ν i • ((toE (xs i), (1 : ℝ)) : Rd d × ℝ) = (y, 1) := by
      refine Prod.ext ?_ ?_
      · simpa [Prod.fst_sum] using hνy
      · simpa [Prod.snd_sum] using hν1
    rw [e] at this
    exact this
  have hsplit : φ (y, 1) = φa y + φ (0, 1) := by
    simp only [φa, LinearMap.comp_apply, LinearMap.inl_apply]
    rw [← map_add, Prod.mk_add_mk, add_zero, zero_add]
  -- `Γ_w(y) = ∑ ν_i w(x_i)`
  have hge : ∑ i, ν i * w (xs i) ≤ concaveEnvelopeOver S w y :=
    sum_le_concaveEnvelopeOver hS hxs hν0 hν1 hνy
  have hyS : y ∈ convexHull ℝ (toE '' S) := by
    refine convexHull_mono ?_ hy
    rintro _ ⟨i, -, rfl⟩
    exact ⟨xs i, hxs i, rfl⟩
  have hle : concaveEnvelopeOver S w y ≤ ∑ i, ν i * w (xs i) := by
    let ω : Option ι → ℝ := fun o => o.elim m₀ fun i => lam i - m₀ * ν i
    let pt : Option ι → Rd d := fun o => o.elim y fun i => toE (xs i)
    have hω0 : ∀ o ∈ Finset.univ, 0 ≤ ω o := by
      rintro (_ | i) _
      · exact hm₀pos.le
      · show 0 ≤ lam i - m₀ * ν i
        by_cases hi : 0 < lam i
        · have hνle : ν i ≤ 1 := by
            rw [← hν1]
            exact Finset.single_le_sum (fun j _ => hν0 j) (Finset.mem_univ i)
          nlinarith [hm₀le i hi, hν0 i]
        · rw [hνq i hi, hlam0 i hi]
          simp
    have hω1 : ∑ o, ω o = 1 := by
      rw [Fintype.sum_option]
      simp only [ω, Option.elim_none, Option.elim_some, Finset.sum_sub_distrib, ← Finset.mul_sum,
        h1, hν1]
      ring
    have hωpt : ∑ o, ω o • pt o = x := by
      rw [Fintype.sum_option]
      simp only [ω, pt, Option.elim_none, Option.elim_some, sub_smul, Finset.sum_sub_distrib,
        mul_smul, ← Finset.smul_sum, hνy, hx]
      abel
    have hmem : ∀ o ∈ Finset.univ, pt o ∈ convexHull ℝ (toE '' S) := by
      rintro (_ | i) _
      · exact hyS
      · exact subset_convexHull ℝ _ ⟨xs i, hxs i, rfl⟩
    have hJ := (concaveOn_concaveEnvelopeOver (w := w) hS).le_map_sum hω0 hω1 hmem
    rw [hωpt, hΓ, Fintype.sum_option] at hJ
    simp only [ω, pt, Option.elim_none, Option.elim_some, smul_eq_mul] at hJ
    have hsum : ∑ i, (lam i - m₀ * ν i) * w (xs i) ≤
        ∑ i, (lam i - m₀ * ν i) * concaveEnvelopeOver S w (toE (xs i)) :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (le_concaveEnvelopeOver hS (hxs i))
        (hω0 (some i) (Finset.mem_univ _))
    have halg : ∑ i, (lam i - m₀ * ν i) * w (xs i) =
        ∑ i, lam i * w (xs i) - m₀ * ∑ i, ν i * w (xs i) := by
      simp only [sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
    by_contra hc
    rw [not_le] at hc
    nlinarith
  linarith

end Representation

/-- Proposition 5.1 (Lemma 4.5 in Imbert-Silvestre), as stated in
`ConcaveEnvelopeRepStmt`. -/
theorem concaveEnvelopeRep : ConcaveEnvelopeRepStmt := by
  intro d _ n w x hx
  have hS := dClosure_cubeZ0_finite (d := d) n
  refine ⟨isLUB_concaveEnvelopeOver_fin (w := w) hS hx,
    fun lam xs hxs h01 h1 hxx hΓ => ⟨fun i hi => ?_, ?_⟩⟩
  · exact concaveEnvelopeOver_eq_of_eq_sum hS hxs (fun i => (h01 i).1) h1 hxx hΓ hi
  · exact exists_affine_of_concaveEnvelopeOver_eq_sum hS hxs (fun i => (h01 i).1) h1 hxx hΓ

end RandomSandpile
