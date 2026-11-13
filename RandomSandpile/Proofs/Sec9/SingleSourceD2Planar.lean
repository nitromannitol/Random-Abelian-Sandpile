import RandomSandpile.Proofs.Sec9.SingleSourceD2Lower

/-!
# Theorem 9.2 in dimension two: the planar steps of Theorem 4.1

Step statements of SIMPLE-PROOF §§2-4 used by the abstract planar exclusion:
* `ComponentBoundStmt` (C2, Lemma 2.1): the negative comparison set of a source profile against an
  equation quadratic with positive definite Hessian is preconnected, and the positive comparison set
  has at most one component besides the source component;
* `AlternatingRaysStmt` (C3, Lemma 3.1): the alternating-rays separation lemma (planar topology);
* `SourceLabelOpenStmt`: being joined to the source is an open condition along a continuous
  family of quadratics and points.

Helpers: `isOpen_posSet`, `isOpen_negSet`, the subsolution inequality at a Peano point.
-/

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped Matrix

namespace RandomSandpile

namespace SingleSourceD2

/-! ### Step statements -/

/-- **(C2) SIMPLE-PROOF Lemma 2.1 (component bound).** Let `F` be degenerate elliptic with the shift
identity, `u` a source profile for `F`, and `Q(x) = c + p·(x - a) + ½(x - a)ᵀN(x - a)` with `N`
symmetric positive definite and `F(N) = 0`. Then `N_Q = negSet u Q` is preconnected, and any two
points of `P_Q = posSet u Q` outside the component of the source lie in one component. -/
def ComponentBoundStmt : Prop :=
  ∀ F : Matrix (Fin 2) (Fin 2) ℝ → ℝ, HasTraceShift F → DegenerateElliptic F →
    ∀ u : Rd 2 → ℝ, IsSourceProfile F u →
      ∀ (c : ℝ) (p a : Rd 2) (N : Matrix (Fin 2) (Fin 2) ℝ), N.IsSymm → N.PosDef → F N = 0 →
        IsPreconnected (negSet u fun x => c + inner ℝ p (x - a) + qM N (x - a)) ∧
        ∀ x ∈ posSet u (fun x => c + inner ℝ p (x - a) + qM N (x - a)),
          ∀ y ∈ posSet u (fun x => c + inner ℝ p (x - a) + qM N (x - a)),
            x ∉ connectedComponentIn (posSet u fun x => c + inner ℝ p (x - a) + qM N (x - a)) 0 →
            y ∉ connectedComponentIn (posSet u fun x => c + inner ℝ p (x - a) + qM N (x - a)) 0 →
            y ∈ connectedComponentIn (posSet u fun x => c + inner ℝ p (x - a) + qM N (x - a)) x

/-- **(C3) SIMPLE-PROOF Lemma 3.1 (alternating rays).** Let `P, N` be disjoint open subsets of the
plane, `N` preconnected, `a ∉ P ∪ N`, `v, w` linearly independent, `r > 0`, and `a ± t v ∈ P`,
`a ± t w ∈ N` for `0 < t ≤ r`. Then `a + r v` and `a - r v` lie in different components of `P`. -/
def AlternatingRaysStmt : Prop :=
  ∀ (P N : Set (Rd 2)) (a v w : Rd 2) (r : ℝ), IsOpen P → IsOpen N → Disjoint P N →
    IsPreconnected N → a ∉ P → a ∉ N → LinearIndependent ℝ ![v, w] → 0 < r →
    (∀ t : ℝ, 0 < t → t ≤ r →
      a + t • v ∈ P ∧ a - t • v ∈ P ∧ a + t • w ∈ N ∧ a - t • w ∈ N) →
      a - r • v ∉ connectedComponentIn P (a + r • v)

/-- **(C4) The source label is open** (SIMPLE-PROOF Theorem 4.1, "being connected to the source is an
open condition"). For `u` continuous off the origin with `u → ∞` at the origin, a jointly continuous
family of functions `Q θ` and a continuous family of points `x θ ≠ 0` with `Q θ (x θ) < u (x θ)`,
the set of parameters for which `x θ` lies in the source component of `posSet u (Q θ)` is open. -/
def SourceLabelOpenStmt : Prop :=
  ∀ (u : Rd 2 → ℝ), ContinuousOn u {x | x ≠ 0} → Tendsto u (𝓝[≠] 0) atTop →
    ∀ (Q : ℝ → Rd 2 → ℝ), Continuous (fun q : ℝ × Rd 2 => Q q.1 q.2) →
    ∀ (x : ℝ → Rd 2), Continuous x → (∀ θ, x θ ≠ 0 ∧ Q θ (x θ) < u (x θ)) →
      IsOpen {θ : ℝ | x θ ∈ connectedComponentIn (posSet u (Q θ)) 0}

/-! ### Helpers -/

/-- The negative comparison set is open. -/
theorem isOpen_negSet {u Q : Rd 2 → ℝ} (hu : ContinuousOn u {x | x ≠ 0}) (hQ : Continuous Q) :
    IsOpen (negSet u Q) := by
  have h := (hQ.continuousOn.sub hu).isOpen_inter_preimage isOpen_compl_singleton
    (isOpen_Ioi (a := (0 : ℝ)))
  convert h using 1
  ext x
  simp only [negSet, mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_Ioi, Pi.sub_apply, sub_pos]

/-- The positive comparison set (with the source adjoined) is open. -/
theorem isOpen_posSet {u Q : Rd 2 → ℝ} (hu : ContinuousOn u {x | x ≠ 0})
    (hu0 : Tendsto u (𝓝[≠] 0) atTop) (hQ : Continuous Q) : IsOpen (posSet u Q) := by
  have hopen : IsOpen {x : Rd 2 | x ≠ 0 ∧ Q x < u x} := by
    have h := (hQ.continuousOn.sub hu).isOpen_inter_preimage isOpen_compl_singleton
      (isOpen_Iio (a := (0 : ℝ)))
    convert h using 1
    ext x
    simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_Iio, Pi.sub_apply, sub_neg]
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rcases hx with hx | hx
  · exact Filter.mem_of_superset (hopen.mem_nhds hx) subset_union_left
  · rw [mem_singleton_iff] at hx
    subst hx
    have hQ0 : ∀ᶠ y in 𝓝[≠] (0 : Rd 2), Q y < Q 0 + 1 :=
      nhdsWithin_le_nhds ((hQ.tendsto 0).eventually (gt_mem_nhds (by linarith)))
    have hu1 : ∀ᶠ y in 𝓝[≠] (0 : Rd 2), Q 0 + 1 < u y := hu0.eventually (eventually_gt_atTop _)
    have h := hQ0.and hu1
    rw [eventually_nhdsWithin_iff] at h
    filter_upwards [h] with y hy
    by_cases hy0 : y = 0
    · exact Or.inr hy0
    · exact Or.inl ⟨hy0, by linarith [(hy hy0).1, (hy hy0).2]⟩

/-- The paraboloid with matrix `Y + ηI` touches `u` from above at a Peano point. -/
theorem isLocalMax_sub_paraboloid_of_taylor {u : Rd 2 → ℝ} {b p : Rd 2}
    {Y : Matrix (Fin 2) (Fin 2) ℝ} (hT : HasSecondOrderTaylorAt u b p Y) {η : ℝ} (hη : 0 < η) :
    IsLocalMax (fun y => u y - (u b + innerSL ℝ p (y - b) +
      qM (Y + η • (1 : Matrix (Fin 2) (Fin 2) ℝ)) (y - b))) b := by
  obtain ⟨ρ, hρ, hb⟩ := hT.bound (half_pos hη)
  refine Metric.eventually_nhds_iff.2 ⟨ρ, hρ, fun z hz => ?_⟩
  have hz' := hb z (by rw [← dist_eq_norm]; exact hz)
  simp only [sub_self, innerSL_apply_apply, inner_zero_right, qM_zero_right, add_zero]
  rw [qM_add_smul_one]
  have h1 := (abs_le.1 hz').2
  have h2 : 0 ≤ ‖z - b‖ ^ 2 := sq_nonneg _
  nlinarith

/-- The subsolution inequality at a Peano point: `F(Y) ≤ 0`. -/
theorem nonpos_of_taylor_of_sub {F : Matrix (Fin 2) (Fin 2) ℝ → ℝ} {V : Set (Rd 2)}
    {u : Rd 2 → ℝ} (hsub : ViscFromAboveLE F V u) (hshift : HasTraceShift F) {b p : Rd 2}
    (hb : b ∈ V) {Y : Matrix (Fin 2) (Fin 2) ℝ} (hYs : Y.IsSymm)
    (hT : HasSecondOrderTaylorAt u b p Y) : F Y ≤ 0 := by
  have key : ∀ η : ℝ, 0 < η → F Y - 2 * η ≤ 0 := by
    intro η hη
    have h := hsub b hb _ (contDiff_paraboloid (u b) p b
      (Y + η • (1 : Matrix (Fin 2) (Fin 2) ℝ))).contDiffAt
      (isLocalMax_sub_paraboloid_of_taylor hT hη)
    rwa [hessian_paraboloid, hessian_qM_of_isSymm (hYs.add (Matrix.isSymm_one.smul _)),
      hshift Y hYs] at h
  by_contra hpos
  have hpos' : 0 < F Y := not_le.mp hpos
  have := key (F Y / 4) (by linarith)
  linarith

/-- `F(H) = 0` at a Peano point of a source profile where it is positive. -/
theorem eq_zero_of_taylor_of_profile {F : Matrix (Fin 2) (Fin 2) ℝ → ℝ} (hshift : HasTraceShift F)
    {u : Rd 2 → ℝ} (hu : IsSourceProfile F u) {a p : Rd 2} (ha : a ≠ 0) (hua : 0 < u a)
    {H : Matrix (Fin 2) (Fin 2) ℝ} (hHs : H.IsSymm) (hT : HasSecondOrderTaylorAt u a p H) :
    F H = 0 :=
  le_antisymm (nonpos_of_taylor_of_sub hu.subsolution hshift ⟨ha, hua⟩ hHs hT)
    (nonneg_of_taylor_of_super hu.supersolution hshift ha hHs hT)

end SingleSourceD2

end RandomSandpile
