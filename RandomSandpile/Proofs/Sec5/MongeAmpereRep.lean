import RandomSandpile.Steps.Sec5.MongeAmpereRep
import RandomSandpile.Infra.ConcaveEnvelope
import RandomSandpile.Proofs.Sec6.MuMonotone

/-! # Lemma 5.3 (the Monge-Ampère measure of the concave envelope): proofs of the steps

Proofs of the step statements of `RandomSandpile/Steps/Sec5/MongeAmpereRep.lean` and of Lemma 5.3
itself, `mongeAmpereRep : MongeAmpereRepStmt`.

* Step 1 is `supGradSetVolume : SupGradSetVolumeStmt` (Lemma 6.1, Step 3);
* `supGradInterNull`: a common supergradient at `x ≠ y` lies in the hyperplane
  `{p : p · (y - x) = w(y) - w(x)}` (`volume_inner_eq_null`);
* `contactSupGrad`: the contact set characterization and the identification of supergradients at
  contact points (`concaveEnvelope_eq_iff_supGrad_nonempty`, `supGrad_eq_supGradR_concaveEnvelope`);
* `concaveEnvelopeAttained`: the admissible pairs `(λ, (x_i))` of the Carathéodory representation
  (`isLUB_concaveEnvelopeOver_fin`) form a compact subset of `ℝ^{d+1} × (ℤ^d)^{d+1}`, so the
  supremum of the continuous function `∑ λ_i w(x_i)` over it is attained;
* `supGradOfRep`: with `L(y) = Γ_w(x) + p · (y - x) ≥ Γ_w(y) ≥ w(y)` on `Q̄_n`,
  `∑ λ_i (L(x_i) - w(x_i)) = L(x) - Γ_w(x) = 0`, so `L(x_i) = w(x_i)` whenever `λ_i > 0`. -/

open MeasureTheory LatticeProb LatticeProb.Sandpile
open scoped ENNReal

namespace RandomSandpile

/-- Supergradient sets at two distinct points of `Ā` meet inside a Lebesgue-null hyperplane. -/
theorem supGradInterNull : SupGradInterNullStmt := by
  intro d w A x y hx hy hxy
  have hu : toE y - toE x ≠ 0 := sub_ne_zero.mpr fun h => hxy (toE_injective h).symm
  refine measure_mono_null (fun p hp => ?_) (volume_inner_eq_null hu (w y - w x))
  have h1 := hp.1 y hy
  have h2 := hp.2 x hx
  show inner ℝ p (toE y - toE x) = w y - w x
  simp only [inner_sub_right] at h1 h2 ⊢
  linarith

/-- At `x ∈ Q_n`: `∂⁺(w, x, Q_n) = ∅` off the contact set, `∂⁺(w, x, Q_n) = ∂⁺(Γ_w, x, Q_n)` on
it. -/
theorem contactSupGrad : ContactSupGradStmt := by
  intro d n w x hx
  refine ⟨fun hc => Set.not_nonempty_iff_eq_empty.1 fun hne =>
    hc ((concaveEnvelope_eq_iff_supGrad_nonempty (w := w) hx).2 hne), fun hc => ?_⟩
  exact supGrad_eq_supGradR_concaveEnvelope (subset_dClosure _ hx) hc

/-- The supremum of the Carathéodory representation (Proposition 5.1) is attained. -/
theorem concaveEnvelopeAttained : ConcaveEnvelopeAttainedStmt := by
  intro d n w x hx
  set S : Set (Site d) := dClosure (cubeZ0 (n : ℝ)) with hSdef
  have hS : S.Finite := dClosure_cubeZ0_finite n
  have hlub := isLUB_concaveEnvelopeOver_fin (w := w) hS hx
  set C : Set ((Fin (d + 1) → ℝ) × (Fin (d + 1) → Site d)) :=
    {q | (∀ i, q.2 i ∈ S) ∧ (∀ i, 0 ≤ q.1 i ∧ q.1 i ≤ 1) ∧ ∑ i, q.1 i = 1 ∧
      ∑ i, q.1 i • toE (q.2 i) = x} with hC
  set f : (Fin (d + 1) → ℝ) × (Fin (d + 1) → Site d) → ℝ :=
    fun q => ∑ i, q.1 i * w (q.2 i) with hf
  have hfc : Continuous f := continuous_finsetSum _ fun i _ =>
    ((continuous_apply i).comp continuous_fst).mul
      ((continuous_of_discreteTopology (f := w)).comp ((continuous_apply i).comp continuous_snd))
  have hK : IsCompact ((Set.univ.pi fun _ : Fin (d + 1) => Set.Icc (0 : ℝ) 1) ×ˢ
      (Set.univ.pi fun _ : Fin (d + 1) => S)) :=
    (isCompact_univ_pi fun _ => isCompact_Icc).prod (isCompact_univ_pi fun _ => hS.isCompact)
  have hCclosed : IsClosed C := by
    have e1 : IsClosed {q : (Fin (d + 1) → ℝ) × (Fin (d + 1) → Site d) | ∀ i, q.2 i ∈ S} :=
      (isClosed_discrete {xs : Fin (d + 1) → Site d | ∀ i, xs i ∈ S}).preimage continuous_snd
    have e2 : IsClosed
        {q : (Fin (d + 1) → ℝ) × (Fin (d + 1) → Site d) | ∀ i, 0 ≤ q.1 i ∧ q.1 i ≤ 1} := by
      simp only [Set.ofPred_forall, Set.ofPred_and]
      exact isClosed_iInter fun i =>
        (isClosed_le continuous_const ((continuous_apply i).comp continuous_fst)).inter
          (isClosed_le ((continuous_apply i).comp continuous_fst) continuous_const)
    have e3 : IsClosed {q : (Fin (d + 1) → ℝ) × (Fin (d + 1) → Site d) | ∑ i, q.1 i = 1} :=
      isClosed_eq (continuous_finsetSum _ fun i _ => (continuous_apply i).comp continuous_fst)
        continuous_const
    have e4 : IsClosed
        {q : (Fin (d + 1) → ℝ) × (Fin (d + 1) → Site d) | ∑ i, q.1 i • toE (q.2 i) = x} :=
      isClosed_eq (continuous_finsetSum _ fun i _ =>
        ((continuous_apply i).comp continuous_fst).smul
          ((continuous_of_discreteTopology (f := toE (d := d))).comp
            ((continuous_apply i).comp continuous_snd))) continuous_const
    exact e1.inter (e2.inter (e3.inter e4))
  have hCc : IsCompact C :=
    hK.of_isClosed_subset hCclosed fun q hq => ⟨fun i _ => hq.2.1 i, fun i _ => hq.1 i⟩
  have hcl := hlub.mem_closure hlub.nonempty
  have hmem : concaveEnvelopeOver S w x ∈ f '' C := by
    refine closure_minimal ?_ (hCc.image hfc).isClosed hcl
    rintro _ ⟨lam, xs, hxs, h01, h1, hxx, rfl⟩
    exact ⟨(lam, xs), ⟨hxs, h01, h1, hxx⟩, rfl⟩
  obtain ⟨⟨lam, xs⟩, ⟨hxs, h01, h1, hxx⟩, hfq⟩ := hmem
  exact ⟨lam, xs, hxs, fun i => (h01 i).1, h1, hxx, hfq.symm⟩

/-- A supergradient of `Γ_w` at `x = ∑ λ_i x_i` with `Γ_w(x) = ∑ λ_i w(x_i)` is a supergradient
of `w` at every `x_i` with `λ_i > 0`. -/
theorem supGradOfRep : SupGradOfRepStmt := by
  intro d n w x p hx hp lam xs hxs h0 h1 hxx hΓ i hi
  set Γ := concaveEnvelope w n with hΓdef
  have hmemK : ∀ {y : Site d}, y ∈ dClosure (cubeZ0 (n : ℝ)) → toE y ∈ cubeHullClosure d n :=
    fun hy => subset_convexHull ℝ _ (Set.mem_image_of_mem toE hy)
  have hL : ∀ j, w (xs j) ≤ Γ x + inner ℝ p (toE (xs j) - x) := fun j =>
    (le_concaveEnvelope (hxs j)).trans (hp _ (hmemK (hxs j)))
  have hinner : ∑ j, lam j * inner ℝ p (toE (xs j) - x) = 0 := by
    have e : ∑ j, lam j • (toE (xs j) - x) = 0 := by
      simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, h1, one_smul, hxx,
        sub_self]
    calc ∑ j, lam j * inner ℝ p (toE (xs j) - x)
        = inner ℝ p (∑ j, lam j • (toE (xs j) - x)) := by
          rw [inner_sum]
          simp only [real_inner_smul_right]
      _ = 0 := by rw [e, inner_zero_right]
  have hterm : ∀ j, 0 ≤ lam j * (Γ x + inner ℝ p (toE (xs j) - x) - w (xs j)) := fun j =>
    mul_nonneg (h0 j) (sub_nonneg.2 (hL j))
  have hsum0 : ∑ j, lam j * (Γ x + inner ℝ p (toE (xs j) - x) - w (xs j)) = 0 := by
    have e : ∀ j, lam j * (Γ x + inner ℝ p (toE (xs j) - x) - w (xs j)) =
        lam j * Γ x + lam j * inner ℝ p (toE (xs j) - x) - lam j * w (xs j) := fun j => by ring
    rw [Finset.sum_congr rfl fun j _ => e j, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.sum_mul, h1, hinner, ← hΓ]
    ring
  have hi0 := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => hterm j).1 hsum0 i (Finset.mem_univ _)
  have hLi : w (xs i) = Γ x + inner ℝ p (toE (xs i) - x) := by
    rcases mul_eq_zero.1 hi0 with h | h
    · exact absurd h hi.ne'
    · linarith
  intro y hy
  have hy' := (le_concaveEnvelope hy).trans (hp _ (hmemK hy))
  have e : inner ℝ p (toE y - x) =
      inner ℝ p (toE (xs i) - x) + inner ℝ p (toE y - toE (xs i)) := by
    rw [← inner_add_right]
    congr 1
    abel
  linarith

/-- Lemma 5.3 (MA-rep):
`∑_{x ∈ Q_n} |∂⁺(w, x, Q_n)| = |∂⁺(w, Q_n)| = ∑_{x ∈ Q_n, Γ_w(x) = w(x)} |∂⁺(Γ_w, x, Q_n)|
  = |∂⁺(Γ_w, 𝒬_n)|`. -/
theorem mongeAmpereRep : MongeAmpereRepStmt :=
  mongeAmpereRep_of_steps supGradSetVolume supGradInterNull contactSupGrad
    concaveEnvelopeAttained supGradOfRep

end RandomSandpile
