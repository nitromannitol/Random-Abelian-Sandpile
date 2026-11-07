import RandomSandpile.Proofs.Sec9.NonPosDefLegalFlatStable

/-!
# Operator fact (11): the integer concave correction `ψ_s`

`integerConcave : IntegerConcaveStmt`. `ψ_s(z) = min_{p ∈ ℤ^d} g_p(z)`, `g_p(z) = p·z +
⌈|p|²/(2s)⌉`. Completing the square, `g_p(z) + s|z|²/2 ≥ |p + s z|²/(2s) ≥ 0`, so the minimum over the
integers exists and `ψ_s + s|z|²/2 ≥ 0`; rounding `p = ⌊-s z + 1/2⌋` gives
`ψ_s + s|z|²/2 ≤ d/(8s) + 1`. For the minimizer `p*` at `x`, `ψ_s ≤ g_{p*}` everywhere with equality
at `x`, and `g_{p*}` is affine, so `ψ_s(x + e_i) + ψ_s(x - e_i) ≤ 2ψ_s(x)`: `Δψ_s ≤ 0`.
-/

noncomputable section

open MeasureTheory LatticeProb LatticeProb.Sandpile Filter Topology

namespace RandomSandpile

namespace SingleSourceH0

variable {d : ℕ}

/-- `g_p(z) = p·z + ⌈|p|²/(2s)⌉`. -/
def psiAffine (s : ℝ) (p z : Fin d → ℤ) : ℤ :=
  (∑ i, p i * z i) + ⌈(∑ i, ((p i : ℤ) : ℝ) ^ 2) / (2 * s)⌉

theorem norm_toE_sq_eq_sum (z : Site d) : ‖toE z‖ ^ 2 = ∑ i, ((z i : ℤ) : ℝ) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [toE, sq_abs]

theorem psiAffine_lower {s : ℝ} (hs : 0 < s) (p z : Fin d → ℤ) :
    -(s * ∑ i, ((z i : ℤ) : ℝ) ^ 2 / 2) ≤ (psiAffine s p z : ℝ) := by
  unfold psiAffine
  push_cast
  have hc := Int.le_ceil ((∑ i, ((p i : ℤ) : ℝ) ^ 2) / (2 * s))
  have h : 0 ≤ ∑ i, (((p i : ℝ) + s * z i) ^ 2 / (2 * s)) :=
    Finset.sum_nonneg fun i _ => by positivity
  have e : ∑ i, (((p i : ℝ) + s * z i) ^ 2 / (2 * s)) =
      (∑ i, (p i : ℝ) * z i) + (∑ i, ((p i : ℤ) : ℝ) ^ 2) / (2 * s) +
        s * ∑ i, ((z i : ℤ) : ℝ) ^ 2 / 2 := by
    rw [Finset.sum_div, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    field_simp
    ring
  have : (∑ i, ((p i * z i : ℤ) : ℝ)) = ∑ i, (p i : ℝ) * z i := by push_cast; rfl
  linarith

theorem psiAffine_upper {s : ℝ} (hs : 0 < s) (z : Fin d → ℤ) :
    ∃ p : Fin d → ℤ, (psiAffine s p z : ℝ) ≤
      -(s * ∑ i, ((z i : ℤ) : ℝ) ^ 2 / 2) + (d / (8 * s) + 1) := by
  refine ⟨fun i => ⌊-s * z i + 1 / 2⌋, ?_⟩
  unfold psiAffine
  push_cast
  have hc := Int.ceil_lt_add_one ((∑ i, ((⌊-s * z i + 1 / 2⌋ : ℤ) : ℝ) ^ 2) / (2 * s))
  have hsq : ∀ i, (((⌊-s * z i + 1 / 2⌋ : ℤ) : ℝ) + s * z i) ^ 2 ≤ 1 / 4 := by
    intro i
    have h1 := Int.floor_le (-s * z i + 1 / 2)
    have h2 := Int.lt_floor_add_one (-s * z i + 1 / 2)
    nlinarith
  have e : ∑ i, ((((⌊-s * z i + 1 / 2⌋ : ℤ) : ℝ) + s * z i) ^ 2 / (2 * s)) =
      (∑ i, ((⌊-s * z i + 1 / 2⌋ : ℤ) : ℝ) * z i) +
        (∑ i, ((⌊-s * z i + 1 / 2⌋ : ℤ) : ℝ) ^ 2) / (2 * s) +
        s * ∑ i, ((z i : ℤ) : ℝ) ^ 2 / 2 := by
    rw [Finset.sum_div, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    field_simp
    ring
  have hle : ∑ i, ((((⌊-s * z i + 1 / 2⌋ : ℤ) : ℝ) + s * z i) ^ 2 / (2 * s)) ≤
      ∑ _i : Fin d, (1 / 4 / (2 * s)) :=
    Finset.sum_le_sum fun i _ => div_le_div_of_nonneg_right (hsq i) (by positivity)
  have hcard : ∑ _i : Fin d, (1 / 4 / (2 * s)) = d / (8 * s) := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    ring
  linarith

/-- the integer concave correction. -/
theorem integerConcave : IntegerConcaveStmt := by
  intro d hd s hs
  classical
  set ψ : Site d → ℤ := fun z => sInf (Set.range fun p : Fin d → ℤ => psiAffine s p z) with hψ
  have hbdd : ∀ z : Site d, BddBelow (Set.range fun p : Fin d → ℤ => psiAffine s p z) := by
    intro z
    refine ⟨⌈-(s * ∑ i, ((z i : ℤ) : ℝ) ^ 2 / 2)⌉, ?_⟩
    rintro _ ⟨p, rfl⟩
    have := psiAffine_lower hs p z
    exact Int.ceil_le.2 this
  have hne : ∀ z : Site d, (Set.range fun p : Fin d → ℤ => psiAffine s p z).Nonempty :=
    fun z => ⟨_, ⟨0, rfl⟩⟩
  have hmem : ∀ z : Site d, ∃ p : Fin d → ℤ, psiAffine s p z = ψ z := fun z =>
    Int.csInf_mem (hne z) (hbdd z)
  have hle : ∀ p z, ψ z ≤ psiAffine s p z := fun p z => csInf_le (hbdd z) ⟨p, rfl⟩
  refine ⟨ψ, fun x => ?_, fun z => ?_⟩
  · obtain ⟨p, hp⟩ := hmem x
    rw [lap_eq_sum_second_diff]
    refine Finset.sum_nonpos fun i _ => ?_
    have h1 := hle p (x + unit i)
    have h2 := hle p (x - unit i)
    have h3 : psiAffine s p (x + unit i) + psiAffine s p (x - unit i) = 2 * psiAffine s p x := by
      simp [psiAffine, unit, Pi.single_apply, mul_add, mul_sub, Finset.sum_add_distrib,
        Finset.sum_sub_distrib]
      ring
    rw [hp] at h3
    linarith
  · obtain ⟨p, hp⟩ := hmem z
    have hn := norm_toE_sq_eq_sum z
    have l1 := psiAffine_lower hs p z
    obtain ⟨q, hq⟩ := psiAffine_upper hs z
    have u1 := hle q z
    have hq' : (ψ z : ℝ) ≤ psiAffine s q z := by exact_mod_cast u1
    have l1' : -(s * ∑ i, ((z i : ℤ) : ℝ) ^ 2 / 2) ≤ (ψ z : ℝ) := by rw [← hp]; exact l1
    have u1' : (ψ z : ℝ) ≤ -(s * ∑ i, ((z i : ℤ) : ℝ) ^ 2 / 2) + (d / (8 * s) + 1) := hq'.trans hq
    have hn' : s * ‖toE z‖ ^ 2 / 2 = s * ∑ i, ((z i : ℤ) : ℝ) ^ 2 / 2 := by
      rw [hn, ← Finset.sum_div]; ring
    rw [hn']
    constructor <;> linarith

end SingleSourceH0

end RandomSandpile
