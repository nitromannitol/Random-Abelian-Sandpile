import RandomSandpile.Steps.Sec9.SingleSource
import RandomSandpile.Proofs.Sec7.MainTheoremViscEff
import RandomSandpile.Proofs.Sec7.Compactness

/-!
# Theorem 9.2, partial variant, from its steps

* `ssNonempty : SSNonemptyStmt`: the toppling function `u(y) = h(N - |y_1|)`, `h` the triangular
  numbers `h(m) = m (m + 1) / 2` for `m ≥ 0` (and `0` for `m ≤ 0`), `N = n + 1`, has
  `Δ u ≤ 1` everywhere and `Δ u(0) = -2N`, so `Δ u + η + n δ_0 ≤ 2d - 1` when `η ≤ 2d - 2`.
* `ssLimitSupersolution_of_steps`: from Lemma 6.4(1), `MuVanishFlatStmt` and, through the
  deterministic core `viscFromBelowGE_effOp_of_minPrinciple` of Theorem 1.1's step.
* `tendstoLocallyUniformlyOn_of_subseq`: the subsequence principle for locally uniform
  convergence on an open set.
* `singleSourceTheoremFlat_of_steps`: `SingleSourceTheoremFlatStmt` from compactness,: a
  continuous limit exists by compactness, lies in the obstacle set by (V) and `v̄_n ≥ 0`, and is its least
  element by minimality; hence every subsequence has a further subsequence converging to it.
-/

noncomputable section

open MeasureTheory LatticeProb LatticeProb.Sandpile Filter Topology

namespace RandomSandpile

variable {d : ℕ}

/-! ### Finiteness of the odometers -/

/-- Triangular numbers `ssTri k = k (k + 1) / 2`. -/
def ssTri : ℕ → ℤ
  | 0 => 0
  | k + 1 => ssTri k + (k + 1)

theorem ssTri_nonneg : ∀ k, 0 ≤ ssTri k
  | 0 => le_rfl
  | k + 1 => by
    have := ssTri_nonneg k
    have hk : (0 : ℤ) ≤ k := Int.natCast_nonneg k
    simp only [ssTri]
    linarith

/-- `ssProfile m = ssTri m⁺`. -/
def ssProfile (m : ℤ) : ℤ := ssTri m.toNat

theorem ssProfile_succ {m : ℤ} (hm : 0 ≤ m) : ssProfile (m + 1) = ssProfile m + (m + 1) := by
  simp only [ssProfile]
  rw [show (m + 1).toNat = m.toNat + 1 by omega, ssTri, Int.toNat_of_nonneg hm]

theorem ssProfile_of_nonpos {m : ℤ} (hm : m ≤ 0) : ssProfile m = 0 := by
  simp only [ssProfile]
  rw [show m.toNat = 0 by omega]
  rfl

theorem ssProfile_secondDiff_le (m : ℤ) :
    ssProfile (m + 1) + ssProfile (m - 1) - 2 * ssProfile m ≤ 1 := by
  rcases le_or_gt 1 m with h | h
  · have e1 := ssProfile_succ (show 0 ≤ m by omega)
    have e2 := ssProfile_succ (show 0 ≤ m - 1 by omega)
    rw [show m - 1 + 1 = m by ring] at e2
    linarith
  · rcases eq_or_lt_of_le (show m ≤ 0 by omega) with h0 | hneg
    · subst h0
      rw [ssProfile_succ le_rfl, ssProfile_of_nonpos (by norm_num : (0 : ℤ) - 1 ≤ 0),
        ssProfile_of_nonpos le_rfl]
      norm_num
    · rw [ssProfile_of_nonpos (by omega : m + 1 ≤ 0), ssProfile_of_nonpos (by omega : m - 1 ≤ 0),
        ssProfile_of_nonpos hneg.le]
      norm_num

/-- The one-dimensional profile `t ↦ h(N - |t|)`. -/
def ssG (N t : ℤ) : ℤ := ssProfile (N - |t|)

theorem ssG_secondDiff_le (N : ℤ) {t : ℤ} (ht : t ≠ 0) :
    ssG N (t + 1) + ssG N (t - 1) - 2 * ssG N t ≤ 1 := by
  simp only [ssG]
  rcases lt_or_gt_of_ne ht with hneg | hpos
  · rw [abs_of_nonpos (by omega : t + 1 ≤ 0), abs_of_neg (by omega : t - 1 < 0),
      abs_of_neg hneg]
    have := ssProfile_secondDiff_le (N + t)
    rw [show N - -(t + 1) = N + t + 1 by ring, show N - -(t - 1) = N + t - 1 by ring,
      show N - -t = N + t by ring]
    exact this
  · rw [abs_of_pos (by omega : 0 < t + 1), abs_of_nonneg (by omega : 0 ≤ t - 1),
      abs_of_pos hpos]
    have := ssProfile_secondDiff_le (N - t)
    rw [show N - (t + 1) = N - t - 1 by ring, show N - (t - 1) = N - t + 1 by ring]
    linarith

theorem ssG_secondDiff_zero {N : ℤ} (hN : 1 ≤ N) :
    ssG N (0 + 1) + ssG N (0 - 1) - 2 * ssG N 0 = -2 * N := by
  simp only [ssG, zero_add, zero_sub, abs_one, abs_neg, abs_zero, sub_zero]
  have := ssProfile_succ (show 0 ≤ N - 1 by omega)
  rw [show N - 1 + 1 = N by ring] at this
  rw [this]
  ring

/-- **Step (N)** (`SSNonemptyStmt`). -/
theorem ssNonempty : SSNonemptyStmt := by
  intro d hd η hη n
  set i₀ : Fin d := ⟨0, by omega⟩
  set N : ℤ := (n : ℤ) + 1 with hN
  have hN1 : 1 ≤ N := by omega
  refine ⟨fun y => ssG N (y i₀), mem_stabilizing_univ.2
    ⟨fun y => ssTri_nonneg _, fun x => ?_⟩⟩
  rw [lap_comp_coord (fun t => ssG N t) i₀ x]
  have hηx := hη x
  by_cases hx0 : x = 0
  · subst hx0
    simp only [Pi.zero_apply, dirac_self, mul_one]
    rw [ssG_secondDiff_zero hN1]
    omega
  · have hdx : dirac 0 x = 0 := by simp [dirac, hx0]
    rw [hdx, mul_zero, add_zero]
    have hlap : ssG N (x i₀ + 1) + ssG N (x i₀ - 1) - 2 * ssG N (x i₀) ≤ 1 := by
      by_cases hxi : x i₀ = 0
      · rw [hxi, ssG_secondDiff_zero hN1]; omega
      · exact ssG_secondDiff_le N hxi
    omega

/-! ### Supersolution property of the limits -/

/-- **Step** from Lemma 6.4(1), `MuVanishFlatStmt` and the interior minimum principle. -/
theorem ssLimitSupersolution_of_steps (h64 : EffectiveOperatorBasicStmt)
    (hVan : MuVanishFlatStmt) (hMinP : SSInteriorMinPrincipleStmt) :
    SSLimitSupersolutionStmt := by
  intro d hd E hmax hflat
  have hrat : ∀ᵐ η ∂E.P, ∀ (q : ℚ) (A : Fin d → Fin d → ℚ), effOp E (symQ A) ≤ (q : ℝ) →
      ∀ u : Rd d → ℝ, IsSSSubseqLimit η u →
        ∀ (a p : Rd d) (r : ℝ), 0 < r → Metric.closedBall a r ⊆ {x : Rd d | x ≠ 0} →
          ∀ x ∈ Metric.closedBall a r, ∃ y ∈ Metric.sphere a r,
            u y - (inner ℝ p (y - a) + qM (symQ A) (y - a) + ql (q : ℝ) (y - a)) ≤
              u x - (inner ℝ p (x - a) + qM (symQ A) (x - a) + ql (q : ℝ) (x - a)) := by
    rw [ae_all_iff]; intro q; rw [ae_all_iff]; intro A
    by_cases hq : effOp E (symQ A) ≤ (q : ℝ)
    · filter_upwards [hMinP d hd E hmax q (symQ A) (symQ_isSymm A)
        ((hVan d hd E hflat (symQ A) (symQ_isSymm A) q).2 hq)] with η hη
      exact fun _ => hη
    · exact Eventually.of_forall fun η h => absurd h hq
  filter_upwards [hrat] with η hη
  exact fun u hu => viscFromBelowGE_effOp_of_minPrinciple h64 hd E isOpen_ne
    fun q A hq => hη q A hq u hu

/-! ### The reduction -/

/-- Subsequential limits are nonnegative off the origin. -/
theorem IsSSSubseqLimit.nonneg {η : Site d → ℤ} {u : Rd d → ℝ} (hu : IsSSSubseqLimit η u)
    {x : Rd d} (hx : x ≠ 0) : 0 ≤ u x := by
  obtain ⟨nk, -, hconv⟩ := hu
  refine ge_of_tendsto' (hconv.tendsto_at hx) fun k => ?_
  exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (Int.cast_nonneg (singleSourceOdometer_nonneg _ _ _))

/-- The subsequence principle for locally uniform convergence on an open subset of `ℝ^d`. -/
theorem tendstoLocallyUniformlyOn_of_subseq {F : ℕ → Rd d → ℝ} {f : Rd d → ℝ}
    {S : Set (Rd d)} (hS : IsOpen S)
    (h : ∀ nk : ℕ → ℕ, StrictMono nk → ∃ φ : ℕ → ℕ, StrictMono φ ∧
      TendstoLocallyUniformlyOn (fun j => F (nk (φ j))) f atTop S) :
    TendstoLocallyUniformlyOn F f atTop S := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hS]
  intro K hKS hK
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  obtain ⟨nk, hnk, hbad⟩ := extraction_of_frequently_atTop hcon
  obtain ⟨φ, hφ, hconv⟩ := h nk hnk
  have hK' := (tendstoLocallyUniformlyOn_iff_forall_isCompact hS).1 hconv K hKS hK
  rw [Metric.tendstoUniformlyOn_iff] at hK'
  obtain ⟨j, hj⟩ := (hK' ε hε).exists
  exact hbad (φ j) hj

/-- **Theorem 9.2, partial variant** (`SingleSourceTheoremFlatStmt`) from compactness, the
supersolution property and the minimality of the limits. -/
theorem singleSourceTheoremFlat_of_steps (hComp : SSCompactnessStmt)
    (hSup : SSLimitSupersolutionStmt) (hMin : SSLimitMinimalStmt) :
    SingleSourceTheoremFlatStmt := by
  intro d hd E hmax hflat
  have hd1 : 1 ≤ d := by omega
  have hbdd : ∀ᵐ η ∂E.P, ∀ x, E.ηmin ≤ η x ∧ η x ≤ E.ηmax := ae_all_iff.2 E.bounded
  have hG : ∀ᵐ η ∂E.P, (∀ x, E.ηmin ≤ η x ∧ η x ≤ 2 * (d : ℤ) - 2) ∧
      (∀ u, IsSSSubseqLimit η u → ViscFromBelowGE (effOp E) {x : Rd d | x ≠ 0} u) ∧
      (∀ v : Rd d → ℝ, Continuous v →
        IsSSSubseqLimit η (fun x => v x + fundamentalSolution d x) →
          ∀ w ∈ singleSourceObstacleSet E, ∀ x, v x ≤ w x) := by
    filter_upwards [hbdd, hSup d hd E hmax hflat, hMin d hd E hmax hflat] with η h1 h2 h3
    exact ⟨fun x => ⟨(h1 x).1, hmax ▸ (h1 x).2⟩, h2, h3⟩
  have hmem : ∀ η : Site d → ℤ,
      (∀ u, IsSSSubseqLimit η u → ViscFromBelowGE (effOp E) {x : Rd d | x ≠ 0} u) →
      ∀ v : Rd d → ℝ, Continuous v →
        IsSSSubseqLimit η (fun x => v x + fundamentalSolution d x) →
          v ∈ singleSourceObstacleSet E := fun η hηV v hvc hv =>
    ⟨hvc, fun x hx => by have := hv.nonneg hx; linarith, hηV _ hv⟩
  obtain ⟨η₀, hη₀b, hη₀V, hη₀M⟩ := hG.exists
  obtain ⟨φ, hφ, v₀, hv₀c, hv₀⟩ := hComp d hd E.ηmin η₀ hη₀b id strictMono_id
  have hv₀L : IsSSSubseqLimit η₀ (fun x => v₀ x + fundamentalSolution d x) := ⟨φ, hφ, hv₀⟩
  have hLeast : IsLeast (singleSourceObstacleSet E) v₀ :=
    ⟨hmem η₀ hη₀V v₀ hv₀c hv₀L, fun w hw x => hη₀M v₀ hv₀c hv₀L w hw x⟩
  rw [singleSourceObstacleSolution_eq_of_isLeast hLeast]
  refine ⟨hLeast, ?_⟩
  filter_upwards [hG] with η hη
  refine ⟨ssNonempty d hd1 η (fun x => (hη.1 x).2), ?_⟩
  refine tendstoLocallyUniformlyOn_of_subseq isOpen_ne fun nk hnk => ?_
  obtain ⟨ψ, hψ, v', hv'c, hv'⟩ := hComp d hd E.ηmin η hη.1 nk hnk
  have hv'L : IsSSSubseqLimit η (fun x => v' x + fundamentalSolution d x) :=
    ⟨nk ∘ ψ, hnk.comp hψ, hv'⟩
  have heq : v' = v₀ := funext fun x =>
    le_antisymm (hη.2.2 v' hv'c hv'L v₀ hLeast.1 x) (hLeast.2 (hmem η hη.2.1 v' hv'c hv'L) x)
  rw [heq] at hv'
  exact ⟨ψ, hψ, hv'⟩

/-- **Theorem 9.2, partial variant** from the finest steps: Lemma 6.4(1), compactness,
`MuVanishFlatStmt`, the interior minimum principle and minimality. -/
theorem singleSourceTheoremFlat_of_remainingSteps (h64 : EffectiveOperatorBasicStmt)
    (hComp : SSCompactnessStmt) (hVan : MuVanishFlatStmt) (hMinP : SSInteriorMinPrincipleStmt)
    (hMin : SSLimitMinimalStmt) : SingleSourceTheoremFlatStmt :=
  singleSourceTheoremFlat_of_steps hComp (ssLimitSupersolution_of_steps h64 hVan hMinP) hMin

end RandomSandpile
