import RandomSandpile.Proofs.Sec9.SingleSourceD2StarDim
import RandomSandpile.Proofs.Sec9.SingleSourceD2WeakLap
import RandomSandpile.Proofs.Sec9.SingleSourceD2PS25

/-!
# Step in dimension two from Pegden-Smart's Proposition 2.5

`ssLimitSubStarD2 : SSCompactnessStmt → PegdenSmartProp25Stmt → SSLimitSubStarD2Stmt`: almost surely
every subsequential limit `u` is a viscosity subsolution of `F*(D²u) ≤ 0` on `{u > 0} ∖ {0}`.

Route (r4's `SingleSourceFstar.ssLimitSubStar`, with its touching input replaced): if `φ`
touches `u` from above at `x` with `F*(D²φ(x)) > 0`, let `H = D²φ(x)` and `ε = F*(H)/(8d)`. On a
small ball `B_ρ(x)` off the origin and inside `{u > 0}`, `u` is a weak solution of `Δu = s`,
`|s| ≤ C` (`ssLimitWeakLaplace`), and `-u` lies strictly above the paraboloid
`-u(x) - Dφ(x)(· - x) - ½(· - x)ᵀ(H + 4εI)(· - x)` on the sphere (second-order Taylor expansion
of `φ`). Pegden-Smart's Proposition 2.5, paraboloid form (`ps25Paraboloid_of_ps25`), gives a point
`b` of the ball at which `u` has a Peano expansion with symmetric matrix `X < H + 4εI`. Degenerate
ellipticity and the shift identity give `F*(X) ≥ F*(H) - 8ε > 0`, against `F*(D²u(b)) ≤ 0` at Peano
points (r4's `ssPeanoStar`, leastness of the odometer).
-/

noncomputable section

open MeasureTheory LatticeProb LatticeProb.Sandpile Filter Topology Metric
open scoped Matrix

namespace RandomSandpile

namespace SingleSourceD2

/-- A Peano expansion of `-u` is one of `u` with the opposite gradient and matrix. -/
theorem hasSecondOrderTaylorAt_of_neg {u : Rd 2 → ℝ} {b p : Rd 2}
    {Y : Matrix (Fin 2) (Fin 2) ℝ} (h : HasSecondOrderTaylorAt (fun y => -u y) b p Y) :
    HasSecondOrderTaylorAt u b (-p) (-Y) := by
  unfold HasSecondOrderTaylorAt at h ⊢
  refine h.neg_left.congr_left fun y => ?_
  rw [inner_neg_left, qM_neg_mat]
  ring

/-- Weak solutions of `Δu = s` change sign with `u` and `s`. -/
theorem isWeakSolutionLaplace_neg' {U : Set (Rd 2)} {u s : Rd 2 → ℝ}
    (h : IsWeakSolutionLaplace U u s) :
    IsWeakSolutionLaplace U (fun y => -u y) (fun y => -s y) := fun φ hφ hc hsupp => by
  simp only [neg_mul, integral_neg]
  rw [h φ hφ hc hsupp]

/-- **Step in dimension two** from compactness and Pegden-Smart's Proposition 2.5. -/
theorem ssLimitSubStarD2 (hComp : SSCompactnessStmt) (h25 : PegdenSmartProp25Stmt) :
    SSLimitSubStarD2Stmt := by
  intro E hmax
  have hd : 2 ≤ 2 := le_rfl
  have hd1 : 1 ≤ 2 := by omega
  have hE : E.ηmax ≤ 2 * ((2 : ℕ) : ℤ) - 1 := by rw [hmax]; omega
  have hPS := ps25Paraboloid_of_ps25 h25
  filter_upwards [SingleSourceFstar.ssPeanoStar muConvergence_unconditional hComp 2 hd E hmax,
    ssLimitWeakLaplace E hmax, ae_all_iff.2 E.bounded] with η hpeano hweak hbd
  intro u hu
  have hbd' : ∀ z, E.ηmin ≤ η z ∧ η z ≤ 2 * ((2 : ℕ) : ℤ) - 2 := fun z =>
    ⟨(hbd z).1, (hbd z).2.trans hmax.le⟩
  have hW := hweak u hu
  obtain ⟨nk, hnk, hconvu⟩ := hu
  -- continuity of `u` off the origin (step)
  obtain ⟨φ₀, hφ₀, v, hvc, hconvφ⟩ := hComp 2 hd E.ηmin η hbd' nk hnk
  have hopen : IsOpen {x : Rd 2 | x ≠ 0} := isOpen_ne
  have huv : Set.EqOn u (fun y => v y + fundamentalSolution 2 y) {x : Rd 2 | x ≠ 0} :=
    fun y hy => tendsto_nhds_unique ((hconvu.tendsto_at hy).comp hφ₀.tendsto_atTop)
      (hconvφ.tendsto_at hy)
  have hucont : ContinuousOn u {x : Rd 2 | x ≠ 0} :=
    (hvc.continuousOn.add (SingleSourceMin.continuousOn_fundamentalSolution 2)).congr huv
  -- the subsolution property
  intro x hx φ hφ hmx
  by_contra hneg
  have hpos : 0 < effOpStar E (hessian φ x) := not_le.1 hneg
  set H := hessian φ x with hHdef
  have hH : H.IsSymm := hessian_isSymm_of_contDiffAt hφ
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = effOpStar E H / (8 * ((2 : ℕ) : ℝ)) := ⟨_, rfl⟩
  have hε0 : 0 < ε := by rw [hε]; exact div_pos hpos (by positivity)
  have h8 : 8 * ((2 : ℕ) : ℝ) * ε = effOpStar E H := by
    rw [hε, mul_div_assoc', mul_div_cancel_left₀ _ (by positivity : (8 * ((2 : ℕ) : ℝ)) ≠ 0)]
  have hH's : (H + (4 * ε) • (1 : Matrix (Fin 2) (Fin 2) ℝ)).IsSymm :=
    hH.add (Matrix.isSymm_one.smul _)
  obtain ⟨ρ₁, hρ₁, hT⟩ := ContDiffAt.taylor_two hφ hε0
  obtain ⟨ρ₂, hρ₂, hm⟩ := Metric.eventually_nhds_iff.1 hmx
  have hUopen : IsOpen {y : Rd 2 | y ≠ 0 ∧ 0 < u y} :=
    hucont.isOpen_inter_preimage hopen (isOpen_Ioi (a := (0 : ℝ)))
  obtain ⟨ρ₃, hρ₃, hball3⟩ := Metric.isOpen_iff.1 hUopen x hx
  obtain ⟨ρ₄, hρ₄, -, s, C, hsm, hsC, hws⟩ := hW x hx.1
  obtain ⟨ρ, hρ0, hρ1, hρ2, hρ3, hρ4⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ρ < ρ₁ ∧ ρ < ρ₂ ∧ ρ < ρ₃ ∧ ρ < ρ₄ := by
    refine ⟨min (min ρ₁ ρ₂) (min ρ₃ ρ₄) / 2, by positivity, ?_, ?_, ?_, ?_⟩ <;>
    · have h0 : 0 < min (min ρ₁ ρ₂) (min ρ₃ ρ₄) := by positivity
      have := min_le_left (min ρ₁ ρ₂) (min ρ₃ ρ₄)
      have := min_le_right (min ρ₁ ρ₂) (min ρ₃ ρ₄)
      have := min_le_left ρ₁ ρ₂
      have := min_le_right ρ₁ ρ₂
      have := min_le_left ρ₃ ρ₄
      have := min_le_right ρ₃ ρ₄
      linarith
  have hsubU : closedBall x ρ ⊆ {y : Rd 2 | y ≠ 0 ∧ 0 < u y} :=
    (closedBall_subset_ball hρ3).trans hball3
  -- `u ≤ ψ - ε|· - x|²` on `B̄_ρ(x)`, `ψ` the quadratic of `D²φ(x) + 4εI`
  have hle : ∀ y, ‖y - x‖ ≤ ρ → u y - (u x + fderiv ℝ φ x (y - x) +
      qM (H + (4 * ε) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) (y - x)) ≤ -(ε * ‖y - x‖ ^ 2) := by
    intro y hy
    have h1 := abs_le.1 (hT y (by linarith))
    have h2 : u y - φ y ≤ u x - φ x := hm (by rw [dist_eq_norm]; linarith)
    rw [qM_add_mat, qM_smul_one]
    linarith [h1.1, h1.2]
  -- Pegden-Smart's Proposition 2.5 for `-u` on `B_ρ(x)`
  have hvol := hPS (fun y => -u y) (fun y => -s y) x ρ C hρ0
    (hucont.mono fun y hy => (hsubU hy).1).neg hsm.neg
    (fun y => (abs_neg (s y)).le.trans (hsC y))
    (isWeakSolutionLaplace_neg' (isWeakSolutionLaplace_mono hws (ball_subset_ball hρ4.le)))
    (-(fderiv ℝ φ x)) (-(H + (4 * ε) • (1 : Matrix (Fin 2) (Fin 2) ℝ))) hH's.neg
    (fun y hy => by
      rw [mem_sphere, dist_eq_norm] at hy
      have h1 := hle y hy.le
      rw [hy] at h1
      have h3 : 0 < ε * ρ ^ 2 := by positivity
      rw [neg_apply, qM_neg_mat]
      linarith)
  obtain ⟨b, hbB, p, Y, hY, hTY, hpd⟩ := nonempty_of_measure_ne_zero hvol.ne'
  have hTu := hasSecondOrderTaylorAt_of_neg hTY
  have hXle : (H + (4 * ε) • (1 : Matrix (Fin 2) (Fin 2) ℝ) - -Y).PosSemidef := by
    have e : Y - -(H + (4 * ε) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) =
        H + (4 * ε) • (1 : Matrix (Fin 2) (Fin 2) ℝ) - -Y := by abel
    rw [e] at hpd
    exact hpd.posSemidef
  -- `F*(D²u(b)) ≥ F*(D²φ(x) + 4εI) = F*(D²φ(x)) - 8ε > 0`, against `ssPeanoStar`
  have hF1 := degenerateElliptic_effOpStar hd1 E hE (-Y) _ hY.neg hH's hXle
  have hF2 := effOpStar_add_smul_one hd1 E hE hH (4 * ε)
  have hF3 := hpeano u ⟨nk, hnk, hconvu⟩ b (-p) (-Y) (hsubU (ball_subset_closedBall hbB)).1
    (hsubU (ball_subset_closedBall hbB)).2 hY.neg hTu
  rw [hF2] at hF1
  linarith

end SingleSourceD2

end RandomSandpile
