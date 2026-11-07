import RandomSandpile.Draft.Section7
import LatticeProb.Walk.SRWPos

/-!
# Steps of Lemma 7.2 (compactness of the rescaled free odometers)

Carving of `RandomSandpile.CompactnessStmt` (Lemma 7.2, `paper/random_piles-corrected.tex`) into four steps and the reduction `compactness_of_steps`.

The printed proof has three moves.

* **Upper bound and support**. Cover `W_n` by the cube `|x|_∞ ≤ ℓ`, `ℓ = O(n)`,
  take `g` from Lemma 7.1 and `u_i(x) = g(x_i)`; then `Δ u_i + η_max 𝟙_{W_n} ≤ 2d - 1` (this uses
  `d ≥ 2`, since `f ≤ 2` off the cube), so each `u_i` is a stabilizing toppling function, and by
  the least action principle `v_n ≤ min_i u_i`. With the [C5] bound `g ≤ C_r (ℓ + 1)²` this gives
  `v_n ≤ C (n + 1)²` and `v_n = 0` off a cube of side `O(n)`. Step `FreeOdometerUpperBoundStmt`.
* **Bounded Laplacian**. `|Δ_{ℤ^d} v_n| ≤ C_{d, η_min, η_max}`: the upper bound is the
  stabilizing inequality, the lower bound is the minimality of `v_n` (where `v_n ≥ 1`, removing one
  toppling at `x` must break the stabilizing inequality at `x`). Step
  `FreeOdometerLapBoundStmt`.
* **Equicontinuity and Arzelà–Ascoli**. The paper cites Kuo–Trudinger
  (*Estimates for solutions of fully nonlinear discrete schemes*, 2005) for equicontinuity of
  `v̄_n`. The argument used here is the discrete interior gradient (Lipschitz) estimate for a
  finitely supported function with bounded Laplacian, obtained from the Green representation
  `u = P^m u - (2d)⁻¹ ∑_y g_m(· - y) Δu(y)` and the gradient bound
  `|∇ g_m(z)| ≤ C (1 + |z|)^{1-d}` of the truncated Green function, uniform in `m`
  (`LatticeProb.exists_srwGreen_gradient`, `d ≥ 2`): for `u` supported in a cube of side `O(R)`
  with `|Δ u| ≤ M`, `|∇ u| ≤ C M (R + 1)`. Step `LapGradientBoundStmt`. With `R = O(n)` it makes
  `v̄_n` Lipschitz at scales `≥ 1/n` uniformly in `n`:
  `|v̄_n(x) - v̄_n(y)| ≤ L (|x - y| + 1/n)`. Since `v̄_n` is a step function (the floor
  `latticeRound` of `rescaleOdo`), only this *asymptotic* equicontinuity holds, and the
  Arzelà–Ascoli theorem is used in the form `AsymptoticArzelaAscoliStmt`.

The reduction also uses the elementary facts proved below: a lattice function with
nearest-neighbour increments `≤ G` is `G`-Lipschitz for the `ℓ¹` distance
(`abs_sub_le_of_unit_increment`), and the rescaling arithmetic of `rescaleOdo`.
-/

noncomputable section

open Filter Topology LatticeProb LatticeProb.Sandpile

namespace RandomSandpile

/-- **Step: upper bound and support of the free odometer**. For `d ≥ 2`, a
bounded `W` and an upper bound `η_max`, there are `C` and `R₀` such that for every `η ≤ η_max` and
every `n`, the class of stabilizing toppling functions of `η 𝟙_{W_n}` on `ℤ^d` is nonempty, and the
free odometer `v_n` satisfies `v_n ≤ C (n + 1)²` and vanishes off the open cube
`{|x|_∞ < R₀ (n + 1)}`. -/
def FreeOdometerUpperBoundStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ W : Set (Rd d), Bornology.IsBounded W → ∀ ηmax : ℤ,
    ∃ C : ℝ, ∃ R₀ : ℕ, ∀ η : Site d → ℤ, (∀ x, η x ≤ ηmax) → ∀ n : ℕ,
      (stabilizing ((discretize W n).indicator η) Set.univ).Nonempty ∧
      (∀ x, (freeOdometer η (discretize W n) x : ℝ) ≤ C * ((n : ℝ) + 1) ^ 2) ∧
      ∀ x : Site d, (∃ i, (R₀ : ℤ) * ((n : ℤ) + 1) ≤ |x i|) →
        freeOdometer η (discretize W n) x = 0

/-- **Step: the Laplacian of the free odometer is bounded** ("`|Δ_{ℤ^d} v_n| ≤
C_{d, η_min, η_max}`"). Whenever the class of stabilizing toppling functions is nonempty,
`|Δ_{ℤ^d} v| ≤ 2d + |η_min| + |η_max|` for the free odometer `v` of `η 𝟙_{W_n}`, for every lattice
domain `W_n`. -/
def FreeOdometerLapBoundStmt : Prop :=
  ∀ (d : ℕ) (ηmin ηmax : ℤ) (η : Site d → ℤ) (Wn : Set (Site d)),
    (∀ x, ηmin ≤ η x ∧ η x ≤ ηmax) → (stabilizing (Wn.indicator η) Set.univ).Nonempty →
      ∀ x, |lap (freeOdometer η Wn) x| ≤ 2 * (d : ℤ) + |ηmin| + |ηmax|

/-- **Step: discrete gradient estimate from a bounded Laplacian** (the regularity input, cited there to Kuo–Trudinger 2005). For `d ≥ 2` there is `C > 0` such that every
`u : ℤ^d → ℤ` vanishing off the open cube `{|x|_∞ < R}` with `|Δ_{ℤ^d} u| ≤ M` has nearest-neighbour
increments `|u(x + e_i) - u(x)| ≤ C M (R + 1)`. -/
def LapGradientBoundStmt : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∃ C : ℝ, 0 < C ∧ ∀ (u : Site d → ℤ) (M : ℝ) (R : ℕ),
    (∀ x : Site d, (∃ i, (R : ℤ) ≤ |x i|) → u x = 0) → (∀ x, |(lap u x : ℝ)| ≤ M) →
      ∀ (x : Site d) (i : Fin d), |(u (x + unit i) : ℝ) - u x| ≤ C * M * ((R : ℝ) + 1)

/-- **Step: the Arzelà–Ascoli theorem for asymptotically equicontinuous sequences**
. A sequence `F_n : ℝ^d → ℝ` that is uniformly bounded, vanishes off a fixed ball, and
is equicontinuous up to an error `e_n → 0`
(`|F_n(x) - F_n(y)| ≤ L |x - y| + e_n`) has a subsequence converging uniformly on `ℝ^d` to a
continuous function. -/
def AsymptoticArzelaAscoliStmt : Prop :=
  ∀ (d : ℕ) (F : ℕ → Rd d → ℝ) (K L ρ : ℝ) (e : ℕ → ℝ),
    (∀ n x, |F n x| ≤ K) → (∀ n x, ρ < ‖x‖ → F n x = 0) →
    (∀ n x y, |F n x - F n y| ≤ L * dist x y + e n) → Tendsto e atTop (𝓝 0) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ vbar : Rd d → ℝ, Continuous vbar ∧
        TendstoUniformly (fun j => F (φ j)) vbar atTop

/-! ### Elementary lemmas of the reduction -/

/-- A lattice function whose nearest-neighbour increments are bounded by `G` is `G`-Lipschitz for
the graph (`ℓ¹`) distance. -/
theorem abs_sub_le_of_unit_increment {d : ℕ} {u : Site d → ℝ} {G : ℝ}
    (hG : ∀ x i, |u (x + unit i) - u x| ≤ G) (a b : Site d) :
    |u a - u b| ≤ G * graphNorm (a - b) := by
  suffices h : ∀ N : ℕ, ∀ a b : Site d, graphNorm (a - b) = N → |u a - u b| ≤ G * N from
    h _ a b rfl
  intro N
  induction N with
  | zero =>
    intro a b h
    rw [graphNorm_eq_zero_iff, sub_eq_zero] at h
    subst h; simp
  | succ N ih =>
    intro a b h
    have hne : a - b ≠ 0 := by
      intro h0; rw [h0] at h; simp [graphNorm] at h
    obtain ⟨c, hc⟩ := exists_dirVec_graphNorm_eq_sub_one hne
    have h' : graphNorm (a + dirVec c - b) = N := by
      rw [show a + dirVec c - b = a - b + dirVec c by abel, hc, h]; rfl
    have hstep : |u a - u (a + dirVec c)| ≤ G := by
      obtain ⟨i, s⟩ := c
      cases s
      · rw [dirVec_eq_neg_unit]
        have := hG (a + -unit i) i
        rwa [show a + -unit i + unit i = a by abel] at this
      · rw [dirVec_eq_unit, abs_sub_comm]; exact hG a i
    calc |u a - u b| ≤ |u a - u (a + dirVec c)| + |u (a + dirVec c) - u b| := abs_sub_le _ _ _
      _ ≤ G + G * N := add_le_add hstep (ih _ _ h')
      _ = G * ((N + 1 : ℕ) : ℝ) := by push_cast; ring

/-- The graph distance between the lattice points `[n x]` and `[n y]` is at most
`d (n |x - y| + 1)`. -/
theorem graphNorm_latticeRound_sub_le {d : ℕ} (n : ℕ) (x y : Rd d) :
    (graphNorm (latticeRound ((n : ℝ) • x) - latticeRound ((n : ℝ) • y)) : ℝ) ≤
      d * (n * ‖x - y‖ + 1) := by
  have hcoord : ∀ i, |((⌊(n : ℝ) * x i⌋ - ⌊(n : ℝ) * y i⌋ : ℤ) : ℝ)| ≤ n * ‖x - y‖ + 1 := by
    intro i
    have h1 := Int.floor_le ((n : ℝ) * x i)
    have h2 := Int.lt_floor_add_one ((n : ℝ) * x i)
    have h3 := Int.floor_le ((n : ℝ) * y i)
    have h4 := Int.lt_floor_add_one ((n : ℝ) * y i)
    have hxy : |x i - y i| ≤ ‖x - y‖ := by
      have := PiLp.norm_apply_le (x - y) i
      simpa [Real.norm_eq_abs] using this
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hm : |(n : ℝ) * x i - n * y i| ≤ n * ‖x - y‖ := by
      rw [← mul_sub, abs_mul, abs_of_nonneg hn]
      exact mul_le_mul_of_nonneg_left hxy hn
    rw [abs_le] at hm ⊢
    push_cast
    constructor <;> linarith [hm.1, hm.2]
  simp only [graphNorm, Nat.cast_sum]
  calc ∑ i, (((latticeRound ((n : ℝ) • x) - latticeRound ((n : ℝ) • y)) i).natAbs : ℝ)
      = ∑ i, |((⌊(n : ℝ) * x i⌋ - ⌊(n : ℝ) * y i⌋ : ℤ) : ℝ)| := by
        refine Finset.sum_congr rfl fun i _ => ?_
        simp [latticeRound, Nat.cast_natAbs]
    _ ≤ ∑ _i : Fin d, ((n : ℝ) * ‖x - y‖ + 1) := Finset.sum_le_sum fun i _ => hcoord i
    _ = d * (n * ‖x - y‖ + 1) := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- Far from the origin the rescaled lattice point leaves the cube `{|z|_∞ < R₀ (n + 1)}`: if
`d (2R₀ + 1) < |x|` and `n ≥ 1`, then `R₀ (n + 1) ≤ |[n x]_i|` for some `i`. -/
theorem exists_le_abs_latticeRound {d : ℕ} {n : ℕ} (hn : 1 ≤ n) (R₀ : ℕ) {x : Rd d}
    (hx : (d : ℝ) * (2 * R₀ + 1) < ‖x‖) :
    ∃ i, (R₀ : ℤ) * ((n : ℤ) + 1) ≤ |latticeRound ((n : ℝ) • x) i| := by
  by_contra hcon
  push Not at hcon
  have hsmall : ∀ i, |x i| ≤ 2 * R₀ + 1 := by
    intro i
    by_contra hi
    push Not at hi
    have h1 := Int.floor_le ((n : ℝ) * x i)
    have h2 := Int.lt_floor_add_one ((n : ℝ) * x i)
    have hlt := hcon i
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hR : (0 : ℝ) ≤ R₀ := Nat.cast_nonneg R₀
    have hlt' : |((⌊(n : ℝ) * x i⌋ : ℤ) : ℝ)| < (R₀ : ℝ) * ((n : ℝ) + 1) := by
      have : |⌊(n : ℝ) * x i⌋| < (R₀ : ℤ) * ((n : ℤ) + 1) := by simpa [latticeRound] using hlt
      exact_mod_cast this
    rw [abs_lt] at hlt'
    rcases le_or_gt 0 (x i) with h0 | h0
    · rw [abs_of_nonneg h0] at hi
      nlinarith
    · rw [abs_of_neg h0] at hi
      nlinarith
  have hnorm : ‖x‖ ≤ ∑ i, |x i| := by
    rw [EuclideanSpace.norm_eq]
    rw [Real.sqrt_le_left (Finset.sum_nonneg fun i _ => abs_nonneg _)]
    calc ∑ i, ‖x i‖ ^ 2 = ∑ i, |x i| ^ 2 := by simp [Real.norm_eq_abs]
      _ ≤ (∑ i, |x i|) ^ 2 := Finset.sum_sq_le_sq_sum_of_nonneg fun i _ => abs_nonneg _
  have : ∑ i, |x i| ≤ (d : ℝ) * (2 * R₀ + 1) := by
    calc ∑ i, |x i| ≤ ∑ _i : Fin d, ((2 : ℝ) * R₀ + 1) := Finset.sum_le_sum fun i _ => hsmall i
      _ = (d : ℝ) * (2 * R₀ + 1) := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  linarith

/-! ### The reduction -/

/-- **Lemma 7.2 from its steps.** -/
theorem compactness_of_steps (hUB : FreeOdometerUpperBoundStmt) (hLap : FreeOdometerLapBoundStmt)
    (hGrad : LapGradientBoundStmt) (hAA : AsymptoticArzelaAscoliStmt) : CompactnessStmt := by
  intro d hd W hW ηmin ηmax η hη
  obtain ⟨C, R₀, hC⟩ := hUB d hd W hW.1 ηmax
  have hC' := hC η fun x => (hη x).2
  refine ⟨fun n => (hC' n).1, ?_⟩
  intro nk hnk
  obtain ⟨Cg, hCg, hgrad⟩ := hGrad d hd
  set M : ℝ := 2 * d + |(ηmin : ℝ)| + |(ηmax : ℝ)| with hM
  have hM0 : 0 ≤ M := by positivity
  set v : ℕ → Site d → ℤ := fun n => freeOdometer η (discretize W n) with hv
  set F : ℕ → Rd d → ℝ := fun n => rescaleOdo (v n) n with hF
  set L : ℝ := Cg * M * (2 * R₀ + 1) * d with hL
  have hL0 : 0 ≤ L := by positivity
  -- nearest-neighbour increments of `v_n`
  have hinc : ∀ n x i, |((v n (x + unit i) : ℤ) : ℝ) - v n x| ≤
      Cg * M * (((R₀ * (n + 1) : ℕ) : ℝ) + 1) := by
    intro n
    refine hgrad (v n) M (R₀ * (n + 1)) (fun x hx => (hC' n).2.2 x (by push_cast at hx ⊢; exact hx))
      fun x => ?_
    have h := hLap d ηmin ηmax η (discretize W n) hη (hC' n).1 x
    have h' : (|lap (v n) x| : ℝ) ≤ ((2 * (d : ℤ) + |ηmin| + |ηmax| : ℤ) : ℝ) := by
      exact_mod_cast h
    simpa [hM] using h'
  -- bounds on the rescaled odometers
  have hbound : ∀ n x, |F n x| ≤ 4 * max C 0 := by
    intro n x
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hF, rescaleOdo]
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hv0 : (0 : ℝ) ≤ v n (latticeRound ((n : ℝ) • x)) := by
      exact_mod_cast freeOdometer_nonneg _ _ _
    have hvC := (hC' n).2.1 (latticeRound ((n : ℝ) • x))
    simp only [hF, rescaleOdo]
    rw [abs_of_nonneg (div_nonneg hv0 (by positivity)), div_le_iff₀ (by positivity)]
    calc (v n (latticeRound ((n : ℝ) • x)) : ℝ) ≤ C * ((n : ℝ) + 1) ^ 2 := hvC
      _ ≤ max C 0 * ((n : ℝ) + 1) ^ 2 := by gcongr; exact le_max_left _ _
      _ ≤ max C 0 * (4 * (n : ℝ) ^ 2) := by gcongr; nlinarith
      _ = 4 * max C 0 * (n : ℝ) ^ 2 := by ring
  have hsupp : ∀ n x, (d : ℝ) * (2 * R₀ + 1) < ‖x‖ → F n x = 0 := by
    intro n x hx
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hF, rescaleOdo]
    simp only [hF, rescaleOdo]
    rw [show v n (latticeRound ((n : ℝ) • x)) = 0 from
      (hC' n).2.2 _ (exists_le_abs_latticeRound hn R₀ hx)]; simp
  have hequi : ∀ n x y, |F n x - F n y| ≤ L * dist x y + L / n := by
    intro n x y
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hF, rescaleOdo]; positivity
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hlip := abs_sub_le_of_unit_increment (u := fun z => ((v n z : ℤ) : ℝ)) (hinc n)
      (latticeRound ((n : ℝ) • x)) (latticeRound ((n : ℝ) • y))
    have hgn := graphNorm_latticeRound_sub_le n x y
    have hG : Cg * M * (((R₀ * (n + 1) : ℕ) : ℝ) + 1) ≤ Cg * M * (2 * R₀ + 1) * n := by
      have hR : (0 : ℝ) ≤ R₀ := Nat.cast_nonneg R₀
      have hCM : 0 ≤ Cg * M := by positivity
      push_cast
      have : (R₀ : ℝ) * (n + 1) + 1 ≤ (2 * R₀ + 1) * n := by nlinarith
      calc Cg * M * ((R₀ : ℝ) * (n + 1) + 1) ≤ Cg * M * ((2 * R₀ + 1) * n) :=
            mul_le_mul_of_nonneg_left this hCM
        _ = Cg * M * (2 * R₀ + 1) * n := by ring
    have hnpos : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
    simp only [hF, rescaleOdo]
    rw [← sub_div, abs_div, abs_of_pos hnpos, div_le_iff₀ hnpos, dist_eq_norm]
    have hGn : 0 ≤ (graphNorm (latticeRound ((n : ℝ) • x) - latticeRound ((n : ℝ) • y)) : ℝ) :=
      Nat.cast_nonneg _
    calc |(v n (latticeRound ((n : ℝ) • x)) : ℝ) - v n (latticeRound ((n : ℝ) • y))|
        ≤ Cg * M * (((R₀ * (n + 1) : ℕ) : ℝ) + 1) *
            graphNorm (latticeRound ((n : ℝ) • x) - latticeRound ((n : ℝ) • y)) := hlip
      _ ≤ (Cg * M * (2 * R₀ + 1) * n) * (d * (n * ‖x - y‖ + 1)) := by
          apply mul_le_mul hG hgn hGn; positivity
      _ = (L * ‖x - y‖ + L / n) * (n : ℝ) ^ 2 := by
          rw [hL]; field_simp
  obtain ⟨φ, hφ, vbar, hvbar, hconv⟩ :=
    hAA d (fun j => F (nk j)) (4 * max C 0) L ((d : ℝ) * (2 * R₀ + 1)) (fun j => L / nk j)
      (fun j x => hbound _ x) (fun j x hx => hsupp _ x hx) (fun j x y => hequi _ x y)
      ((tendsto_const_div_atTop_nhds_zero_nat L).comp hnk.tendsto_atTop)
  exact ⟨φ, hφ, vbar, hvbar, hconv⟩

end RandomSandpile
