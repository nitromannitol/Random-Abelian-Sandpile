import RandomSandpile.Steps.Sec7.DivisibleHomogenize

/-!
# Deterministic homogenization of the Green potential (Lemma 7.3)

Proof of `GreenHomogenizeStmt` from the Green's function estimates (exit_time)
(`GreenBallExitTimeStmt`), the boundary layer bound (`GreenBallBoundaryLayerStmt`) and the summed
(difference) estimate (`GreenBallGradientSumStmt`), .

Fix `ε > 0`, a boundary width `δ`, and a dyadic scale `β = 2^{-j}` with `√d β ≤ δ`. For
`x ∈ B_n`, `n ≥ 2/β`, split `B_n` along the dyadic cubes `Q_k = Q_{j,k}(n)` (`dyadicCube`,
the pieces `A_{βn}(z_i)`); `κ(y)` (`cubeIndex`) is the index of the cube
containing `y`, and the indices range over the finite set `[-2^j, 2^j]^d` (`cubeIndexSet`).

* A cube is *good* if it lies in `B_{(1-δ)n}`. A point of a bad cube is at distance at most
  `√d βn ≤ δn` from a point outside `B_{(1-δ)n}`, so it lies in the layer `|y| ≥ (1-2δ)n`, whose
  contribution is at most `K ∑_{|y| ≥ (1-2δ)n} g_n(x, y)`.
* In a good cube `Q`, write `g = g_n(x, ·)`, `a_Q = |Q|⁻¹ ∑_Q g` (the pooling
  value; the paper pools at a point `z_i`) and
  `∑_Q g f = a_Q ∑_Q f + ∑_Q (g - a_Q) f`. The first term is at most
  `(∑_Q g) θ (2/β)^d` when `|∑_Q f| ≤ θ n^d` (from (ergodic), since `|Q| ≥ (βn/2)^d`); the
  second is at most `K 2^d d (2βn) ∑_Q |∇g|` by the discrete Poincaré inequality on boxes
  (`BoxPoincare`), so the good cubes contribute `θ (2/β)^d ∑_{B_n} g + C K βn ∑_{B_{(1-δ)n}} |∇g|`
  (`abs_sum_le_cubes`).
* With (exit_time), the boundary layer bound and the summed (difference) estimate, this is
  `≤ (θ (2/β)^d + C K C_δ β + C K δ) n²` (the rearrangement error is `C β n²`); for
  `|x| ≥ (1-δ)n` the bound `K ∑_{B_n} g_n(x, ·) ≤ K ((n+1)² - |x|²)/(2d) ≤ C K δ n²` suffices
.

The Poincaré inequality is a hypothesis `BoxPoincare d` of `greenHomogenize_of_poincare`;
it is proved in `Proofs/Sec7/DivisibleHomogenizePoincare.lean`.
-/

noncomputable section

open LatticeProb Filter Topology

namespace RandomSandpile

variable {d : ℕ}

namespace DivisibleHomogenize

open OdometerLowerBound

/-! ### Lattice geometry -/

/-- `|x_i| ≤ |x|`. -/
theorem abs_coord_le_norm (x : Site d) (i : Fin d) : |(x i : ℝ)| ≤ ‖toE x‖ := by
  have h := PiLp.norm_apply_le (toE x) i
  simpa [Real.norm_eq_abs] using h

/-- `|x| ≤ √d s` if every coordinate satisfies `|x_i| ≤ s`. -/
theorem norm_toE_le_sqrt_mul (x : Site d) {s : ℝ} (hs : 0 ≤ s) (h : ∀ i, |(x i : ℝ)| ≤ s) :
    ‖toE x‖ ≤ Real.sqrt d * s := by
  rw [EuclideanSpace.norm_eq, ← Real.sqrt_sq hs, ← Real.sqrt_mul (Nat.cast_nonneg d)]
  apply Real.sqrt_le_sqrt
  calc ∑ i, ‖toE x i‖ ^ 2 ≤ ∑ _i : Fin d, s ^ 2 := Finset.sum_le_sum fun i _ => by
        simpa [Real.norm_eq_abs, sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (h i) 2
    _ = d * s ^ 2 := by simp

/-! ### Dyadic cubes -/

theorem mem_dyadicCube {j : ℕ} {k y : Site d} {N : ℕ} :
    y ∈ dyadicCube j k N ↔
      ∀ i, (N : ℝ) * ((k i : ℝ) / 2 ^ j) ≤ y i ∧ (y i : ℝ) < N * (((k i : ℝ) + 1) / 2 ^ j) := by
  simp only [dyadicCube, rectBox, Fintype.mem_piFinset, Finset.mem_Ico, Int.ceil_le, Int.lt_ceil]

/-- The index `κ(y) = ⌊2^j y / n⌋` of the dyadic cube `Q_{j,κ(y)}(n)` containing `y`. -/
def cubeIndex (j n : ℕ) (y : Site d) : Site d := fun i => ⌊(y i : ℝ) * 2 ^ j / n⌋

theorem mem_dyadicCube_iff_cubeIndex {j n : ℕ} (hn : 0 < n) {k y : Site d} :
    y ∈ dyadicCube j k n ↔ cubeIndex j n y = k := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h2 : (0 : ℝ) < 2 ^ j := by positivity
  rw [mem_dyadicCube, funext_iff]
  refine forall_congr' fun i => ?_
  simp only [cubeIndex]
  rw [Int.floor_eq_iff, le_div_iff₀ hn', div_lt_iff₀ hn']
  have e1 : (n : ℝ) * ((k i : ℝ) / 2 ^ j) ≤ y i ↔ (k i : ℝ) * n ≤ y i * 2 ^ j := by
    rw [← mul_div_assoc, div_le_iff₀ h2]; constructor <;> intro h <;> linarith
  have e2 : (y i : ℝ) < n * (((k i : ℝ) + 1) / 2 ^ j) ↔ y i * 2 ^ j < ((k i : ℝ) + 1) * n := by
    rw [← mul_div_assoc, lt_div_iff₀ h2]; constructor <;> intro h <;> linarith
  rw [e1, e2]

/-- A side of a dyadic cube has at least `βn/2` sites when `βn ≥ 2` (`β = 2^{-j}`). -/
theorem side_ge {n j : ℕ} (hn : 2 * 2 ^ j ≤ (n : ℝ)) (a : ℝ) :
    (n : ℝ) / (2 * 2 ^ j) ≤
      ((Finset.Ico ⌈(n : ℝ) * (a / 2 ^ j)⌉ ⌈(n : ℝ) * ((a + 1) / 2 ^ j)⌉).card : ℝ) := by
  rw [Int.card_Ico]
  have h2j : (0 : ℝ) < 2 ^ j := by positivity
  have h1 := Int.le_ceil ((n : ℝ) * ((a + 1) / 2 ^ j))
  have h2 := Int.ceil_lt_add_one ((n : ℝ) * (a / 2 ^ j))
  have h3 : (((⌈(n : ℝ) * ((a + 1) / 2 ^ j)⌉ - ⌈(n : ℝ) * (a / 2 ^ j)⌉ : ℤ)) : ℝ) ≤
      ((⌈(n : ℝ) * ((a + 1) / 2 ^ j)⌉ - ⌈(n : ℝ) * (a / 2 ^ j)⌉).toNat : ℝ) := by
    exact_mod_cast Int.self_le_toNat _
  have e : (n : ℝ) * ((a + 1) / 2 ^ j) = n * (a / 2 ^ j) + n / 2 ^ j := by ring
  have e2 : (n : ℝ) / (2 * 2 ^ j) = (n / 2 ^ j) / 2 := by ring
  have hn2 : 2 ≤ (n : ℝ) / 2 ^ j := by rw [le_div_iff₀ h2j]; linarith
  push_cast at h3
  linarith

/-- A side of a dyadic cube has at most `2βn` sites when `βn ≥ 1`. -/
theorem side_le {n j : ℕ} (hn : 2 ^ j ≤ (n : ℝ)) (a : ℝ) :
    (((⌈(n : ℝ) * ((a + 1) / 2 ^ j)⌉ - ⌈(n : ℝ) * (a / 2 ^ j)⌉ : ℤ)) : ℝ) ≤ 2 * n / 2 ^ j := by
  have h2j : (0 : ℝ) < 2 ^ j := by positivity
  have h1 := Int.ceil_lt_add_one ((n : ℝ) * ((a + 1) / 2 ^ j))
  have h2 := Int.le_ceil ((n : ℝ) * (a / 2 ^ j))
  have e : (n : ℝ) * ((a + 1) / 2 ^ j) = n * (a / 2 ^ j) + n / 2 ^ j := by ring
  have e2 : 2 * (n : ℝ) / 2 ^ j = 2 * (n / 2 ^ j) := by ring
  have hn1 : 1 ≤ (n : ℝ) / 2 ^ j := by rw [le_div_iff₀ h2j]; linarith
  push_cast
  linarith

/-- `|Q_{j,k}(n)| ≥ (βn/2)^d` when `βn ≥ 2`. -/
theorem card_dyadicCube_ge {n j : ℕ} (hn : 2 * 2 ^ j ≤ (n : ℝ)) (k : Site d) :
    ((n : ℝ) / (2 * 2 ^ j)) ^ d ≤ ((dyadicCube j k n).card : ℝ) := by
  rw [dyadicCube, rectBox, Fintype.card_piFinset, Nat.cast_prod]
  calc ((n : ℝ) / (2 * 2 ^ j)) ^ d = ∏ _i : Fin d, ((n : ℝ) / (2 * 2 ^ j)) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ ≤ _ := Finset.prod_le_prod (fun _ _ => by positivity) fun i _ => side_ge hn (k i : ℝ)

/-- Two points of a dyadic cube differ by less than `βn` in each coordinate. -/
theorem abs_sub_le_of_mem_dyadicCube {j n : ℕ} {k y y' : Site d} (hy : y ∈ dyadicCube j k n)
    (hy' : y' ∈ dyadicCube j k n) (i : Fin d) : |((y' - y) i : ℝ)| ≤ n / 2 ^ j := by
  rw [mem_dyadicCube] at hy hy'
  obtain ⟨a1, a2⟩ := hy i
  obtain ⟨b1, b2⟩ := hy' i
  have e : (n : ℝ) * (((k i : ℝ) + 1) / 2 ^ j) = n * ((k i : ℝ) / 2 ^ j) + n / 2 ^ j := by ring
  rw [Pi.sub_apply, Int.cast_sub, abs_le]
  constructor <;> linarith

/-- The diameter of a dyadic cube is at most `√d βn`. -/
theorem norm_sub_le_of_mem_dyadicCube {j n : ℕ} {k y y' : Site d} (hy : y ∈ dyadicCube j k n)
    (hy' : y' ∈ dyadicCube j k n) : ‖toE y' - toE y‖ ≤ Real.sqrt d * ((n : ℝ) / 2 ^ j) := by
  rw [← toE_sub]
  exact norm_toE_le_sqrt_mul _ (by positivity) (abs_sub_le_of_mem_dyadicCube hy hy')

/-- The finite set of cube indices `[-2^j, 2^j]^d`; it contains `κ(y)` for every `y ∈ B_n`. -/
def cubeIndexSet (d j : ℕ) : Finset (Site d) :=
  Fintype.piFinset fun _ => Finset.Icc (-(2 : ℤ) ^ j) (2 ^ j)

theorem cubeIndex_mem {j n : ℕ} (hn : 0 < n) {y : Site d} (hy : ‖toE y‖ < n) :
    cubeIndex j n y ∈ cubeIndexSet d j := by
  rw [cubeIndexSet, Fintype.mem_piFinset]
  intro i
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h2 : (0 : ℝ) < 2 ^ j := by positivity
  have hyi := (abs_coord_le_norm y i).trans_lt hy
  rw [abs_lt] at hyi
  simp only [cubeIndex, Finset.mem_Icc]
  constructor
  · rw [Int.le_floor, le_div_iff₀ hn']
    push_cast
    nlinarith
  · have h3 : (y i : ℝ) * 2 ^ j / n < 2 ^ j := by rw [div_lt_iff₀ hn']; nlinarith
    have h4 : ((⌊(y i : ℝ) * 2 ^ j / n⌋ : ℤ) : ℝ) < (2 : ℝ) ^ j :=
      lt_of_le_of_lt (Int.floor_le _) h3
    exact_mod_cast h4.le

/-! ### The rearrangement in one cube and over all cubes -/

/-- The discrete L¹ Poincaré inequality on lattice boxes `∏_i [l_i, u_i)` of side at most `L`:
`∑_Q |g - ⟨g⟩_Q| ≤ 2^d d L ∑_{q ∈ Q} ∑_i |g(q + e_i) - g(q)|`. -/
def BoxPoincare (d : ℕ) : Prop :=
  ∀ (l u : Fin d → ℤ) (L : ℝ), (∀ i, ((u i - l i : ℤ) : ℝ) ≤ L) → ∀ g : Site d → ℝ,
    ∑ y ∈ Fintype.piFinset (fun i => Finset.Ico (l i) (u i)),
        |g y - (∑ z ∈ Fintype.piFinset (fun i => Finset.Ico (l i) (u i)), g z) /
          ((Fintype.piFinset (fun i => Finset.Ico (l i) (u i))).card : ℝ)| ≤
      2 ^ d * d * L * ∑ q ∈ Fintype.piFinset (fun i => Finset.Ico (l i) (u i)),
        ∑ i : Fin d, |g (q + unit i) - g q|

/-- **One cube**: pooling the grains of `Q` at the mean value `⟨g⟩_Q` and
redistributing them. -/
theorem abs_sum_cube_le (hP : BoxPoincare d) {j n : ℕ} (hn : 2 * 2 ^ j ≤ (n : ℝ)) {θ K : ℝ}
    (hθ0 : 0 ≤ θ) (g f : Site d → ℝ) (hg : ∀ y, 0 ≤ g y) (hf : ∀ y, |f y| ≤ K) (k : Site d)
    (hθ : |∑ y ∈ dyadicCube j k n, f y| ≤ θ * (n : ℝ) ^ d) :
    |∑ y ∈ dyadicCube j k n, g y * f y| ≤
      θ * (2 * 2 ^ j) ^ d * ∑ y ∈ dyadicCube j k n, g y +
        K * (2 ^ d * d * (2 * n / 2 ^ j)) *
          ∑ q ∈ dyadicCube j k n, ∑ i : Fin d, |g (q + unit i) - g q| := by
  have h2j : (0 : ℝ) < 2 ^ j := by positivity
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le (by positivity) hn
  have hc0 : (0 : ℝ) < ((n : ℝ) / (2 * 2 ^ j)) ^ d := by positivity
  have hc := card_dyadicCube_ge (d := d) hn k
  set Q := dyadicCube j k n with hQ
  have hcpos : (0 : ℝ) < Q.card := hc0.trans_le hc
  set a := (∑ z ∈ Q, g z) / (Q.card : ℝ) with ha
  have hK : 0 ≤ K := (abs_nonneg _).trans (hf 0)
  have hsumg : 0 ≤ ∑ z ∈ Q, g z := Finset.sum_nonneg fun z _ => hg z
  have ha0 : 0 ≤ a := div_nonneg hsumg hcpos.le
  have hsplit : ∑ y ∈ Q, g y * f y = a * ∑ y ∈ Q, f y + ∑ y ∈ Q, (g y - a) * f y := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun y _ => by ring
  have h1 : |a * ∑ y ∈ Q, f y| ≤ θ * (2 * 2 ^ j) ^ d * ∑ y ∈ Q, g y := by
    rw [abs_mul, abs_of_nonneg ha0]
    have hθn : 0 ≤ θ * (n : ℝ) ^ d := by positivity
    calc a * |∑ y ∈ Q, f y| ≤ a * (θ * (n : ℝ) ^ d) := mul_le_mul_of_nonneg_left hθ ha0
      _ = (∑ z ∈ Q, g z) * (θ * (n : ℝ) ^ d) / Q.card := by rw [ha]; ring
      _ ≤ (∑ z ∈ Q, g z) * (θ * (n : ℝ) ^ d) / ((n : ℝ) / (2 * 2 ^ j)) ^ d :=
          div_le_div_of_nonneg_left (mul_nonneg hsumg hθn) hc0 hc
      _ = θ * (2 * 2 ^ j) ^ d * ∑ y ∈ Q, g y := by
          rw [div_pow]; field_simp
  have hn1 : 2 ^ j ≤ (n : ℝ) := by linarith
  have hPQ : ∑ y ∈ Q, |g y - a| ≤
      2 ^ d * d * (2 * n / 2 ^ j) * ∑ q ∈ Q, ∑ i : Fin d, |g (q + unit i) - g q| :=
    hP (fun i => ⌈(n : ℝ) * ((k i : ℝ) / 2 ^ j)⌉) (fun i => ⌈(n : ℝ) * (((k i : ℝ) + 1) / 2 ^ j)⌉)
      (2 * n / 2 ^ j) (fun i => side_le hn1 (k i : ℝ)) g
  have h2 : |∑ y ∈ Q, (g y - a) * f y| ≤
      K * (2 ^ d * d * (2 * n / 2 ^ j)) * ∑ q ∈ Q, ∑ i : Fin d, |g (q + unit i) - g q| := by
    calc |∑ y ∈ Q, (g y - a) * f y| ≤ ∑ y ∈ Q, |(g y - a) * f y| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ y ∈ Q, K * |g y - a| := Finset.sum_le_sum fun y _ => by
          rw [abs_mul, mul_comm]; exact mul_le_mul_of_nonneg_right (hf y) (abs_nonneg _)
      _ = K * ∑ y ∈ Q, |g y - a| := by rw [Finset.mul_sum]
      _ ≤ K * (2 ^ d * d * (2 * n / 2 ^ j) * ∑ q ∈ Q, ∑ i : Fin d, |g (q + unit i) - g q|) :=
          mul_le_mul_of_nonneg_left hPQ hK
      _ = _ := by ring
  rw [hsplit]
  exact (abs_add_le _ _).trans (add_le_add h1 h2)

/-- **All cubes**: the Green potential `∑_{B_n} g f` is bounded by the pooled
term, the rearrangement error and the boundary layer. -/
theorem abs_sum_le_cubes (hP : BoxPoincare d) {j n : ℕ} {δ θ K : ℝ}
    (g f : Site d → ℝ) (hg : ∀ y, 0 ≤ g y) (hf : ∀ y, |f y| ≤ K)
    (hn : 2 * 2 ^ j ≤ (n : ℝ)) (hδ0 : 0 ≤ δ) (hδ : Real.sqrt d * ((n : ℝ) / 2 ^ j) ≤ δ * n)
    (hθ0 : 0 ≤ θ) (hθ : ∀ k ∈ cubeIndexSet d j, |∑ y ∈ dyadicCube j k n, f y| ≤ θ * (n : ℝ) ^ d)
    (S Sδ : Finset (Site d)) (hS : ∀ y, y ∈ S ↔ ‖toE y‖ < n)
    (hSδ : ∀ y, y ∈ Sδ ↔ ‖toE y‖ < (1 - δ) * n) :
    |∑ y ∈ S, g y * f y| ≤
      θ * (2 * 2 ^ j) ^ d * ∑ y ∈ S, g y +
        K * (2 ^ d * d * (2 * n / 2 ^ j)) * ∑ y ∈ Sδ, ∑ i : Fin d, |g (y + unit i) - g y| +
          K * ∑ y ∈ S.filter (fun y => (1 - 2 * δ) * n ≤ ‖toE y‖), g y := by
  classical
  have hnR : (0 : ℝ) < n := lt_of_lt_of_le (by positivity) hn
  have hn0 : 0 < n := by exact_mod_cast hnR
  have hK : 0 ≤ K := (abs_nonneg _).trans (hf 0)
  set κ : Site d → Site d := cubeIndex j n with hκ
  set Gd : Site d → Prop := fun k => dyadicCube j k n ⊆ Sδ with hGd
  have hSδS : Sδ ⊆ S := fun y hy => (hS y).2 <| lt_of_lt_of_le ((hSδ y).1 hy) (by nlinarith)
  have hyκ : ∀ y, y ∈ dyadicCube j (κ y) n := fun y => (mem_dyadicCube_iff_cubeIndex hn0).2 rfl
  have hfib : ∀ F : Site d → ℝ, ∑ y ∈ S.filter (fun y => Gd (κ y)), F y =
      ∑ k ∈ (cubeIndexSet d j).filter Gd, ∑ y ∈ dyadicCube j k n, F y := by
    intro F
    rw [← Finset.sum_fiberwise_of_maps_to (s := S.filter (fun y => Gd (κ y)))
      (t := (cubeIndexSet d j).filter Gd) (g := κ) ?_ F]
    · refine Finset.sum_congr rfl fun k hk => Finset.sum_congr ?_ fun _ _ => rfl
      have hGk : Gd k := (Finset.mem_filter.1 hk).2
      ext y
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨_, hyk⟩
        exact (mem_dyadicCube_iff_cubeIndex hn0).2 hyk
      · intro hy
        have hyk : κ y = k := (mem_dyadicCube_iff_cubeIndex hn0).1 hy
        refine ⟨⟨hSδS (hGk hy), ?_⟩, hyk⟩
        rw [hyk]
        exact hGk
    · intro y hy
      obtain ⟨hyS, hG⟩ := Finset.mem_filter.1 hy
      exact Finset.mem_filter.2 ⟨cubeIndex_mem hn0 ((hS y).1 hyS), hG⟩
  have hsubδ : S.filter (fun y => Gd (κ y)) ⊆ Sδ := fun y hy => (Finset.mem_filter.1 hy).2 (hyκ y)
  have hbad : S.filter (fun y => ¬ Gd (κ y)) ⊆
      S.filter (fun y => (1 - 2 * δ) * n ≤ ‖toE y‖) := by
    intro y hy
    obtain ⟨hyS, hG⟩ := Finset.mem_filter.1 hy
    refine Finset.mem_filter.2 ⟨hyS, ?_⟩
    obtain ⟨y', hy'Q, hy'S⟩ := Finset.not_subset.1 hG
    have h1 : (1 - δ) * n ≤ ‖toE y'‖ := not_lt.1 fun h => hy'S ((hSδ y').2 h)
    have h2 := norm_sub_le_of_mem_dyadicCube (hyκ y) hy'Q
    have h3 := norm_sub_norm_le (toE y') (toE y)
    nlinarith
  have hc : 0 ≤ θ * (2 * 2 ^ j) ^ d := by positivity
  have hc' : 0 ≤ K * (2 ^ d * d * (2 * n / 2 ^ j)) := by positivity
  have hA : |∑ y ∈ S.filter (fun y => Gd (κ y)), g y * f y| ≤
      θ * (2 * 2 ^ j) ^ d * ∑ y ∈ S, g y +
        K * (2 ^ d * d * (2 * n / 2 ^ j)) * ∑ y ∈ Sδ, ∑ i : Fin d, |g (y + unit i) - g y| := by
    rw [hfib]
    calc _ ≤ ∑ k ∈ (cubeIndexSet d j).filter Gd, |∑ y ∈ dyadicCube j k n, g y * f y| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ (cubeIndexSet d j).filter Gd,
            (θ * (2 * 2 ^ j) ^ d * ∑ y ∈ dyadicCube j k n, g y +
              K * (2 ^ d * d * (2 * n / 2 ^ j)) *
                ∑ q ∈ dyadicCube j k n, ∑ i : Fin d, |g (q + unit i) - g q|) :=
          Finset.sum_le_sum fun k hk =>
            abs_sum_cube_le hP hn hθ0 g f hg hf k (hθ k (Finset.mem_filter.1 hk).1)
      _ = θ * (2 * 2 ^ j) ^ d * ∑ y ∈ S.filter (fun y => Gd (κ y)), g y +
            K * (2 ^ d * d * (2 * n / 2 ^ j)) *
              ∑ y ∈ S.filter (fun y => Gd (κ y)), ∑ i : Fin d, |g (y + unit i) - g y| := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hfib, hfib]
      _ ≤ _ := add_le_add
          (mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.filter_subset _ _) fun y _ _ => hg y) hc)
          (mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg hsubδ
            fun y _ _ => Finset.sum_nonneg fun i _ => abs_nonneg _) hc')
  have hB : |∑ y ∈ S.filter (fun y => ¬ Gd (κ y)), g y * f y| ≤
      K * ∑ y ∈ S.filter (fun y => (1 - 2 * δ) * n ≤ ‖toE y‖), g y := by
    calc _ ≤ ∑ y ∈ S.filter (fun y => ¬ Gd (κ y)), |g y * f y| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ y ∈ S.filter (fun y => ¬ Gd (κ y)), K * g y := Finset.sum_le_sum fun y _ => by
          rw [abs_mul, abs_of_nonneg (hg y), mul_comm]
          exact mul_le_mul_of_nonneg_right (hf y) (hg y)
      _ = K * ∑ y ∈ S.filter (fun y => ¬ Gd (κ y)), g y := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum_of_subset_of_nonneg hbad fun y _ _ => hg y) hK
  rw [← Finset.sum_filter_add_sum_filter_not S (fun y => Gd (κ y))]
  calc _ ≤ |∑ y ∈ S.filter (fun y => Gd (κ y)), g y * f y| +
        |∑ y ∈ S.filter (fun y => ¬ Gd (κ y)), g y * f y| := abs_add_le _ _
    _ ≤ _ := by linarith [hA, hB]

/-! ### Arithmetic for the choice of constants -/

theorem arith_exit {n D x2 : ℝ} (hx2 : 0 ≤ x2) (hn1 : 1 ≤ n) (hD : 2 ≤ D) :
    (n + 1) ^ 2 - x2 ≤ n ^ 2 * (2 * D) := by
  nlinarith [mul_le_mul_of_nonneg_right hD (sq_nonneg n)]

theorem arith_layer {n D δ : ℝ} (hn1 : 1 ≤ n) (hD : 2 ≤ D) (hδ : 0 < δ)
    (h3 : 3 * n ≤ δ * n ^ 2) : (n + 1) ^ 2 - ((1 - 2 * δ) * n) ^ 2 ≤ 2 * δ * n ^ 2 * (2 * D) := by
  have hδn : 0 ≤ δ * n ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hD hδn, sq_nonneg (δ * n)]

theorem arith_bdry {n D δ x2 : ℝ} (hn1 : 1 ≤ n) (hD : 2 ≤ D) (hδ : 0 < δ)
    (h3 : 3 * n ≤ δ * n ^ 2) (hx : ((1 - δ) * n) ^ 2 ≤ x2) :
    (n + 1) ^ 2 - x2 ≤ δ * n ^ 2 * (2 * D) := by
  have hδn : 0 ≤ δ * n ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hD hδn, sq_nonneg (δ * n)]

end DivisibleHomogenize

open DivisibleHomogenize OdometerLowerBound

/-- **Deterministic homogenization** from (exit_time), the boundary layer bound,
the summed (difference) estimate and the Poincaré inequality on boxes. Constants: `δ =
min(1/4, ε / (16 (K + 1)))`, `2^j > max(√d / δ, 8 K 2^d d C_δ / ε)`, `θ = ε / (4 (2^{j+1})^d)`. -/
theorem greenHomogenize_of_poincare (hP : ∀ d, BoxPoincare d) (hExit : GreenBallExitTimeStmt)
    (hLayer : GreenBallBoundaryLayerStmt) (hGrad : GreenBallGradientSumStmt) :
    GreenHomogenizeStmt := by
  intro d hd f K hf hcube ε hε
  have hd1 : 1 ≤ d := by omega
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hK : 0 ≤ K := (abs_nonneg _).trans (hf 0)
  set δ : ℝ := min (1 / 4) (ε / (16 * (K + 1))) with hδdef
  have hδ0 : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ14 : δ ≤ 1 / 4 := min_le_left _ _
  have hδK : K * δ ≤ ε / 16 := by
    have h1 : δ ≤ ε / (16 * (K + 1)) := min_le_right _ _
    have h2 : K * δ ≤ K * (ε / (16 * (K + 1))) := mul_le_mul_of_nonneg_left h1 hK
    have h3 : K * (ε / (16 * (K + 1))) ≤ ε / 16 := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    linarith
  obtain ⟨C, hC0, hC⟩ := hGrad d hd δ hδ0 (by linarith)
  obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt
    (max (Real.sqrt d / δ) (8 * K * 2 ^ d * d * C / ε)) (by norm_num : (1 : ℝ) < 2)
  have h2j : (0 : ℝ) < 2 ^ j := by positivity
  have hj1 : Real.sqrt d ≤ δ * 2 ^ j := by
    have := (le_max_left _ _).trans_lt hj
    rw [div_lt_iff₀ hδ0] at this
    linarith
  have hj2 : 8 * K * 2 ^ d * d * C ≤ ε * 2 ^ j := by
    have := (le_max_right _ _).trans_lt hj
    rw [div_lt_iff₀ hε] at this
    linarith
  set θ : ℝ := ε / (4 * (2 * 2 ^ j) ^ d) with hθdef
  have hθ0 : 0 < θ := by positivity
  have hθe : θ * (2 * 2 ^ j) ^ d = ε / 4 := by rw [hθdef]; field_simp
  have hev : ∀ᶠ N : ℕ in atTop, ∀ k ∈ cubeIndexSet d j,
      |(∑ y ∈ dyadicCube j k N, f y) / (N : ℝ) ^ d| < θ := by
    rw [Filter.eventually_all_finset]
    intro k _
    have h := (hcube j k).abs
    rw [abs_zero] at h
    exact h.eventually (gt_mem_nhds hθ0)
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 hev
  refine ⟨max N₀ (max (2 * 2 ^ j) ⌈3 / δ⌉₊), fun n hn x hx => ?_⟩
  have hnN : N₀ ≤ n := le_of_max_le_left hn
  have hn2 : 2 * 2 ^ j ≤ n := le_of_max_le_left (le_of_max_le_right hn)
  have hn3 : ⌈3 / δ⌉₊ ≤ n := le_of_max_le_right (le_of_max_le_right hn)
  have hnR : (2 : ℝ) * 2 ^ j ≤ n := by exact_mod_cast hn2
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le (by positivity) hnR
  have hn1 : (1 : ℝ) ≤ n := by
    have : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    linarith
  have h3n : 3 ≤ δ * n := by
    have := (Nat.le_ceil (3 / δ)).trans (by exact_mod_cast hn3 : (⌈3 / δ⌉₊ : ℝ) ≤ n)
    rw [div_le_iff₀ hδ0] at this
    linarith
  have h3n' : 3 * (n : ℝ) ≤ δ * (n : ℝ) ^ 2 := by
    calc 3 * (n : ℝ) ≤ δ * n * n := mul_le_mul_of_nonneg_right h3n hnpos.le
      _ = δ * (n : ℝ) ^ 2 := by ring
  have hεn : 0 ≤ ε * (n : ℝ) ^ 2 := by positivity
  set S := (ballZ0_finite (d := d) (n : ℝ)).toFinset with hSdef
  have hS : ∀ y, y ∈ S ↔ ‖toE y‖ < n := fun y => by rw [Set.Finite.mem_toFinset, mem_ballZ0]
  set g : Site d → ℝ := greenKilled (ballZ0 (n : ℝ)) x with hgdef
  have hg : ∀ y, 0 ≤ g y := fun y => greenKilled_nonneg _ _ _
  have hpot : ∀ F : Site d → ℝ, greenPotential (ballZ0 (n : ℝ)) F x = ∑ y ∈ S, g y * F y :=
    fun F => by rw [greenPotential]; exact finsum_mem_eq_finite_toFinset_sum _ (ballZ0_finite _)
  have h2d : (0 : ℝ) < 2 * d := by positivity
  have hSg : ∑ y ∈ S, g y ≤ (((n : ℝ) + 1) ^ 2 - ‖toE x‖ ^ 2) / (2 * d) := by
    have := hExit d hd1 n x hx
    rw [hpot] at this
    simpa using this
  have hgf : |∑ y ∈ S, g y * f y| ≤ K * ∑ y ∈ S, g y := by
    calc |∑ y ∈ S, g y * f y| ≤ ∑ y ∈ S, |g y * f y| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ y ∈ S, K * g y := Finset.sum_le_sum fun y _ => by
          rw [abs_mul, abs_of_nonneg (hg y), mul_comm]
          exact mul_le_mul_of_nonneg_right (hf y) (hg y)
      _ = K * ∑ y ∈ S, g y := by rw [Finset.mul_sum]
  rw [hpot]
  by_cases hxδ : ‖toE x‖ < (1 - δ) * n
  · set Sδ := (ballZ0_finite (d := d) ((1 - δ) * (n : ℝ))).toFinset with hSδdef
    have hSδ : ∀ y, y ∈ Sδ ↔ ‖toE y‖ < (1 - δ) * n := fun y => by
      rw [Set.Finite.mem_toFinset, mem_ballZ0]
    have hgrad : ∑ y ∈ Sδ, ∑ i : Fin d, |g (y + unit i) - g y| ≤ C * n := by
      have := hC n x (mem_ballZ0.2 hxδ)
      rwa [finsum_mem_eq_finite_toFinset_sum _ (ballZ0_finite _)] at this
    have hρ0 : 0 ≤ (1 - 2 * δ) * (n : ℝ) := mul_nonneg (by linarith) hnpos.le
    have hρn : (1 - 2 * δ) * (n : ℝ) ≤ n := by
      have : 0 ≤ 2 * δ * (n : ℝ) := by positivity
      linarith
    have hlay : ∑ y ∈ S.filter (fun y => (1 - 2 * δ) * n ≤ ‖toE y‖), g y ≤
        (((n : ℝ) + 1) ^ 2 - ((1 - 2 * δ) * n) ^ 2) / (2 * d) := by
      have := hLayer d hd1 n ((1 - 2 * δ) * n) hρ0 hρn x
      rw [hpot] at this
      simp only [mul_ite, mul_one, mul_zero] at this
      rwa [← Finset.sum_filter] at this
    have hθk : ∀ k ∈ cubeIndexSet d j, |∑ y ∈ dyadicCube j k n, f y| ≤ θ * (n : ℝ) ^ d := by
      intro k hk
      have h := hN₀ n hnN k hk
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) ^ d),
        div_lt_iff₀ (by positivity)] at h
      exact h.le
    have hδc : Real.sqrt d * ((n : ℝ) / 2 ^ j) ≤ δ * n := by
      rw [mul_div_assoc', div_le_iff₀ h2j]
      calc Real.sqrt d * n ≤ δ * 2 ^ j * n := mul_le_mul_of_nonneg_right hj1 hnpos.le
        _ = δ * n * 2 ^ j := by ring
    have hmain := abs_sum_le_cubes (hP d) g f hg hf hnR hδ0.le hδc hθ0.le hθk S Sδ hS hSδ
    have t1 : θ * (2 * 2 ^ j) ^ d * ∑ y ∈ S, g y ≤ ε / 4 * (n : ℝ) ^ 2 := by
      rw [hθe]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      refine hSg.trans ?_
      rw [div_le_iff₀ h2d]
      exact arith_exit (sq_nonneg _) hn1 hdR
    have t2 : K * (2 ^ d * d * (2 * n / 2 ^ j)) *
        ∑ y ∈ Sδ, ∑ i : Fin d, |g (y + unit i) - g y| ≤ ε / 4 * (n : ℝ) ^ 2 := by
      calc _ ≤ K * (2 ^ d * d * (2 * n / 2 ^ j)) * (C * n) :=
            mul_le_mul_of_nonneg_left hgrad (by positivity)
        _ = (2 * (K * 2 ^ d * d * C) / 2 ^ j) * (n : ℝ) ^ 2 := by ring
        _ ≤ ε / 4 * (n : ℝ) ^ 2 := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            rw [div_le_iff₀ h2j]
            linarith only [hj2]
    have t3 : K * ∑ y ∈ S.filter (fun y => (1 - 2 * δ) * n ≤ ‖toE y‖), g y ≤
        ε / 8 * (n : ℝ) ^ 2 := by
      calc _ ≤ K * ((((n : ℝ) + 1) ^ 2 - ((1 - 2 * δ) * n) ^ 2) / (2 * d)) :=
            mul_le_mul_of_nonneg_left hlay hK
        _ ≤ K * (2 * δ * (n : ℝ) ^ 2) := by
            apply mul_le_mul_of_nonneg_left _ hK
            rw [div_le_iff₀ h2d]
            exact arith_layer hn1 hdR hδ0 h3n'
        _ = 2 * (K * δ) * (n : ℝ) ^ 2 := by ring
        _ ≤ ε / 8 * (n : ℝ) ^ 2 := mul_le_mul_of_nonneg_right (by linarith only [hδK]) (sq_nonneg _)
    linarith only [hmain, t1, t2, t3, hεn]
  · have hxn : (1 - δ) * n ≤ ‖toE x‖ := not_lt.1 hxδ
    have hx0 : 0 ≤ (1 - δ) * (n : ℝ) := mul_nonneg (by linarith) hnpos.le
    have hsq : ((1 - δ) * n) ^ 2 ≤ ‖toE x‖ ^ 2 := pow_le_pow_left₀ hx0 hxn 2
    have hb : (((n : ℝ) + 1) ^ 2 - ‖toE x‖ ^ 2) / (2 * d) ≤ δ * n ^ 2 := by
      rw [div_le_iff₀ h2d]
      exact arith_bdry hn1 hdR hδ0 h3n' hsq
    calc |∑ y ∈ S, g y * f y| ≤ K * ∑ y ∈ S, g y := hgf
      _ ≤ K * (δ * n ^ 2) := mul_le_mul_of_nonneg_left (hSg.trans hb) hK
      _ = (K * δ) * n ^ 2 := by ring
      _ ≤ ε * n ^ 2 := mul_le_mul_of_nonneg_right (by linarith only [hδK, hε]) (sq_nonneg _)

end RandomSandpile
