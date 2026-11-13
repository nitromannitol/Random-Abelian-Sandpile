import RandomSandpile.Defs.Odometer
import LatticeProb.Sandpile.LeastAction

/-!
# Rossin's observation: periodic sandpiles of low density are stabilizable

`paper/random_piles-corrected.tex` (proof of Lemma 7.6(3)): "by Rossin's
observation [Ros00] (see Fact 3.5 in [LPS16]), as a sandpile configuration on `ℤ^d`, `Δ_{ℤ^d} u` is
stabilizable, and so by toppling it, we find a subquadratic, finite `w : ℤ^d → ℕ`".

The source. [LPS16] (L. Levine, W. Pegden, C. K. Smart, *Apollonian structure in the Abelian
sandpile*, GAFA 26 (2016)), p. 11, after Fact 3.5, states Rossin's observation as: *on any finite
connected graph, a chip configuration with fewer chips than there are edges in the graph will
necessarily stabilize*; Lemma 3.4 of [LPS16] transfers stabilizability between an `N`-periodic
configuration on `ℤ^d` and the torus `ℤ^d / N ℤ^d`. The torus has `d N^d` edges, so the threshold
is: **the sum of `η` over a period is `< d N^d`** (average density `< d`; see
`RossinStabilizableStmt`).

The proof here works on `ℤ^d` directly with Lattice-Probability's parallel toppling procedure
`LatticeProb.Sandpile.podo` (a legal toppling procedure, `podo_isLegal`), which stays `N`-periodic:
1. (Rossin's count) if every site has toppled by time `t`, then each site `x` holds at least one
   chip per edge `{x, y}` whose endpoint `y` toppled last no earlier than `x`; summing over a
   period, the configuration has at least `d N^d` chips, while toppling conserves the sum over a
   period. So at every time some site has not toppled.
2. The configuration stays bounded, so the odometer has bounded Laplacian; as it vanishes
   somewhere in every period, it is bounded uniformly in time; hence the parallel toppling
   procedure stops, and its final odometer is the least stabilizing toppling function (least
   action principle, `LatticeProb.Sandpile.le_of_isLegalToppling`).
-/

noncomputable section

open LatticeProb LatticeProb.Sandpile

namespace RandomSandpile

variable {d : ℕ}

/-- `f : ℤ^d → ℤ` is `N`-periodic: invariant under translation by the sublattice `N ℤ^d`. Every
function periodic with respect to a full-rank sublattice `Γ ⊆ ℤ^d` is `N`-periodic for
`N = [ℤ^d : Γ]`. -/
def IsPeriodic (N : ℕ) (f : Site d → ℤ) : Prop :=
  ∀ x z : Site d, f (x + (N : ℤ) • z) = f x

/-- The period box `{0, …, N - 1}^d`, a fundamental domain of `N ℤ^d`; it has `N^d` sites. -/
def periodBox (d N : ℕ) : Finset (Site d) :=
  Fintype.piFinset fun _ => Finset.Ico (0 : ℤ) N

/-- **Rossin's observation** ([Ros00], as stated in [LPS16] p. 11 and Lemma 3.4):
an `N`-periodic sandpile `η : ℤ^d → ℤ` with fewer than `d N^d` chips in a period (the number of
edges of the torus `ℤ^d / N ℤ^d`), that is with average density `< d`, is stabilizable: the
parallel toppling procedure stops, and its final odometer `w` is `N`-periodic, bounded, and is the
least `w ≥ 0` with `Δ_{ℤ^d} w + η ≤ 2d - 1` (the odometer of `η`).

The threshold cannot be raised to "average `≤ 2d - 1`": for `d = 1` and `N ≥ 2` the `N`-periodic
sandpile `2, 0, 1, …, 1` has average `1 = 2d - 1` and a toppling wave that never stops; and an
average `> 2d - 1` is never stabilizable, since the least odometer is periodic ([LPS16] Lemma 3.4),
a periodic odometer does not change the sum over a period, and a stable configuration has at most
`(2d - 1) N^d` chips there. In the printed use, `Δu + η̃ ≤ 2d - 1` with `η̃` of
average `≥ 2d - 1` gives `Δu` average `≤ 0 < d`. -/
def RossinStabilizableStmt : Prop :=
  ∀ (d N : ℕ) (η : Site d → ℤ), 0 < N → IsPeriodic N η →
    ∑ x ∈ periodBox d N, η x < (d : ℤ) * (N : ℤ) ^ d →
    Stabilizable η ∧ ∃ w : Site d → ℤ, (∃ T : ℕ, ∀ t, T ≤ t → podo η t = w) ∧
      IsPeriodic N w ∧ BddAbove (Set.range w) ∧ IsLeast (stabilizing η Set.univ) w

namespace Rossin

variable {N : ℕ}

/-! ### Periodic functions and sums over a period -/

/-- Coordinatewise reduction modulo `N`, into the period box. -/
def red (N : ℕ) (x : Site d) : Site d := fun i => x i % (N : ℤ)

theorem red_mem (hN : 0 < N) (x : Site d) : red N x ∈ periodBox d N := by
  simp only [periodBox, Fintype.mem_piFinset, Finset.mem_Ico, red]
  intro i
  exact ⟨Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ (by omega)⟩

theorem red_of_mem {x : Site d} (hx : x ∈ periodBox d N) : red N x = x := by
  simp only [periodBox, Fintype.mem_piFinset, Finset.mem_Ico] at hx
  funext i
  exact Int.emod_eq_of_lt (hx i).1 (hx i).2

theorem red_add_smul (N : ℕ) (x : Site d) :
    red N x + (N : ℤ) • (fun i => x i / (N : ℤ)) = x := by
  funext i
  simp only [red, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  exact Int.emod_add_mul_ediv (x i) N

theorem red_red_add (N : ℕ) (x y : Site d) : red N (red N x + y) = red N (x + y) := by
  funext i
  simp only [red, Pi.add_apply]
  exact Int.emod_add_emod (x i) N (y i)

theorem _root_.RandomSandpile.IsPeriodic.red_eq {f : Site d → ℤ} (hf : IsPeriodic N f) (x : Site d) :
    f (red N x) = f x := by
  conv_rhs => rw [← red_add_smul N x]
  exact (hf _ _).symm

theorem _root_.RandomSandpile.IsPeriodic.comp_add {f : Site d → ℤ} (hf : IsPeriodic N f) (y : Site d) :
    IsPeriodic N fun x => f (x + y) := by
  intro x z
  show f (x + (N : ℤ) • z + y) = f (x + y)
  rw [add_right_comm]
  exact hf _ _

theorem _root_.RandomSandpile.IsPeriodic.comp_sub {f : Site d → ℤ} (hf : IsPeriodic N f) (y : Site d) :
    IsPeriodic N fun x => f (x - y) := by
  intro x z
  show f (x + (N : ℤ) • z - y) = f (x - y)
  rw [add_sub_right_comm]
  exact hf _ _

/-- The sum over a period of a periodic function is invariant under translation. -/
theorem sum_box_add {f : Site d → ℤ} (hN : 0 < N) (hf : IsPeriodic N f) (z : Site d) :
    ∑ x ∈ periodBox d N, f (x + z) = ∑ x ∈ periodBox d N, f x := by
  rw [show ∑ x ∈ periodBox d N, f (x + z) = ∑ x ∈ periodBox d N, f (red N (x + z)) from
    Finset.sum_congr rfl fun x _ => (hf.red_eq _).symm]
  refine Finset.sum_nbij' (fun x => red N (x + z)) (fun x => red N (x + -z))
    (fun x _ => red_mem hN _) (fun x _ => red_mem hN _) ?_ ?_ (fun x _ => rfl)
  · intro x hx
    rw [red_red_add, add_neg_cancel_right, red_of_mem hx]
  · intro x hx
    rw [red_red_add, neg_add_cancel_right, red_of_mem hx]

theorem sum_box_sub {f : Site d → ℤ} (hN : 0 < N) (hf : IsPeriodic N f) (z : Site d) :
    ∑ x ∈ periodBox d N, f (x - z) = ∑ x ∈ periodBox d N, f x := by
  simp only [sub_eq_add_neg]
  exact sum_box_add hN hf _

theorem card_periodBox (d N : ℕ) : (periodBox d N).card = N ^ d := by
  simp [periodBox, Fintype.card_piFinset]

theorem _root_.RandomSandpile.IsPeriodic.lap {v : Site d → ℤ} (hv : IsPeriodic N v) : IsPeriodic N (lap v) := by
  intro x z
  simp only [Sandpile.lap, nbrSumZ]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [add_right_comm x, add_sub_right_comm x, hv, hv]
  · rw [hv]

/-- The sum over a period of the Laplacian of a periodic function vanishes. -/
theorem sum_box_lap {v : Site d → ℤ} (hN : 0 < N) (hv : IsPeriodic N v) :
    ∑ x ∈ periodBox d N, lap v x = 0 := by
  have h1 : ∑ x ∈ periodBox d N, nbrSumZ v x =
      ∑ _i : Fin d, 2 * ∑ x ∈ periodBox d N, v x := by
    simp only [nbrSumZ]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_add_distrib, sum_box_add hN hv (unit i), sum_box_sub hN hv (unit i)]
    ring
  simp only [Sandpile.lap, Finset.sum_sub_distrib, h1, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, ← Finset.mul_sum, nsmul_eq_mul]
  ring

/-! ### The parallel toppling procedure of a periodic sandpile -/

/-- The indicator of the sites toppling at step `t` of the parallel toppling procedure. -/
def topInd (η : Site d → ℤ) (t : ℕ) (x : Site d) : ℤ :=
  if 2 * (d : ℤ) ≤ pconf η t x then 1 else 0

theorem podo_succ_eq (η : Site d → ℤ) (t : ℕ) : podo η (t + 1) = podo η t + topInd η t := by
  funext x
  rfl

theorem lap_add' (u w : Site d → ℤ) (x : Site d) : lap (u + w) x = lap u x + lap w x := by
  simp only [Sandpile.lap, nbrSumZ, Pi.add_apply, Finset.sum_add_distrib]
  ring

theorem nbrSumZ_nonneg {u : Site d → ℤ} (hu : ∀ y, 0 ≤ u y) (x : Site d) : 0 ≤ nbrSumZ u x :=
  Finset.sum_nonneg fun _ _ => add_nonneg (hu _) (hu _)

theorem pconf_succ (η : Site d → ℤ) (t : ℕ) (x : Site d) :
    pconf η (t + 1) x = pconf η t x + lap (topInd η t) x := by
  simp only [pconf, podo_succ_eq, lap_add']
  ring

/-- The parallel toppling odometer is a legal toppling procedure. Copied from Lattice-Probability,
`LatticeProb/Sandpile/RadiusConsequences.lean` (`LatticeProb.Sandpile.podo_isLegal`), to avoid
importing that module's measure-theoretic dependencies. -/
theorem isLegalToppling_podo (s0 : Site d → ℤ) : IsLegalToppling s0 (podo s0) := by
  refine ⟨funext fun y => rfl, fun k x => ?_⟩
  rw [podo_succ]
  by_cases h : 2 * (d : ℤ) ≤ pconf s0 k x
  · right
    exact ⟨by simp [h], h⟩
  · left
    simp [h]

theorem podo_mono' (η : Site d → ℤ) {s t : ℕ} (hst : s ≤ t) (x : Site d) :
    podo η s x ≤ podo η t x := by
  induction hst with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans ((isLegalToppling_podo η).le_succ _ x)

theorem isPeriodic_podo {η : Site d → ℤ} (hη : IsPeriodic N η) (t : ℕ) :
    IsPeriodic N (podo η t) := by
  induction t with
  | zero => intro x z; rfl
  | succ t ih =>
    intro x z
    rw [podo_succ, podo_succ, pconf, pconf, ih x z, hη x z, ih.lap x z]

theorem isPeriodic_pconf {η : Site d → ℤ} (hη : IsPeriodic N η) (t : ℕ) :
    IsPeriodic N (pconf η t) := by
  intro x z
  simp only [pconf, hη x z, (isPeriodic_podo hη t).lap x z]

/-- Parallel toppling never pushes a site below `min (η x) 0`: a toppling site keeps `≥ 0`
chips, a non-toppling site only gains. -/
theorem min_le_pconf (η : Site d → ℤ) (t : ℕ) (x : Site d) : min (η x) 0 ≤ pconf η t x := by
  induction t with
  | zero => simp [pconf, Sandpile.lap, nbrSumZ]
  | succ t ih =>
    have hnn : 0 ≤ nbrSumZ (topInd η t) x :=
      nbrSumZ_nonneg (fun y => by unfold topInd; split_ifs <;> norm_num) x
    rw [pconf_succ, Sandpile.lap]
    unfold topInd at hnn ⊢
    split_ifs with h
    · have : min (η x) 0 ≤ 0 := min_le_right _ _
      linarith
    · linarith

/-- Parallel toppling conserves the sum over a period. -/
theorem sum_box_pconf {η : Site d → ℤ} (hN : 0 < N) (hη : IsPeriodic N η) (t : ℕ) :
    ∑ x ∈ periodBox d N, pconf η t x = ∑ x ∈ periodBox d N, η x := by
  simp only [pconf, Finset.sum_add_distrib, sum_box_lap hN (isPeriodic_podo hη t), add_zero]

/-! ### Rossin's count: at every time some site has not toppled -/

/-- A site that does not topple at the times `a, …, b - 1` keeps its odometer value. -/
theorem podo_eq_of_no_topple (η : Site d → ℤ) (x : Site d) {a b : ℕ} (hab : a ≤ b)
    (h : ∀ r, a ≤ r → r < b → ¬ 2 * (d : ℤ) ≤ pconf η r x) : podo η b x = podo η a x := by
  induction hab with
  | refl => rfl
  | @step m hab ih =>
    rw [podo_succ, ite_eq_right (h m hab (Nat.lt_succ_self m)), add_zero]
    exact ih fun r h1 h2 => h r h1 (Nat.lt_succ_of_lt h2)

theorem exists_topple_of_one_le {η : Site d → ℤ} {t : ℕ} {x : Site d}
    (h : 1 ≤ podo η t x) : ∃ r, r < t ∧ 2 * (d : ℤ) ≤ pconf η r x := by
  by_contra hne
  have h0 := podo_eq_of_no_topple η x (Nat.zero_le t) fun r _ hr hle => hne ⟨r, hr, hle⟩
  rw [h0] at h
  simp at h

/-- The last time `τ(x) < t` at which `x` topples (`0` if there is none). -/
def lastTop (η : Site d → ℤ) (t : ℕ) (x : Site d) : ℕ :=
  Nat.findGreatest (fun r => 2 * (d : ℤ) ≤ pconf η r x) (t - 1)

/-- If `x` has toppled before time `t`, it toppled at `τ(x) < t` and never again before `t`. -/
theorem lastTop_spec {η : Site d → ℤ} {t : ℕ} {x : Site d} (h : 1 ≤ podo η t x) :
    lastTop η t x < t ∧ 2 * (d : ℤ) ≤ pconf η (lastTop η t x) x ∧
      podo η t x = podo η (lastTop η t x) x + 1 := by
  obtain ⟨r, hrt, hr⟩ := exists_topple_of_one_le h
  have hle : lastTop η t x ≤ t - 1 := Nat.findGreatest_le _
  have hspec : 2 * (d : ℤ) ≤ pconf η (lastTop η t x) x :=
    Nat.findGreatest_spec (P := fun r => 2 * (d : ℤ) ≤ pconf η r x) (m := r) (by omega) hr
  have hlt : lastTop η t x < t := by omega
  refine ⟨hlt, hspec, ?_⟩
  rw [podo_eq_of_no_topple η x (a := lastTop η t x + 1) (b := t) hlt ?_, podo_succ,
    ite_eq_left hspec]
  intro r h1 h2
  exact Nat.findGreatest_is_greatest (P := fun r => 2 * (d : ℤ) ≤ pconf η r x)
    (show lastTop η t x < r by omega) (by omega)

theorem lastTop_periodic {η : Site d → ℤ} (hη : IsPeriodic N η) (t : ℕ) (x z : Site d) :
    lastTop η t (x + (N : ℤ) • z) = lastTop η t x := by
  have h := fun r => isPeriodic_pconf hη r x z
  simp only [lastTop, h]

/-- **Rossin's local count.** If every site has toppled before time `t`, then `x` holds at
least one chip for each neighbour `y` whose last toppling `τ(y)` is not earlier than `τ(x)`:
after its last toppling `x` holds `≥ 0` chips, and each such `y` sends it a chip afterwards. -/
theorem ind_le_pconf {η : Site d → ℤ} {t : ℕ} (h1 : ∀ y, 1 ≤ podo η t y) (x : Site d) :
    ∑ i : Fin d, ((if lastTop η t x ≤ lastTop η t (x + unit i) then (1 : ℤ) else 0) +
      (if lastTop η t x ≤ lastTop η t (x - unit i) then 1 else 0)) ≤ pconf η t x := by
  obtain ⟨hlt, hx, hxv⟩ := lastTop_spec (h1 x)
  have hD : ∀ y, (if lastTop η t x ≤ lastTop η t y then (1 : ℤ) else 0) ≤
      podo η t y - podo η (lastTop η t x) y := by
    intro y
    obtain ⟨_, _, hyv⟩ := lastTop_spec (h1 y)
    split_ifs with hle
    · have := podo_mono' η hle y
      omega
    · have := podo_mono' η hlt.le y
      omega
  have hsum : ∑ i : Fin d, ((if lastTop η t x ≤ lastTop η t (x + unit i) then (1 : ℤ) else 0) +
      (if lastTop η t x ≤ lastTop η t (x - unit i) then 1 else 0)) ≤
      nbrSumZ (podo η t) x - nbrSumZ (podo η (lastTop η t x)) x := by
    rw [nbrSumZ, nbrSumZ, ← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum fun i _ => by linarith [hD (x + unit i), hD (x - unit i)]
  have hmul : 2 * (d : ℤ) * podo η t x = 2 * (d : ℤ) * podo η (lastTop η t x) x + 2 * d := by
    rw [hxv]; ring
  simp only [pconf, Sandpile.lap] at hx ⊢
  linarith

/-- **Rossin's count** ([LPS16] p. 11): if every site has toppled before time `t`, the
configuration holds at least `d N^d` chips in a period, the number of edges of the torus
`ℤ^d / N ℤ^d`; each edge `{x, x + e_i}` is charged to an endpoint that toppled last no earlier
than the other. Since toppling conserves the sum over a period, so does `η`. -/
theorem rossin_count {η : Site d → ℤ} (hN : 0 < N) (hη : IsPeriodic N η) {t : ℕ}
    (h1 : ∀ y, 1 ≤ podo η t y) : (d : ℤ) * (N : ℤ) ^ d ≤ ∑ x ∈ periodBox d N, η x := by
  rw [← sum_box_pconf hN hη t]
  have hτ : ∀ x z, lastTop η t (x + (N : ℤ) • z) = lastTop η t x := lastTop_periodic hη t
  calc (d : ℤ) * (N : ℤ) ^ d = ∑ _x ∈ periodBox d N, ∑ _i : Fin d, (1 : ℤ) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, card_periodBox,
          nsmul_eq_mul, mul_one]
        push_cast
        ring
    _ ≤ ∑ x ∈ periodBox d N, ∑ i : Fin d,
          ((if lastTop η t x ≤ lastTop η t (x + unit i) then (1 : ℤ) else 0) +
            (if lastTop η t (x + unit i) ≤ lastTop η t x then 1 else 0)) := by
        gcongr with x _ i _
        split_ifs <;> omega
    _ = ∑ x ∈ periodBox d N, ∑ i : Fin d,
          ((if lastTop η t x ≤ lastTop η t (x + unit i) then (1 : ℤ) else 0) +
            (if lastTop η t x ≤ lastTop η t (x - unit i) then 1 else 0)) := by
        simp only [Finset.sum_add_distrib]
        congr 1
        rw [Finset.sum_comm]
        conv_rhs => rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        have hper : IsPeriodic N fun x =>
            if lastTop η t x ≤ lastTop η t (x - unit i) then (1 : ℤ) else 0 := by
          intro x z
          simp only [add_sub_right_comm x, hτ]
        have := sum_box_add hN hper (unit i)
        simp only [add_sub_cancel_right] at this
        exact this
    _ ≤ ∑ x ∈ periodBox d N, pconf η t x := Finset.sum_le_sum fun x _ => ind_le_pconf h1 x

/-- Below density `d`, at every time of the parallel toppling procedure some site has not yet
toppled. -/
theorem exists_podo_eq_zero {η : Site d → ℤ} (hN : 0 < N) (hη : IsPeriodic N η)
    (hsum : ∑ x ∈ periodBox d N, η x < (d : ℤ) * (N : ℤ) ^ d) (t : ℕ) :
    ∃ z, podo η t z = 0 := by
  by_contra h
  have h1 : ∀ y, 1 ≤ podo η t y := fun y => by
    have h0 := (isLegalToppling_podo η).nonneg t y
    have hne : podo η t y ≠ 0 := fun h' => h ⟨y, h'⟩
    omega
  exact absurd (rossin_count hN hη h1) (not_le.2 hsum)

/-! ### A uniform bound on the odometer -/

/-- The configuration stays below `∑_{period} (η - min (η, 0))`. -/
theorem pconf_le {η : Site d → ℤ} (hN : 0 < N) (hη : IsPeriodic N η) (t : ℕ) (x : Site d) :
    pconf η t x ≤ ∑ y ∈ periodBox d N, (η y - min (η y) 0) := by
  rw [← (isPeriodic_pconf hη t).red_eq x]
  have hx := red_mem hN x
  have h : pconf η t (red N x) + ∑ y ∈ (periodBox d N).erase (red N x), pconf η t y =
      ∑ y ∈ periodBox d N, pconf η t y := Finset.add_sum_erase _ _ hx
  rw [sum_box_pconf hN hη t] at h
  have h2 : ∑ y ∈ (periodBox d N).erase (red N x), min (η y) 0 ≤
      ∑ y ∈ (periodBox d N).erase (red N x), pconf η t y :=
    Finset.sum_le_sum fun y _ => min_le_pconf η t y
  have h3 : min (η (red N x)) 0 + ∑ y ∈ (periodBox d N).erase (red N x), min (η y) 0 =
      ∑ y ∈ periodBox d N, min (η y) 0 := Finset.add_sum_erase _ (fun y => min (η y) 0) hx
  have h4 : min (η (red N x)) 0 ≤ 0 := min_le_right _ _
  rw [Finset.sum_sub_distrib]
  linarith

/-- The Laplacian bound for the odometer, uniform in time. -/
def lapBound (η : Site d → ℤ) (N : ℕ) : ℤ :=
  ∑ y ∈ periodBox d N, (η y - min (η y) 0) + ∑ y ∈ periodBox d N, |η y|

theorem lapBound_nonneg (η : Site d → ℤ) (N : ℕ) : 0 ≤ lapBound η N :=
  add_nonneg (Finset.sum_nonneg fun y _ => by have := min_le_left (η y) 0; linarith)
    (Finset.sum_nonneg fun y _ => abs_nonneg _)

theorem lap_podo_le {η : Site d → ℤ} (hN : 0 < N) (hη : IsPeriodic N η) (t : ℕ) (x : Site d) :
    lap (podo η t) x ≤ lapBound η N := by
  have h1 := pconf_le hN hη t x
  have h2 : |η (red N x)| ≤ ∑ y ∈ periodBox d N, |η y| :=
    Finset.single_le_sum (f := fun y => |η y|) (fun y _ => abs_nonneg _) (red_mem hN x)
  rw [hη.red_eq] at h2
  have h3 := neg_abs_le (η x)
  simp only [pconf] at h1
  unfold lapBound
  linarith

/-- `pathBound K d L = K (1 + 2d + ⋯ + (2d)^(L-1))`. -/
def pathBound (K : ℤ) (d : ℕ) : ℕ → ℤ
  | 0 => 0
  | L + 1 => K + 2 * d * pathBound K d L

theorem pathBound_nonneg {K : ℤ} (hK : 0 ≤ K) : ∀ L, 0 ≤ pathBound K d L
  | 0 => le_rfl
  | L + 1 => by
    have := pathBound_nonneg hK L
    simp only [pathBound]
    positivity

/-- A nonnegative `v` with `Δ v ≤ K` grows by at most `v ↦ K + 2d v` along an edge. -/
theorem nbr_le {v : Site d → ℤ} (hv : ∀ x, 0 ≤ v x) {K : ℤ} (hK : ∀ x, lap v x ≤ K)
    (y : Site d) (i : Fin d) :
    v (y + unit i) ≤ K + 2 * d * v y ∧ v (y - unit i) ≤ K + 2 * d * v y := by
  have hs : v (y + unit i) + v (y - unit i) ≤ nbrSumZ v y :=
    Finset.single_le_sum (f := fun j => v (y + unit j) + v (y - unit j))
      (fun j _ => add_nonneg (hv _) (hv _)) (Finset.mem_univ i)
  have hl := hK y
  rw [Sandpile.lap] at hl
  have := hv (y + unit i)
  have := hv (y - unit i)
  constructor <;> linarith

theorem sum_natAbs_step (x y z : Site d) (i : Fin d) (hy : ∀ j, j ≠ i → y j = x j) :
    ∑ j, (y j - z j).natAbs + (x i - z i).natAbs =
      ∑ j, (x j - z j).natAbs + (y i - z i).natAbs := by
  have he : ∑ j ∈ Finset.univ.erase i, (y j - z j).natAbs =
      ∑ j ∈ Finset.univ.erase i, (x j - z j).natAbs :=
    Finset.sum_congr rfl fun j hj => by rw [hy j (Finset.ne_of_mem_erase hj)]
  have h1 : (y i - z i).natAbs + ∑ j ∈ Finset.univ.erase i, (y j - z j).natAbs =
      ∑ j, (y j - z j).natAbs := Finset.add_sum_erase _ (fun j => (y j - z j).natAbs) (Finset.mem_univ i)
  have h2 : (x i - z i).natAbs + ∑ j ∈ Finset.univ.erase i, (x j - z j).natAbs =
      ∑ j, (x j - z j).natAbs := Finset.add_sum_erase _ (fun j => (x j - z j).natAbs) (Finset.mem_univ i)
  omega

/-- A nonnegative `v` with `Δ v ≤ K` and `v(z) = 0` is at most `pathBound K d L` at
`ℓ¹`-distance `≤ L` from `z`. -/
theorem le_pathBound {v : Site d → ℤ} (hv : ∀ x, 0 ≤ v x) {K : ℤ} (hK0 : 0 ≤ K)
    (hK : ∀ x, lap v x ≤ K) {z : Site d} (hz : v z = 0) :
    ∀ (L : ℕ) (x : Site d), ∑ i, (x i - z i).natAbs ≤ L → v x ≤ pathBound K d L := by
  intro L
  induction L with
  | zero =>
    intro x hx
    have hxz : x = z := by
      funext i
      have := (Finset.sum_eq_zero_iff.1 (Nat.le_zero.1 hx)) i (Finset.mem_univ i)
      omega
    rw [hxz, hz]
    rfl
  | succ L ih =>
    intro x hx
    by_cases hxz : x = z
    · rw [hxz, hz]
      exact pathBound_nonneg hK0 _
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hxz
    have hmul : ∀ y, v y ≤ pathBound K d L → K + 2 * d * v y ≤ pathBound K d (L + 1) := by
      intro y hy
      have := mul_le_mul_of_nonneg_left hy (by positivity : (0 : ℤ) ≤ 2 * d)
      simp only [pathBound]
      linarith
    rcases lt_or_gt_of_ne hi with hlt | hlt
    · -- `x i < z i`: step from `x + e_i`
      have hy : ∀ j, j ≠ i → (x + unit i) j = x j := fun j hj => by
        simp [unit, hj]
      have hyi : (x + unit i) i = x i + 1 := by simp [unit]
      have hs := sum_natAbs_step x (x + unit i) z i hy
      rw [hyi] at hs
      have hyL := ih (x + unit i) (by omega)
      have := (nbr_le hv hK (x + unit i) i).2
      rw [add_sub_cancel_right] at this
      exact this.trans (hmul _ hyL)
    · -- `z i < x i`: step from `x - e_i`
      have hy : ∀ j, j ≠ i → (x - unit i) j = x j := fun j hj => by
        simp [unit, hj]
      have hyi : (x - unit i) i = x i - 1 := by simp [unit]
      have hs := sum_natAbs_step x (x - unit i) z i hy
      rw [hyi] at hs
      have hyL := ih (x - unit i) (by omega)
      have := (nbr_le hv hK (x - unit i) i).1
      rw [sub_add_cancel] at this
      exact this.trans (hmul _ hyL)

/-- Below density `d`, the parallel toppling odometer of a periodic sandpile is bounded
uniformly in time. -/
theorem podo_le_bound {η : Site d → ℤ} (hN : 0 < N) (hη : IsPeriodic N η)
    (hsum : ∑ x ∈ periodBox d N, η x < (d : ℤ) * (N : ℤ) ^ d) (t : ℕ) (x : Site d) :
    podo η t x ≤ pathBound (lapBound η N) d (d * N) := by
  obtain ⟨z, hz⟩ := exists_podo_eq_zero hN hη hsum t
  have hx : z + red N (x - z) + (N : ℤ) • (fun i => (x - z) i / (N : ℤ)) = x := by
    rw [add_assoc, red_add_smul, add_sub_cancel]
  rw [← hx, isPeriodic_podo hη t]
  refine le_pathBound ((isLegalToppling_podo η).nonneg t) (lapBound_nonneg η N)
    (lap_podo_le hN hη t) hz _ _ ?_
  calc ∑ i, ((z + red N (x - z)) i - z i).natAbs ≤ ∑ _i : Fin d, N := by
        refine Finset.sum_le_sum fun i _ => ?_
        have h1 := Int.emod_nonneg ((x - z) i) (by omega : (N : ℤ) ≠ 0)
        have h2 := Int.emod_lt_of_pos ((x - z) i) (by omega : (0 : ℤ) < N)
        simp only [Pi.add_apply, add_sub_cancel_left, red]
        omega
    _ = d * N := by simp

/-! ### The parallel toppling procedure stops -/

theorem podo_succ_congr {η : Site d → ℤ} {s t : ℕ} (h : podo η s = podo η t) :
    podo η (s + 1) = podo η (t + 1) := by
  have ht : topInd η s = topInd η t := by
    funext x
    unfold topInd pconf
    rw [h]
  rw [podo_succ_eq, podo_succ_eq, h, ht]

theorem exists_podo_succ_eq {η : Site d → ℤ} (hN : 0 < N) (hη : IsPeriodic N η)
    (hsum : ∑ x ∈ periodBox d N, η x < (d : ℤ) * (N : ℤ) ^ d) :
    ∃ T, podo η (T + 1) = podo η T := by
  by_contra hne
  simp only [not_exists] at hne
  set B := pathBound (lapBound η N) d (d * N)
  have hgrow : ∀ t : ℕ, (t : ℤ) ≤ ∑ x ∈ periodBox d N, podo η t x := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      obtain ⟨x, hx⟩ := Function.ne_iff.1 (hne t)
      have hx' : podo η (t + 1) (red N x) ≠ podo η t (red N x) := by
        rwa [(isPeriodic_podo hη (t + 1)).red_eq, (isPeriodic_podo hη t).red_eq]
      have hmono : ∀ y, podo η t y ≤ podo η (t + 1) y := (isLegalToppling_podo η).le_succ t
      have hstep : 1 ≤ ∑ y ∈ periodBox d N, (podo η (t + 1) y - podo η t y) := by
        have := Finset.single_le_sum (f := fun y => podo η (t + 1) y - podo η t y)
          (fun y _ => by linarith [hmono y]) (red_mem hN x)
        have := hmono (red N x)
        have : podo η t (red N x) + 1 ≤ podo η (t + 1) (red N x) := by omega
        linarith
      rw [Finset.sum_sub_distrib] at hstep
      push_cast
      linarith
  have hbd : ∀ t, ∑ x ∈ periodBox d N, podo η t x ≤ (N ^ d : ℕ) * B := by
    intro t
    calc ∑ x ∈ periodBox d N, podo η t x ≤ ∑ _x ∈ periodBox d N, B :=
          Finset.sum_le_sum fun x _ => podo_le_bound hN hη hsum t x
      _ = (N ^ d : ℕ) * B := by simp [card_periodBox]
  have h0 : 0 ≤ ((N ^ d : ℕ) : ℤ) * B :=
    mul_nonneg (by positivity) (pathBound_nonneg (lapBound_nonneg η N) _)
  -- `t ≤ S_t ≤ N^d B` fails at `t = N^d B + 1`
  have h5 : ((((N ^ d : ℕ) : ℤ) * B).toNat : ℤ) = ((N ^ d : ℕ) : ℤ) * B := Int.toNat_of_nonneg h0
  have := (hgrow ((((N ^ d : ℕ) : ℤ) * B).toNat + 1)).trans (hbd _)
  push_cast at this h5
  linarith

end Rossin

open Rossin in
/-- **Rossin's observation**, proved. -/
theorem rossinStabilizable : RossinStabilizableStmt := by
  intro d N η hN hη hsum
  obtain ⟨T, hT⟩ := exists_podo_succ_eq hN hη hsum
  have hconst : ∀ t, T ≤ t → podo η t = podo η T := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => rfl
    | succ t _ ih => rw [podo_succ_congr ih, hT]
  refine ⟨⟨T, hconst⟩, podo η T, ⟨T, hconst⟩, isPeriodic_podo hη T,
    ⟨_, fun _ ⟨x, hx⟩ => hx ▸ podo_le_bound hN hη hsum T x⟩, ?_, ?_⟩
  · rw [mem_stabilizing_univ]
    refine ⟨(isLegalToppling_podo η).nonneg T, fun x => ?_⟩
    by_contra hx
    have h := congrFun hT x
    rw [podo_succ, pconf, ite_eq_left (by omega)] at h
    omega
  · intro u hu x
    rw [mem_stabilizing_univ] at hu
    exact le_of_isLegalToppling (isLegalToppling_podo η) hu.1
      (fun y => by have := hu.2 y; omega) T x

end RandomSandpile
