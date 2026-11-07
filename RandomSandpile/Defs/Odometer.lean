import RandomSandpile.Defs.Toppling
import LatticeProb.Sandpile.LeastAction

/-!
# Odometers and stabilized sandpiles (Theorem 1.1, Lemma 7.4, Theorems 9.1 and 9.2)

`paper/random_piles-corrected.tex` (Theorem 1.1), 254-285 (the open-boundary
odometer and Proposition 3.1), 1026-1031 (the free-boundary odometer `v_n` of Section 7),
1211-1222 (Lemma 7.4), 1569-1576 (Theorem 9.1) and 1610-1616 (Theorem 9.2).

Every odometer of the paper is the *pointwise least* stabilizing toppling function of some class,
so all of them are instances of one construction, `pointwiseInf S`, the pointwise infimum (in `ℕ`)
of a set `S` of nonnegative integer functions on `ℤ^d`:

* `stabilizingOpen η A`, `openOdometer η A`: the stabilizing toppling functions vanishing on `∂A`
  and their least element, the odometer of `η` in `A` with the *open* boundary condition
  (asserts that it is the legal stabilizing one);
* `freeOdometer η W`, `freeSandpile η W`: the odometer `v_n` of `η · 1_{W_n}` on all of `ℤ^d`, with
  the *free* boundary condition, and the stable sandpile `s_n = η · 1_{W_n} + Δ_{ℤ^d} v_n`
  (1026-1031);
* `singleSourceOdometer η m`: the odometer of `η + m δ_0` on all of `ℤ^d`;
* `rescaleOdo v n`, `rescaleSandpile s n`, `rescaleSingleSource v n`: the rescalings
  `v̄_n(x) = n⁻² v_n([nx])`, `s̄_n(x) = s_n([nx])` (113) and
  `v̄_n(x) = n^{-2/d} v_n([n^{1/d} x])`.

The free and single-source sets are instances of Section 2's `stabilizing η' A` with `A = ℤ^d`
(`Set.univ`): then `∂A = ∅`, `Ā = ℤ^d`, and `stabilizing η' univ` is the set of all `v ≥ 0` with
`Δ_{ℤ^d} v + η' ≤ 2d - 1` everywhere (`mem_stabilizing_univ`).

## Junk values

`pointwiseInf S = 0` when `S = ∅` (`Nat.sInf_empty`). When `S ≠ ∅`, the pointwise infimum of a
class of stabilizing toppling functions is itself stabilizing (`pointwiseInf_mem_stabilizing`):
each odometer is then the least element of its class (`isLeast_openOdometer`,
`isLeast_freeOdometer`, `isLeast_singleSourceOdometer`). Hence:

* `openOdometer η A`: the class is nonempty for every finite `A` when `d ≥ 1`
  (`stabilizingOpen_nonempty`), in particular for `A = W_n` with `W` bounded and for `A = B_n`;
  statements about bounded domains need no extra conjunct.
* `freeOdometer η W`: nonemptiness of `stabilizing (W_n.indicator η) univ` (finiteness of the
  free-boundary odometer of a sandpile with finitely many chips) is not proved here; the paper
  gets it from the Lemma 7.1 bound. A statement whose conclusion would hold for the junk value
  `0` must assume or assert `(stabilizing ((discretize W n).indicator η) Set.univ).Nonempty`.
* `singleSourceOdometer η m`: the class is nonempty only for a stable background with room,
  e.g. `η ≤ 2d - 2` (Theorem 9.2's hypothesis `η_max = 2d - 2`); for `η ≡ 2d - 1` it is empty
  for `m ≥ 1` and the junk value `0` is returned. Statements must assert nonemptiness the same way.
-/

noncomputable section

open LatticeProb LatticeProb.Sandpile

namespace RandomSandpile

variable {d : ℕ}

/-! ### The pointwise infimum of a class of toppling functions -/

/-- The pointwise infimum `x ↦ inf {u(x) : u ∈ S}` of a set `S` of nonnegative integer functions,
computed in `ℕ` (so it is `0` at every site when `S = ∅`). For a nonempty class of stabilizing
toppling functions it is the least element of the class (`isLeast_pointwiseInf`). -/
def pointwiseInf (S : Set (Site d → ℤ)) : Site d → ℤ :=
  fun x => ((sInf {n : ℕ | ∃ u ∈ S, u x = n} : ℕ) : ℤ)

theorem pointwiseInf_nonneg (S : Set (Site d → ℤ)) (x : Site d) : 0 ≤ pointwiseInf S x :=
  Int.natCast_nonneg _

theorem pointwiseInf_le {S : Set (Site d → ℤ)} (hS : ∀ u ∈ S, ∀ x, 0 ≤ u x) {u : Site d → ℤ}
    (hu : u ∈ S) (x : Site d) : pointwiseInf S x ≤ u x := by
  have hmem : (u x).toNat ∈ {n : ℕ | ∃ u ∈ S, u x = n} :=
    ⟨u, hu, (Int.toNat_of_nonneg (hS u hu x)).symm⟩
  calc pointwiseInf S x ≤ ((u x).toNat : ℤ) := Int.ofNat_le.2 (Nat.sInf_le hmem)
    _ = u x := Int.toNat_of_nonneg (hS u hu x)

/-- The infimum at each site is attained by a member of the class. -/
theorem exists_eq_pointwiseInf {S : Set (Site d → ℤ)} (hS : ∀ u ∈ S, ∀ x, 0 ≤ u x)
    (hne : S.Nonempty) (x : Site d) : ∃ u ∈ S, u x = pointwiseInf S x := by
  obtain ⟨u, hu⟩ := hne
  have hmem : (u x).toNat ∈ {n : ℕ | ∃ u ∈ S, u x = n} :=
    ⟨u, hu, (Int.toNat_of_nonneg (hS u hu x)).symm⟩
  exact Nat.sInf_mem ⟨_, hmem⟩

/-- If every member of the class vanishes at `y`, so does the pointwise infimum (also for the
empty class, by the junk value `sInf ∅ = 0`). -/
theorem pointwiseInf_eq_zero {S : Set (Site d → ℤ)} {y : Site d} (hy : ∀ u ∈ S, u y = 0) :
    pointwiseInf S y = 0 := by
  have h : {n : ℕ | ∃ u ∈ S, u y = n} ⊆ {0} := by
    rintro n ⟨u, hu, hn⟩
    rw [hy u hu] at hn
    exact_mod_cast hn.symm
  rcases Set.subset_singleton_iff_eq.1 h with h | h <;> simp [pointwiseInf, h]

theorem nonneg_of_subset_stabilizing {S : Set (Site d → ℤ)} {η : Site d → ℤ} {A : Set (Site d)}
    (hSA : S ⊆ stabilizing η A) : ∀ u ∈ S, ∀ x, 0 ≤ u x :=
  fun _ hu => (hSA hu).1.1

/-- The pointwise infimum of a nonempty class of stabilizing toppling functions is stabilizing:
at each `x ∈ A` it touches from below a member `u` of the class, so its Laplacian at `x` is at
most `Δ_{ℤ^d} u(x)` (`LatticeProb.Sandpile.lap_le_lap_of_le`). -/
theorem pointwiseInf_mem_stabilizing {S : Set (Site d → ℤ)} {η : Site d → ℤ} {A : Set (Site d)}
    (hSA : S ⊆ stabilizing η A) (hne : S.Nonempty) : pointwiseInf S ∈ stabilizing η A := by
  have hS := nonneg_of_subset_stabilizing hSA
  refine ⟨⟨pointwiseInf_nonneg S, fun x hx => pointwiseInf_eq_zero
    fun u hu => (hSA hu).1.2 x hx⟩, fun x hx => ?_⟩
  obtain ⟨u, hu, hux⟩ := exists_eq_pointwiseInf hS hne x
  have hlap : lap (pointwiseInf S) x ≤ lap u x :=
    lap_le_lap_of_le (fun y => pointwiseInf_le hS hu y) hux.symm
  linarith [(hSA hu).2 x hx]

/-- If the pointwise infimum of a class of nonnegative functions belongs to the class, it is the
least element of the class (for the pointwise order on `ℤ^d → ℤ`). -/
theorem isLeast_pointwiseInf {S : Set (Site d → ℤ)} (hS : ∀ u ∈ S, ∀ x, 0 ≤ u x)
    (hmem : pointwiseInf S ∈ S) : IsLeast S (pointwiseInf S) :=
  ⟨hmem, fun _ hu x => pointwiseInf_le hS hu x⟩

/-! ### Toppling on all of `ℤ^d` -/

@[simp] theorem bdry_univ : bdry (Set.univ : Set (Site d)) = ∅ := by
  ext y; simp [mem_bdry]

@[simp] theorem dClosure_univ : dClosure (Set.univ : Set (Site d)) = Set.univ :=
  Set.eq_univ_of_univ_subset (subset_dClosure _)

/-- With `A = ℤ^d`, a stabilizing toppling function is any `v ≥ 0` with
`Δ_{ℤ^d} v + η ≤ 2d - 1` everywhere. -/
theorem mem_stabilizing_univ {η v : Site d → ℤ} :
    v ∈ stabilizing η Set.univ ↔ (∀ x, 0 ≤ v x) ∧ ∀ x, lap v x + η x ≤ 2 * (d : ℤ) - 1 := by
  simp [stabilizing, IsTopplingFn]

/-! ### The open-boundary odometer -/

/-- The stabilizing toppling functions for `η` in `A` that vanish on `∂A`,
`{u ∈ 𝓢(η, A) : u = 0 on ∂A}` (Proposition 3.1(2)). -/
def stabilizingOpen (η : Site d → ℤ) (A : Set (Site d)) : Set (Site d → ℤ) :=
  {u | u ∈ stabilizing η A ∧ ∀ y ∈ bdry A, u y = 0}

/-- The odometer of `η` in `A` with the *open* boundary condition: the pointwise least
stabilizing toppling function vanishing on `∂A`,
`v = inf {u : Ā → ℕ : u ∈ 𝓢(η, A), u = 0 on ∂A}` (Proposition 3.1(2)). Grains
leaving `A` fall off, and `v = 0` off `A`. Proposition 3.1 (`LeastActionStmt`) asserts that it is
also the longest legal toppling and the unique legal stabilizing toppling vanishing on `∂A`.
It is the `w_n` of Lemma 7.4 (with `A = B_n`) and the `v_n` of Theorem 9.1
(with `A = W_n`). For finite `A` and `d ≥ 1` the class is nonempty
(`stabilizingOpen_nonempty`) and `openOdometer η A` is its least element
(`isLeast_openOdometer_of_finite`); otherwise it is the junk value `0` when the class is empty. -/
def openOdometer (η : Site d → ℤ) (A : Set (Site d)) : Site d → ℤ :=
  pointwiseInf (stabilizingOpen η A)

theorem stabilizingOpen_subset (η : Site d → ℤ) (A : Set (Site d)) :
    stabilizingOpen η A ⊆ stabilizing η A :=
  fun _ hu => hu.1

theorem openOdometer_nonneg (η : Site d → ℤ) (A : Set (Site d)) (x : Site d) :
    0 ≤ openOdometer η A x :=
  pointwiseInf_nonneg _ x

/-- `openOdometer η A` is the least element of `stabilizingOpen η A` whenever that class is
nonempty. -/
theorem isLeast_openOdometer {η : Site d → ℤ} {A : Set (Site d)}
    (hne : (stabilizingOpen η A).Nonempty) :
    IsLeast (stabilizingOpen η A) (openOdometer η A) := by
  have hS := nonneg_of_subset_stabilizing (stabilizingOpen_subset η A)
  refine isLeast_pointwiseInf hS ⟨pointwiseInf_mem_stabilizing (stabilizingOpen_subset η A) hne,
    fun y hy => pointwiseInf_eq_zero fun u hu => hu.2 y hy⟩

/-- The open-boundary odometer vanishes off `A`: on `∂A` by
the boundary condition, off `Ā` because toppling functions vanish there. -/
theorem openOdometer_eq_zero_of_not_mem {η : Site d → ℤ} {A : Set (Site d)} {x : Site d}
    (hx : x ∉ A) : openOdometer η A x = 0 := by
  refine pointwiseInf_eq_zero fun u hu => ?_
  by_cases hxb : x ∈ bdry A
  · exact hu.2 x hxb
  · refine hu.1.1.2 x fun hc => ?_
    rcases (dClosure_eq A ▸ hc : x ∈ A ∪ bdry A) with h | h
    exacts [hx h, hxb h]

/-- The open-boundary odometer lies below every stabilizing toppling function vanishing on `∂A`
(no nonemptiness needed). -/
theorem openOdometer_le {η : Site d → ℤ} {A : Set (Site d)} {u : Site d → ℤ}
    (hu : u ∈ stabilizingOpen η A) : openOdometer η A ≤ u :=
  fun x => pointwiseInf_le (nonneg_of_subset_stabilizing (stabilizingOpen_subset η A)) hu x

open Classical in
/-- The quadratic barrier used for `stabilizingOpen_nonempty`: `C (R - x_{i₀}²)` on `A` and `0` off
`A`. -/
private def openBarrier (A : Set (Site d)) (i₀ : Fin d) (C R : ℤ) : Site d → ℤ :=
  fun y => if y ∈ A then C * (R - y i₀ ^ 2) else 0

private theorem unit_apply_sq (i i₀ : Fin d) :
    (unit i : Site d) i₀ ^ 2 = if i = i₀ then 1 else 0 := by
  by_cases h : i = i₀
  · subst h; simp [unit]
  · simp [unit, Ne.symm h, h]

/-- For finite `A` and `d ≥ 1`, some stabilizing toppling function vanishes on `∂A`: the barrier
`u = C (R - x_{i₀}²)` on `A`, `u = 0` off `A`, with `R` exceeding `x_{i₀}²` on `Ā` and
`C ≥ max_A η`, has `Δ_{ℤ^d} u ≤ -2C` in `A`. -/
theorem stabilizingOpen_nonempty (hd : 0 < d) (η : Site d → ℤ) {A : Set (Site d)}
    (hA : A.Finite) : (stabilizingOpen η A).Nonempty := by
  classical
  let i₀ : Fin d := ⟨0, hd⟩
  obtain ⟨K, hK⟩ := (hA.image fun x : Site d => |x i₀|).bddAbove
  obtain ⟨Cη, hCη⟩ := (hA.image η).bddAbove
  have hK' : ∀ x ∈ A, |x i₀| ≤ K := fun x hx => hK ⟨x, hx, rfl⟩
  have hCη' : ∀ x ∈ A, η x ≤ Cη := fun x hx => hCη ⟨x, hx, rfl⟩
  set C : ℤ := max Cη 0 with hC
  set R : ℤ := (|K| + 1) ^ 2 with hR
  have hC0 : 0 ≤ C := le_max_right _ _
  -- the quadratic `g = C (R - x_{i₀}²)` dominates the barrier at `x ∈ A` and its neighbours
  have hsq : ∀ y : Site d, |y i₀| ≤ |K| + 1 → 0 ≤ R - y i₀ ^ 2 := by
    intro y hy
    have h0 : 0 ≤ |y i₀| := abs_nonneg _
    have : y i₀ ^ 2 ≤ (|K| + 1) ^ 2 := by
      rw [← sq_abs (y i₀)]; exact pow_le_pow_left₀ h0 hy 2
    linarith
  have hnb : ∀ x ∈ A, ∀ (i : Fin d) (s : ℤ), |s| ≤ 1 →
      |(x + s • unit i) i₀| ≤ |K| + 1 := by
    intro x hx i s hs
    have hu : |s * (unit i : Site d) i₀| ≤ 1 := by
      rw [abs_mul]
      have : |(unit i : Site d) i₀| ≤ 1 := by
        by_cases h : i = i₀
        · subst h; simp [unit]
        · simp [unit, Ne.symm h]
      nlinarith [abs_nonneg s, abs_nonneg ((unit i : Site d) i₀)]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    calc |x i₀ + s * (unit i : Site d) i₀| ≤ |x i₀| + |s * (unit i : Site d) i₀| := abs_add_le _ _
      _ ≤ |K| + 1 := add_le_add ((hK' x hx).trans (le_abs_self K)) hu
  let u := openBarrier A i₀ C R
  have hule : ∀ x ∈ A, ∀ (i : Fin d) (s : ℤ), |s| ≤ 1 →
      u (x + s • unit i) ≤ C * (R - (x + s • unit i) i₀ ^ 2) := by
    intro x hx i s hs
    simp only [u, openBarrier]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg hC0 (hsq _ (hnb x hx i s hs))
  refine ⟨u, ⟨⟨fun y => ?_, fun y hy => ?_⟩, fun x hx => ?_⟩, fun y hy => ?_⟩
  · simp only [u, openBarrier]
    split_ifs with h
    · exact mul_nonneg hC0 (hsq y (by
        have := hK' y h; linarith [le_abs_self K]))
    · exact le_rfl
  · simp only [u, openBarrier, if_neg (fun h => hy (subset_dClosure A h))]
  · -- `Δ u (x) ≤ ∑_i (g(x+e_i) + g(x-e_i) - 2 g(x)) = -2C`
    have hux : u x = C * (R - x i₀ ^ 2) := by simp [u, openBarrier, hx]
    have hplus : ∀ i : Fin d, u (x + unit i) ≤ C * (R - (x + unit i) i₀ ^ 2) := fun i => by
      simpa using hule x hx i 1 (by simp)
    have hminus : ∀ i : Fin d, u (x - unit i) ≤ C * (R - (x - unit i) i₀ ^ 2) := fun i => by
      simpa [sub_eq_add_neg] using hule x hx i (-1) (by simp)
    have hlap : lap u x ≤ -2 * C := by
      rw [lap_eq_sum_second_diff]
      calc ∑ i : Fin d, (-2 * u x + u (x + unit i) + u (x - unit i))
          ≤ ∑ i : Fin d, (if i = i₀ then -2 * C else 0) := by
            refine Finset.sum_le_sum fun i _ => ?_
            have h2 : -2 * C * (unit i : Site d) i₀ ^ 2 = if i = i₀ then -2 * C else 0 := by
              rw [unit_apply_sq]; split_ifs <;> ring
            rw [← h2, hux]
            have hp := hplus i
            have hm := hminus i
            simp only [Pi.add_apply, Pi.sub_apply] at hp hm
            nlinarith [hp, hm]
        _ = -2 * C := by simp [i₀]
    have hη := hCη' x hx
    have hCη0 : Cη ≤ C := le_max_left _ _
    have hd1 : (1 : ℤ) ≤ d := by exact_mod_cast hd
    linarith
  · have hyA : y ∉ A := (mem_bdry.1 hy).1
    simp [u, openBarrier, hyA]

theorem isLeast_openOdometer_of_finite (hd : 0 < d) (η : Site d → ℤ) {A : Set (Site d)}
    (hA : A.Finite) : IsLeast (stabilizingOpen η A) (openOdometer η A) :=
  isLeast_openOdometer (stabilizingOpen_nonempty hd η hA)

/-! ### The free-boundary odometer `v_n` and the stable sandpile `s_n` (1026-1031) -/

/-- The odometer `v_n` of `η` on `W_n` with the *free* boundary condition (1026-1031):
the sandpile is `η · 1_{W_n}` (`η` in `W_n`, `0` elsewhere) and topplings may occur anywhere in
`ℤ^d`, so
`v_n = min {v : ℤ^d → ℕ : Δ_{ℤ^d} v + η 1_{W_n} ≤ 2d - 1}`,
here `pointwiseInf (stabilizing (Wn.indicator η) univ)`. The displayed set reads
`Δ_{ℤ^d} v_n` inside the braces: a typo for `Δ_{ℤ^d} v`, the bound variable. The argument `Wn` is
the lattice domain, `W_n = discretize W n` in the paper.

Junk value: `0` if the class is empty; its nonemptiness (finiteness of the free odometer) is not
proved here, see the module docstring. When it is nonempty, `freeOdometer η Wn` is the least
element (`isLeast_freeOdometer`). -/
def freeOdometer (η : Site d → ℤ) (Wn : Set (Site d)) : Site d → ℤ :=
  pointwiseInf (stabilizing (Wn.indicator η) Set.univ)

/-- The stable sandpile `s_n = η 1_{W_n} + Δ_{ℤ^d} v_n` (113) reached from `η · 1_{W_n}`
with the free boundary condition. -/
def freeSandpile (η : Site d → ℤ) (Wn : Set (Site d)) : Site d → ℤ :=
  fun x => Wn.indicator η x + lap (freeOdometer η Wn) x

theorem freeOdometer_nonneg (η : Site d → ℤ) (Wn : Set (Site d)) (x : Site d) :
    0 ≤ freeOdometer η Wn x :=
  pointwiseInf_nonneg _ x

theorem isLeast_freeOdometer {η : Site d → ℤ} {Wn : Set (Site d)}
    (hne : (stabilizing (Wn.indicator η) Set.univ).Nonempty) :
    IsLeast (stabilizing (Wn.indicator η) Set.univ) (freeOdometer η Wn) :=
  isLeast_pointwiseInf (nonneg_of_subset_stabilizing subset_rfl)
    (pointwiseInf_mem_stabilizing subset_rfl hne)

theorem freeOdometer_le {η : Site d → ℤ} {Wn : Set (Site d)} {v : Site d → ℤ}
    (hv : v ∈ stabilizing (Wn.indicator η) Set.univ) : freeOdometer η Wn ≤ v :=
  fun x => pointwiseInf_le (nonneg_of_subset_stabilizing subset_rfl) hv x

/-- `s_n` is stable, `s_n ≤ 2d - 1` on `ℤ^d`, whenever the free odometer is finite. -/
theorem freeSandpile_le {η : Site d → ℤ} {Wn : Set (Site d)}
    (hne : (stabilizing (Wn.indicator η) Set.univ).Nonempty) (x : Site d) :
    freeSandpile η Wn x ≤ 2 * (d : ℤ) - 1 := by
  have h := (mem_stabilizing_univ.1 (isLeast_freeOdometer hne).1).2 x
  simp only [freeSandpile]; linarith

/-! ### The single-source odometer -/

/-- The odometer of the sandpile `η + m δ_0` (`m` chips added at the origin) on all of `ℤ^d`: the pointwise least `v : ℤ^d → ℕ` with `Δ_{ℤ^d} v + η + m δ_0 ≤ 2d - 1`, here
`pointwiseInf (stabilizing (η + m δ_0) univ)`. Theorem 9.2 describes it as the element of
`𝓛(η + m δ_0, ℤ^d) ∩ 𝓢(η + m δ_0, ℤ^d)`; the least action principle identifies the two.

Junk value: `0` if the class is empty, e.g. for `η ≡ 2d - 1` and `m ≥ 1`; Theorem 9.2 assumes
`η ≤ 2d - 2`. When the class is nonempty it is the least element
(`isLeast_singleSourceOdometer`). -/
def singleSourceOdometer (η : Site d → ℤ) (m : ℕ) : Site d → ℤ :=
  pointwiseInf (stabilizing (fun x => η x + (m : ℤ) * dirac 0 x) Set.univ)

theorem singleSourceOdometer_nonneg (η : Site d → ℤ) (m : ℕ) (x : Site d) :
    0 ≤ singleSourceOdometer η m x :=
  pointwiseInf_nonneg _ x

theorem isLeast_singleSourceOdometer {η : Site d → ℤ} {m : ℕ}
    (hne : (stabilizing (fun x => η x + (m : ℤ) * dirac 0 x) Set.univ).Nonempty) :
    IsLeast (stabilizing (fun x => η x + (m : ℤ) * dirac 0 x) Set.univ)
      (singleSourceOdometer η m) :=
  isLeast_pointwiseInf (nonneg_of_subset_stabilizing subset_rfl)
    (pointwiseInf_mem_stabilizing subset_rfl hne)

theorem singleSourceOdometer_le {η : Site d → ℤ} {m : ℕ} {v : Site d → ℤ}
    (hv : v ∈ stabilizing (fun x => η x + (m : ℤ) * dirac 0 x) Set.univ) :
    singleSourceOdometer η m ≤ v :=
  fun x => pointwiseInf_le (nonneg_of_subset_stabilizing subset_rfl) hv x

/-! ### Rescalings (113, 1616) -/

/-- The rescaled odometer `v̄_n(x) = n⁻² v_n([nx])` (1031, 1576), with `[·]` the
coordinatewise floor `latticeRound` (see its docstring for the other readings of `[·]`, among them
the "rescaled linear interpolation"). -/
def rescaleOdo (v : Site d → ℤ) (n : ℕ) : Rd d → ℝ :=
  fun x => (v (latticeRound ((n : ℝ) • x)) : ℝ) / (n : ℝ) ^ 2

/-- The rescaled sandpile `s̄_n(x) = s_n([nx])`, real-valued so that its weak-* limit in
`L^∞(ℝ^d)` and the integral `∫ s̄_n` make sense. -/
def rescaleSandpile (s : Site d → ℤ) (n : ℕ) : Rd d → ℝ :=
  fun x => (s (latticeRound ((n : ℝ) • x)) : ℝ)

/-- The single-source scaling `v̄_n(x) = n^{-2/d} v_n([n^{1/d} x])`, where `v_n` is the
odometer of `η + n δ_0` (`singleSourceOdometer η n`). -/
def rescaleSingleSource (v : Site d → ℤ) (n : ℕ) : Rd d → ℝ :=
  fun x => (n : ℝ) ^ (-(2 / (d : ℝ))) * (v (latticeRound ((n : ℝ) ^ (1 / (d : ℝ)) • x)) : ℝ)

end RandomSandpile
