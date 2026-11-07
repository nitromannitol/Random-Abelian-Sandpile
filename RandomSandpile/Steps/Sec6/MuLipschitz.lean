import RandomSandpile.Draft.Section6
import RandomSandpile.Steps.Sec6.MuMonotone
import RandomSandpile.Proofs.Sec5.MuBounded

/-! # Lemma 6.3 (Lipschitz continuity of `μ` and `μ*` in `l`): proof steps

The proof of Lemma 6.3 (`MuLipschitzStmt`), repaired as in ,
decomposed into step statements, and the reduction `muLipschitz_of_steps` concluding exactly
`MuLipschitzStmt` from them.

The printed proof applies Lemma 6.2 with `β = 1 - s`. It needs a bending of size `≍ s n²` at
`∂B_n` from every contact point of `B_{(1-s)n}`, and it needs `w_n` close to achieving the
supremum in `μ(B_n, η, l, M)`. As drafted, Lemma 6.2 (`StrictConcavityStmt`) provides neither: its
constant is uniform in `β`, but its proof only gives `C(β) ≍ (1-β)²`, and its
`w_n` is not near-maximizing. The repaired argument uses three steps:

* `NearMaxBendingStmt` (Lemma 6.2', proposed replacement of Lemma 6.2): a near-maximizing
  `w_n ∈ S(B_n, η, l, M)` whose gap at `y ∈ ∂B_n` above the supporting plane at a contact point
  `x₀ ∈ B_{βn}` is at least `c α (1-β) n |y - x₀|`, with `c` independent of `β`. This is what the
  printed proof of Lemma 6.2 gives (uniform concavity `D²φ̄ ≤ -λ` of the limit and convexity of the
  gap along rays). Dually for `μ*`.
* `ShellBoundStmt`, a consequence of Lemma 5.5 on the annulus `B_1 \ B̄_{1-τ}`: the supergradients
  of any `w ∈ S(B_n, η, l, M)` at the points of the shell `B_n \ B_{(1-τ)n}` have measure at most
  `((1 - (1-τ)^d) μ(l, M) + ε) |B_n| ≤ (d τ μ(l, M) + ε) |B_n|` for large `n`. The per-site bound of Lemma 5.4 would give density
  `C_{ηmax, l, M}` in place of `μ(l, M)`, hence only Hölder-`1/2` continuity.
* `BoundaryGapStmt`, deterministic (the ABP argument): if `f - p · (·)` is larger at
  some `x₀ ∈ A` than everywhere on `∂A`, then `p ∈ ∂⁺(f, A)`; dually for `∂⁻`.

The level shift `S(A, η, l, M) + q_s = S(A, η, l - s, M)` is `PerturbedShiftStmt` (Lemma 6.1). The
finiteness of the limit at level `l - s` (resp. `l + s`) comes from the support lemmas
`mu_le_ncard`, `muStar_le_ncard` of Lemma 5.4. The constant of Lemma 6.3 is `C = 3 / (2c)`.

Reading. `B_r = ballZ0 r` and `∂B_n = bdry (ballZ0 n)`. The shell is
`ballZ0 n \ ballZ0 ((1 - τ) n)`. The near-maximizing property is stated against the deterministic
limit: `|∂⁺(w_n, B_n)| ≥ (μ(l, M) - ε) |B_n|`. -/

open MeasureTheory LatticeProb Filter
open scoped ENNReal

namespace RandomSandpile

/-- Step 1 (Lemma 6.2', the corrected form of Lemma 6.2 that its printed proof establishes). There is `c = c(ηmin, ηmax, l, M, d) > 0` with the following
property. If `α := μ(l, M) > 0`, then for a.e. `η`, every `ε > 0` and every `0 < β < 1`, for all
large `n` some `w_n ∈ S(B_n, η, l, M)` is near-maximizing, `|∂⁺(w_n, B_n)| ≥ (α - ε) |B_n|`, and
bends: for `x₀ ∈ B_{βn}`, `p₀ ∈ ∂⁺(w_n, x₀, B_n)` and `y ∈ ∂B_n`,
`w_n(y) ≤ w_n(x₀) + p₀ · (y - x₀) - c α (1-β) n |y - x₀|`. Dually for `μ*`, with `S*`, `∂⁻` and the
reversed inequality.

Since `|y - x₀| ≥ (1-β) n`, the bending implies the drop `c (1-β)² α n²` of the drafted Lemma 6.2,
with a constant that depends on `β`. A nonempty `∂⁺(w_n, x₀, B_n)` forces `x₀` to be a contact
point (`concaveEnvelopeOn_eq_iff_supGrad_nonempty`), so the contact condition is not repeated. -/
def NearMaxBendingStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ (ηmin ηmax : ℤ) (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ),
    ∃ c : ℝ, 0 < c ∧ ∀ E : RandomEnvironment d, E.ηmin = ηmin → E.ηmax = ηmax →
      (0 < muBar E l M →
        ∀ᵐ η ∂E.P, ∀ ε : ℝ, 0 < ε → ∀ β : ℝ, 0 < β → β < 1 → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
          ∃ w ∈ perturbedSub (ballZ0 (n : ℝ)) η l M,
            ENNReal.ofReal ((muBar E l M - ε) * ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ)) ≤
                volume (supGradSet w (ballZ0 (n : ℝ))) ∧
              ∀ x₀ ∈ ballZ0 (β * n), ∀ p₀ ∈ supGrad w x₀ (ballZ0 (n : ℝ)),
                ∀ y ∈ bdry (ballZ0 (d := d) (n : ℝ)),
                  w y ≤ w x₀ + inner ℝ p₀ (toE y - toE x₀) -
                    c * muBar E l M * ((1 - β) * n) * ‖toE y - toE x₀‖) ∧
      (0 < muStarBar E l M →
        ∀ᵐ η ∂E.P, ∀ ε : ℝ, 0 < ε → ∀ β : ℝ, 0 < β → β < 1 → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
          ∃ w ∈ perturbedSuper (ballZ0 (n : ℝ)) η l M,
            ENNReal.ofReal ((muStarBar E l M - ε) * ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ)) ≤
                volume (subGradSet w (ballZ0 (n : ℝ))) ∧
              ∀ x₀ ∈ ballZ0 (β * n), ∀ p₀ ∈ subGrad w x₀ (ballZ0 (n : ℝ)),
                ∀ y ∈ bdry (ballZ0 (d := d) (n : ℝ)),
                  w x₀ + inner ℝ p₀ (toE y - toE x₀) +
                    c * muStarBar E l M * ((1 - β) * n) * ‖toE y - toE x₀‖ ≤ w y)

/-- Step 2 (the shell estimate; Lemma 5.5 on the annulus `W = B_1 \ B̄_{1-τ}`). For a.e. `η`, every
`0 < τ < 1` and `ε > 0`, and all large `n`, every `w ∈ S(B_n, η, l, M)` satisfies
`|⋃_{x ∈ B_n \ B_{(1-τ)n}} ∂⁺(w, x, B_n)| ≤ ((1 - (1-τ)^d) μ(l, M) + ε) |B_n|`; dually for `μ*`.

Derivation. Restricting `u ∈ 𝓛(η, B_n)` to the closure of the shell gives an element of `𝓛` of
the shell (`LocLegalRestrictStmt`). Testing on a smaller set enlarges supergradients, so the left
side is at most `μ(shell)`. Lemma 5.5 gives `μ(shell) = (μ(l, M) + o(1)) |shell|`, and lattice-point
counting gives `|shell| = (1 - (1-τ)^d + o(1)) |B_n|`. The reduction uses `1 - (1-τ)^d ≤ d τ`. The statement is made
for every `M`: `q_M` only sees the symmetric part of `M`. -/
def ShellBoundStmt : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ (E : RandomEnvironment d) (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ),
    ∀ᵐ η ∂E.P, ∀ τ : ℝ, 0 < τ → τ < 1 → ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      (∀ w ∈ perturbedSub (ballZ0 (n : ℝ)) η l M,
        volume (⋃ x ∈ ballZ0 (d := d) (n : ℝ) \ ballZ0 ((1 - τ) * n),
            supGrad w x (ballZ0 (n : ℝ))) ≤
          ENNReal.ofReal (((1 - (1 - τ) ^ d) * muBar E l M + ε) *
            ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ))) ∧
      (∀ w ∈ perturbedSuper (ballZ0 (n : ℝ)) η l M,
        volume (⋃ x ∈ ballZ0 (d := d) (n : ℝ) \ ballZ0 ((1 - τ) * n),
            subGrad w x (ballZ0 (n : ℝ))) ≤
          ENNReal.ofReal (((1 - (1 - τ) ^ d) * muStarBar E l M + ε) *
            ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ)))

/-- Step 3 (the ABP argument). Let `Ā` be finite and `x₀ ∈ A`. If
`f(y) - p · y < f(x₀) - p · x₀` for every `y ∈ ∂A`, then the maximum of `f - p · (·)` over `Ā` is
attained in `A`, so `p ∈ ∂⁺(f, A)`. Dually, if `f(x₀) - p · x₀ < f(y) - p · y` on `∂A`, then
`p ∈ ∂⁻(f, A)`. -/
def BoundaryGapStmt : Prop :=
  ∀ (d : ℕ) (A : Set (Site d)) (f : Site d → ℝ) (x₀ : Site d) (p : Rd d),
    (dClosure A).Finite → x₀ ∈ A →
      ((∀ y ∈ bdry A, f y - inner ℝ p (toE y) < f x₀ - inner ℝ p (toE x₀)) →
          p ∈ supGradSet f A) ∧
        ((∀ y ∈ bdry A, f x₀ - inner ℝ p (toE x₀) < f y - inner ℝ p (toE y)) →
          p ∈ subGradSet f A)

namespace MuLipschitz

variable {d : ℕ}

/-! ### Lattice balls

The next lemmas (except `toE_zero`, `dClosure_ballZ0_finite`, `ncard_ballZ0_pos`) are copied from `RandomSandpile/Steps/Sec7/OdometerLowerBound.lean` (same
proofs), inside the namespace `MuLipschitz` to avoid a name clash. -/

theorem toE_zero : toE (0 : Site d) = 0 := by
  ext i; simp

theorem mem_ballZ0 {r : ℝ} {x : Site d} : x ∈ ballZ0 r ↔ ‖toE x‖ < r := by
  simp [ballZ0, ballZ, toE_zero]

/-- The lattice ball `B_r` is finite. -/
theorem ballZ0_finite (r : ℝ) : (ballZ0 (d := d) r).Finite := by
  refine (Set.finite_Icc (fun _ : Fin d => -⌈r⌉) fun _ => ⌈r⌉).subset fun x hx => ?_
  have hx' := mem_ballZ0.1 hx
  have hi : ∀ i, |(x i : ℝ)| < r := fun i => by
    have := PiLp.norm_apply_le (toE x) i
    simp only [toE_apply, Real.norm_eq_abs] at this
    linarith
  refine ⟨fun i => ?_, fun i => ?_⟩
  · have h1 := (abs_lt.1 (hi i)).1
    have h2 : (-⌈r⌉ : ℝ) ≤ x i := by linarith [Int.le_ceil r]
    exact_mod_cast h2
  · have h1 := (abs_lt.1 (hi i)).2
    have h2 : (x i : ℝ) ≤ ⌈r⌉ := by linarith [Int.le_ceil r]
    exact_mod_cast h2

theorem toE_add (x y : Site d) : toE (x + y) = toE x + toE y := by
  ext i; simp

theorem toE_sub (x y : Site d) : toE (x - y) = toE x - toE y := by
  ext i; simp

theorem norm_toE_unit (i : Fin d) : ‖toE (unit i)‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  simp [unit, Pi.single_apply, apply_ite]

/-- On `∂B_r`, `|y| ≥ r`. -/
theorem le_norm_of_mem_bdry_ballZ0 {r : ℝ} {y : Site d} (hy : y ∈ bdry (ballZ0 r)) :
    r ≤ ‖toE y‖ :=
  not_lt.1 fun h => (mem_bdry.1 hy).1 (mem_ballZ0.2 h)

/-- On `∂B_r`, `|y| < r + 1`. -/
theorem norm_lt_of_mem_bdry_ballZ0 {r : ℝ} {y : Site d} (hy : y ∈ bdry (ballZ0 r)) :
    ‖toE y‖ < r + 1 := by
  obtain ⟨-, x, hx, i, hi | hi⟩ := mem_bdry.1 hy
  · have hy' : y = x - unit i := by rw [hi]; abel
    rw [hy', toE_sub]
    calc ‖toE x - toE (unit i)‖ ≤ ‖toE x‖ + ‖toE (unit i)‖ := norm_sub_le _ _
      _ < r + 1 := by rw [norm_toE_unit]; linarith [mem_ballZ0.1 hx]
  · rw [hi, toE_add]
    calc ‖toE x + toE (unit i)‖ ≤ ‖toE x‖ + ‖toE (unit i)‖ := norm_add_le _ _
      _ < r + 1 := by rw [norm_toE_unit]; linarith [mem_ballZ0.1 hx]

/-- The closure `B̄_r` is finite. -/
theorem dClosure_ballZ0_finite (r : ℝ) : (dClosure (ballZ0 (d := d) r)).Finite := by
  refine (ballZ0_finite (r + 1)).subset fun y hy => ?_
  rcases hy with hy | hy
  · exact mem_ballZ0.2 (by linarith [mem_ballZ0.1 hy])
  · exact mem_ballZ0.2 (norm_lt_of_mem_bdry_ballZ0 hy)

theorem ncard_ballZ0_pos {n : ℕ} (hn : 1 ≤ n) : 0 < (ballZ0 (d := d) (n : ℝ)).ncard :=
  Set.ncard_pos (ballZ0_finite _) |>.2
    ⟨0, mem_ballZ0.2 (by simp only [toE_zero, norm_zero]; exact_mod_cast hn)⟩

/-! ### The quadratic comparison (Step 1 of the repaired proof) -/

/-- For `|x₀| < n` and `y ∈ ∂B_n`: `q_s(y) - q_s(x₀) < (3 s n / (2d)) |y - x₀|`. -/
theorem qlZ_sub_lt {s κ : ℝ} {n : ℕ} {x₀ y : Site d} (hd : 1 ≤ d) (hs : 0 < s)
    (hx : ‖toE x₀‖ < n) (hy : y ∈ bdry (ballZ0 (n : ℝ))) (hκ : 3 * s * n / (2 * d) ≤ κ) :
    qlZ s y - qlZ s x₀ < κ * ‖toE y - toE x₀‖ := by
  have hy1 := le_norm_of_mem_bdry_ballZ0 hy
  have hy2 := norm_lt_of_mem_bdry_ballZ0 hy
  have hD : ‖toE y‖ - ‖toE x₀‖ ≤ ‖toE y - toE x₀‖ := norm_sub_norm_le _ _
  have hx0 : 0 ≤ ‖toE x₀‖ := norm_nonneg _
  have hDpos : 0 < ‖toE y - toE x₀‖ := by linarith
  have hn : (1 : ℝ) ≤ n := by
    have : (0 : ℝ) < n := by linarith
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (by exact_mod_cast this.ne')
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have key : ‖toE y‖ ^ 2 - ‖toE x₀‖ ^ 2 < 3 * n * ‖toE y - toE x₀‖ := by
    have h1 : ‖toE y‖ ^ 2 - ‖toE x₀‖ ^ 2 = (‖toE y‖ - ‖toE x₀‖) * (‖toE y‖ + ‖toE x₀‖) := by
      ring
    rw [h1]
    calc (‖toE y‖ - ‖toE x₀‖) * (‖toE y‖ + ‖toE x₀‖)
        ≤ ‖toE y - toE x₀‖ * (‖toE y‖ + ‖toE x₀‖) :=
          mul_le_mul_of_nonneg_right hD (by linarith)
      _ < ‖toE y - toE x₀‖ * (2 * n + 1) := mul_lt_mul_of_pos_left (by linarith) hDpos
      _ ≤ 3 * n * ‖toE y - toE x₀‖ := by nlinarith
  simp only [qlZ, ql]
  rw [← sub_div, div_lt_iff₀ (by positivity)]
  calc s * ‖toE y‖ ^ 2 - s * ‖toE x₀‖ ^ 2 = s * (‖toE y‖ ^ 2 - ‖toE x₀‖ ^ 2) := by ring
    _ < s * (3 * n * ‖toE y - toE x₀‖) := mul_lt_mul_of_pos_left key hs
    _ = 3 * s * n / (2 * d) * ‖toE y - toE x₀‖ * (2 * d) := by field_simp
    _ ≤ κ * ‖toE y - toE x₀‖ * (2 * d) := by gcongr

/-- A bending of size `κ |y - x₀|` with `κ ≥ 3 s n / (2d)` puts the slope `p` into
`∂⁺(w + q_s, B_n)`. -/
theorem mem_supGradSet_add_qlZ (hABP : BoundaryGapStmt) {n : ℕ} {s κ : ℝ} {w : Site d → ℝ}
    {x₀ : Site d} {p : Rd d} (hd : 1 ≤ d) (hs : 0 < s) (hx₀ : x₀ ∈ ballZ0 (n : ℝ))
    (hκ : 3 * s * n / (2 * d) ≤ κ)
    (hbend : ∀ y ∈ bdry (ballZ0 (d := d) (n : ℝ)),
      w y ≤ w x₀ + inner ℝ p (toE y - toE x₀) - κ * ‖toE y - toE x₀‖) :
    p ∈ supGradSet (fun x => w x + qlZ s x) (ballZ0 (n : ℝ)) := by
  refine (hABP d _ _ x₀ p (dClosure_ballZ0_finite _) hx₀).1 fun y hy => ?_
  have h1 := qlZ_sub_lt hd hs (mem_ballZ0.1 hx₀) hy hκ
  have h2 := hbend y hy
  rw [inner_sub_right] at h2
  linarith

/-- Dual of `mem_supGradSet_add_qlZ`: the slope `p` lies in `∂⁻(w - q_s, B_n)`. -/
theorem mem_subGradSet_sub_qlZ (hABP : BoundaryGapStmt) {n : ℕ} {s κ : ℝ} {w : Site d → ℝ}
    {x₀ : Site d} {p : Rd d} (hd : 1 ≤ d) (hs : 0 < s) (hx₀ : x₀ ∈ ballZ0 (n : ℝ))
    (hκ : 3 * s * n / (2 * d) ≤ κ)
    (hbend : ∀ y ∈ bdry (ballZ0 (d := d) (n : ℝ)),
      w x₀ + inner ℝ p (toE y - toE x₀) + κ * ‖toE y - toE x₀‖ ≤ w y) :
    p ∈ subGradSet (fun x => w x - qlZ s x) (ballZ0 (n : ℝ)) := by
  refine (hABP d _ _ x₀ p (dClosure_ballZ0_finite _) hx₀).2 fun y hy => ?_
  have h1 := qlZ_sub_lt hd hs (mem_ballZ0.1 hx₀) hy hκ
  have h2 := hbend y hy
  rw [inner_sub_right] at h2
  linarith

/-! ### The finite-`n` inequality -/

/-- Splitting `B_n` into `B_{(1-τ)n}` and the shell: a near-maximizing bent `w ∈ S(B_n, η, l, M)`
with a small shell gives `μ(B_n, η, l - s, M) ≥ (α - C s - 2ε) |B_n|`. -/
theorem ofReal_le_mu_sub (hshift : PerturbedShiftStmt) (hABP : BoundaryGapStmt)
    {η : Site d → ℤ} {l s α ε τ κ Cs : ℝ} {M : Matrix (Fin d) (Fin d) ℝ} {n : ℕ} (hd : 1 ≤ d)
    (hs : 0 < s) (hCs : 0 ≤ Cs + ε) (hκ : 3 * s * n / (2 * d) ≤ κ) {w : Site d → ℝ}
    (hw : w ∈ perturbedSub (ballZ0 (n : ℝ)) η l M)
    (hN : ENNReal.ofReal ((α - ε) * ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ)) ≤
      volume (supGradSet w (ballZ0 (n : ℝ))))
    (hB : ∀ x₀ ∈ ballZ0 ((1 - τ) * n), ∀ p₀ ∈ supGrad w x₀ (ballZ0 (n : ℝ)),
      ∀ y ∈ bdry (ballZ0 (d := d) (n : ℝ)),
        w y ≤ w x₀ + inner ℝ p₀ (toE y - toE x₀) - κ * ‖toE y - toE x₀‖)
    (hS : volume (⋃ x ∈ ballZ0 (d := d) (n : ℝ) \ ballZ0 ((1 - τ) * n),
        supGrad w x (ballZ0 (n : ℝ))) ≤
      ENNReal.ofReal ((Cs + ε) * ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ))) :
    ENNReal.ofReal ((α - Cs - 2 * ε) * ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ)) ≤
      mu (ballZ0 (n : ℝ)) η (l - s) M := by
  set B := ballZ0 (d := d) (n : ℝ)
  set N : ℝ := (B.ncard : ℝ)
  -- the shifted function lies in `S(B_n, η, l - s, M)`
  have hw' : (fun x => w x + qlZ s x) ∈ perturbedSub B η (l - s) M := by
    have h := (hshift d B η (l - s) s M).1
    rw [sub_add_cancel] at h
    rw [h] at hw
    obtain ⟨w', hw', rfl⟩ := hw
    convert hw' using 1
    funext x
    simp
  have hinner : (⋃ x ∈ B ∩ ballZ0 ((1 - τ) * n), supGrad w x B) ⊆
      supGradSet (fun x => w x + qlZ s x) B := by
    intro p hp
    simp only [Set.mem_iUnion] at hp
    obtain ⟨x₀, ⟨hx₀, hx₀'⟩, hp⟩ := hp
    exact mem_supGradSet_add_qlZ hABP hd hs hx₀ hκ (hB x₀ hx₀' p hp)
  have hsplit : supGradSet w B ⊆ (⋃ x ∈ B ∩ ballZ0 ((1 - τ) * n), supGrad w x B) ∪
      ⋃ x ∈ B \ ballZ0 ((1 - τ) * n), supGrad w x B := by
    intro p hp
    simp only [supGradSet, Set.mem_iUnion] at hp
    obtain ⟨x, hx, hp⟩ := hp
    by_cases hx' : x ∈ ballZ0 ((1 - τ) * n)
    · exact Or.inl (Set.mem_biUnion ⟨hx, hx'⟩ hp)
    · exact Or.inr (Set.mem_biUnion ⟨hx, hx'⟩ hp)
  have hmu : volume (supGradSet (fun x => w x + qlZ s x) B) ≤ mu B η (l - s) M :=
    le_iSup₂ (f := fun w (_ : w ∈ perturbedSub B η (l - s) M) => volume (supGradSet w B)) _ hw'
  have htot : ENNReal.ofReal ((α - ε) * N) ≤
      mu B η (l - s) M + ENNReal.ofReal ((Cs + ε) * N) :=
    hN.trans <| (measure_mono hsplit).trans <| (measure_union_le _ _).trans <|
      add_le_add ((measure_mono hinner).trans hmu) hS
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  calc ENNReal.ofReal ((α - Cs - 2 * ε) * N)
      = ENNReal.ofReal ((α - ε) * N - (Cs + ε) * N) := by ring_nf
    _ = ENNReal.ofReal ((α - ε) * N) - ENNReal.ofReal ((Cs + ε) * N) :=
        ENNReal.ofReal_sub _ (mul_nonneg hCs hN0)
    _ ≤ mu B η (l - s) M := tsub_le_iff_right.2 htot

/-- Dual of `ofReal_le_mu_sub`: `μ*(B_n, η, l + s, M) ≥ (α* - C s - 2ε) |B_n|`. -/
theorem ofReal_le_muStar_add (hshift : PerturbedShiftStmt) (hABP : BoundaryGapStmt)
    {η : Site d → ℤ} {l s α ε τ κ Cs : ℝ} {M : Matrix (Fin d) (Fin d) ℝ} {n : ℕ} (hd : 1 ≤ d)
    (hs : 0 < s) (hCs : 0 ≤ Cs + ε) (hκ : 3 * s * n / (2 * d) ≤ κ) {w : Site d → ℝ}
    (hw : w ∈ perturbedSuper (ballZ0 (n : ℝ)) η l M)
    (hN : ENNReal.ofReal ((α - ε) * ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ)) ≤
      volume (subGradSet w (ballZ0 (n : ℝ))))
    (hB : ∀ x₀ ∈ ballZ0 ((1 - τ) * n), ∀ p₀ ∈ subGrad w x₀ (ballZ0 (n : ℝ)),
      ∀ y ∈ bdry (ballZ0 (d := d) (n : ℝ)),
        w x₀ + inner ℝ p₀ (toE y - toE x₀) + κ * ‖toE y - toE x₀‖ ≤ w y)
    (hS : volume (⋃ x ∈ ballZ0 (d := d) (n : ℝ) \ ballZ0 ((1 - τ) * n),
        subGrad w x (ballZ0 (n : ℝ))) ≤
      ENNReal.ofReal ((Cs + ε) * ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ))) :
    ENNReal.ofReal ((α - Cs - 2 * ε) * ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ)) ≤
      muStar (ballZ0 (n : ℝ)) η (l + s) M := by
  set B := ballZ0 (d := d) (n : ℝ)
  set N : ℝ := (B.ncard : ℝ)
  have hw' : (fun x => w x - qlZ s x) ∈ perturbedSuper B η (l + s) M := by
    have h := (hshift d B η (l + s) s M).2
    rw [add_sub_cancel_right] at h
    rw [h] at hw
    obtain ⟨w', hw', rfl⟩ := hw
    convert hw' using 1
    funext x
    simp
  have hinner : (⋃ x ∈ B ∩ ballZ0 ((1 - τ) * n), subGrad w x B) ⊆
      subGradSet (fun x => w x - qlZ s x) B := by
    intro p hp
    simp only [Set.mem_iUnion] at hp
    obtain ⟨x₀, ⟨hx₀, hx₀'⟩, hp⟩ := hp
    exact mem_subGradSet_sub_qlZ hABP hd hs hx₀ hκ (hB x₀ hx₀' p hp)
  have hsplit : subGradSet w B ⊆ (⋃ x ∈ B ∩ ballZ0 ((1 - τ) * n), subGrad w x B) ∪
      ⋃ x ∈ B \ ballZ0 ((1 - τ) * n), subGrad w x B := by
    intro p hp
    simp only [subGradSet, Set.mem_iUnion] at hp
    obtain ⟨x, hx, hp⟩ := hp
    by_cases hx' : x ∈ ballZ0 ((1 - τ) * n)
    · exact Or.inl (Set.mem_biUnion ⟨hx, hx'⟩ hp)
    · exact Or.inr (Set.mem_biUnion ⟨hx, hx'⟩ hp)
  have hmu : volume (subGradSet (fun x => w x - qlZ s x) B) ≤ muStar B η (l + s) M :=
    le_iSup₂ (f := fun w (_ : w ∈ perturbedSuper B η (l + s) M) => volume (subGradSet w B))
      _ hw'
  have htot : ENNReal.ofReal ((α - ε) * N) ≤
      muStar B η (l + s) M + ENNReal.ofReal ((Cs + ε) * N) :=
    hN.trans <| (measure_mono hsplit).trans <| (measure_union_le _ _).trans <|
      add_le_add ((measure_mono hinner).trans hmu) hS
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  calc ENNReal.ofReal ((α - Cs - 2 * ε) * N)
      = ENNReal.ofReal ((α - ε) * N - (Cs + ε) * N) := by ring_nf
    _ = ENNReal.ofReal ((α - ε) * N) - ENNReal.ofReal ((Cs + ε) * N) :=
        ENNReal.ofReal_sub _ (mul_nonneg hCs hN0)
    _ ≤ muStar B η (l + s) M := tsub_le_iff_right.2 htot

/-! ### Passing to the limit -/

/-- If `F η n ≤ K` eventually and `F η n ≥ a - ε` eventually for every `ε > 0`, both for a.e. `η`,
then `a ≤ (∫⁻ limsup_n F η n).toReal`. -/
theorem le_toReal_lintegral_limsup {E : RandomEnvironment d} {F : Config d → ℕ → ℝ≥0∞} {K a : ℝ}
    (hK : ∀ᵐ η ∂E.P, ∀ᶠ n in atTop, F η n ≤ ENNReal.ofReal K)
    (ha : ∀ᵐ η ∂E.P, ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ENNReal.ofReal (a - ε) ≤ F η n) :
    a ≤ (∫⁻ η, limsup (F η) atTop ∂E.P).toReal := by
  have hfin : ∫⁻ η, limsup (F η) atTop ∂E.P ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := ∫⁻ _, ENNReal.ofReal K ∂E.P) (by simp) ?_
    exact lintegral_mono_ae (hK.mono fun η h => limsup_le_of_le (by isBoundedDefault) h)
  have hlow : ∫⁻ _, ENNReal.ofReal a ∂E.P ≤ ∫⁻ η, limsup (F η) atTop ∂E.P := by
    refine lintegral_mono_ae (ha.mono fun η h => ?_)
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    have h1 : ENNReal.ofReal (a - ε) ≤ limsup (F η) atTop :=
      le_limsup_of_frequently_le (h ε (by exact_mod_cast hε)).frequently (by isBoundedDefault)
    calc ENNReal.ofReal a = ENNReal.ofReal ((a - ε) + ε) := by ring_nf
      _ ≤ ENNReal.ofReal (a - ε) + ENNReal.ofReal ε := ENNReal.ofReal_add_le
      _ ≤ limsup (F η) atTop + ε := by rw [ENNReal.ofReal_coe_nnreal]; gcongr
  rw [lintegral_const, measure_univ, mul_one] at hlow
  exact (ENNReal.ofReal_le_iff_le_toReal hfin).1 hlow

/-- `ofReal r ≤ m / |B_n|` from `ofReal (r |B_n|) ≤ m`, for `n ≥ 1`. -/
theorem ofReal_le_div_ncard {r : ℝ} {m : ℝ≥0∞} {n : ℕ} (hn : 1 ≤ n)
    (h : ENNReal.ofReal (r * ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ)) ≤ m) :
    ENNReal.ofReal r ≤ m / ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ≥0∞) := by
  have hpos := ncard_ballZ0_pos (d := d) hn
  rw [ENNReal.le_div_iff_mul_le (Or.inl (by exact_mod_cast hpos.ne')) (Or.inl (by simp))]
  rwa [ENNReal.ofReal_mul' (Nat.cast_nonneg _), ENNReal.ofReal_natCast] at h

/-- `m / |B_n| ≤ ofReal K` from `m ≤ ofReal (K |B_n|)`, for `n ≥ 1`. -/
theorem div_ncard_le_ofReal {K : ℝ} {m : ℝ≥0∞} {n : ℕ}
    (h : m ≤ ENNReal.ofReal (K * ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ))) :
    m / ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ≥0∞) ≤ ENNReal.ofReal K := by
  refine ENNReal.div_le_of_le_mul ?_
  rwa [ENNReal.ofReal_mul' (Nat.cast_nonneg _), ENNReal.ofReal_natCast] at h

end MuLipschitz

open MuLipschitz in
/-- **Reduction for Lemma 6.3** (repaired proof). The bending of near-maximizers
(`NearMaxBendingStmt`, Lemma 6.2'), the shell estimate (`ShellBoundStmt`, from Lemma 5.5), the ABP
argument (`BoundaryGapStmt`) and the level shift (`PerturbedShiftStmt`) give `MuLipschitzStmt`
with `C = 3 / (2c)`. -/
theorem muLipschitz_of_steps (hshift : PerturbedShiftStmt) (hABP : BoundaryGapStmt)
    (hbend : NearMaxBendingStmt) (hshell : ShellBoundStmt) : MuLipschitzStmt := by
  intro d hd ηmin ηmax l M
  obtain ⟨c, hc, hcE⟩ := hbend d hd ηmin ηmax l M
  have hd1 : 1 ≤ d := by omega
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  refine ⟨3 / (2 * c), by positivity, fun E hmin hmax s hs0 _ => ⟨?_, ?_⟩⟩
  · -- `μ(l) ≤ μ(l - s) + s C`
    set α := muBar E l M with hαdef
    have hnn : 0 ≤ muBar E (l - s) M := ENNReal.toReal_nonneg
    by_cases hα : α ≤ 3 / (2 * c) * s
    · linarith
    rw [not_le] at hα
    have hαpos : 0 < α := lt_of_le_of_lt (by positivity) hα
    set τ := 3 * s / (2 * d * c * α) with hτ
    have hτpos : 0 < τ := by positivity
    have hτ1 : τ < 1 := by
      rw [hτ, div_lt_one (by positivity)]
      have : 3 / (2 * c) * s * 1 ≤ 3 / (2 * c) * s * d := by
        gcongr; exact_mod_cast hd1
      have h2 : 3 / (2 * c) * s * d < α * d := by nlinarith
      calc 3 * s = 3 / (2 * c) * s * (2 * c) := by field_simp
        _ < α * d * (2 * c) := by nlinarith
        _ = 2 * d * c * α := by ring
    have hdτα : d * τ * α = 3 / (2 * c) * s := by
      rw [hτ]; field_simp
    have hκ : ∀ n : ℕ, 3 * s * n / (2 * d) ≤ c * α * ((1 - (1 - τ)) * n) := by
      intro n
      rw [sub_sub_cancel, hτ]
      apply le_of_eq
      field_simp
    suffices h : α - 3 / (2 * c) * s ≤ muBar E (l - s) M by linarith
    obtain ⟨K, hK⟩ : ∃ K : ℝ, ∀ᵐ η ∂E.P, ∀ n : ℕ,
        mu (ballZ0 (n : ℝ)) η (l - s) M ≤
          ENNReal.ofReal (K * ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ)) := by
      refine ⟨_, (ae_all_iff.2 fun x => (E.bounded x).mono fun _ h => h.2).mono
        fun η hη n => mu_le_ncard hd1 (ballZ0_finite _) (fun x _ => hη x) (l - s) M⟩
    refine le_toReal_lintegral_limsup (K := K)
      (hK.mono fun η h => Eventually.of_forall fun n => div_ncard_le_ofReal (h n)) ?_
    filter_upwards [(hcE E hmin hmax).1 hαpos, hshell d hd E l M] with η hb hsh
    intro ε hε
    obtain ⟨n₀, hn₀⟩ := hb (ε / 2) (by positivity) (1 - τ) (by linarith) (by linarith)
    obtain ⟨n₁, hn₁⟩ := hsh τ hτpos hτ1 (ε / 2) (by positivity)
    filter_upwards [eventually_ge_atTop (max (max n₀ n₁) 1)] with n hn
    have hn0 : n₀ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
    have hn1 : n₁ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
    have hn2 : 1 ≤ n := le_trans (le_max_right _ _) hn
    obtain ⟨w, hw, hN, hB⟩ := hn₀ n hn0
    have hS := (hn₁ n hn1).1 w hw
    have hbern : 1 - d * τ ≤ (1 - τ) ^ d := by
      have := one_add_mul_le_pow (show (-2 : ℝ) ≤ -τ by linarith) d
      rw [← sub_eq_add_neg, mul_neg, ← sub_eq_add_neg] at this
      exact this
    have hcoef : (1 - (1 - τ) ^ d) * α ≤ 3 / (2 * c) * s := by
      rw [← hdτα]; nlinarith
    have := ofReal_le_mu_sub (Cs := 3 / (2 * c) * s) hshift hABP hd1 hs0 (by positivity) (hκ n)
      hw hN hB (hS.trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (by rw [hαdef] at hcoef; linarith) (Nat.cast_nonneg _))))
    refine ofReal_le_div_ncard hn2 (le_trans (le_of_eq ?_) this)
    congr 1
    rw [hαdef]
    ring
  · -- `μ*(l) ≤ μ*(l + s) + s C`
    set α := muStarBar E l M with hαdef
    have hnn : 0 ≤ muStarBar E (l + s) M := ENNReal.toReal_nonneg
    by_cases hα : α ≤ 3 / (2 * c) * s
    · linarith
    rw [not_le] at hα
    have hαpos : 0 < α := lt_of_le_of_lt (by positivity) hα
    set τ := 3 * s / (2 * d * c * α) with hτ
    have hτpos : 0 < τ := by positivity
    have hτ1 : τ < 1 := by
      rw [hτ, div_lt_one (by positivity)]
      have : 3 / (2 * c) * s * 1 ≤ 3 / (2 * c) * s * d := by
        gcongr; exact_mod_cast hd1
      have h2 : 3 / (2 * c) * s * d < α * d := by nlinarith
      calc 3 * s = 3 / (2 * c) * s * (2 * c) := by field_simp
        _ < α * d * (2 * c) := by nlinarith
        _ = 2 * d * c * α := by ring
    have hdτα : d * τ * α = 3 / (2 * c) * s := by
      rw [hτ]; field_simp
    have hκ : ∀ n : ℕ, 3 * s * n / (2 * d) ≤ c * α * ((1 - (1 - τ)) * n) := by
      intro n
      rw [sub_sub_cancel, hτ]
      apply le_of_eq
      field_simp
    suffices h : α - 3 / (2 * c) * s ≤ muStarBar E (l + s) M by linarith
    obtain ⟨K, hK⟩ : ∃ K : ℝ, ∀ᵐ η ∂E.P, ∀ n : ℕ,
        muStar (ballZ0 (n : ℝ)) η (l + s) M ≤
          ENNReal.ofReal (K * ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ)) := by
      refine ⟨_, (ae_all_iff.2 fun x => (E.bounded x).mono fun _ h => h.1).mono
        fun η hη n => muStar_le_ncard hd1 (ballZ0_finite _) (fun x _ => hη x) (l + s) M⟩
    refine le_toReal_lintegral_limsup (K := K)
      (hK.mono fun η h => Eventually.of_forall fun n => div_ncard_le_ofReal (h n)) ?_
    filter_upwards [(hcE E hmin hmax).2 hαpos, hshell d hd E l M] with η hb hsh
    intro ε hε
    obtain ⟨n₀, hn₀⟩ := hb (ε / 2) (by positivity) (1 - τ) (by linarith) (by linarith)
    obtain ⟨n₁, hn₁⟩ := hsh τ hτpos hτ1 (ε / 2) (by positivity)
    filter_upwards [eventually_ge_atTop (max (max n₀ n₁) 1)] with n hn
    have hn0 : n₀ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
    have hn1 : n₁ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
    have hn2 : 1 ≤ n := le_trans (le_max_right _ _) hn
    obtain ⟨w, hw, hN, hB⟩ := hn₀ n hn0
    have hS := (hn₁ n hn1).2 w hw
    have hbern : 1 - d * τ ≤ (1 - τ) ^ d := by
      have := one_add_mul_le_pow (show (-2 : ℝ) ≤ -τ by linarith) d
      rw [← sub_eq_add_neg, mul_neg, ← sub_eq_add_neg] at this
      exact this
    have hcoef : (1 - (1 - τ) ^ d) * α ≤ 3 / (2 * c) * s := by
      rw [← hdτα]; nlinarith
    have := ofReal_le_muStar_add (Cs := 3 / (2 * c) * s) hshift hABP hd1 hs0 (by positivity) (hκ n)
      hw hN hB (hS.trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (by rw [hαdef] at hcoef; linarith) (Nat.cast_nonneg _))))
    refine ofReal_le_div_ncard hn2 (le_trans (le_of_eq ?_) this)
    congr 1
    rw [hαdef]
    ring

end RandomSandpile
