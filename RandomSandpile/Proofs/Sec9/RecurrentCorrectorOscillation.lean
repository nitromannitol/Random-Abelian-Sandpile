import RandomSandpile.Proofs.Sec9.RecurrentCorrectorLaplacian
import RandomSandpile.Proofs.Sec9.RecurrentCompactnessDyadic

/-! # Dyadic oscillation bounds for recurrent correctors -/

noncomputable section
open Filter Topology LatticeProb LatticeProb.Sandpile
namespace RandomSandpile
open SSComp SSGreen

/-- A translated lattice box lies in the Euclidean ball obtained by adding
its Euclidean coordinate-radius to the norm of its center. -/
theorem translated_box_norm_le {d S : ℕ} (c z : Site d) (hz : z ∈ box d S) :
    ‖toE (c + z)‖ ≤ ‖toE c‖ + Real.sqrt d * S := by
  have hz' : ‖toE z‖ ≤ Real.sqrt d * S := by
    apply norm_le_sqrt_mul_of_abs_le (toE z) (by positivity)
    intro i
    have hi : |z i| ≤ (S : ℤ) := hz i
    change |(z i : ℝ)| ≤ (S : ℝ)
    exact_mod_cast hi
  rw [OpenBoundaryLapLipschitz.toE_add']
  calc
    ‖toE c + toE z‖ ≤ ‖toE c‖ + ‖toE z‖ := norm_add_le _ _
    _ ≤ ‖toE c‖ + Real.sqrt d * S := by linarith

/-- On translated boxes contained in a fixed macroscopic ball, the recurrent
corrector has geometric oscillation decay with quadratic Poisson forcing. -/
theorem recurrent_corrector_lattice_dyadic {d : ℕ} (hd : 2 ≤ d)
    {ηmin ηmax : ℤ} {η : Site d → ℤ}
    (hη : ∀ x, ηmin ≤ η x ∧ η x ≤ ηmax) (hfinite : SingleSourceFinite η)
    (htail : SingleSourceVanishingTail η) (κ Cg Rg : ℝ) (hRg : 1 ≤ Rg)
    (hasymp : ∀ z : Site d, Rg ≤ ‖toE z‖ →
      |ssGreen d z - fundamentalSolution d (toE z) - κ| ≤ Cg * ‖toE z‖ ^ (-(d : ℝ)))
    (m : ℝ) : ∃ q B C : ℝ, 0 ≤ q ∧ q < 1 ∧ 0 ≤ B ∧ 0 ≤ C ∧
      ∀ᶠ n : ℕ in atTop, ∀ (k R S : ℕ) (c : Site d),
        1 ≤ R → 2 ^ k * R ≤ S →
        (∀ z ∈ box d S, ‖toE (c + z)‖ ≤ m * ssScale d n) →
        ∀ x ∈ box d R, ∀ y ∈ box d R,
          |((n : ℝ) ^ (-(2 / (d : ℝ))) * ssW d η n (c + x)) -
            ((n : ℝ) ^ (-(2 / (d : ℝ))) * ssW d η n (c + y))| ≤
            q ^ k * B + C * (((S : ℝ) + 1) / ssScale d n) ^ 2 := by
  obtain ⟨q, C, hq0, hq1, hC, hdyadic⟩ := poisson_pairwise_dyadic_uniform d (by omega)
  obtain ⟨B, hB⟩ := recurrent_corrector_lattice_ball_bound hd hη hfinite htail κ Cg Rg hRg
    hasymp m
  let K : ℝ := |(ηmin : ℝ)| + |(ηmax : ℝ)| + |(2 * (d : ℝ) - 1)|
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨q, 2 * max B 0, C * K, hq0, hq1, by positivity, by positivity, ?_⟩
  filter_upwards [hB, eventually_ge_atTop 1] with n hn hn1
  intro k R S c hR hRS hball x hx y hy
  let s := ssScale d n
  let f : Site d → ℝ := fun p => (n : ℝ) ^ (-(2 / (d : ℝ))) * ssW d η n p +
    (n : ℝ) ^ (-(2 / (d : ℝ))) * n * κ + ssShift d n
  have hs : 0 < s := ssScale_pos hn1
  have hosc : ∀ z ∈ box d S, ∀ w ∈ box d S, |f (c + z) - f (c + w)| ≤ 2 * max B 0 := by
    intro z hz w hw
    have hzB := hn (c + z) (hball z hz)
    have hwB := hn (c + w) (hball w hw)
    have htri := abs_sub (f (c + z)) (f (c + w))
    dsimp [f] at htri
    linarith [le_max_left B (0 : ℝ)]
  have hlap : ∀ z ∈ box d S,
      |nbrSum f (c + z) - 2 * (d : ℝ) * f (c + z)| ≤ (s ^ 2)⁻¹ * K := by
    intro z hz
    exact recurrent_corrector_abs_lapR_le hd hη hfinite κ n (c + z)
  have h := hdyadic k R S c f (2 * max B 0) ((s ^ 2)⁻¹ * K) hR hRS
    (by positivity) hosc hlap x hx y hy
  have hforce : C * ((s ^ 2)⁻¹ * K) * ((S : ℝ) + 1) ^ 2 =
      C * K * (((S : ℝ) + 1) / s) ^ 2 := by field_simp
  rw [hforce] at h
  convert h using 1
  dsimp [f]
  ring

end RandomSandpile
