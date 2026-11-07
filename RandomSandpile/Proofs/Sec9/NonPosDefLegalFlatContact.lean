import RandomSandpile.Proofs.Sec9.NonPosDefLegalFlatSteps
import RandomSandpile.Proofs.FinalSteps
import RandomSandpile.Proofs.Sec3.LeastAction
import RandomSandpile.Infra.ConcaveEnvelope

/-!
# Operator fact (11): contact bend and least-action comparison

* `locLegal_le_of_bdry`: a locally legal `u` on `A` lies below a stabilizing `z` on all of
  `ℤ^d` as soon as it does on `∂A` (least action applied to `z - w`, `w` the boundary part of `u`).
* `contactBend`: `ContactBendStmt` from Lemma 6.2 (`strictConcavity_closed`, `C = c(1-β)²`)
  with `β = 1/2`: a near-maximizer `w = u - q_A` has positive supergradient volume in `B_{n/2}`, so
  some `x₀` has a supergradient `p₀`, hence is a contact point, and the bend gives the bound on `∂B_n`.
-/

noncomputable section

open MeasureTheory LatticeProb LatticeProb.Sandpile Filter Topology

namespace RandomSandpile

namespace SingleSourceH0

variable {d : ℕ}

theorem lap_sub_apply (u v : Site d → ℤ) (x : Site d) : lap (u - v) x = lap u x - lap v x := by
  simp only [lap, nbrSumZ, Pi.sub_apply, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring

/-- A locally legal toppling below a stabilizing one on the boundary is below it everywhere. -/
theorem locLegal_le_of_bdry {A : Set (Site d)} {η u z : Site d → ℤ} (hu : u ∈ locLegal η A)
    (hz : z ∈ stabilizing η A) (hb : ∀ y ∈ bdry A, u y ≤ z y) : u ≤ z := by
  obtain ⟨w, uh, hw, huh, rfl, hw0, huh0, hleg⟩ := hu
  have hzt : z - w ∈ stabilizing (fun y => lap w y + η y) A := by
    refine ⟨⟨fun x => ?_, fun x hx => ?_⟩, fun x hx => ?_⟩
    · by_cases hxc : x ∈ dClosure A
      · rw [dClosure_eq] at hxc
        rcases hxc with hxA | hxb
        · simp [hw0 x hxA, hz.1.1 x]
        · have := hb x hxb
          simp only [Pi.add_apply, huh0 x hxb, add_zero] at this
          simpa using this
      · simp [hw.2 x hxc, hz.1.2 x hxc]
    · simp [hw.2 x hx, hz.1.2 x hx]
    · have := hz.2 x hx
      rw [lap_sub_apply]
      linarith
  have hle := legalLeStabilizing d A _ uh (z - w) hleg hzt
  intro x
  have := hle x
  simp only [Pi.sub_apply, Pi.add_apply] at this ⊢
  linarith

/-- `ContactBendStmt`. -/
theorem contactBend : ContactBendStmt := by
  intro d hd E A hA hpos
  obtain ⟨C, hC, hSC⟩ := strictConcavity_closed d hd E.ηmin E.ηmax 0 A
  have hconc := (hSC E rfl rfl).1 hpos
  refine ⟨C * (1 - 1 / 2) ^ 2 * muBar E 0 A, by
    have : (0 : ℝ) < (1 - 1 / 2) ^ 2 := by norm_num
    positivity, ?_⟩
  filter_upwards [hconc] with η hη
  obtain ⟨n₀, hn₀⟩ := hη (1 / 2) (by norm_num) (by norm_num)
  refine ⟨max n₀ 1, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  obtain ⟨w, hw, hvol, hbend⟩ := hn₀ n (le_trans (le_max_left _ _) hn)
  obtain ⟨u, hu, rfl⟩ := mem_perturbedSub.1 hw
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hcard : 0 < (ballZ0 (d := d) (1 / 2 * (n : ℝ))).ncard := by
    apply Set.ncard_pos (MuLipschitz.ballZ0_finite _) |>.2
    exact ⟨0, MuLipschitz.mem_ballZ0.2 (by rw [MuLipschitz.toE_zero, norm_zero]; linarith)⟩
  have hpos' : 0 < ENNReal.ofReal (muBar E 0 A / 2 * ((ballZ0 (d := d) (1 / 2 * (n : ℝ))).ncard : ℝ)) := by
    rw [ENNReal.ofReal_pos]
    have : (0 : ℝ) < ((ballZ0 (d := d) (1 / 2 * (n : ℝ))).ncard : ℝ) := by exact_mod_cast hcard
    positivity
  have hne := MeasureTheory.nonempty_of_measure_ne_zero (hpos'.trans_le hvol).ne'
  obtain ⟨p', hp'⟩ := hne
  simp only [Set.mem_iUnion] at hp'
  obtain ⟨x₀, hx₀, hp₀⟩ := hp'
  have hx₀n : x₀ ∈ ballZ0 (d := d) (n : ℝ) := by
    rw [MuLipschitz.mem_ballZ0] at hx₀ ⊢
    linarith
  have hcontact : concaveEnvelopeOn (ballZ0 (n : ℝ)) (fun x => (u x : ℝ) - (qlZ 0 x + qMZ A x))
      (toE x₀) = (u x₀ : ℝ) - (qlZ 0 x₀ + qMZ A x₀) :=
    concaveEnvelopeOn_eq_of_mem_supGrad (MuLipschitz.ballZ0_finite _)
      (mem_dClosure_of_mem hx₀n) hp₀
  refine ⟨u, x₀, p', hu, hx₀n, fun y hy => ?_⟩
  have h := hbend x₀ hx₀ hcontact p' hp₀ y hy
  have hql : ∀ z : Site d, qlZ 0 z = 0 := fun z => by simp [qlZ, ql]
  simp only [hql, zero_add] at h
  nlinarith [h]

end SingleSourceH0

end RandomSandpile
