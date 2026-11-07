import RandomSandpile.Proofs.Sec9.RecurrentMonotone
import RandomSandpile.Steps.Sec6.MuLipschitz

/-! Finite-volume curvature shift for recurrent competitors. -/

open MeasureTheory LatticeProb LatticeProb.Sandpile Filter
open scoped ENNReal
noncomputable section
namespace RandomSandpile
open MuLipschitz
variable {d : ℕ}

/-- A bent recurrent near-maximizer with small shell mass bounds the recurrent
upper measure at a lower scalar curvature. -/
theorem recurrent_ofReal_le_mu_sub (hABP : BoundaryGapStmt)
    {η : Site d → ℤ} {l s α ε τ κ Cs : ℝ} {M : Matrix (Fin d) (Fin d) ℝ} {n : ℕ} (hd : 1 ≤ d)
    (hs : 0 < s) (hCs : 0 ≤ Cs + ε) (hκ : 3 * s * n / (2 * d) ≤ κ) {w : Site d → ℝ}
    (hw : w ∈ recurrentPerturbed (ballZ0 (n : ℝ)) η l M)
    (hN : ENNReal.ofReal ((α - ε) * ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ)) ≤
      volume (supGradSet w (ballZ0 (n : ℝ))))
    (hB : ∀ x₀ ∈ ballZ0 ((1 - τ) * n), ∀ p₀ ∈ supGrad w x₀ (ballZ0 (n : ℝ)),
      ∀ y ∈ bdry (ballZ0 (d := d) (n : ℝ)),
        w y ≤ w x₀ + inner ℝ p₀ (toE y - toE x₀) - κ * ‖toE y - toE x₀‖)
    (hS : volume (⋃ x ∈ ballZ0 (d := d) (n : ℝ) \ ballZ0 ((1 - τ) * n),
        supGrad w x (ballZ0 (n : ℝ))) ≤
      ENNReal.ofReal ((Cs + ε) * ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ))) :
    ENNReal.ofReal ((α - Cs - 2 * ε) * ((ballZ0 (d := d) (n : ℝ)).ncard : ℝ)) ≤
      muRecurrent (ballZ0 (n : ℝ)) η (l - s) M := by
  set B := ballZ0 (d := d) (n : ℝ)
  set N : ℝ := (B.ncard : ℝ)
  have hw' : (fun x => w x + qlZ s x) ∈ recurrentPerturbed B η (l - s) M := by
    obtain ⟨r, hr, rfl⟩ := hw
    refine ⟨r, hr, ?_⟩
    funext x
    simp only [qlZ_sub]
    ring
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
  have hmu : volume (supGradSet (fun x => w x + qlZ s x) B) ≤ muRecurrent B η (l - s) M :=
    le_iSup₂ (f := fun w (_ : w ∈ recurrentPerturbed B η (l - s) M) => volume (supGradSet w B)) _ hw'
  have htot : ENNReal.ofReal ((α - ε) * N) ≤
      muRecurrent B η (l - s) M + ENNReal.ofReal ((Cs + ε) * N) :=
    hN.trans <| (measure_mono hsplit).trans <| (measure_union_le _ _).trans <|
      add_le_add ((measure_mono hinner).trans hmu) hS
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  calc ENNReal.ofReal ((α - Cs - 2 * ε) * N)
      = ENNReal.ofReal ((α - ε) * N - (Cs + ε) * N) := by ring_nf
    _ = ENNReal.ofReal ((α - ε) * N) - ENNReal.ofReal ((Cs + ε) * N) :=
        ENNReal.ofReal_sub _ (mul_nonneg hCs hN0)
    _ ≤ muRecurrent B η (l - s) M := tsub_le_iff_right.2 htot

end RandomSandpile
