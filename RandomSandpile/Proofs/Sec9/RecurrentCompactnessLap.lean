import RandomSandpile.Proofs.Sec9.SingleSourceCompactness
import RandomSandpile.Draft.Section9Recurrent

/-! # Uniform Laplacian bound for finite single-source odometers -/

noncomputable section
open Filter Topology LatticeProb LatticeProb.Sandpile

namespace RandomSandpile

variable {d : ℕ}

/-- A bounded background with finite odometers gives a uniform bound after removing the source. -/
theorem recurrent_abs_lap_add_le {ηmin ηmax : ℤ} {η : Site d → ℤ}
    (hη : ∀ x, ηmin ≤ η x ∧ η x ≤ ηmax) (hfinite : SingleSourceFinite η)
    (n : ℕ) (y : Site d) :
    |(lap (singleSourceOdometer η n) y : ℝ) + (n : ℝ) * (if y = 0 then 1 else 0)|
      ≤ |(ηmin : ℝ)| + |(ηmax : ℝ)| + |(2 * (d : ℝ) - 1)| := by
  have hne := hfinite n
  have hlow := SSComp.min_le_ssSandpile hne y
  have hup := (mem_stabilizing_univ.1 (isLeast_singleSourceOdometer hne).1).2 y
  have h1 := (hη y).1
  have h2 := (hη y).2
  have hint : |lap (singleSourceOdometer η n) y + (n : ℤ) * dirac 0 y|
      ≤ |ηmin| + |ηmax| + |2 * (d : ℤ) - 1| := by
    rw [abs_le]
    have ha := neg_abs_le ηmin
    have hb := le_abs_self ηmax
    have hc := neg_abs_le (2 * (d : ℤ) - 1)
    have hc' := le_abs_self (2 * (d : ℤ) - 1)
    have hm : -|ηmin| ≤ min (η y) 0 :=
      le_min (by linarith) (by have := abs_nonneg ηmin; linarith)
    have hd0 := abs_nonneg ηmax
    constructor <;> linarith
  have hreal : ((|lap (singleSourceOdometer η n) y + (n : ℤ) * dirac 0 y| : ℤ) : ℝ)
      ≤ ((|ηmin| + |ηmax| + |2 * (d : ℤ) - 1| : ℤ) : ℝ) := Int.cast_le.2 hint
  push_cast at hreal
  have hcast : (n : ℝ) * (if y = 0 then 1 else 0) = (n : ℝ) * ((dirac 0 y : ℤ) : ℝ) := by
    by_cases hy : y = 0
    · rw [if_pos hy, hy, SSComp.ssDirac_self]; simp
    · rw [if_neg hy, SSComp.ssDirac_of_ne hy]; simp
  rw [hcast]
  exact hreal

end RandomSandpile
