import RandomSandpile.Proofs.Sec9.RecurrentBending
import RandomSandpile.Proofs.Sec9.RecurrentCenter

/-! Central contacts for recurrent near-maximizers. -/

open MeasureTheory LatticeProb LatticeProb.Sandpile Filter Metric
open scoped ENNReal Topology Matrix
noncomputable section
namespace RandomSandpile
variable {d : ℕ}

/-- Positive upper density yields bending near-maximizers with a contact point
in every fixed central ball. -/
theorem recurrent_upper_contact (hd : 2 ≤ d) (E : RandomEnvironment d)
    (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (hα : 0 < muRecurrentBar E l M) :
    ∃ c : ℝ, 0 < c ∧ ∀ᵐ η ∂E.P, ∃ r : ℕ → Site d → ℤ,
      (∀ n : ℕ, IsRecurrentFunction η (ballZ0 (n : ℝ)) (r n)) ∧
      ∀ β : ℝ, 0 < β → β < 1 → ∀ᶠ n : ℕ in atTop,
        ∃ x₀ ∈ ballZ0 (d := d) (β * n),
        ∃ p₀ ∈ supGrad (fun x => (r n x : ℝ) - (qlZ l x + qMZ M x)) x₀ (ballZ0 (n : ℝ)),
          ∀ y ∈ bdry (ballZ0 (d := d) (n : ℝ)),
            ((r n y : ℝ) - (qlZ l y + qMZ M y)) ≤
              ((r n x₀ : ℝ) - (qlZ l x₀ + qMZ M x₀)) + inner ℝ p₀ (toE y - toE x₀) -
                c * muRecurrentBar E l M * ((1 - β) * n) * ‖toE y - toE x₀‖ := by
  obtain ⟨c, hc, hb⟩ := recurrent_upper_bending hd E l M hα
  refine ⟨c, hc, ?_⟩
  filter_upwards [hb, recurrent_upper_center hd E l M hα] with η hb hcenter
  obtain ⟨r, hr, hnear, hbend⟩ := hb
  refine ⟨r, hr, ?_⟩
  intro β hβ hβ1
  obtain ⟨ε, hε, hmass⟩ := hcenter β hβ hβ1
  filter_upwards [hmass, hnear ε hε, hbend β hβ hβ1] with n hm hn hb
  have hp := hm _ ⟨r n, hr n, rfl⟩ hn
  have hne : (⋃ x ∈ ballZ0 (d := d) (β * n),
      supGrad (fun x => (r n x : ℝ) - (qlZ l x + qMZ M x)) x (ballZ0 (n : ℝ))).Nonempty := by
    by_contra h
    simp only [Set.not_nonempty_iff_eq_empty.mp h, measure_empty, lt_self_iff_false] at hp
  obtain ⟨p, hp⟩ := hne
  obtain ⟨x, hx, hp⟩ := Set.mem_iUnion₂.mp hp
  exact ⟨x, hx, p, hp, hb x hx p hp⟩

/-- Positive lower density yields bending near-maximizers with a contact point
in every fixed central ball. -/
theorem recurrent_lower_contact (hd : 2 ≤ d) (E : RandomEnvironment d)
    (l : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (hα : 0 < muStarRecurrentBar E l M) :
    ∃ c : ℝ, 0 < c ∧ ∀ᵐ η ∂E.P, ∃ r : ℕ → Site d → ℤ,
      (∀ n : ℕ, IsRecurrentFunction η (ballZ0 (n : ℝ)) (r n)) ∧
      ∀ β : ℝ, 0 < β → β < 1 → ∀ᶠ n : ℕ in atTop,
        ∃ x₀ ∈ ballZ0 (d := d) (β * n),
        ∃ p₀ ∈ subGrad (fun x => (r n x : ℝ) - (qlZ l x + qMZ M x)) x₀ (ballZ0 (n : ℝ)),
          ∀ y ∈ bdry (ballZ0 (d := d) (n : ℝ)),
            ((r n y : ℝ) - (qlZ l y + qMZ M y)) ≥
              ((r n x₀ : ℝ) - (qlZ l x₀ + qMZ M x₀)) + inner ℝ p₀ (toE y - toE x₀) +
                c * muStarRecurrentBar E l M * ((1 - β) * n) * ‖toE y - toE x₀‖ := by
  obtain ⟨c, hc, hb⟩ := recurrent_lower_bending hd E l M hα
  refine ⟨c, hc, ?_⟩
  filter_upwards [hb, recurrent_lower_center hd E l M hα] with η hb hcenter
  obtain ⟨r, hr, hnear, hbend⟩ := hb
  refine ⟨r, hr, ?_⟩
  intro β hβ hβ1
  obtain ⟨ε, hε, hmass⟩ := hcenter β hβ hβ1
  filter_upwards [hmass, hnear ε hε, hbend β hβ hβ1] with n hm hn hb
  have hp := hm _ ⟨r n, hr n, rfl⟩ hn
  have hne : (⋃ x ∈ ballZ0 (d := d) (β * n),
      subGrad (fun x => (r n x : ℝ) - (qlZ l x + qMZ M x)) x (ballZ0 (n : ℝ))).Nonempty := by
    by_contra h
    simp only [Set.not_nonempty_iff_eq_empty.mp h, measure_empty, lt_self_iff_false] at hp
  obtain ⟨p, hp⟩ := hne
  obtain ⟨x, hx, hp⟩ := Set.mem_iUnion₂.mp hp
  exact ⟨x, hx, p, hp, hb x hx p hp⟩

end RandomSandpile
