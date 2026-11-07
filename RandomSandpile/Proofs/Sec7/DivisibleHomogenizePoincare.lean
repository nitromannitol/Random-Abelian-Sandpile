import LatticeProb.Site

/-!
Discrete L¹ Poincaré inequality on lattice boxes, used for the rearrangement error of Lemma 7.3
.

For a box `Q = ∏ᵢ [lᵢ, uᵢ) ⊆ ℤ^d` with side lengths `≤ L`, we prove
`∑_{y ∈ Q} |g y - avg_Q g| ≤ L ∑_{q ∈ Q} ∑ᵢ |g (q + eᵢ) - g q|`
(`sum_abs_sub_avg_le_box_sharp`), and the weakened form with constant `2^d * d * L`
(`sum_abs_sub_avg_le_box`).

The proof interpolates coordinate by coordinate between two points `y, z ∈ Q`
(`interp m y z` takes the first `m` coordinates from `z` and the rest from `y`), bounds each
one-dimensional increment by the full sum of `|g (q + eᵢ) - g q|` along the line, and counts
the resulting configurations through two measure-preserving involutions on `Q × Q` and `Q × Iₘ`.
-/

noncomputable section

open LatticeProb

namespace RandomSandpile

namespace DivisibleHomogenize

variable {d : ℕ}

/-- The box `∏ᵢ [lᵢ, uᵢ)`. -/
abbrev ibox (l u : Fin d → ℤ) : Finset (Site d) :=
  Fintype.piFinset (fun i => Finset.Ico (l i) (u i))

/-- One-dimensional telescoping bound for the increments of `G` along `[s, t)`. -/
theorem abs_sub_le_sum_Ico (G : ℤ → ℝ) (s : ℤ) :
    ∀ t : ℤ, s ≤ t → |G t - G s| ≤ ∑ r ∈ Finset.Ico s t, |G (r + 1) - G r| := by
  intro t hst
  induction t, hst using Int.leInduction with
  | base => simp
  | succ t hst ih =>
    have hI : Finset.Ico s (t + 1) = insert t (Finset.Ico s t) := by
      ext x
      simp only [Finset.mem_Ico, Finset.mem_insert]
      omega
    rw [hI, Finset.sum_insert (by simp)]
    calc |G (t + 1) - G s| ≤ |G (t + 1) - G t| + |G t - G s| := abs_sub_le _ _ _
      _ ≤ _ := by linarith

/-- Two values of `G` at points of `[a, b)` differ by at most the total increment on `[a, b)`. -/
theorem abs_sub_le_sum_Ico_of_mem (G : ℤ → ℝ) {a b s t : ℤ} (hs : s ∈ Finset.Ico a b)
    (ht : t ∈ Finset.Ico a b) :
    |G s - G t| ≤ ∑ r ∈ Finset.Ico a b, |G (r + 1) - G r| := by
  have hsub : ∀ {s t : ℤ}, s ∈ Finset.Ico a b → t ∈ Finset.Ico a b → s ≤ t →
      |G t - G s| ≤ ∑ r ∈ Finset.Ico a b, |G (r + 1) - G r| := by
    intro s t hs ht hst
    refine (abs_sub_le_sum_Ico G s t hst).trans ?_
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => abs_nonneg _)
    intro r hr
    simp only [Finset.mem_Ico] at hs ht hr ⊢
    omega
  rcases le_total s t with h | h
  · rw [abs_sub_comm]
    exact hsub hs ht h
  · exact hsub ht hs h

theorem update_add_unit (p : Site d) (m : Fin d) (r : ℤ) :
    Function.update p m r + unit m = Function.update p m (r + 1) := by
  funext i
  by_cases h : i = m
  · subst h
    simp [unit]
  · simp [unit, h]

/-- The one-dimensional bound along the `m`-th coordinate line through `p`. -/
theorem abs_update_sub_le (g : Site d → ℝ) (p : Site d) (m : Fin d) {a b s t : ℤ}
    (hs : s ∈ Finset.Ico a b) (ht : t ∈ Finset.Ico a b) :
    |g (Function.update p m s) - g (Function.update p m t)| ≤
      ∑ r ∈ Finset.Ico a b,
        |g (Function.update p m r + unit m) - g (Function.update p m r)| := by
  have := abs_sub_le_sum_Ico_of_mem (fun r => g (Function.update p m r)) hs ht
  simpa only [update_add_unit] using this

/-- The point whose first `m` coordinates come from `z` and the remaining ones from `y`. -/
def interp (m : ℕ) (y z : Site d) : Site d := fun i => if (i : ℕ) < m then z i else y i

theorem interp_zero (y z : Site d) : interp 0 y z = y := by
  funext i
  simp [interp]

theorem interp_dim (y z : Site d) : interp d y z = z := by
  funext i
  simp [interp, i.isLt]

theorem interp_succ (m : Fin d) (y z : Site d) :
    interp ((m : ℕ) + 1) y z = Function.update (interp m y z) m (z m) := by
  funext i
  by_cases h : i = m
  · subst h
    simp [interp]
  · have hv : (i : ℕ) ≠ (m : ℕ) := fun hh => h (Fin.ext hh)
    have hlt : (i : ℕ) < (m : ℕ) + 1 ↔ (i : ℕ) < (m : ℕ) := by omega
    simp [interp, Function.update_of_ne h, hlt]

theorem update_interp_self (m : Fin d) (y z : Site d) :
    Function.update (interp m y z) m (y m) = interp m y z := by
  rw [Function.update_eq_self_iff]
  simp [interp]

theorem interp_interp (m : ℕ) (y z : Site d) :
    interp m (interp m y z) (interp m z y) = y := by
  funext i
  by_cases h : (i : ℕ) < m <;> simp [interp, h]

theorem interp_mem {l u : Fin d → ℤ} {y z : Site d} (hy : y ∈ ibox l u) (hz : z ∈ ibox l u)
    (m : ℕ) : interp m y z ∈ ibox l u := by
  rw [Fintype.mem_piFinset] at hy hz ⊢
  intro i
  by_cases h : (i : ℕ) < m
  · simpa [interp, h] using hz i
  · simpa [interp, h] using hy i

theorem update_mem {l u : Fin d → ℤ} {p : Site d} (hp : p ∈ ibox l u) (m : Fin d) {r : ℤ}
    (hr : r ∈ Finset.Ico (l m) (u m)) : Function.update p m r ∈ ibox l u := by
  rw [Fintype.mem_piFinset] at hp ⊢
  intro i
  by_cases h : i = m
  · subst h
    simpa using hr
  · simpa [Function.update_of_ne h] using hp i

/-- Counting: the interpolation point is equidistributed in the box. -/
theorem sum_sum_interp (l u : Fin d → ℤ) (m : ℕ) (H : Site d → ℝ) :
    ∑ y ∈ ibox l u, ∑ z ∈ ibox l u, H (interp m y z) =
      ((ibox l u).card : ℝ) * ∑ p ∈ ibox l u, H p := by
  rw [← Finset.sum_product' (f := fun y z => H (interp m y z))]
  have h : ∑ x ∈ ibox l u ×ˢ ibox l u, H (interp m x.1 x.2) =
      ∑ x ∈ ibox l u ×ˢ ibox l u, H x.1 := by
    refine Finset.sum_nbij' (fun x => (interp m x.1 x.2, interp m x.2 x.1))
      (fun x => (interp m x.1 x.2, interp m x.2 x.1)) ?_ ?_ ?_ ?_ ?_
    · intro x hx
      rw [Finset.mem_product] at hx ⊢
      exact ⟨interp_mem hx.1 hx.2 m, interp_mem hx.2 hx.1 m⟩
    · intro x hx
      rw [Finset.mem_product] at hx ⊢
      exact ⟨interp_mem hx.1 hx.2 m, interp_mem hx.2 hx.1 m⟩
    · intro x _
      exact Prod.ext (interp_interp m x.1 x.2) (interp_interp m x.2 x.1)
    · intro x _
      exact Prod.ext (interp_interp m x.1 x.2) (interp_interp m x.2 x.1)
    · intro x _
      rfl
  rw [h, Finset.sum_product]
  simp [Finset.sum_const, Finset.mul_sum]

/-- Counting: the point `update p m r` is equidistributed in the box. -/
theorem sum_sum_update (l u : Fin d → ℤ) (m : Fin d) (F : Site d → ℝ) :
    ∑ p ∈ ibox l u, ∑ r ∈ Finset.Ico (l m) (u m), F (Function.update p m r) =
      ((Finset.Ico (l m) (u m)).card : ℝ) * ∑ q ∈ ibox l u, F q := by
  rw [← Finset.sum_product' (f := fun p r => F (Function.update p m r))]
  have h : ∑ x ∈ ibox l u ×ˢ Finset.Ico (l m) (u m), F (Function.update x.1 m x.2) =
      ∑ x ∈ ibox l u ×ˢ Finset.Ico (l m) (u m), F x.1 := by
    refine Finset.sum_nbij' (fun x => (Function.update x.1 m x.2, x.1 m))
      (fun x => (Function.update x.1 m x.2, x.1 m)) ?_ ?_ ?_ ?_ ?_
    · intro x hx
      rw [Finset.mem_product] at hx ⊢
      refine ⟨update_mem hx.1 m hx.2, ?_⟩
      have := Fintype.mem_piFinset.1 hx.1 m
      exact this
    · intro x hx
      rw [Finset.mem_product] at hx ⊢
      refine ⟨update_mem hx.1 m hx.2, ?_⟩
      have := Fintype.mem_piFinset.1 hx.1 m
      exact this
    · intro x _
      refine Prod.ext ?_ ?_
      · simp
      · simp
    · intro x _
      refine Prod.ext ?_ ?_
      · simp
      · simp
    · intro x _
      rfl
  rw [h, Finset.sum_product]
  simp [Finset.sum_const, Finset.mul_sum]

/-- Coordinate-by-coordinate interpolation bound for two points of the box. -/
theorem abs_sub_le_path (l u : Fin d → ℤ) (g : Site d → ℝ) {y z : Site d}
    (hy : y ∈ ibox l u) (hz : z ∈ ibox l u) :
    |g y - g z| ≤ ∑ m : Fin d, ∑ r ∈ Finset.Ico (l m) (u m),
      |g (Function.update (interp m y z) m r + unit m) -
        g (Function.update (interp m y z) m r)| := by
  have h1 : g z - g y =
      ∑ k ∈ Finset.range d, (g (interp (k + 1) y z) - g (interp k y z)) := by
    rw [Finset.sum_range_sub (fun k => g (interp k y z)) d]
    simp [interp_zero, interp_dim]
  rw [abs_sub_comm, h1]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.sum_range]
  refine Finset.sum_le_sum (fun m _ => ?_)
  have key := abs_update_sub_le g (interp m y z) m (a := l m) (b := u m)
    (s := z m) (t := y m) (Fintype.mem_piFinset.1 hz m) (Fintype.mem_piFinset.1 hy m)
  rw [update_interp_self] at key
  rw [interp_succ]
  exact key

/-- The double sum of pairwise differences over the box. -/
theorem sum_sum_abs_sub_le (l u : Fin d → ℤ) (g : Site d → ℝ) :
    ∑ y ∈ ibox l u, ∑ z ∈ ibox l u, |g y - g z| ≤
      ((ibox l u).card : ℝ) * ∑ m : Fin d, ((Finset.Ico (l m) (u m)).card : ℝ) *
        ∑ q ∈ ibox l u, |g (q + unit m) - g q| := by
  have hm : ∀ m : Fin d, ∑ y ∈ ibox l u, ∑ z ∈ ibox l u, ∑ r ∈ Finset.Ico (l m) (u m),
      |g (Function.update (interp m y z) m r + unit m) -
        g (Function.update (interp m y z) m r)| =
      ((ibox l u).card : ℝ) * (((Finset.Ico (l m) (u m)).card : ℝ) *
        ∑ q ∈ ibox l u, |g (q + unit m) - g q|) := by
    intro m
    refine (sum_sum_interp l u m
      (fun p => ∑ r ∈ Finset.Ico (l m) (u m),
        |g (Function.update p m r + unit m) - g (Function.update p m r)|)).trans ?_
    rw [sum_sum_update l u m (fun q => |g (q + unit m) - g q|)]
  calc ∑ y ∈ ibox l u, ∑ z ∈ ibox l u, |g y - g z|
      ≤ ∑ y ∈ ibox l u, ∑ z ∈ ibox l u, ∑ m : Fin d, ∑ r ∈ Finset.Ico (l m) (u m),
        |g (Function.update (interp m y z) m r + unit m) -
          g (Function.update (interp m y z) m r)| :=
        Finset.sum_le_sum fun y hy => Finset.sum_le_sum fun z hz =>
          abs_sub_le_path l u g hy hz
    _ = ∑ y ∈ ibox l u, ∑ m : Fin d, ∑ z ∈ ibox l u, ∑ r ∈ Finset.Ico (l m) (u m),
        |g (Function.update (interp m y z) m r + unit m) -
          g (Function.update (interp m y z) m r)| :=
        Finset.sum_congr rfl fun y _ => Finset.sum_comm
    _ = ∑ m : Fin d, ∑ y ∈ ibox l u, ∑ z ∈ ibox l u, ∑ r ∈ Finset.Ico (l m) (u m),
        |g (Function.update (interp m y z) m r + unit m) -
          g (Function.update (interp m y z) m r)| := Finset.sum_comm
    _ = _ := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun m _ => hm m

theorem card_Ico_le_of_nonempty {l u : Fin d → ℤ} {L : ℝ}
    (hL : ∀ i, ((u i - l i : ℤ) : ℝ) ≤ L) (hQ : (ibox l u).Nonempty) (m : Fin d) :
    ((Finset.Ico (l m) (u m)).card : ℝ) ≤ L := by
  have hne : (Finset.Ico (l m) (u m)).Nonempty := Fintype.piFinset_nonempty.1 hQ m
  have hlt : l m < u m := Finset.nonempty_Ico.1 hne
  have h := Int.card_Ico_of_le (l m) (u m) hlt.le
  have h2 : (((Finset.Ico (l m) (u m)).card : ℤ) : ℝ) = ((u m - l m : ℤ) : ℝ) := by
    rw [h]
  have h3 : (((Finset.Ico (l m) (u m)).card : ℤ) : ℝ) = ((Finset.Ico (l m) (u m)).card : ℝ) :=
    Int.cast_natCast _
  rw [← h3, h2]
  exact hL m

/-- Sharp form: constant `L`. -/
theorem sum_abs_sub_avg_le_box_sharp {d : ℕ} (l u : Fin d → ℤ) (L : ℝ)
    (hL : ∀ i, ((u i - l i : ℤ) : ℝ) ≤ L) (g : Site d → ℝ) :
    ∑ y ∈ Fintype.piFinset (fun i => Finset.Ico (l i) (u i)),
        |g y - (∑ z ∈ Fintype.piFinset (fun i => Finset.Ico (l i) (u i)), g z) /
          ((Fintype.piFinset (fun i => Finset.Ico (l i) (u i))).card : ℝ)| ≤
      L * ∑ q ∈ Fintype.piFinset (fun i => Finset.Ico (l i) (u i)),
        ∑ i : Fin d, |g (q + unit i) - g q| := by
  rcases (ibox l u).eq_empty_or_nonempty with hQ | hQ
  · simp [hQ]
  have hN : (0 : ℝ) < ((ibox l u).card : ℝ) := by exact_mod_cast hQ.card_pos
  have h1 : ∀ y ∈ ibox l u, |g y - (∑ z ∈ ibox l u, g z) / ((ibox l u).card : ℝ)| ≤
      (∑ z ∈ ibox l u, |g y - g z|) / ((ibox l u).card : ℝ) := by
    intro y _
    have h : g y - (∑ z ∈ ibox l u, g z) / ((ibox l u).card : ℝ) =
        (∑ z ∈ ibox l u, (g y - g z)) / ((ibox l u).card : ℝ) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
      field_simp
    rw [h, abs_div, abs_of_pos hN]
    gcongr
    exact Finset.abs_sum_le_sum_abs _ _
  calc ∑ y ∈ ibox l u, |g y - (∑ z ∈ ibox l u, g z) / ((ibox l u).card : ℝ)|
      ≤ ∑ y ∈ ibox l u, (∑ z ∈ ibox l u, |g y - g z|) / ((ibox l u).card : ℝ) :=
        Finset.sum_le_sum h1
    _ = (∑ y ∈ ibox l u, ∑ z ∈ ibox l u, |g y - g z|) / ((ibox l u).card : ℝ) :=
        (Finset.sum_div _ _ _).symm
    _ ≤ (((ibox l u).card : ℝ) * ∑ m : Fin d, ((Finset.Ico (l m) (u m)).card : ℝ) *
          ∑ q ∈ ibox l u, |g (q + unit m) - g q|) / ((ibox l u).card : ℝ) := by
        gcongr
        exact sum_sum_abs_sub_le l u g
    _ = ∑ m : Fin d, ((Finset.Ico (l m) (u m)).card : ℝ) *
          ∑ q ∈ ibox l u, |g (q + unit m) - g q| := by
        field_simp
    _ ≤ ∑ m : Fin d, L * ∑ q ∈ ibox l u, |g (q + unit m) - g q| :=
        Finset.sum_le_sum fun m _ =>
          mul_le_mul_of_nonneg_right (card_Ico_le_of_nonempty hL hQ m)
            (Finset.sum_nonneg fun _ _ => abs_nonneg _)
    _ = L * ∑ q ∈ ibox l u, ∑ i : Fin d, |g (q + unit i) - g q| := by
        rw [← Finset.mul_sum]
        congr 1
        exact Finset.sum_comm

/-- The discrete `L¹` Poincaré inequality on a box (constant `2^d * d * L`, weaker than the
sharp constant `L`). -/
theorem sum_abs_sub_avg_le_box {d : ℕ} (l u : Fin d → ℤ) (L : ℝ)
    (hL : ∀ i, ((u i - l i : ℤ) : ℝ) ≤ L) (g : Site d → ℝ) :
    ∑ y ∈ Fintype.piFinset (fun i => Finset.Ico (l i) (u i)),
        |g y - (∑ z ∈ Fintype.piFinset (fun i => Finset.Ico (l i) (u i)), g z) /
          ((Fintype.piFinset (fun i => Finset.Ico (l i) (u i))).card : ℝ)| ≤
      2 ^ d * d * L * ∑ q ∈ Fintype.piFinset (fun i => Finset.Ico (l i) (u i)),
        ∑ i : Fin d, |g (q + unit i) - g q| := by
  refine (sum_abs_sub_avg_le_box_sharp l u L hL g).trans ?_
  rcases (ibox l u).eq_empty_or_nonempty with hQ | hQ
  · simp [hQ]
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  have hL0 : 0 ≤ L :=
    (Nat.cast_nonneg _).trans (card_Ico_le_of_nonempty hL hQ ⟨0, hd⟩)
  have hX : 0 ≤ ∑ q ∈ ibox l u, ∑ i : Fin d, |g (q + unit i) - g q| :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hc : (1 : ℝ) ≤ 2 ^ d * d := by
    have h2 : 1 ≤ 2 ^ d := Nat.one_le_two_pow
    have : 1 ≤ 2 ^ d * d := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by positivity) hd.ne')
    exact_mod_cast this
  calc L * ∑ q ∈ ibox l u, ∑ i : Fin d, |g (q + unit i) - g q|
      = 1 * (L * ∑ q ∈ ibox l u, ∑ i : Fin d, |g (q + unit i) - g q|) := by ring
    _ ≤ (2 ^ d * d) * (L * ∑ q ∈ ibox l u, ∑ i : Fin d, |g (q + unit i) - g q|) :=
        mul_le_mul_of_nonneg_right hc (mul_nonneg hL0 hX)
    _ = _ := by ring

end DivisibleHomogenize

end RandomSandpile
