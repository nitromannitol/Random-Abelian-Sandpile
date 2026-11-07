import RandomSandpile.Defs.Lattice

/-!
# Bounded Lipschitz domains

The main theorem takes a bounded Lipschitz domain `W ⊆ ℝ^d`. Neither Mathlib nor
Lattice-Probability has this notion, so we write the standard one (Grisvard, *Elliptic problems in
nonsmooth domains*, Definition 1.2.1.1; Evans–Gariepy, *Measure theory and fine properties of
functions*, §4.2): `W` is a bounded, open, connected set whose boundary is, near each of its
points, the graph of a Lipschitz function of `d - 1` variables, with `W` on one side of it.
-/

noncomputable section

namespace RandomSandpile

variable {d : ℕ}

/-- `W ⊆ ℝ^d` is a *bounded Lipschitz domain*: `W` is bounded, open and connected, and for every
boundary point `x₀ ∈ ∂W` there are a radius `r > 0`, a unit vector `e` (the vertical direction
after a rigid motion) and a Lipschitz function `γ`, such that inside the ball `B_r(x₀)` the set `W`
is exactly the region strictly above the graph of `γ`:
`W ∩ B_r(x₀) = {y ∈ B_r(x₀) : γ(z') < z·e}`, where `z = y - x₀` and `z' = z - (z·e) e` is its
component in the hyperplane `e^⊥`.

This is the usual definition with the rotated coordinates `(z', z_d)`, `z_d = z·e`, written without
choosing a basis of `e^⊥`: `γ` is only evaluated on `e^⊥ ≅ ℝ^{d-1}`, every Lipschitz function on
`e^⊥` extends to a Lipschitz function on `ℝ^d` with the same constant (compose with the orthogonal
projection, which is `1`-Lipschitz), and conversely the restriction of a Lipschitz function on
`ℝ^d` to `e^⊥` is Lipschitz. -/
def IsLipschitzDomain (W : Set (Rd d)) : Prop :=
  Bornology.IsBounded W ∧ IsOpen W ∧ IsConnected W ∧
    ∀ x₀ ∈ frontier W, ∃ r : ℝ, 0 < r ∧ ∃ e : Rd d, ‖e‖ = 1 ∧
      ∃ (L : NNReal) (γ : Rd d → ℝ), LipschitzWith L γ ∧
        ∀ y ∈ Metric.ball x₀ r,
          (y ∈ W ↔ γ ((y - x₀) - inner ℝ (y - x₀) e • e) < inner ℝ (y - x₀) e)

end RandomSandpile
