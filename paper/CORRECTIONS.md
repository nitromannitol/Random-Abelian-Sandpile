# Corrections to the published version

The corrected draft [`random_piles-corrected.tex`](random_piles-corrected.tex) differs from the arXiv
source [`random_piles.tex`](random_piles.tex) by the corrections below. Each is marked in the
corrected draft by a comment `% CORRECTION [Cn]` at the end of the changed line, giving the printed
text and the reason; C13 replaces the statement and the proof of Theorem 9.2 by a block whose lines
are marked in the same way. The script [`make_corrected.py`](make_corrected.py) produces the
corrected draft from the arXiv source by applying them. The numbering of the paper is unchanged. Each
correction was tested in an independent model review. The numbers C7, C9 and C10 are not used.

| Id | Result | Printed | Corrected | Reason |
| --- | --- | --- | --- | --- |
| C1 | Lemma 6.3 | `μ*(l, M) ≥ μ*(l + s, M) + sC` | `μ*(l, M) ≤ μ*(l + s, M) + sC` | As printed it forces `C ≤ 0` where `μ*` vanishes (Lemma 5.4), contradicting the first inequality. |
| C2 | Lemma 6.2 | `α := μ(l_M, M)`; `p₀ · (y − x)` | `α := μ(l, M)`; `p₀ · (y − x₀)` | Index typos: the proof uses Lemma 5.5 at `(l, M)`, and the contact point is `x₀`. |
| C3 | Theorems 1.1 and 9.2 | `F̄_η(D²v̄) ≤ 0` in `W`; `F̄_η(D²(v̄ + G)) ≤ 0` | `F̄_η(D²v̄) ≥ 0` in `W`; `F̄_η(D²(v̄ + G)) ≥ 0`, in the viscosity sense with test functions touching from below | `F̄_η` is nonincreasing in the Hessian (Lemma 6.4), and the least supersolution satisfies `≥ 0`. For `d = 2` and `η ≡ 0`, `F̄_η(0) = 4/3 > 0`, which contradicts the printed condition of Theorem 9.2 on the region where the limit vanishes. |
| C4 | Lemma 6.2 | there is `w_n ∈ S(B_n, η, l, M)` with the bending property | the same `w_n` also satisfies the first inequality of (spreadout), `α/2 · \|B_{βn}\| ≤ \|∂⁺(Γ_{w_n}, B_{βn})\|` | As printed the lemma is vacuous (`w_n = K 1_{∂B_n} − q_l − q_M` with `K` large has no contact point in `B_n`); the proof chooses `w_n` with the displayed inequality, and the proof of Lemma 6.3 uses it. |
| C5 | Lemma 7.1, and its use in Lemma 7.2 | `g(x) ≤ C x²`; `v_n(x) ≤ C_d \|x\|²` | `g(x) ≤ C (ℓ + 1)²`; `v_n(x) ≤ C (n + 1)²` | The printed bound fails at `x = 0` (`r = ℓ = 1`: `g(0) = 5`); the proof of Lemma 7.2 needs only `v_n ≤ C n²`. |
| C6 | Proposition 5.1 | for each `x_i`, `Γ_w(x_i) = w(x_i)` and `Γ_w` is linear on the convex hull | only for the `x_i` with `λ_i > 0` | A point with weight `0` is arbitrary. |
| C8 | Proposition 5.3 | no hypothesis linking the process to the shifts | `η ↦ f(A, η)` measurable and `f(A, T_y η) = f(y + A, η)` | Without them the conclusion fails: `f(A) = \|A ∩ H\|`, `H` a half-space, is subadditive and bounded, and its limit depends on `W`. |
| C11 | Lemma 6.2 | `C := C_{η_min, η_max, l, M, d}` | `C := C_{η_min, η_max, l, M, d, β}` | The proof gives `C(β) = c(1 − β)²`. |
| C12 | Theorem 1.1 | `R > 0` depending on `W` and `E(η(0))` | `R > 0` depending on `W`, `d` and `η_max` | The radius comes from the box of Lemma 7.2, obtained through Lemma 7.1, whose size depends on `η_max`. This is a weakening adopted by the author: the printed dependence is neither proved nor refuted here. |
| C13 | Theorem 9.2 | the single-source limit is described with the operator `F̄_η` | the operator `F̄ᴿ_η`, defined with recurrent functions in both curvature classes; the same conclusion for every bounded stationary ergodic background with finite odometers and a vanishing tail (VT); `F̄ᴿ_η = F̄_η` for backgrounds recurrent on every finite set, and the two differ for `η ≡ 0` | The statement is replaced by one that is proved; the corrected draft also gives its proof, which the paper did not print. |
| C14 | Section 8.1 (Proposition 8.1) | a domain `V ∈ ℤᵈ`; excess mass `1 − η(x)`; `v` counts the total mass emitted by each site | a finite domain `V ⊂ ℤᵈ` with sinks outside `V`; excess mass `η(x) − 1`; `v` counts the mass sent from each site to each of its neighbors | An infinite domain need not stabilize; an unstable site has `η(x) > 1`; with the unnormalized Laplacian in Proposition 8.1 the odometer is the total emission divided by `2d`. |
| C15 | Theorem 9.1 | `v̄_n` converges to the unique viscosity solution `v̄ ∈ C(ℝᵈ)` | `v̄_n` converges to the function `v̄ ∈ C(ℝᵈ)` that vanishes outside `W` and whose restriction to `W̄` is the unique viscosity solution | The equation and the boundary condition determine `v̄` only on `W̄`. |
| P1 | Section 6, definition of `F̄_η` | the intermediate value argument uses continuity of `μ(·, M)` and `μ*(·, M)` | a footnote: the constant of Lemma 6.3 can be chosen uniformly for `l` in compact sets | The definition of `l_M` needs this continuity. The printed proof of Lemma 6.3 gives a constant for each fixed `l` only; the Lean proof of the uniform version is described below. |

**Lemma 5.4.** The Lean statement is a generalization: it holds for all integer bounds, with the
threshold `l ≤ −max(η_max, 0) − tr M`. In the paper's setting high density forces `η_max ≥ 2d`, and
the threshold is the printed one; for a negative upper bound the printed threshold is false.

## Where the Lean proofs depart from the printed argument

- **Lemmas 6.3 and 6.4.** Lemma 6.3 is proved with a constant uniform for `l` in bounded sets
  (`MuLipschitzLocStmt` in
  [`RandomSandpile/Proofs/Sec6/EffectiveOperatorBasicLip.lean`](../RandomSandpile/Proofs/Sec6/EffectiveOperatorBasicLip.lean)),
  by applying the bending estimate of Lemma 6.2 to near-maximizing sequences, whose Laplacians are
  bounded uniformly for `l` in bounded sets. This gives the continuity in `l` used in Lemma 6.4.
- **Lemma 7.6.** The paper quotes it from Pegden and Smart. Here it is proved from their Propositions
  2.4 and 2.5 and the equivalence of viscosity and weak solutions (Ishii), by an argument localized
  to balls
  ([`RandomSandpile/Proofs/Sec7/PegdenSmartAdapter.lean`](../RandomSandpile/Proofs/Sec7/PegdenSmartAdapter.lean));
  no Aleksandrov–Bakelman–Pucci estimate on general domains is needed.
- **Theorems 9.1 and 9.2.** The paper prints no proof of either. Theorem 9.1 is proved by the
  argument of Section 7 with the open boundary condition, and Theorem 9.2 by the argument given with
  correction C13 in the corrected draft.
