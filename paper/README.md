# The paper

This directory holds the paper that the Lean development formalizes:

> Ahmed Bou-Rabee,
> *Convergence of the random Abelian sandpile*,
> Annals of Probability 49(6) (2021), 3168–3196,
> [doi:10.1214/21-AOP1528](https://doi.org/10.1214/21-AOP1528);
> [arXiv:1909.07849](https://arxiv.org/abs/1909.07849).

It is included by its author and is not covered by the Apache license of the Lean code.

| File | Content |
| --- | --- |
| [`random_piles.tex`](random_piles.tex) | The LaTeX source of arXiv:1909.07849, unmodified. |
| [`random_piles.pdf`](random_piles.pdf) | That source, compiled. |
| [`random_piles-corrected.tex`](random_piles-corrected.tex) | The corrected draft that the Lean statements follow: the arXiv source with local corrections, each marked by a comment `% CORRECTION [Cn]` at the end of the changed line. |
| [`random_piles-corrected.pdf`](random_piles-corrected.pdf) | The corrected draft, compiled. |
| [`CORRECTIONS.md`](CORRECTIONS.md) | The list of corrections, with the reason for each, and the places where the Lean proofs depart from the printed argument. The [README](../README.md#corrections-to-the-published-version) of the repository summarizes them. |
| [`make_corrected.py`](make_corrected.py) | Produces the corrected draft from the arXiv source by applying the corrections; each is an exact replacement that must occur exactly once, and the numbering of the paper is checked to be unchanged. |
| `*.png` | The figures of the arXiv source. |
| [`random_piles.bbl`](random_piles.bbl), [`random_piles-corrected.bbl`](random_piles-corrected.bbl) | The bibliography of the arXiv source, one identical copy for each version of the paper. |

To regenerate the corrected draft, or to check that it is up to date, run from the repository root

```bash
python3 paper/make_corrected.py            # write paper/random_piles-corrected.tex
python3 paper/make_corrected.py --check    # compare with the committed file
```

To compile either version, run `pdflatex` three times on its `.tex` file in this directory.
