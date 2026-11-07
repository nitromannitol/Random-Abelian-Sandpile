#!/usr/bin/env python3
"""Generate paper/random_piles-corrected.tex from the arXiv source paper/random_piles.tex.

Each correction is a minimal edit of a single source line, except C13, which replaces the statement
and the proof of Theorem 9.2. Each edited line ends with a comment `% CORRECTION [Cn]: <printed text
and reason>`; the list, with the reasons, is paper/CORRECTIONS.md. Applied:
  C1  Lemma 6.3          second inequality reversed
  C2  Lemma 6.2          index typos mu(l_M,M) -> mu(l,M), (y-x) -> (y-x_0)
  C3  Theorems 1.1, 9.2  sign of the F-bar_eta inequality; the viscosity sense made explicit
  C4  Lemma 6.2          intended reading: w_n also satisfies the first inequality of (spreadout)
  C5  Lemma 7.1          g(x) <= C (l+1)^2, and its use in Lemma 7.2
  C6  Proposition 5.1    contact and affine claims only for the x_i with lambda_i > 0
  C8  Proposition 5.3    stationarity and measurability of the subadditive process
  C11 Lemma 6.2          the constant C depends on beta
  C12 Theorem 1.1        R depends on W, d and eta_max
  C13 Theorem 9.2        the recurrent operator, and the extension under (VT)
  C14 Section 8.1        the divisible sandpile: finite domain, excess eta(x) - 1, mass sent to each neighbor
  C15 Theorem 9.1        uniqueness on the closure of W; the limit vanishes outside W
  P1  Section 6          proof correction (local uniformity of the constant of Lemma 6.3), as a footnote;
                         the printed proof of Lemma 6.3 does not give it, and the footnote says so
The numbers C7, C9 and C10 are not used.

The script checks that every edited line occurs exactly once in the source and that the numbered
environments, sectioning commands, labels and equations agree between the source and the output
(same theorem numbering).

Usage:  python3 -I paper/make_corrected.py          (write the corrected tex)
        python3 -I paper/make_corrected.py --check  (compare with the existing file)
"""

import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
SRC = ROOT / "paper" / "random_piles.tex"
DST = ROOT / "paper" / "random_piles-corrected.tex"

# (tag, printed line suffix, corrected line suffix, note). The printed suffix runs to the end of
# its source line, trailing spaces included; the note is appended as ` % CORRECTION [tag]: note`.
EDITS = [
    ("C3",
     r"\bar{F}_{\eta}(D^2 \bar{v}) \leq 0 \mbox{ in $W$,and } \bar{F}_0(D^2 \bar{v}) \leq 0 \mbox{ in $\R^d$}\},",
     r"\bar{F}_{\eta}(D^2 \bar{v}) \geq 0 \mbox{ in $W$,and } \bar{F}_0(D^2 \bar{v}) \leq 0 \mbox{ in $\R^d$}\},",
     r"Theorem 1.1, printed \bar{F}_{\eta}(D^2 \bar{v}) \leq 0 in W. \bar{F}_\eta is nonincreasing in M"
     r" (Lemma 6.4(1)), so the printed inequality fails for every test function touching from below at"
     r" which D^2 is very negative; the least supersolution satisfies \geq 0"),
    ("C3",
     "and the differential inequalities are interpreted in the viscosity sense. ",
     "and the differential inequalities are interpreted in the viscosity sense, with test functions"
     " touching from below.",
     "Theorem 1.1, the viscosity sense made explicit: both inequalities are supersolution conditions"),
    ("C12",
     r"for some constant $R > 0$ depending on $W$ and $\E(\eta(0))$, and weakly, ",
     r"for some constant $R > 0$ depending on $W$, $d$ and $\eta_{\max}$, and weakly,",
     r"Theorem 1.1, printed 'depending on $W$ and $\E(\eta(0))$'. R comes from the box of Lemma 7.2"
     r" (obtained through Lemma 7.1), whose size depends on \eta_{\max}"),
    ("C6",
     r"then for each $x_i$, $\Gamma_w(x_i) = w(x_i)$ and $\Gamma_w$ is linear in $\conv(x_1, \ldots, x_{d+1})$. ",
     r"then for each $x_i$ with $\lambda_i > 0$, $\Gamma_w(x_i) = w(x_i)$, and $\Gamma_w$ is linear in"
     r" $\conv(\{x_i : \lambda_i > 0\})$.",
     r"Proposition 5.1, printed for every x_i: an x_i with \lambda_i = 0 is arbitrary"
     r" (x = x_1 a contact point, \lambda_1 = 1)"),
    ("C8",
     r"Let $f: \Omega \to \mathcal{M}_C$ be a subadditive process. There exists",
     r"Let $f: \Omega \to \mathcal{M}_C$ be a subadditive process such that $\eta \mapsto f(A, \eta)$ is"
     r" measurable and $f(A, T_y \eta) = f(y + A, \eta)$ for all $A \in \mathcal{U}_0$ and $y \in \Z^d$."
     r" There exists",
     r"Proposition 5.3, stationarity and measurability of f added. Without them the conclusion fails:"
     r" f(A, \eta) = |A \cap H| with H a half-space is in M_1, and the limit depends on W"),
    ("C2",
     r"Suppose that $\alpha := \mu(l_M,M) > 0$. There exists a constant $C := C_{\eta_{\min}, \eta_{\max}, l, M, d}$"
     r"  so that for each $\eta$ in a set $\Omega_{l,M}$ of full probability and $0 < \beta < 1$ the following"
     r" holds. There is an $n_0 \in \N$ ",
     r"Suppose that $\alpha := \mu(l,M) > 0$. There exists a constant"
     r" $C := C_{\eta_{\min}, \eta_{\max}, l, M, d, \beta}$  so that for each $\eta$ in a set $\Omega_{l,M}$"
     r" of full probability and $0 < \beta < 1$ the following holds. There is an $n_0 \in \N$",
     r"Lemma 6.2, printed \mu(l_M,M) (index typo; the proof uses Lemma 5.5 at (l,M)) % CORRECTION [C11]:"
     r" printed C_{\eta_{\min}, \eta_{\max}, l, M, d}. The constant also depends on \beta: the proof gives"
     r" C(\beta) = c(1-\beta)^2"),
    ("C4",
     r"there exists $w_n \in S(B_{n}, \eta, l, M)$ so that for each $x_0 \in \{ \Gamma_{w_n} = w_n\} \cap B_{\beta n}$"
     r" and $p_0 \in \partial^+(w_n, x_0, B_n)$",
     r"there exists $w_n \in S(B_{n}, \eta, l, M)$ with"
     r" $\frac{\alpha}{2} |B_{\beta n}| \leq |\partial^+(\Gamma_{w_n},B_{\beta n})|$ and so that for each"
     r" $x_0 \in \{ \Gamma_{w_n} = w_n\} \cap B_{\beta n}$ and $p_0 \in \partial^+(w_n, x_0, B_n)$",
     r"Lemma 6.2, intended reading (a proof gap, not a statement error). As printed nothing links w_n to"
     r" \mu, so w_n = K 1_{\partial B_n} - q_l - q_M (K large) has no contact point in B_n and makes the"
     r" lemma vacuous; the proof chooses w_n satisfying the first inequality of (spreadout), and the"
     r" proof of Lemma 6.3 needs it"),
    ("C2",
     r"w_n(y) \leq w_n(x_0) + p_0 \cdot (y-x) - C \alpha n^2",
     r"w_n(y) \leq w_n(x_0) + p_0 \cdot (y-x_0) - C \alpha n^2",
     r"Lemma 6.2, printed (y-x); the contact point is x_0"),
    ("C1",
     r"\mu^*(l,M) \geq \mu^*(l+s,M) + sC. ",
     r"\mu^*(l,M) \leq \mu^*(l+s,M) + sC.",
     r"Lemma 6.3, printed \geq. As printed it forces C \leq 0 where \mu^* vanishes (Lemma 5.4), which"
     r" contradicts the first inequality"),
    ("P1",
     r"The above results show Lipschitz continuity of $\mu$ for each fixed $l \in \R$. Repeating this for every rational $l$ ",
     r"The above results show Lipschitz continuity of $\mu$ for each fixed $l \in \R$.\footnote{The constant"
     r" of Lemma \ref{continuity} can be chosen uniformly for $l$ in compact sets; this is the continuity of"
     r" $\mu(\cdot, M)$ and $\mu^*(\cdot, M)$ used in the intermediate value argument below. The argument"
     r" above does not establish this as written; a complete proof, which applies Lemma \ref{strict-convexity}"
     r" to near-maximizing sequences, whose Laplacians are bounded uniformly for $l$ in compact sets, is part"
     r" of the accompanying Lean formalization.} Repeating this for every rational $l$",
     r"proof correction, no statement change: the intermediate value argument needs continuity in l, and the"
     r" printed proof of Lemma 6.3 does not give it"),
    ("C5",
     r"g(x) \leq C x^2. ",
     r"g(x) \leq C (\ell+1)^2.",
     r"Lemma 7.1, printed g(x) \leq C x^2, false at x = 0 (r = 1, \ell = 1: g(0) = 5); the proof of"
     r" Lemma 7.2 needs only v_n \leq C n^2"),
    ("C5",
     r"v_n(x) \leq \min(u_1(x), \ldots, u_d(x)) \leq C_d |x|^2.",
     r"v_n(x) \leq \min(u_1(x), \ldots, u_d(x)) \leq C (n+1)^2.",
     r"proof of Lemma 7.2, printed C_d |x|^2; Lemma 7.1 as corrected, with \ell = C_{d,W} n"),
    ("C3",
     r"\bar{v} := \inf\{ \bar{v} \in C(\R^d) | \bar{v} \geq -G \mbox{ and } \bar{F}_\eta(D^2 (\bar{v}+G)) \leq 0\}.",
     r"\bar{v} := \inf\{ \bar{v} \in C(\R^d) | \bar{v} \geq -G \mbox{ and } \bar{F}_\eta(D^2 (\bar{v}+G)) \geq 0\}.",
     r"Theorem 9.2, printed \leq 0: the sign error of Theorem 1.1. The literal statement is false"
     r" (d = 2, \eta = 0, \bar{F}_\eta(0) = 4/3 > 0)"),
    ('C14',
     'Begin with some, possibly fractional, distribution of sand and holes, on a domain $V \\in \\Z^d$,  $\\eta : V \\to \\R$.  A site $x \\in V$ is unstable whenever $\\eta(x) > 1$, ',
     'Begin with some, possibly fractional, distribution of sand and holes, on a finite domain $V \\subset \\Z^d$, with sinks outside $V$, $\\eta : V \\to \\R$.  A site $x \\in V$ is unstable whenever $\\eta(x) > 1$, ',
     "Section 8.1, printed 'on a domain $V \\in \\Z^d$': the divisible sandpile is run on a finite domain with sinks outside it (an infinite domain need not stabilize)"),
    ('C14',
     'in which case the {\\it excess mass}, $1 - \\eta(x)$, is equally distributed among the neighbors of $x$ until every site is stable. The odometer function, ',
     'in which case the {\\it excess mass}, $\\eta(x) - 1$, is equally distributed among the neighbors of $x$ until every site is stable. The odometer function, ',
     'Section 8.1, printed excess mass $1 - \\eta(x)$: an unstable site has $\\eta(x) > 1$'),
    ('C14',
     '$v$, then counts the total mass emitted by each site. Here, the starting point is also a discrete PDE: the ',
     '$v$, then counts the total mass sent from each site to each of its neighbors. Here, the starting point is also a discrete PDE: the ',
     "Section 8.1, printed 'the total mass emitted by each site': with the unnormalized Laplacian in Proposition 8.1, v counts the mass sent to each neighbor (total emission divided by 2d)"),
    ('C15',
     'Almost surely, as $n \\to \\infty$, the rescaled functions $\\bar{v}_n:= n^{-2} v_n([n x])$ converge uniformly to the unique viscosity solution $\\bar{v} \\in C(\\R^d)$ of the deterministic equation',
     'Almost surely, as $n \\to \\infty$, the rescaled functions $\\bar{v}_n:= n^{-2} v_n([n x])$ converge uniformly to the function $\\bar{v} \\in C(\\R^d)$ that vanishes outside $W$ and whose restriction to $\\bar{W}$ is the unique viscosity solution of the deterministic equation',
     "Theorem 9.1, printed 'the unique viscosity solution $\\bar{v} \\in C(\\R^d)$': the equation and the boundary condition determine $\\bar{v}$ only on $\\bar{W}$; the limit vanishes outside $W$"),
]

NUMBERED = re.compile(
    r"\\begin\{(?:theorem|prop|corollary|lemma|definition|remark|equation|align|eqnarray|gather)\*?\}"
    r"|\\end\{(?:equation|align|eqnarray|gather)\*?\}"
    r"|\\(?:section|subsection|subsubsection|appendix)\*?(?![A-Za-z])"
    r"|\\label\{[^}]*\}|\\tag\{[^}]*\}|\\nonumber(?![A-Za-z])|\\notag(?![A-Za-z])"
)

# Every adopted correction has a marker (C11 shares the line of C2).
MARKERS = ["C1", "C2", "C3", "C4", "C5", "C6", "C8", "C11", "C12", "C13", "C14", "C15", "P1"]


# C13 (Theorem 9.2) replaces a block of the line-corrected text: the statement and the proof of the theorem.
BLOCK_EDITS = [
    ("C13",
     'Straightforward modifications of the arguments appearing above and in \\cite{pegden2013convergence} show that single source sandpiles on random backgrounds also have scaling limits. \nSee Figure \\ref{fig_SS_rand} for an example. \n\n\\begin{theorem}\nLet $v_n$ be the odometer function for the sandpile with $n$ chips at the origin \non a stationary, ergodic, random background $\\eta_{\\min} \\leq \\eta \\leq \\eta_{\\max} = 2d-2$, \n\\[\nv_n  \\in \\mathcal{L}(\\eta + n \\delta_0 , \\Z^d) \\cap \\mathcal{S}(\\eta + n \\delta_0, \\Z^d) .\n\\] \nAlmost surely, as $n \\to \\infty$, the rescaled functions $\\bar{v}_n:= n^{-2/d} v_n([n^{1/d} x])$ converge locally uniformly away from the origin to $\\bar{v} + G$, where $G$ is the fundamental solution of the Laplacian in $\\R^d$ and $\\bar{v} \\in C(\\R^d)$ is the unique viscosity solution of the obstacle problem, \n\\[\n\\bar{v} := \\inf\\{ \\bar{v} \\in C(\\R^d) | \\bar{v} \\geq -G \\mbox{ and } \\bar{F}_\\eta(D^2 (\\bar{v}+G)) \\geq 0\\}. % CORRECTION [C3]: Theorem 9.2, printed \\leq 0: the sign error of Theorem 1.1. The literal statement is false (d = 2, \\eta = 0, \\bar{F}_\\eta(0) = 4/3 > 0)\n\\]\n\\end{theorem}\n',
     '% CORRECTION [C13]: recurrent operator and corrected single-source theorem.\nFor a finite $A\\subset\\Z^d$, let $\\mathcal R(\\eta,A)$ consist of the integer-valued functions $r$ on $\\bar A$ such that $\\eta+\\Delta r\\leq2d-1$ in $A$ and, for every nonempty $E\\subseteq A$ and every integer-valued $w$ on $\\bar E$ with $\\eta+\\Delta w\\leq2d-1$ in $E$, % CORRECTION [C13]\n\\[\\max_E(r-w)\\leq\\max_{\\partial E}(r-w).\\] % CORRECTION [C13]\nEquivalently, every nonempty $E\\subseteq A$ contains a site $x$ at which $(\\eta+\\Delta r)(x)$ is at least the number of neighbors of $x$ in $E$. Define both $S_R$ and $S_R^*$ by replacing the respective classes in the definitions of $S$ and $S^*$ in Section 5 by $\\mathcal R(\\eta,A)$ (a constant may be added to make $r$ nonnegative). Let $\\mu_R$ and $\\mu_R^*$ be the corresponding upper and lower gradient measures, and denote their limiting densities by the same symbols. Their unique common zero in $l$ defines $\\bar F^R_\\eta(M)$. The recurrent operator is continuous and degenerate elliptic, and $\\bar F^R_\\eta(M+tI)=\\bar F^R_\\eta(M)-dt$. % CORRECTION [C13]\n\n\\begin{theorem} % CORRECTION [C13]\nLet $d\\geq2$ and let $v_n$ be the odometer function for $n$ chips at the origin on a stationary, ergodic random background $\\eta_{\\min}\\leq\\eta\\leq2d-2$. Almost surely, $\\bar v_n(x):=n^{-2/d}v_n([n^{1/d}x])$ converges locally uniformly on $\\R^d\\setminus\\{0\\}$ to $\\bar v+G$, where $\\Delta G=-\\delta_0$, $\\bar v\\in C(\\R^d)$, and $\\bar v$ is the least element of % CORRECTION [C13]\n\\[\\{w\\in C(\\R^d):w+G\\geq0,\\quad \\bar F^R_\\eta(D^2(w+G))\\geq0\\text{ in }\\R^d\\setminus\\{0\\}\\}.\\] % CORRECTION [C13]; sign retains [C3]\nThe viscosity inequality uses test functions touching from below. The same conclusion holds for any uniformly bounded, stationary ergodic background for which all $\\eta+n\\delta_0$ have finite odometers and, almost surely, % CORRECTION [C13]\n\\[\\lim_{R\\to\\infty}\\limsup_{n\\to\\infty}n^{-2/d}\\sup_{|z|\\geq Rn^{1/d}}v_n(z)=0.\\tag{VT}\\] % CORRECTION [C13]\nIf $\\eta$ is recurrent on every finite set, then $\\bar F^R_\\eta=\\bar F_\\eta$; these operators differ for $\\eta\\equiv0$. % CORRECTION [C13]\n\\end{theorem} % CORRECTION [C13]\n\n\\begin{proof} % CORRECTION [C13]\nThe recurrence condition is preserved by restriction. Recurrentizing a stabilizing function with fixed boundary gives the least signed stabilizing function and shows $\\mu_R^*=\\mu^*$; a constant shift preserves gradient measures. Applying Proposition 5.3, Lemmas 5.2, 6.1--6.3 and the separation argument of Lemma \\ref{flat} to recurrent functions gives the two limiting curvature densities, their unique common zero, and the stated properties of $\\bar F^R_\\eta$. The comparison in the separation argument is automatic for two recurrent functions. The same ABP argument as in Section \\ref{subsec:proof_of_theorem} gives recurrent quadratic correctors and the viscosity inequalities used below. For $\\eta$ recurrent on every finite set, legal topplings have recurrent final configurations, yielding equality with the original operator; for $\\eta\\equiv0$ the two values at zero are different. % CORRECTION [C13]\nUnder the height bound, least action compares the odometer with that for the constant background $2d-2$; Theorem 1.1 of Fey, Levine and Peres \\cite{fey2010growth} bounds its toppled set by a ball of radius $Cn^{1/d}$, giving (VT). More generally assume (VT). Subtract the discrete fundamental solution $G_n$ from $\\bar v_n$. The resulting functions have uniformly bounded discrete Laplacians; (VT), the discrete maximum principle, and discrete Harnack compactness give locally uniform subsequential limits $\\bar v\\in C(\\R^d)$, including at the source. Also $U=\\bar v+G\\geq0$ and $U\\to0$ at infinity. % CORRECTION [C13]\nAway from zero, stabilization and the recurrent correctors give $\\bar F^R_\\eta(D^2U)\\geq0$. On $\\{U>0\\}$, every site of a fixed finite set topples eventually; ordering last topplings proves that the final configuration there is recurrent, so the other corrector inequality gives $\\bar F^R_\\eta(D^2U)\\leq0$ in $\\{U>0\\}$. Both inequalities are in the viscosity sense. % CORRECTION [C13]\nFor any competitor $V=w+G\\geq0$, compare $U_a(x)=a^2U(x/a)$, $0<a<1$, with $V+\\epsilon$ on an annulus. The inner boundary inequality follows from the smaller singular coefficient of $U_a$, and the outer one from $U_a\\to0$. Bounded-domain viscosity comparison follows from degenerate ellipticity and the strict quadratic perturbation supplied by $\\bar F^R_\\eta(M+tI)=\\bar F^R_\\eta(M)-dt$; it applies on the positive set of $U_a$. Letting the radii tend to zero and infinity, $\\epsilon\\downarrow0$, and $a\\uparrow1$ gives $U\\leq V$. Thus every subsequential limit is the same least element, proving convergence. % CORRECTION [C13]\n\\end{proof} % CORRECTION [C13]\n\n'),
]


def strip_comments(text: str) -> str:
    """Remove TeX comments (an unescaped `%` to the end of its line)."""
    return "\n".join(re.sub(r"(?<!\\)%.*", "", line) for line in text.split("\n"))


def numbering(text: str) -> list:
    """The sequence of tokens that determine the numbering of the paper."""
    # A named \tag (the (VT) display of C13) advances no counter.
    return [t for t in NUMBERED.findall(strip_comments(text)) if not t.startswith("\\tag")]


def corrected(source: str) -> str:
    text = source
    for tag, printed, fixed, note in EDITS:
        old = printed + "\n"
        count = text.count(old)
        if count != 1:
            sys.exit(f"[{tag}] expected exactly one source line ending with {printed!r}, found {count}")
        text = text.replace(old, f"{fixed} % CORRECTION [{tag}]: {note}\n")
    for tag, old, new in BLOCK_EDITS:
        if text.count(old) != 1:
            sys.exit(f"[{tag}] expected exactly one occurrence of the replaced block, found {text.count(old)}")
        text = text.replace(old, new)
    if numbering(text) != numbering(source):
        sys.exit("the corrected tex changes the numbering of the paper")
    for tag in MARKERS:
        if f"% CORRECTION [{tag}]" not in text:
            sys.exit(f"[{tag}] missing marker")
    return text


def main() -> None:
    out = corrected(SRC.read_text(encoding="utf-8"))
    if "--check" in sys.argv[1:]:
        if DST.read_text(encoding="utf-8") != out:
            sys.exit(f"{DST.relative_to(ROOT)} differs from the generated text")
        print(f"{DST.relative_to(ROOT)} is up to date ({len(EDITS)} edits)")
    else:
        DST.write_text(out, encoding="utf-8")
        print(f"wrote {DST.relative_to(ROOT)} ({len(EDITS)} edits)")


if __name__ == "__main__":
    main()
