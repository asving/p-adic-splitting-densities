# p-adic splitting densities: uniform rationality and palindromy

For a finite extension $K/\mathbb{Q}_p$ with residue field of size $q$, let
$\rho(n,\sigma;q)$ be the density (normalized Haar measure) of monic degree-$n$
polynomials over $\mathcal{O}_K$ whose factorization type is $\sigma$ (the multiset of
ramification/residue pairs $(e_i,f_i)$ of the irreducible factors). This repository
accompanies a paper proving:

> **Theorem.** For each $n$ and $\sigma$, the projective density $\rho(n,\sigma;q)$ is a
> single rational function $R_\sigma(q)\in\mathbb{Q}(q)$ — the *same* at every prime,
> **including the wild primes $p\mid n$** — and it is palindromic: $R_\sigma(1/q)=R_\sigma(q)$.

The uniformity across wild primes is the new content. The earlier route to the
Bhargava–Cremona–Fisher conjecture used an $S_n$-equivariant smooth resolution, which
**provably fails when $p\mid n$** (the relevant degeneration is inseparable on tangent
spaces). The repair is a direct **Okutsu–Montes / Guàrdia–Montes–Nart (GMN)** recursion:
the density decomposes over a finite set of combinatorial OM tree-shapes, each
contributing a cluster volume that is a uniform rational function of $q$ (built from a
lattice-volume factor and a finite-field residual count), with infinitely many descent
depths resummed by a geometric self-loop. Palindromy is then **free downstream of
uniformity**: it holds at tame primes by the classical (Igusa–Denef–Meuser) functional
equation, and a single rational function agreeing with a palindromic one at the infinitely
many tame primes is palindromic identically.

## Contents

| Path | What it is |
|------|------------|
| `paper/main.pdf`, `paper/main.tex` | The paper. |
| `paper/certificate.pdf`, `paper/certificate.tex` | **Certificate of correctness**: the exact assumed-vs-proven ledger for the Lean development plus the cross-checks. Read this for precise claims. |
| `lean/` | Lean 4 (v4.31.0 / mathlib v4.31.0) formalization. See `lean/README.md`. |
| `verification/` | Reproducible cross-checks: the symbolic OM density engine vs. BCFG root-count moments, and the PARI `factorpadic` oracle. See `verification/README.md`. |
| `docs/ASSUMED_VS_PROVEN.md` | Plain-text mirror of the certificate ledger. |
| `docs/GMN_citations.md` | Map from the OM/Montes inputs we cite to the exact theorem numbers in GMN. |

## Status — what is and is not proven (please read)

The **mathematical result is complete modulo the published Montes/GMN algorithm**, which
is accepted literature (Guàrdia–Montes–Nart, *Trans. Amer. Math. Soc.* **364** (2012),
arXiv:0807.2620). In that standard sense the theorem is proven. It is also extensively
cross-checked:

- the trusted **PARI `factorpadic` oracle** confirms the densities at $n\le 4$, including
  the wild prime $p=2$ and the slope-$\tfrac12$ Artin–Schreier inseparable stratum;
- the **symbolic OM engine reproduces the BCFG root-count moments exactly through $n=6$**
  (every $P(n,r;q)$ and binomial moment, as exact rational functions).

The **Lean formalization is sound but conditional**, and we are precise about this:

- The capstone `Goal.goal_theorem_montes` is sorry-free with axiom footprint
  `{propext, Classical.choice, Quot.sound, tame_functionalEquation}` — Lean's core plus the
  one cited tame functional equation. The novel argument (the OM cluster-volume recursion,
  the geometric collapse, the $U_N\to0$ tail bound, the decomposition theorem, rationality,
  and the palindromy transfer) is machine-checked Lean-core-only.
- It is **conditional** on a hypothesis bundle: a minimal box-wise identification
  (`boxHaarEquidist`, `nodeMeasure_boxSum`: per-box Haar volume = the proved closed-form
  value), the GMN count-shadow hypotheses (partition / descent / finite-termination), and
  the tame functional equation. mathlib v4.31.0 has **no $p$-adic Haar measure and no
  Montes machinery**, so the actual density $\rho$ is not constructed inside Lean (the only
  instance of the bundle in the project is a trivial degree-0 witness). This is **not** an
  unconditional machine-checked proof.
- The remaining gap is **combinatorial, not analytic**: $p$-adic density is a limit of
  counting fractions over $\mathbb{Z}/p^N$ (no Lebesgue measure needed); closing it means
  formalizing the Montes cell-count bijection (Newton polygons + residual polynomials), a
  large but in-principle constructive task.

`paper/certificate.pdf` and `docs/ASSUMED_VS_PROVEN.md` give the exact per-theorem axiom
footprints.

## Building

**Paper.** `cd paper && pdflatex main && pdflatex main` (bibliography via `reference.bib`);
likewise `pdflatex certificate`.

**Lean.** Requires [`elan`](https://github.com/leanprover/elan) and Lean 4.31.0.
```
cd lean
lake exe cache get      # fetch the prebuilt mathlib cache (large)
lake build LeanUrat
```
Verify the axiom footprints with `lake env lean LeanUrat/AxChk_baseline.lean`. See
`lean/README.md` for details and a known environmental build caveat.

**Verification.** Needs Python 3 with `sympy`; the oracle additionally needs PARI/GP via
`cypari2`.
```
cd verification
python3 cert_crosschecks.py       # 25 exact symbolic / finite-field checks
python3 reconcile_om_bcfg.py      # OM engine vs BCFG moments, exact through n=5/6
python3 quartic_oracle.py         # PARI factorpadic oracle (needs cypari2)
```

## References

- M. Bhargava, J. Cremona, T. Fisher, S. Gajović, *The proportion of polynomials of bounded
  degree that split completely / have a root over $\mathbb{Z}_p$*, arXiv:2101.09590.
- J. Guàrdia, J. Montes, E. Nart, *Newton polygons of higher order in algebraic number
  theory*, Trans. Amer. Math. Soc. **364** (2012), no. 1, 361–416, arXiv:0807.2620.
