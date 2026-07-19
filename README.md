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
| `paper/certificate.pdf`, `paper/certificate.tex` | Certificate of correctness (the paper's assumed-vs-proven ledger + cross-checks). |
| `lean/` | Lean 4 (v4.31.0 / mathlib v4.31.0) formalization (~117 modules). See `lean/README.md`. |
| `docs/PROJECT_STATE.md` | **Current authoritative state**: what is proved, the trusted axiom base, the module ↔ math-proof map, and the in-progress order-≥2 work. Start here. |
| `docs/HUMAN_PROOF.md` | The math-language proof write-up (13 sections). |
| `docs/AXIOM_FAITHFULNESS.md` | Audit of every trusted axiom against its published source. |
| `docs/GMN_citations.md` | Map from the OM/Montes inputs we cite to the exact GMN theorem numbers. |
| `docs/ASSUMED_VS_PROVEN.md` | Earlier assumed-vs-proven ledger (superseded by `PROJECT_STATE.md`; kept for history). |
| `docs/in-progress/` | Design blueprints for the order-≥2 (deep-wild) formalization. |
| `docs/references/montes-blueprint.pdf` | Our blueprint of the Montes/GMN inputs. |
| `verification/` | Reproducible cross-checks: the symbolic OM density engine vs. BCFG root-count moments, and the PARI `factorpadic` oracle. See `verification/README.md`. |

## Status — what is and is not proven (please read)

The **mathematical result is complete modulo the published Montes/GMN algorithm**, which
is accepted literature (Guàrdia–Montes–Nart, *Trans. Amer. Math. Soc.* **364** (2012),
arXiv:0807.2620). In that standard sense the theorem is proven. It is also extensively
cross-checked:

- the trusted **PARI `factorpadic` oracle** confirms the densities at $n\le 4$, including
  the wild prime $p=2$ and the slope-$\tfrac12$ Artin–Schreier inseparable stratum;
- the **symbolic OM engine reproduces the BCFG root-count moments exactly through $n=6$**
  (every $P(n,r;q)$ and binomial moment, as exact rational functions).

The **Lean formalization is `sorry`-free but, at the top level, does not yet *non-vacuously*
prove the full theorem.** We are precise about exactly what is and is not established (a standing
semantic audit enforces this honesty; see `docs/PROJECT_STATE.md` for the per-capstone detail).

**Genuinely machine-checked, non-vacuous:**

- A **$p$-uniform rationality engine.** The count-native OM cluster-volume recursion plus the
  `RatFn` closure produce, over all primes *including wild*, a uniform rational function of $q$
  (genuinely $q$-varying; the wild contribution is a lattice-volume factor × a finite-field
  residual count). The soundness fixes are real: `IsPalindromic` is the faithful degree-robust
  $R(1/x)=R(x)$, and `TameFunctionalEquation` is a definition (an earlier *false* global axiom
  was caught and removed).
- A **real order-0 density theorem** — `Order0RealDensity.montes_order0_density_general_prime`:
  an actual `Nat.card` fiber count over `monicBox p N n`, uniform-rational over all primes, with
  a machine-checked positivity/non-vacuity gate. **But** it covers the **order-0
  separable/unramified stratum only**, in the **monic** (not projective) normalization, carries
  **no palindromy**, and is consumed by none of the `Goal` capstones.
- The Okutsu–Montes classifier subsystem is formalized (higher-order Newton polygons, residual
  polynomials, the OM tree/type, φ-adic development) — the ~95-module `lean/LeanUrat/OM/`.

**`sorry`-free but NOT yet a non-vacuous proof of the full theorem:**

- The palindromic capstones (`goal_theorem`, `goal_theorem_montes`, `goal_theorem_via_montes`)
  are **`∀ F : DensityFoundation` conditionals over a *free* density field** (`Interface.lean`):
  they say "for every abstract density satisfying the bridge + tame-functional-equation
  hypotheses, it is uniform-rational and palindromic." `goal_theorem_via_montes` is `sorry`-free
  with a Lean-core-only footprint `{propext, Classical.choice, Quot.sound}` — **but its only
  `sorry`-free non-vacuous instance is the trivial degree-0 witness** (n=0, density ≡ 1).
- The intended **real all-orders instance** (`M9.montes_unconditional`) is, *by its own
  docstring*, currently **vacuous**: with the present order-0 decode every coefficient is
  identically 0 (density ≡ 0), it is **σ-independent**, and it is gated behind a hypothesis that
  is **false** for the real instance. De-vacuification (repair the decode so cells carry real
  payloads; resolve per-type σ) is the standing obligation.
- **Palindromy is assumed, not proved on a real instance:** it enters only as the tame
  functional-equation hypothesis/axiom (Del Corso–Dvornicich / Igusa–Denef–Meuser), which on the
  current (constant-0) instance holds trivially.

**Trusted base + hygiene.** A few explicitly-`axiom`-declared citations, each a triple-checked
faithful semantic port: the GMN **theorem of the index** ($\mathrm{ind}\le v_p(\mathrm{disc})$,
read-set-restricted / arising-key); the **Denef–Igusa** $p$-adic cell recursion; the
**Del Corso–Dvornicich** tame functional equation. A standing "semantic guardian" re-audits these
(two false axioms were caught and removed this way); see `docs/AXIOM_FAITHFULNESS.md`,
`lean/notes/SEMANTIC_AUDIT_LOG.md`. Exactly **one banked `sorry`**
(`Classifier.npVertices_stable_of_hull_preserved`), **off** the capstone path.

**In progress:** de-vacuifying the real density instance (decode repair + σ-resolution), and
extending classifier faithfulness from order ≤ 1 to order ≥ 2 (the deep-wild OM tower). See
`docs/in-progress/`.

**Bottom line.** The mathematics is complete modulo the published Montes/GMN algorithm and is
extensively cross-checked; the Lean contribution to date is a genuine $p$-uniform rationality
engine, a real order-0 density theorem, and the formalized OM classifier — but it is **not** an
unconditional, non-vacuous machine-checked proof of the full palindromic all-orders theorem. The
headline palindromic capstones are abstract conditionals whose only real instances are currently
trivial or vacuous. `docs/PROJECT_STATE.md` is the authority; `lake build LeanUrat.AxChk_baseline`
prints the machine-checked per-theorem footprints.

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
