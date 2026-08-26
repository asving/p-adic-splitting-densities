# Verdict — MHENS: the dv-graded one-slope Hensel engine (the C.34/C.35 root)

**Verdict: ENGINE DESIGNED AND PROVED at math grade (4 named OPENs, none load-bearing
for the eight C.35 rows) — plus one ⚠ STOP-THE-LINE STATEMENT-DEFECT FINDING: the
signed C.34 uniqueness clause and signed C.35 `blockFactor_spec` clause 3 are REFUTED
on the defective stratum `D′ ∤ deg g`, by a concrete ℤ₂ instance, machine-verified
numerically.**  Full document: `docs/in-progress/HENSEL_ENGINE_2026-08-26.md`.
Certificate: `verification/dv_hensel_cert.py` + `.log` (**2832 checks, 0 FAILS**).
Probe: `leanfinal/scratch/MHENS_probe.lean` (`lake env lean` exit 0; all seven
declarations Lean-core).  No git commits; no files outside the deliverables touched.

## 1. ⚠ The finding (owner statement-gate; read doc §7 first)

`HasLabel` (C.29, DECISION C-D1's closure-free surrogate) is LEAKY: it does not pin the
degree, so a labelled block absorbs any monic factor `q` of degree `< D′` with unit
content (`W(q) = 0`, slot read `1` — the graded ring's identity).  Concrete instance
(doc §7.1, cert Sec 5): frame `ℤ₂`, `Φ′ = x² + 2x + 12` (audited: pure at `(1,1)`,
`ψ = T²+T+1` irreducible, disc a 2-adic non-square), `(u,ℓ) = (3,1)`, `K = F₄`,
`r = Z + θ`; `fS = x² + 6x + 12` has `R(fS) = r` exactly; the DEFECTIVE ambient
`g := fS·(x+1)` (degree 3) is `IsDvPure` with `R(g) = r` EXACTLY — so `HasLabel L g`
holds and `g = fS·(x+1) = g·1` are TWO labelled splits with different blocks.
Refuted thereby: (i) signed C.34's uniqueness clause (every hypothesis of the signed
pack holds); (ii) `BlockFrontier` from `BlockContext` — the planned F1.H3 target is
FALSE as stated; (iii) signed C.35 `blockFactor_spec` clause 3 (`3 ≠ 2·mult₂`).
**Normalization-robust**: both residuals share the slot-height pattern `(3,0)`, so any
twist convention hits them identically (machine-checked).  The `D′ ∣ deg` stratum is
immune (a floor-cap pigeonhole — doc §5 B1 — seals it; cert Sec 6 found no second
split there).  **Recommended repair R1**: pin the label
(`HasLabel′ := HasLabel ∧ D′ ∣ deg`) in C.34's clauses and `BlockFrontier`'s maximality
quantifier — this matches the classical LEMMA HE7-6 ("`D″ | deg f_S`",
`spec/EFF-HE7.md:1653`), whose degree pin the corpus surrogate dropped.  The eight
`_of_frontier` rows survive unchanged as conditionals.  C35b's D13 refutation was this
leak's visible tip; the new content is that signed CONCLUSIONS are false, not merely
one route blocked.

## 2. The engine (doc §2–§6), and the honest reskin answer

Four theorems, stated before proofs as charged.  **M (the root, new)**: the MIXED
product law at the dv-carrier — `dvSupp`, `dvSideMin/Max` additive and
`R(gz) = τ·R(g)·R(z)` for ALL nonzero `g, z` (τ an explicit twist unit; `= 1` on the
cite's fence).  Proof: the landed C130nv2 bank (superadditivity + endpoint assembly +
`stageHeight_mul`) plus ONE new atom — slot no-cancellation via the FGMN ψ-degree
argument: digits have level-1 residual degree `< f₁ = deg ψ`, and the order-1 GENERAL
product law (`resPoly_mul_gen`, B39a:883) fires at `isKey_X`.  **A (existence,
F1.H1)**: B.41-shaped conclusion with exact residuals; Newton iteration whose
contraction is EXACTLY `+1` in the ℓ-cleared weight per step; limit = a mechanical
B.40 reskin (B.40 is Monic-fenced, not IsKey-fenced — reusable); completeness consumed
THERE ONLY.  **B (uniqueness, F1.H2)**: Newton-free — M forces `m' = m` and
defect-vanishing pins the competitor's degree; a degree pigeonhole on `a' − a`
finishes.  Completeness-free.  **C (placement/maximality, for F1.H3)**: prime-by-prime
over `K₀[x]` with Gauss descent; squarefreeness (from `BlockContext`) consumed here
only.  §8 assembles `BlockFrontier′` from `BlockContext` through the C.33 cite pair.
**Reskin verdict**: mathlib has NO factorization Hensel (root-lifting only); the
architecture is B.39/B.40/B.41's reskinned at the dv-carrier; the solve/transport/
uniqueness ingredients are genuinely new corpus mathematics; the limit leg is landed
machinery nearly verbatim.

## 3. Deltas against the plan's F1 table

* `fgmn_dv_exact_mul` cannot power the engine (pure×pure only); the MIXED law M is
  unavoidable (solve, transport, uniqueness all need it) — and once MH.3 lands, **the
  cite becomes a provable theorem and can be RETIRED** (doc §9.2).
* Revised pricing (doc §9): H0 unchanged (35–60); H1 realistic 520–880 incl. the
  shared root MH.1–MH.3 (plan: 140–240, under-priced); H2 100–160 with a CHANGED
  mechanism (pigeonhole, completeness-free); H3 310–530 + the R1 owner gate (plan:
  70–120).  16 formalization-trivial nodes MH.0a–MH.16 with exact landed inputs.
* The perturbation node MH.6 is the SAME mechanism as the plan's F3.3
  (`refine_invariants`) — coordinate the two units.
* New first row: MH.16, the machine-checked refutation (C35b-style), must land before
  anyone formalizes against the unrepaired signatures.

## 4. Certification (examples-first, executed)

`verification/dv_hensel_cert.py`: 600 random mixed pairs — M's three laws held on all
(falsifier preregistered, did not fire); the Newton run converged in 50 steps with the
contraction attained with EQUALITY every step (the sharp law); negative controls fired
(non-coprime residuals, point-sided ambient); the §7 refutation confirmed end-to-end;
uniqueness brute search on the `D′`-divisible ambient found only the engine's factor.

## 5. OPENs (doc §9.3) — none blocks the eight rows

OPEN-1 order-1 stability M1a (routine); OPEN-2 defective-stratum EXISTENCE (true
classically; unconsumed by F1); OPEN-3 the C.22 `slotRes`/`twistExp` definitional
chases (τ-carrying statements absorb any fixed-unit surprise); OPEN-4 the other-slope
point-side lemma X1 (convexity, short).
