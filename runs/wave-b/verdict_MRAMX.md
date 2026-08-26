# Unit MRAMX verdict — completion-free ramified level-1 norm exactness (2026-08-26)

**Charge:** BLOCKED mechanism 2 of the C.27 chain (plan F2.3–F2.6): state and prove, MATH-first
and completion-free, ramified level-1 exactness at `AdjoinRoot F.key` — the B53b analogue one
level up — including the initial-determinant noncancellation as its own statement.

**Verdict: PROVED at math level, no open gaps; statement carriers elaborate in Lean; two F2.6
sub-pieces already proved Lean-core; cert battery exact on 4,443 instances with the predicted
negative control.** Fresh-context adversarial verification: see the addendum at the end.

## Deliverables (all on disk)

1. `docs/in-progress/RAMIFIED_EXACTNESS_2026-08-26.md` — the theorem (T1 exactness, T2
   scalar-membership certificate), the complete proof, the node decomposition (X0–X9 + I1)
   wired to plan rows F2.3–F2.6, and the mandated fences.
2. `verification/ramx_cert.py` + `verification/ramx_cert.log` — examples-first certificate.
3. `leanfinal/scratch/MRAMX_probe.lean` — elaboration + two proofs (`lake env lean` exit 0,
   all four footprints exactly `[propext, Classical.choice, Quot.sound]`).
4. This verdict. No git commits; nothing outside these files touched.

## The theorem (T1) and certificate (T2)

For `F : KeyFrame O π` (key `Φ′` monic irreducible, `D′ = e₁f₁`, pure of slope `h/e₁`,
residual `ψ` irreducible of degree `f₁`) and every `A₀ ≠ 0` with `deg A₀ < D′`:

    v( Norm_{AdjoinRoot Φ′ / O} (A₀ mod Φ′) ) = f₁ • stageHeight(A₀)          (T1)
    norm ≠ 0  ∧  algebraMap(norm) ∈ Ideal.span {A₀ mod Φ′}                     (T2)

T2 is exactly the input pair of the landed BW1 transfer (`normA_ne_zero_of_normB_ne_zero`,
`addVal_norm_symm`, DEC4_check.lean:42-131) — the honest contract enforced: exactness
SUPPLIES scalar membership, quotient symmetry TRANSFERS it; the refuted bare norm-nonzero
implication is not resurrected.

## The proof route (and how it generalizes B53b's completion-avoidance)

B53b avoids completions because at `h = 0` the order upstairs is an unramified DVR and the
evaluated class is `π^c`·unit. That mechanism is unavailable under ramification. The
generalization: the weight `W := stageHeight` (landed `suppVal X · h e₁`) induces a finite
filtration on the free module `A = AdjoinRoot Φ′`; `v(norm) = length_O(A/zA)` by the LANDED
generic dictionary (`B53c.length_quot_eq_addVal_norm`); the length is counted along the
filtration chain, per-grade dimension `d(γ) − d(γ−s)`, telescoping to `f₁·s`. Everything is
finite `Polynomial`/`Finset` algebra — no completion, no Hensel, no new cite.

**The one genuinely new mechanism** (the plan's F2.5 "initial-determinant noncancellation",
restated): LEMMA NC — `W((P·Q) %ₘ Φ′) = W(P) + W(Q)` for `deg P, deg Q < D′` — proved by
initial forms in `k[t,x]` (`wt t = e₁`, `wt x = h`): a cancellation would force
`in(Sq)·S(ψ) = in(P)·in(Q)`, the spread decomposition reduces this to `z·ψ = u·v` in `k[y]`,
and `ψ` irreducible (UFD `k[y]`) forces an x-degree `≥ D′` on one side — contradiction. The
plan's unclear "initial multiplication matrix / basis permutation" step is SUPERSEDED: no
matrix analysis is needed; the no-cancellation lives one level down, in one variable.

## Certificate (examples-first, run before the general argument was written up)

`ramx_cert.py`: 7 positive frames — Eisenstein ×2, (e₁,h,f₁)=(2,1,2) at p=2, (3,2,1) at p=2,
(2,1,2) at p=3, (1,1,2) at p=5, degenerate h=0 — every nonzero `A₀` over coefficient grids,
norm computed TWO independent ways (resultant AND multiplication-matrix determinant,
asserted equal): **4,443/4,443 exact**. NEGATIVE control: `Φ′ = x²+18` over `ℤ_(3)` — pure,
coprime, irreducible over the (incomplete) base, but ψ = (y−1)(y+1) REDUCIBLE — **10
violations** (first: `A₀ = x+3`, v(N)=3 > f₁s=2), exactly where the proof predicts (the UFD
step). `hresirr` is the load-bearing hypothesis, also over incomplete O.

## Lean state

`MRAMX_probe.lean` (exit 0, Lean-core footprints): T1/T2 ∀-closure carriers ELABORATE
against landed vocabulary (F2.3 de-risked); PROVED: `keyFrame_isDomain` (from `F.hirr`
alone) and `norm_mem_span_self` — the full generic Cayley–Hamilton membership half of T2
(via `LinearMap.aeval_self_charpoly` + `LinearMap.det_eq_sign_charpoly_coeff`).

Honest re-sizing for transcription: **480–780 lines** vs the plan's 285–485 — larger in
total because the graded route builds level-1 initial-form infrastructure (X2–X4), but
every node is formalization-trivial (no graded-ring typeclasses, no completion, no cite),
the heaviest single proof (X3, level-1 Gauss exactness) is a literal convolution, and X9 is
already half-banked. Node table with per-node inputs/sizing: the doc §5.

## Fences held

- Factor-label heredity and order-2 no-cancellation: NOT assumed, NOT supplied (T1/T2 are
  KeyFrame-only; general-`C` C.27 stays strictly above the C.35 frontier per C27x:77-82).
- No cite consumed; explicitly NOT `fgmn_dv_exact_mul` (C66b is the level-2 dv-polygon law
  above the frame floor — disjoint from the level-1 X-polygon statements proved here).
- `D′ ∤ deg g` endpoint caveat: consumer (F2.7) territory, untouched.
- New-statement trust boundary: T1/T2 flagged for the standing faithfulness review.

## Recommendation to the orchestrator

1. Codex adversarial verification of the doc when the primary window resets (22:26 today;
   it was 99% used at unit time — a fresh-context Claude verification was run instead, see
   addendum). Verification charge: quote-and-classify against doc §3.
2. Transcription order: X1→X2→X3→X4+I1→X5 (the new mechanism), then X6→X7→X8, X9-remainder;
   X0 carriers can land first (probe-ready).
3. F2.7 (`slot2_exact_resigned_key`) becomes reachable once X0–X9 land: its two supplies
   (T1 value + T2 certificate through the BW1 transfer) are exactly this unit's outputs.

## Addendum — fresh-context adversarial verification (completed 2026-08-26)

A fresh-context Claude verifier (quote-and-classify charge, fix-nothing; permitted reads:
the doc + C01/B34/B14 only) returned **ACCEPT — no critical errors; §3.1–§3.8 all CLEAN**.
It re-derived the §3.2–§3.4 mechanics independently, ran concrete numeric traces of the
band count on the (2,1,1) and (2,1,2) frames (band dims sum to v(norm) in each), confirmed
acyclicity, completion-freeness (no hidden completeness/locality of A anywhere), every
degenerate case (h=0, e₁=1, f₁=1, constant A₀, γ=0, γ<s, s=0, unit z), and traced the
negative control to failure exactly and only at the UFD step. Three findings, all
justification-gap class:

1. **I1 (resPoly ↔ ψ identification)** — acknowledged in-document; it is the single entry
   point of `Irreducible ψ`, so the Lean transcription of I1 is the one place T1/NC's
   soundness must be re-checked against B16/B20/B28/B29 (node I1 already says this).
2. **Landed-cite form** — the B53c dictionary's exact hypotheses are asserted, not
   displayed (mathematically sound; standard trust-boundary form risk).
3. **Instance-count typo** — headline said 4,433; table sums to 4,443. FIXED in both the
   doc and this verdict (per-battery counts and results unchanged).

Codex re-verification when the primary window resets (22:26) remains recommended as the
decorrelated second pass, prioritized per the repo's verification policy.
