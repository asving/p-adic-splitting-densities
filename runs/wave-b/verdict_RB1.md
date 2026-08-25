# Verdict — unit RB1 (Chapter C, READY batch 1 from `verdict_CCUR.md`)

Deliverable: `leanfinal/Uniformity/ChapC/C150rb1.lean` (only new file written by this unit).

Batch-1 assignment (`runs/wave-b/verdict_CCUR.md`, "Ranked READY batches" §, batch 1):
`entry_band_faithful` (C.75), `shadow_attained_of_certificate` (C.74 family), `blockDeg_eq`
(C.64), `towerLocus_fibration` (C.53). Three landed; the fourth is genuinely BLOCKED, not a
wiring nit — see below.

## `entry_band_faithful` (C.75) — **LANDED**

Wired as a corollary of `Uniformity.Density.Tower.C131y.shadow_faithful_band` (the general
C.72 faithful-band theorem) plus `TowerDatum.one_le_margin` (C.71). The signed hypothesis
`hm : m ≤ (μ₂ - j) * T.E₂` is non-strict and arithmetically weaker than `shadow_faithful_band`'s
strict `m < T.theta μ₂ j`; since `T.theta μ₂ j = (μ₂ - j) * T.E₂ + T.margin` and
`1 ≤ T.margin` (`one_le_margin`), `m ≤ (μ₂-j)*T.E₂ < T.theta μ₂ j` closes the gap
(`simp only [TowerDatum.theta]; omega`, then apply `shadow_faithful_band`). Signature verified
byte-identical to `leanspec/Leanspec/ChapC.lean:3497-3505`.

## `shadow_attained_of_certificate` (C.74 family) — **LANDED**

`TouchCert T hπ μ₂ j` (`C74.lean`, def only, `Uniformity.Density.Tower.TouchCert`) unfolds
definitionally to a `dv2Hgt` equation on `shadowDev T (Φ₂^μ₂) j - dev Φ₂ (Φ₂^μ₂) j`.
`dev_pow_self` (C.52, `Uniformity.Density.Tower.dev_pow_self`) gives the Kronecker-delta digit
law `dev φ (φ^μ) j = if j = μ then 1 else 0` for any monic `φ` of positive degree; instantiated
at `φ = composedKey T` (positivity of degree via `composedKey_natDegree_D₂`, C.53b, plus
`F.he₁`/`F.hf₁`/`T.he₂`/`T.hf₂`) and `j < μ₂` this gives the first conjunct
`dev (composedKey T) (Φ₂^μ₂) j = 0` directly; substituting into the certificate and
`sub_zero`-ing gives the second. Signature verified byte-identical to
`leanspec/Leanspec/ChapC.lean:3466-3470`.

## `blockDeg_eq` (C.64) — **LANDED**

A direct wrap of the already-proved `Uniformity.Density.Tower.C64.blockDeg_eq_resigned`
(`C64.lean`, amendment A-C.10): its hypothesis/conclusion list is byte-identical to the
re-signed leanspec form (the naked form, without the `hlab`/`hdvd` riders, was machine-refuted
in the same file, `blockDegEq_false`). No adapter needed beyond the rename. Signature verified
byte-identical to `leanspec/Leanspec/ChapC.lean:2291-2296`.

## `towerLocus_fibration` (C.53) — **BLOCKED (genuine gap, not a wiring nit)**

The verdict's batch-1 row 4 asked this unit to "verify the hypothesis list matches the signed
axiom exactly and wrap/rename" `towerLocus_fibration_of_leg1` (`C53b.lean:733`). It does not
match, and the mismatch is load-bearing:

* The leanspec-signed `towerLocus_fibration` (`ChapC.lean:2048-2055`) is **unconditional**:
  its full hypothesis list is `(T, hπ, hh, [IsAdicComplete …], [Finite (ResidueField O)],
  μ₂ N, hμ₂)`.
* `towerLocus_fibration_of_leg1` proves the identical CONCLUSION shape, but only under one
  additional explicit hypothesis, `h1 : TowerBudgetIff T μ₂` — leg 1 of C.53's two-leg
  decomposition, i.e. C.52's signed `towerLocus_iff_budget` (the FULL iff, both directions,
  for every monic `f` of degree `μ₂D₂`).
* `TowerBudgetIff` is an iff. Only the `⟸` half is landed
  (`mem_towerLocus_of_budget`, C.131ae, `runs/wave-b/verdict_C131ae.md`). The `⟹` half
  (`budget_of_mem_towerLocus`, C.131af′, C.52 Step 3, "the reverse correspondence") is
  confirmed **not landed anywhere in the corpus**: `rg -n "budget_of_mem_towerLocus"
  leanfinal/Uniformity/` returns only prose references (a proof-spine comment in `C52.lean`,
  and `C131ae.lean`'s own docstring naming it explicitly as unbuilt future work, with a
  precise description of the missing digit-correspondence mechanism). The untracked scratch
  file `leanfinal/scratch/DEC2_check.lean` (another agent's in-flight work, not touched by
  this unit) contains an "elaboration only — no proof, no `sorry`, no axiom" stub for exactly
  this reverse direction, which confirms rather than contradicts that it is still open.

Consequently `h1 : TowerBudgetIff T μ₂` cannot be constructed for a general `TowerDatum T`
today — supplying it is the genuine unattempted proof work named at C.52/C.53's own blocked
records (`C52_BLOCKED_2026-08-18.md` obstruction 4, `C53_LEG2_REFUTED_2026-08-20.md`), not a
20-30 minute wrap. Landing a declaration named `towerLocus_fibration` that carries `h1` as an
extra hypothesis would silently narrow the unconditional signed statement — a statement change
this campaign's honesty discipline does not permit without sign-off, and in any case would not
be the theorem the axiom claims. No declaration under the name `towerLocus_fibration` is added.
This is the same disposition the corpus already gives this exact gap under a different name
(`towerLocus_fibration_of_leg1` itself is the honest, hypothesis-carrying repair; nothing new
to add on top of it).

## Verification

```sh
cd leanfinal
lake env lean Uniformity/ChapC/C150rb1.lean
# 0 errors; 1 harmless linter warning (`hh` unused in shadow_attained_of_certificate — kept
# for byte-fidelity with the signed binder list); exit 0.
```

`#print axioms` footprint for all three landed declarations (AxCheck footer, also run inline
by `lake env lean`):

```
Uniformity.Density.Tower.entry_band_faithful               : [propext, Classical.choice, Quot.sound]
Uniformity.Density.Tower.shadow_attained_of_certificate     : [propext, Classical.choice, Quot.sound]
Uniformity.Density.Tower.blockDeg_eq                        : [propext, Classical.choice, Quot.sound]
```

Lean core only for all three — no cite (`fgmn_dv_exact_mul`/C66b or otherwise) is inherited by
any of them; none of the three routes through `composedKey_pow_mem_towerLocus` or any other
cite-carrying declaration.

No file other than `leanfinal/Uniformity/ChapC/C150rb1.lean` and this verdict was created or
modified by this unit. `leanspec/`, roll-ups, and sibling units' files
(`C150rb2.lean`, `C150rb3.lean`, `E57i*.lean`, `C27.lean`) were read-only referenced, never
edited.
