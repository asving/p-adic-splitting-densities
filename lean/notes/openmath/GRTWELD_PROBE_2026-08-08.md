# GRT WELD PROBE — the W-2 lift-junction falsification run (blueprint T1/T2), sealed prereg + verdict

**Unit:** GRT WELD PROBE (the weld campaign's mandated FIRST unit, per
`docs/in-progress/GRT_WELD_BLUEPRINT_2026-08-08.md` §3.2 "The concrete
falsification test" and §6 recommended order item (1)). **Genre: sealed
machine probe** — instance evidence only; nothing here is a proof step; no
`.lean` touched; no gate fired; no acceptance arc opened. **Author:** Fable
probe unit, campaign date 2026-08-08 (wallclock 2026-08-04).

## The junction under test (verbatim from the blueprint)

> **W-2** | THE LIFT JUNCTION: the classifier's canonical key polynomial at
> each level equals the harness canonical ε-corrected lift Φ_{m+1} — or,
> failing byte-equality, an explicit unit-covariance law transporting all
> value-layer statements across GMN-admissible representatives | J-A |
> **L — HIGHEST RISK** |

and its falsifier (blueprint §3.2): **(T1)** lift comparison — committed
`build_Phi2/3`-pattern harness lifts vs a **fresh from-print GMN Def-2.12
transcription** (NOT imported from `grb_order2_check.py`), on roster towers +
wild quartic-oracle shapes, PARI ground truth per ℤ_p row, unit ratios
recorded; **(T2)** cocycle transport — c_T computed on the CLASSIFIER lifts
over in-window anchor pairs vs the [ILN]† closed form z̄^δ·∏ z_j^{D_j} at the
same (γ, γ′); prediction under W-2-as-stated: 0 violations; any RED = W-2
falsified as byte-equality, and the T1 unit-ratio table then decides
covariance-law vs broken-transfer.

## The runner (sealed at commit 1)

`verification/openmath/grt_weld_probe.py` — deterministic, exact arithmetic,
no randomness. Full preregistration (families F0/F1/F2/F2s/F2b/F3/F3b/F4/QO +
mutation controls MG/MH with designated rows, roster, convention pins
(P-ell)/(P-lift)/(P-root)/(P-index), and the honest build-phase smoke
disclosure) lives in the runner's docstring — that docstring is part of this
seal. Compressed here:

- **Harness leg (committed, verbatim):** `iterlawn_pe_reimpl.Tower` — the
  sealed ITERLAWN-PE engine (K7 baseline 940/0); its `_build_lift(m)` IS the
  canonical ε-corrected lift; its `check_pair`/`gamma_checks` ARE the
  value/cocycle battery (K5 = L6-(n), K6 = W-MULT, K7 = THE LAW, K12 =
  π-shift/ρ-monodromy).
- **Classifier leg (fresh from print, decorrelated):** GMN
  `docs/references/HigherNewton.tex` — Prop. `construct` (tex 1166–1258) +
  Thm. `phir` (tex 1260–1283) + the representative Definition (tex 1285; the
  project's "Thm 2.11/Def 2.12" cite per `docs/GMN_citations.md`), plus the
  fresh residual evaluator (Def `t(i)`, Def `rescoeff`, Def `defresidual`,
  order-one base case, Prop `propertiesv` items 3/4, eq `vrphir`). Nothing
  imported from `grb_order2_check.py`.
- **External anchors:** PARI `factorpadic` + `nfinit`/`idealprimedec` per
  ℤ_p row (both legs' top lifts: irreducible + exact (e,f)); five concrete
  wild shapes (x⁴−2, x⁴+4x+4, x⁴+2x²+2, x⁴+12 over ℚ₂; x³−3 over ℚ₃) whose
  types the classifier leg extracts FRESH from f and PARI cross-decides.
- **Roster:** 13 towers (2/3/4 reads; ℤ₂/ℤ₃/F₂[[t]]/F₃[[t]]; wild p | e_j on
  8 rows; d0 = 2 rows; g ≥ 2 residue-growth rows; e_i = 1 flat rows; the
  committed ITERLAWN I4A/I4B/I4C verbatim) + the 5 shapes.

## SEALED PREDICTIONS (commit 1; battery not yet run)

| family | sealed identity | predicted |
|---|---|---|
| F0 | φ₂^cls == Φ₁^har byte-equal (untwisted base junction) | 0 violations |
| F1 | **W-2-as-stated**: φ_r^cls == Φ_{r−1}^har byte-equal, all r ≥ 3 | **RED expected** (smoke-informed), with z-monomial slot-ratio table per failure |
| F2 | ADM-ORBIT: every harness lift is a GMN Def-2.12 representative up to the print's own ℓ-convention freedom (∃ units ξ, w: R(y) = w·ψ(ξy)) | 0 violations |
| F2s | ADM-STRICT (pinned ℓ ∈ [0,e)) | recorded only, not RED-scored |
| F2b | cls self-check: R(φ^cls) == c·ψ exactly (Thm-phir's own conclusion) | 0 violations |
| F3 | **cocycle transport**: K5/K6/K7/K12 (+K1–K4/K13) on ClsTower (committed engine running ON classifier lifts) | **0 violations** |
| F3b | baseline control (same battery, harness lifts) | 0 violations |
| F4 | PARI: both top lifts irreducible, unique prime, (e,f) = (∏e_j, d0∏g_j), ℤ_p rows | 0 mismatches |
| QO | fresh extraction verdict == PARI full type on the 5 shapes | 0 mismatches |
| MG | teeth: garbled cls leg (c₁ := 1, texp := 0) caught by the strict self-check on T2C/T3C/T3A (visible-twist rows) | ≥ 1 failure per designated row |
| MH | teeth: P-reading (refuted Def-3.15 extraction artifact) harness towers caught by the SAME cocycle battery on T2A/T2B/T2D | ≥ 1 violation per designated row |

**Honest smoke disclosure (pre-seal, part of the record):** build-phase
reduced runs showed F0 green; F1 byte-INEQUALITY at top junctions of
twist-visible rows with systematic z-monomial slot ratios (T2A r=3 slot-0
ratio z₁²; T3B r=4 ratio z₁; interior junctions byte-equal on smoked rows);
F2-orbit green; F2s strict failures exactly at the F1 rows (the harness lift
represents the ψ-**twisted** type under the pinned ℓ; the twist is inside the
print's ℓ-freedom orbit R(y) ↦ unit·R(z^{kh}y)); F2b/F4/QO green; **F3 = 0
violations on every smoked ClsTower**; MG/MH visibility pre-verified (MG
teeth exist only on rows with nonzero true total twist — on low-h f_top = 1
rows the two dropped twists cancel exactly, texp + cexp = ⌊ℓh/e⌋ = 0 — hence
the designation). The sealed F1 identity remains byte-equality (the
blueprint's W-2-as-stated), NOT sanitized to the smoke.

**Derived structure worth recording at seal time (candidate law, informal):**
at an f_top = 1 top slot the GMN construction's total residue twist exponent
is ⌊ℓ_{r−2}·u_j/e_{r−2}⌋ + (−ℓ_{r−2}·v_{r−1}(φ_{r−1})/e_{r−2})·e_{r−1}f_{r−1}
while the harness ε-correction exponent is l·u − l′·s at the same weight —
different integers whose difference is the observed z-monomial; equality in
the residue field holds iff ord(z) divides the difference. This is exactly
the "explicit unit-covariance law" branch of W-2; the battery decides its
scope.

## VERDICT (commit 2, from the artifacts)

**Artifacts:** `verification/openmath/grt_weld_probe_output.txt`,
`verification/openmath/grt_weld_probe_results.json` (deterministic; 1,391
samples; 1.3 s). Observed vs sealed:

| family | sealed | observed | verdict |
|---|---|---|---|
| F0 CHAIN-BASE | 0 | **0/21** | GREEN |
| F1 LIFT-BYTE (W-2-as-stated) | RED expected | **18 byte-unequal of 30 r ≥ 3 junctions** | RED — **byte-equality FALSIFIED** |
| F2 ADM-ORBIT | 0 | **6/51** | **RED — but with an exact confinement law (below)** |
| F2s ADM-STRICT (recorded) | recorded | 18 (exactly the F1 rows) | recorded |
| F2b CLS-SELF | 0 | **0/51** | GREEN (fresh transcription internally exact) |
| F3 COCYCLE TRANSPORT | 0 | **96/576** (K6: 48, K7: 48; K5/K12: 0) | **RED — confined (below)** |
| F3b baseline control | 0 | **0/576** | GREEN |
| F4 PARI (both legs, 9 ℤ_p towers) | 0 | **0/24** | GREEN |
| QO shapes | 0 | **0/5** (x⁴−2→(4,1), x⁴+4x+4→(4,1) 2-level wild, x⁴+2x²+2→(4,1), x⁴+12→(2,2), x³−3→(3,1); extraction == PARI on all) | GREEN |
| MG teeth | ≥1 per row | 1/2/1 on T2C/T3C/T3A | GREEN |
| MH teeth | ≥1 per row | 12/15/10 on T2A/T2B/T2D | GREEN |

### The failure shape, precisely (the directive's revision-scope warning)

**(1) Byte-equality is FALSIFIED — minimal witness.** Tower T2A = ℤ₂,
d0 = 1, reads (2,1,2),(2,1,1) (wild, K₁ = F₄): harness Φ₂ =
(16,16,16,8,12,0,4,0,1) vs GMN φ₃ = (16,0,16,8,12,0,4,0,1) (coefficient
tuples low→high): the single slot-0 development coefficient differs by the
unit **z₁²** (hand-account, recorded at seal: harness ε-exponent l·u−l′·s = 4
vs GMN ⌊ℓγ₂/e⌋ − ℓf₁h₁e₂ = 0 at the same weight; 4 ≢ 0 mod ord(z₁) = 3).

**(2) At the FIRST diverged junction the discrepancy is ALWAYS the residual-
coordinate character — never structural.** All 18 F1 rows: pure z-monomial
slot ratios, zero weight/support mismatches; multi-slot case I4C r=3 shows
ratios (z₁, z₁², 1 = z₁³) at slots j = 0,1,2 — exactly geometric ξ^j with
ξ = z₁. Correspondingly F2-ORBIT is GREEN at **every** top junction and
**every first divergence** (45/51): the harness lift is always a GMN
Def-2.12 representative of the ξ-twisted residual class, inside the print's
own unpinned-ℓ convention orbit. This is W-2's covariance branch, machine-
confirmed at the junction level, with (ξ, w) recorded per level in the JSON.

**(3) ABOVE an interior divergence the naive-bytes continuation is not a
covariance matter at all — the chains split as TYPE chains.** The 6 F2
failures and all 96 F3 failures sit exclusively at junctions strictly above
an interior (non-top) diverged junction: rows T3A/T3C/T3D/T3E/I4C. Mechanism
machine-confirmed on all five rows: v₃(φ₃^cls − Φ₂^har) = v₃(key) **exactly**
— the two level-3 keys are MacLane-INEQUIVALENT (difference at key weight,
not above), so they induce different level-4 valuations; the r ≥ 4
comparisons then show WEIGHT/SUPPORT mismatches (no longer unit ratios), the
harness lift fails vok/onesided on the GMN chain, and the ClsTower (GMN
lifts injected under the harness ψ-bytes) breaks exactly K6 W-MULT + K7 THE
LAW (48 + 48; K5 anchor values and K12 monodromy stay green) on T3A/T3C/T3D/
I4C. The five F3-informative rows split 4 RED / 1 GREEN (T3E, the flat-
middle e₁ = 1 row, transports despite interior divergence — recorded, not
explained). NOTE the trivial/non-trivial split honestly: on the 11 rows
whose interior lifts are byte-equal, F3 = 0 is a consistency statement
(anchors never consume the top lift); the informative F3 evidence is the
confinement to — and the near-totality of failure on — the interior-diverged
rows.

**(4) Root cause of (3) — a KEYING clause the weld statement is missing.**
After the first twisted junction the same ψ-bytes denote DIFFERENT residue
classes in the two chains (the classifier's z and the harness's z differ by
the character ξ). The classifier chain continued on raw ψ-bytes is a valid
GMN type chain (F2b = 0, PARI green) — but it is a *conjugate* type, not the
harness's type. So W-2's quantification "the classifier's canonical key
polynomial at each level [of the same type t]" is ill-posed across the seam
without a **ψ-transport clause**: the level-(m+1) residual ψ must be carried
through the recorded level-m covariance (ξ, w) before the next classifier
lift is built.

### LAW-KEYED ruling for the W-2 unit (the blueprint's design decision)

- **Byte-equality branch: DEAD** (18 witnesses; systematic).
- **Covariance branch: ALIVE and now SPECIFIED** — per-junction the law is
  the residual-coordinate character (R(y) ↦ w·R(ξy), ξ a z-monomial, =
  the print's own ℓ-convention freedom), machine-green at all 45 first-
  divergence/top junctions; but the covariance is NOT a per-level ornament:
  W-2 must be drafted as **admissible-representative + unit-covariance +
  ψ-TRANSPORT THREADED THROUGH THE TOWER** (the conjugation must be applied
  to every deeper residual before the next lift). Without the transport
  clause, the transfer genuinely breaks at depth ≥ 2 past a twist (the (3)
  witnesses), and with the chains naively identified the [ILN]† closed form
  does not transport (K6/K7 RED). No accepted corpus text is touched: the
  corpus is proved on harness lifts (F3b = 0 re-confirms), and the harness
  lifts are GMN-admissible (F2-orbit at their own junctions).
- **First live weld evidence:** on every tower where the type-keying is
  coherent (byte-equal interiors — 11 rows incl. both wild 4-read committed
  instances), the committed value/cocycle battery holds verbatim with the
  classifier-side objects in play, 480/480 pair-samples clean; and the
  fresh print evaluator + PARI certify every harness lift as a real
  classifier key polynomial (F2-orbit + F4: 24/24 (e,f)-certificates,
  wild rows included).

**Follow-up unit implied (not executed here):** the transported-ψ probe —
rebuild the classifier chain with ψ's conjugated through the recorded (ξ, w)
at each diverged junction and re-run F1/F2/F3; prediction (unsealed,
informal): byte-comparison returns to single-junction z-monomial ratios and
F3 returns to 0. That unit, plus stating the ψ-transport clause as
mathematics, is the corrected drafting scope for W-2 (still priced L).

**Fences:** instance evidence only (16 towers incl. 3 committed ITERLAWN
instances, 5 concrete shapes, orders ≤ 4, residue fields ≤ F₉); the ℓ-orbit
reading of Def 2.12 is a convention analysis, review-owed; F_p[[t]] rows
have no PARI leg (displayed deferral); T3E's clean transport is an
unexplained observation; nothing here is a proof step; BLOCKED-ON-CARRIER-
TIE and the P0 application gate stand.

— GRT WELD PROBE unit, campaign date 2026-08-08.
