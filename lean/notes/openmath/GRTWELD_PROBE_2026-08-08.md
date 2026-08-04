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

**PENDING — sealed before the battery.** Commit 1 seals this note (prereg +
smoke disclosure above) and the runner; the battery then runs once; commit 2
replaces this section with the LAW-KEYED verdict read off
`verification/openmath/grt_weld_probe_output.txt` and
`verification/openmath/grt_weld_probe_results.json`, with counts per family
against the sealed table, the minimal F1 witness (if RED), and the scope
ruling for the W-2 unit (byte-equality vs covariance-law drafting).

— GRT WELD PROBE unit, campaign date 2026-08-08.
