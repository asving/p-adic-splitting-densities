# Verdict — MHFIX: the Hensel engine's critical break repaired at the root

**Date:** 2026-08-27
**Unit:** MHFIX (Fable math tier)
**Charge:** repair MHDISP finding 3 — M1(2)'s bare `slotRes` multiplicativity is FALSE
(machine-refuted at the `(2,2,3)/F₉` mirror); deliver the CORRECTED Theorem M with the
generic stage-letter carry pinned.

## The carry formula (the deliverable's core)

The generic carry is the **twist-exponent cocycle defect**

> `δ(k,k′) := twistExp(k+k′) − twistExp(k) − twistExp(k′) ∈ {0,1}`, with
> `e₁·δ(k,k′) = slotIdx(k) + slotIdx(k′) − slotIdx(k+k′)` (the slot-index carry bit),

and the corrected root **M1′** (doc §3.1′): for digits `a, b` at height floors
`ka ≤ w(a)`, `kb ≤ w(b)`, with `E := (a·b) %ₘ key`:

1. `twistRead (ka+kb) E = twistRead ka a · twistRead kb b`  (**τ = 1** — C.22's inverse
   twist trivializes the carry cocycle exactly);
2. `slotRes (ka+kb) E = η^{δ(ka,kb)} · slotRes ka a · slotRes kb b`;
3. at exact finite heights both right reads are NONZERO, hence `w(E) = ka+kb` — old
   M1(1), recovered WITHOUT the M1a stability step (OPEN-1 retired from the critical
   path).

Consequently Theorem M clause 3 is restated as `R(gz) = R(g)·R(z)` — **τ = 1
identically** (dvResPoly's reads are already inverse-twisted); the ∃-τ form is the
weakening by `τ := 1`.  Refutation-mirror check: δ(3,3) = 3−1−1 = 1 at `(e₁,h) = (2,3)`
(the η the probe measured); the landed S2 law `s2_graded_mul_twisted` (carry
`X^{(β%2)(β′%2)}`) is exactly this δ at `e₁ = 2` — an independently landed instance.

## Evidence ledger (each item's honest grade)

| artifact | status |
|---|---|
| `verification/mhfix_cert.py` (NEW) | **473,961 checks, 0 FAILS** — TW-δ on every coprime `(e₁ ≤ 8, h ≤ 12)`, `k,k′ ≤ 60`; M1′ (all 3 clauses) at 7 audited frames (`e₁ ∈ {1,2,3,4}`, `f₁ ∈ {1,2,3}`, carry live at every `e₁>1` frame); full `R(gz) = R(g)R(z)`, τ = 1, + `W`/side additivity on 250 mixed pairs at the live-carry `(3,2,2,3)` frame, strict floor `u/ℓ = 25/2` — the twist-nontrivial genre the old `e₁=1` cert never exercised |
| `leanfinal/scratch/MHFIX_probe.lean` (NEW) | `lake env lean` **exit 0, zero `sorry`, zero `axiom`**; **PROVED generic**: `twistExp_add_carry` (TW-δ) and `twistRead_mul_of_slotRes_carry` (carry ⟹ twist form), footprints exactly `[propext, Classical.choice, Quot.sound]`; 4 corrected statement shapes elaborate; `existsUnit_of_tauOne` proved; executable δ=1 AND δ=0 carry rows at the F₉ gate; axiom-free numeral δ-grids at `(2,3),(3,2),(5,3)` |
| doc §3.1′ (M1′ + full proof) | **MATH-PROVED**: associated-graded model `gr_w(O[x]) ≅ k_r[Π,X̄]` + one reading homomorphism `ρ̃(Π) = η^{−i₀}`, `ρ̃(X̄) = η^{(1−i₀h)/e₁}` that restricts to `η^{−q(k)}·ρ_k` per grade and kills the key's symbol via `ψ(η) = 0` (B.29 convention verified against source).  Consumes only landed Lean facts + standard commutative algebra.  NOT Lean-transcribed |
| Codex adversarial passes (quote-and-classify, fix-nothing, fresh context) | **two consecutive CLEAN verdicts.**  Pass 1: no offending passages.  Pass 2 (work-showing charge): re-derived the exponent identity, the window enumeration, the f₁ = 2 key-symbol list, and Step 6's three ℕ∞ cases; ATTACK 1 (below-the-line coefficient) refuted — `w(A) ≥ k` excludes it coefficientwise; ATTACK 2 (reversed ψ-indexing) confirmed the stated B.29 orientation is ESSENTIAL (`Σψ_j η^j = ψ(η)`; the reversal gives `η^{f₁}ψ′(η⁻¹)`, not forced to vanish) and that the proof uses exactly the source convention; no circular use of the refuted M1(2) |
| doc amendment | 18 `[MHFIX 2026-08-27]` markers: corrected §2 M(3), new §3.1′, §3.2/§3.3 assembly re-grades, §9 node gate/rows/ordering/OPEN inventory, §10.4 |

## Honest status of M and MH.1

* **M1′ / MH.1:** OPEN (transcription-ready) — no longer BLOCKED-CRITICAL.  Statement
  pinned (probe shapes), math proof complete, arithmetic core Lean-proved, S2 twin
  landed as the proof pattern (`s2GradedRes_mul_of_exact` coefficientwise route, no `gr`
  construction needed in Lean).  Sizing 250–450 lines.
* **Theorem M:** clauses 1 + sideMin-additivity and clause 3 are MATH-PROVED conditional
  ONLY on MH.1's transcription (their assembly inputs — `dev_mul_endpoint_split`,
  `dev_mul_conv_split`, `twistRead_add_of_le`/`_finsetSum_of_le`/`_eq_zero_of_lt`,
  `lt_line_dev_term`, `stageHeight_add_eq_left_of_lt` — are all landed and generic).
  `dvSideMax`-additivity is PROOF-OUTLINE grade (node MH.2).  The generic `hsurv` supply
  is discharged by M1′(3) + the landed strict floor split.
* **MHDISP's record is untouched:** M1(2) as originally stated remains FALSE and
  withdrawn; M1′ is its correction.  The ∃-τ speculation is settled as τ = 1.
* **`fgmn_dv_exact_mul`:** once MH.1–MH.3 land, the cite becomes a theorem with unit 1
  (§9.2 unchanged, now with the unit pinned).

## May the MH fleet fire?

**NOT YET — the fence stands, but gate 1 of MHDISP's three is now designed-and-proved.**

* **Immediately schedulable:** the MH.1 Lean transcription (+ promotion of the probe's
  TW-δ/bridge theorems into a ChapC module, the MH.0c remainder).  Everything it needs
  is named in the doc's MH.1 row.
* **Still gating the fleet:** MH.8's bounded-window `W`/Gauss conversions and X1
  (OPEN-4) — untouched by this unit — plus the actual LANDING of MH.1.  Per MHDISP:
  gates must be green in Lean, not merely math-proved.  MH.2–MH.9/MH.11–MH.15 stay
  fenced until then.

## Deliverables

* `docs/in-progress/HENSEL_ENGINE_2026-08-26.md` — amended in place ([MHFIX 2026-08-27])
* `verification/mhfix_cert.py` — NEW, GREEN (473,961 checks / 0 fails)
* `leanfinal/scratch/MHFIX_probe.lean` — NEW, GREEN (exit 0, Lean-core footprints)
* `runs/wave-b/verdict_MHFIX.md` — this file

No commit was made.
