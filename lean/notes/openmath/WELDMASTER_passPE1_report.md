# WELDMASTER pass PE1 — hostile verification report

**Target:** `lean/notes/openmath/WELDMASTER_2026-08-08.md` (WELD MASTER-TRANSPORT,
LEDGER-Λ-genre consolidation; seal b375f42 / verdict 0baeb3b; runner
`verification/openmath/weldmaster_checks.py`).
**Verifier:** hostile pass PE1, fresh context, wallclock 2026-08-06. Nothing fixed;
offending passages quoted and classified per the standing charge (CRITICAL ERROR =
breaks the chain; JUSTIFICATION GAP = assume and continue). Fences and boxes read
as part of every statement. Context read at HEAD: the four junction notes
(GRTW2/GRTJA post-r1/GRTJB post-r4/GRTJC post-r2), ITERLAWN ([ILN]†),
WELD_SYNTHESIS f71cd68, LEDGERLAMBDA, the [ILN]/weld tail of
BRIDGE_ADJUDICATIONS, and the two engine files at their pinned md5s.

## VERDICT LINE

**0 CRITICAL ERRORS · 5 JUSTIFICATION GAPS (F-1..F-5) · 3 minor defects
(F-6..F-8). NOT CLEAN — the acceptance counter stays 0/2.** The two new
theorem-shaped items (WM-COB, WM-RHO) re-derive SOUND on exactly the claimed
footprints; the machine leg reproduces bit-identically and the two-commit seal
verifies. The findings are all citation-precision / conditionality-carriage /
battery-billing defects — the consolidation genre's own failure mode, none
touching a displayed identity.

## MACHINE LEG (mandatory; re-run 2026-08-06)

* `python3 weldmaster_checks.py` → **exit 0**, `VERDICT: ALL GREEN`, elapsed 0.6 s.
  All 10 family counts match the note's verdict block exactly: WM-PIN 2/0 ·
  WM-EPS 615/0 · WM-COB-I 1,885/0 · WM-COB-OFFW 513/0 · WM-COB-F 1,885/0 ·
  WM-COB-C 897/0 · WM-RHO 87/0 · WM-FENCE-XI 349/0 · WM-FENCE-EQ 171/0 ·
  WM-SHEAR 804/0 (Σ = 7,208 samples, 0 violations). Teeth: SIGN 374 ·
  DELTA 861 · SHEAR 514 · XI 47 — all fired. Census identical (fence rows
  22/9/26; κ hist {0:292, 1:87, 2:18, 3:37, 4:6, 5:9, 6:2, 7:6}; 29 towers;
  897 pairs scored; 804/342 hulls).
* The re-run's summary block is **byte-identical** to the committed
  `weldmaster_checks_output.txt` at 0baeb3b and at HEAD (diff shows only the
  stdout-only per-tower lines, which the artifact omits by design).
* **Seal verified:** b375f42 is an ancestor of 0baeb3b; at b375f42 the note ends
  S5 with the placeholder `**[VERDICT — appended at commit 2 from the committed
  artifacts.]**` and contains zero result strings; the 0baeb3b diff touches only
  the verdict block (+25/−1) and adds the two artifacts; runner md5
  `6b406f81c250d25f615f715fa9eff474` identical at b375f42, 0baeb3b, and HEAD.
* **Independent confirmations beyond the charge:** (a) the verdict claim "the
  dint_ok gate never excluded a pair" is CONFIRMED arithmetically — Σ over the
  29 towers of reps²·(NR−1) = 1,885 = the observed WM-COB-I count, and
  Σ min(3,reps)²·(NR−1) = 513 = the observed OFFW count, so zero pairs were
  gated; (b) roster claims verified against `grt_jc_probe.ROSTER` (29 rows;
  p ∈ {2,3,5}; d₀ ≤ 3; NR ≤ 4; wild p = 5 legs C2F/C3G/C4H; g = 2 rows;
  eq-char rows C2E/C3D/C3J/C4G/I4C; I4A/I4B/I4C); (c) the smoke subset in the
  docstring matches the note ({C2A, C2I, C3A, I4B}).

## WHAT SURVIVED HOSTILE RE-DERIVATION (stated so the findings are scoped)

* **WM-COB(i) re-derived sound on exactly the claimed footprint.** [ILN]† S2 at
  HEAD says verbatim "Throughout S2, γ, γ′ ∈ ℤ are arbitrary"; SHIFT-(n)
  (β_j″ = B_j + S_j) and D_j-INT are graded "PROVED, generic, unconditional"
  in its clause table. The abscissa tie (a) is definitional in both [ILN] S0.2
  and the engine (`split` computes s_j = ℓ_{j−1}β_j mod e_{j−1} via `eq12`).
  The three-line computation checks: ℓ(β+β′−β″) = −ℓS_j by SHIFT, the s-sum is
  the defect by (a), quotient = −D_j by the S0.3 definition; integrality of
  every t_j is Bézout. (ii) is z_j raised to (i); (iii) telescopes and carries
  the scored-stratum fence at the claim, in WM4's status cell, and at both
  consumption sites (M3, WM-CLASS). The Remark's footprint-ordering claim
  ((i)–(ii) strictly smaller than the value law's) is correct.
* **WM-RHO re-derived sound.** The shift structure (γ ↦ γ+E fixes every s_j and
  shifts β_j by E_j) matches [ILN]† S2's ℤ/E-descent lemma line for line;
  t_j(β_j+E_j) = t_j(β_j) + ℓ_{j−1}E_{j−1} is exact; ρ_T as displayed.
* **WM-CLASS algebra re-derived** (Ẽ := E∘σ, σν+σν′ = σ(ν+ν′)+κE, WM-RHO
  iterated gives ∂Ẽ = ∂E·ρ_T^κ, substitution into WM-COB(iii) gives the
  display). Honestly labeled DISPLAY (review-owed) in S2.2 AND in WM6's status
  cell; nothing in the note or its ledger entry consumes it at proof grade.
* **The citation face table checked cell-by-cell against HEAD:** (M0) JB-DEV(i)
  row 1 + JA-PIN clauses 1–7 (lift clause = W-2, as JA states) + W2-C1, with
  rows 1–2 carried; (M1) JA-VAL as stated in JA §3.1, JB-AFF/JB-VTX with the
  phrase "THE SHEARED FRAME IS THE PRINT'S OWN NEXT-LEVEL BOOKKEEPING" verbatim
  from JB-VTX(a), perimeter `P<q` 0 ≤ q ≤ qcap + u ≥ 0 rider + (d4) NO-LEG all
  carried — **the r4 leaves-only re-scope of JB's line laws does NOT touch any
  cited face** (M1 consumes JA-VAL and JB-VTX, not JB-TREE(iii)'s λ_E/line
  functional, and the note's only line-face mention is the LED-Λ attempt-grade
  bookkeeping sentence); (M2) JA-EPS/JA-RES ("unconditional at m = 2" verbatim
  from JA §3.4) + W2-C2/(HR-REC) with the per-digit-proviso/(R-coll)/(C-coll)/
  W2-BOX-1 riders; (M3) W-6..W-9 at JC's r2 grades with the two-tier
  (DMULT-w)-CITED/(DMULT-s)-MEASURED split carried correctly, JC-LOC quoted
  faithfully, JC-BOX-2/4/8 real and apt; (M4) the §3.4 closed form,
  W2-C3(i)–(iii), the §4.3 convention fence, and W2-OPEN-1 displayed OPEN.
  [JC]†'s separately-listed "W-1" dependency was checked and **rides inside
  [JA]†** (GRTJC line 264: "W-1 (J-A), ATTEMPT GRADE"; GRTJA's header covers
  blueprint rows W-0/W-1/W-4) — carried by the stack's J-A entry, not omitted.
* **PERIM-μ re-derived exactly.** (a): JA-VDIND's display "z_{m−1}^{i·A_{m−1}} = 1
  for every attained i" IS (PERIM-(m−1)) at the attained set; (R-coll)'s
  every-recursion-node form (2 ≤ q ≤ m−1) is quoted verbatim from JA §3.4.
  (b): JB §0M column (c) at HEAD reads "at every m ≥ 2 a HYPOTHESIS (JA-VDIND's
  ABSOLUTE character-triviality z_{m−1}^{i·A_{m−1}} = 1 at every attained
  abscissa)" and "Unconditional at m ≤ 1 ONLY ((VD-1) = W2-L3)" — both carried
  verbatim, m ≤ 1 perimeter intact. (c): ξ_Q = χ_{Q−1}^{γ_Q}·z_{Q−1}^{−e_{Q−1}A_{Q−1}}
  matches W2 §3.4 (index-shifted); at χ_{Q−1} = 1 the one-line evaluation to
  χ^{(Q−1)}_{e_{Q−1}} = ϑ_Q is exact; the slot-grid reading matches W2 §3.1's
  slots k_j = s + je_{Q−1} and §3.2's letter-twist sentence; the χ-chain +
  mod-wrap caveat (I4B r = 5) is carried, matching W2 §3.5. The absolute ⟹
  slot-grid implication and its failing converse check (ord(z)|A ⟹ ord(z)|eA).
* **LEDGERLAMBDA precedent quote verbatim** ("it does not edit, bracket, or
  retire them"); [SYN] = f71cd68 confirmed; JA/JB/JC/W2 counters at HEAD all
  0/2 as the daggers state; JB-EPS's ε′ display quoted correctly in LAW-2 and
  the ∂t sign convention is used consistently across WM-COB(i)/LAW-2/∂E.

## FINDINGS

### F-1. JUSTIFICATION GAP (conditionality carriage stale against the post-r4 [JB]† it declares) — the most serious finding

The note declares **"[JB]† = `GRTJB_PROOF_2026-08-08.md` (post-r4, 0/2)"** and
promises "their full conditionality ledgers carried verbatim", then carries the
**pre-r4** evidence-frontier count at three sites:

> S1 Remark: "JB's rows 5/12/22 evidence frontier all ride"
> S4 one-line stack: "JB §0M incl. rows 5/12/22 NO-LEG"
> S4 bullet: "JB rows 5/12/22 stay NO-LEG"

[JB]† at HEAD (§0M summary, r4/F-2 — committed at ae0acdf, BEFORE the
WELDMASTER seal b375f42) struck exactly this count and recounted:

> "~~(1) Three cells hold an open proviso with NO machine leg beside it — rows
> 5 (RES), 12 (d4), 22 (v = 0)~~ **[r4, F-2 — RECOUNTED under the sentence's own
> criterion; the struck count missed row 4 and its uniqueness claim was false.
> (1) FOUR cells hold an open proviso with NO machine leg beside it — rows 4
> (the (GRID) grid/attained-abscissa half…), 5 (RES), 12 (d4) and 22 (v = 0) —
> and TWO of them, rows 4 and 12, are the u ≥ 0 riders…]**"

The ledger tail confirms ("NO-LEG census corrected: FOUR (rows 4/5/12/22…)",
JB-r4 entry, 2026-08-06). So the consolidation's carried frontier omits row 4
(JB-DEV(iii)(GRID)'s grid/attained-abscissa half — an undischarged u ≥ 0 rider
with no machine leg), repeating a figure its own source marks FALSE. Mitigant:
the u ≥ 0 proviso itself IS carried in (M1)'s conditionality cell, so no face
consumes the missing row's content unfenced; the defect is that a note whose
entire proof is "citation at the cited conditionality" reproduces a
struck-through ledger cell three times. **Honesty defect: moderate** (the
"carried verbatim" claim is falsified in this cell).

### F-2. JUSTIFICATION GAP (WM-SHEAR is same-computation, billed as an "M1 re-key")

S5 bills the family as:

> "WM-SHEAR   M1 re-key: fresh-hull(Σ_q(U)) == fresh-hull(H) vertex-for-vertex
> + slope law + min tie. PREDICTED 0."

and the decorrelation paragraph discloses only the min tie as non-independent
("its min tie recomputes the engine's own weight recursion — disclosed as a
sanity leg, not IND"). In the runner, BOTH point sets come from the same engine
numbers: `Upts = (i, wq + i·T.wPhi[q])`, `Hpts = (i, T.e[q]·wq + i·T.gam[q+1])`
with the same `wq = T.wlev(q, Ai)`, and the engine defines
`gam[j+1] = e_j·wPhi[j] + h_j` (iterlawn_pe_reimpl.py line 270; gam[1] = h₀
covers q = 0) — so `shearU ≡ Hpts` is an arithmetic identity of the harness
engine, not a harness-vs-print comparison; `hullSU == hullH` cannot fail for
any true or false M1. The residual content is (a) hull-commutes-with-shear —
[JB]†'s generic two-line LEMMA JB-AFF, tower-free — and (b) the min tie, which
is `wlev`'s own defining recursion (engine line 425), i.e. also
same-computation. Under [JB]†'s own IND/SAME/NONE taxonomy ("SAME … the
violation is UNREACHABLE and the leg carries NO information … never advertised
as a second engine") this family is SAME, in contrast to JB's genuinely IND
shear families (print `G.vgen`/`G.vkey` vs harness `T.wlev`/`T.gam`). The
804/0 therefore adds no evidence for the (M1) face beyond checking the fresh
hull code, and the verdict gloss "the shear law exercised on genuinely
multi-vertex polygons" plus the ledger's "shear re-keyed fresh on 804 polygons"
inherit the overbilling. (The runner docstring's "the IND content is the
hull/vertex/slope covariance under the fresh shear" claims IND for generic
convexity.) The other nine families and all four teeth survive this audit:
WM-COB-I/OFFW/F/C, WM-RHO, WM-FENCE-XI/EQ key the NOTE's new displays with a
genuinely fresh t-implementation against the committed engine leg; the
off-window γ−E legs genuinely exercise the arbitrary-ℤ scope (negative
arguments through `split`/`constants`); the four teeth are genuinely wrong
mutations of the note's own displays (the Def-t(i) sign flip is the real
confusable JA-EPS's sign display warns about).

### F-3. JUSTIFICATION GAP ((M2)'s identification cell overstates against the note's own fence)

The (M2) row's identification column:

> "the ε-kit IS the print's t(i)-twist in eq12-canonical coordinates; **all
> transport characters are values/differences of ONE cochain (S2, S3)**"

contradicts the note's own S2.3/S3 fences:

> S2.3: "Likewise the mod-wrap boundary … and the **χ-chain at m ≥ 2 are NOT
> reduced to cochain values by this note**"
> S3 caveat: "χ_{Q−1} ≠ 1 makes ξ_Q a χ-corrected character, **not a bare
> χ^{(μ)} value**"

The defensible verb is the (M2) clause text's own "generated by ONE 1-cochain"
(products of powers of cochain values through the descent operator), not
"values/differences of". A consumer reading the table cell alone would carry
the χ-chain at m ≥ 2 as cochain data, which S2.3 explicitly fences out. One
cell, wording-level; the clause text and the fences are consistent with each
other.

### F-4. JUSTIFICATION GAP (S0's cochain display cites JA-EPS beyond its quantifier)

S0 displays, for **β ∈ ℤ**:

> "ε_j(β)  = z_j^{−t_j(β)}                       [JA-EPS, PROVED in [JA]†]"

but [JA]† JA-EPS at HEAD is quantified as "For every m ≥ 1 and every β ∈ ℤ
**in the level-m weight lattice**" (𝒲_m ⊆ ℤ_{≥0} per JB r4/F-8's definition).
The note then uses the identity at arguments outside any weight lattice:
WM-RHO quantifies "every γ ∈ ℤ" through E(γ) = ∏ε_j(β_j(γ)); the WM-COB-OFFW
legs and WM-CLASS's Ẽ evaluate ε_j at split weights of off-window/negative γ,
where β_j can be negative. The identity IS unconditionally true there — the
correct carrier is [ILN]† EXP-KIT (EPS-CLOSED: "(s(β) − ℓβ)/e ∈ ℤ and
ε(β) = z^{(s(β)−ℓβ)/e}", accepted, β unrestricted; machine-confirmed by WM-EPS
615/0 over ranges wider than any lattice) — but that lemma is not cited at the
display; JA-EPS as pointed does not deliver the range consumed. Purely a
mis-aimed/narrow citation; no mathematical consequence (and conservatively it
OVER-prices (ii) by attaching a 0/2 input to an [ILN]-unconditional identity).

### F-5. JUSTIFICATION GAP (S4's "full conditionality stack" drops one [ILN] residual [JC]† carries)

S4's one line prices [ILN]† as:

> "[ILN]† ACCEPTED (SHIFT-(n)/D_j-INT unconditional; value law on the scored
> stratum; residuals (RM-m ≥ 2), (W-MULT-DCX-m), standard-lift)"

[JC]† §10.2 — whose W-6..W-9 the (M3) face consumes "with their full
conditionality ledgers carried verbatim" — prices the same engine as:

> "[ILN]† ACCEPTED (scored stratum; residuals (RM-m ≥ 2), (W-MULT-DCX-m),
> **(ITER-LAW-LIFT)**, standard-lift only) + GRB/CARRY-1/D-REAL
> ACCEPTED-conditional (§0 ladder **+ [T] pins**) …"

The (ITER-LAW-LIFT) residual (the open lift-transport leg, currently the
LIFTCORNER arc's subject) and the "[T] pins" qualifier are absent from
WELDMASTER's stack at every site. Since S4 titles itself "the full
conditionality stack" and otherwise enumerates at exactly this granularity,
the omission is a completeness defect of the enumerated stack (the blanket
"ledgers carried verbatim" sentence catches it only implicitly). Everything
else charged in (5) checks out: no WELD-M clause reads as unconditional
anywhere (WM1's status is "PROVED-BY-CITATION at the cited grades (0/2 each)",
and the "no grade upgrade by composition" bullet is correct and honored);
W2-OPEN-1/(VD-m)/(DMULT-s)/J3b/hExhaust/P0 all explicitly ride.

### F-6. MINOR (verdict-block gloss): "battery has teeth on every new display"

The four preregistered teeth key WM-COB-I (sign), the composite display (δ),
the shear, and the c₁ tie. **WM-RHO and WM-FENCE-EQ have no tooth**, and both
are new displays (WM-RHO is a new PROVED lemma). The sealed S5 teeth list is
honest; the commit-2 gloss "all ≥ 1, battery has teeth on every new display"
overstates coverage.

### F-7. MINOR ((F-c) mis-grades [RMG] downward): the fence surface reads

> "(F-c) … and the [RMG]/LED-Λ attempt grades where [JB]† consumes them."

[JB]† consumes [RMG] as **ACCEPTED**, not attempt (§4 grade cap: "consuming
[RMG] as ACCEPTED and LED-Λ at ATTEMPT grade"). Conservative direction
(under-grading an accepted input), but factually wrong as citation precision
in a note whose content is citations.

### F-8. MINOR (WM-CLASS's κ ∈ ℤ_{≥0} asserted without its one-line warrant)

S2.2 defines "κ(ν,ν′) := (σν + σν′ − σ(ν+ν′))/E ∈ ℤ_{≥0}". Integrality is
immediate; **non-negativity** needs σν + σν′ ∈ W (window additivity —
[ILN]† Lemma WINDOW-(n), proved unconditional) plus σ's minimality, neither
cited. Census-backed (κ observed 0..7, all ≥ 0) and inside a corollary that is
honestly display-grade throughout, so a gap of justification only.

## HONESTY GRADE

Above-genre-par overall: the grade-cap sentence, the per-claim footprints, the
scored-stratum fence at all three (iii)-consumption sites, the OPEN/NO-LEG/
MEASURED riders, the synthesis-spot-checks-as-measured-support demotion, and
the "no grade upgrade by composition" rule are all present and (except F-1's
cell and F-5's residual) accurate against HEAD sources. The defects found are:
one stale ledger cell repeated thrice (F-1, moderate), one battery family
billed above its evidence class (F-2, moderate at the billing level), one
identification cell wider than the note's own fence (F-3), one mis-aimed
citation (F-4), one stack omission (F-5), and three minor precision slips
(F-6/7/8). No CRITICAL: no displayed identity is wrong, no face consumes more
than its citation proves at the mathematical level, nothing is upgraded, and
both new proofs are complete and correct as written.

**Counter: 0/2 (this pass does not count as clean).** Repair guidance is not
this pass's job; the findings above name their sites exactly.

— PE1 verifier, fresh context, 2026-08-06.
