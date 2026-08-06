# GRTJC — J-C, THE CARRY-ALGEBRA JUNCTION (W-6..W-9): the composite-stage graded target exists (localize + gauge, with the ℤ → ℤ/E collapse proved), TC-3 is load-bearing EXACTLY at δ ≥ g_m (theorem, not observation), the anchor-transport isomorphism Ψ with the measured inner normalization ∏_{j≤m} z_j^{D_j}, harness-val = TC-read, and the cocycle semantics — four separately boxed clauses, each an honest proof or an honestly boxed obstruction

**Unit:** GRTJC COMPOSER (Phase 1 of `docs/in-progress/GRTJC_BRIEF_2026-08-05.md`,
dispatched on the instrument's verdict). **Genre: PROOF NOTE at attempt grade —
own acceptance counter 0/2.** No `.lean` touched, no gate fires, **no gate
retires**: DITERSUP §S3 gate J3b stays BLOCKED-ON-CARRIER-TIE (this note
DISPLAYS the tie it would need, and by construction cannot retire it — J3b
retires only when (J-C)(ii) survives its own hostile arc), the Asvin P0
application gate stands, and no density/menu/count statement is made anywhere.
**Author:** Fable composer unit, campaign date 2026-08-08 (wallclock 2026-08-05).

**Instrument consumed:** `lean/notes/openmath/GRTJC_PROBE_2026-08-08.md` (seal
`7212e56` → verdict `fc89b03`; runner `verification/openmath/grt_jc_probe.py`):
29 towers, m ∈ {1,2,3}, 669 scored pairs, **22 families all GREEN, 0
violations**, all 29 rows EXHAUSTIVE (structure constant determined with zero
witness input from the harness side; per-pair uniqueness machine-proved). Its
five measurements M1–M5 are this note's structure constants. **Its refutation is
honored:** the brief's germ hypothesis ("the inner normalization factor at
general m is −z_{m+1}") is reading H-D and FAILS on 138/669 pairs; the measured
inner factor is ∏_{j=1}^{m} z_j^{D_j} — the INNER letters. This note proves the
instrument's law, not the brief's guess.

**Own machine leg:** `verification/openmath/grt_jc_checks.py` (two-commit seal;
predictions §9.1 sealed BEFORE the run at commit `6ad01d1`) — it tests THIS
note's clauses, not the instrument's: the slot-span theorem, the scalar-image
lemma, the ψ-kernel witness, the fibred-index bijection, the cocycle identity,
the cyclic-genre law, with five planted teeth. **VERDICT (§9.2): 10 families,
8,566 scored samples, 0 violations, all five teeth fired (1,054 firings),
29 rows, 2.0 s** — including the note's own new sharp prediction (slot set of an
anchor product == {δ}) at **609/609**, and one battery-driven correction applied
to §6(d) (the cyclic law's converse is FALSE — 13 collapse-geography rows are
NOT-CYCLIC).

~~**[r1] S-STATUS (CURRENT): attempt grade, acceptance counter 0/2, ONE hostile
pass RUN and ONE repair round applied.** Arc: composed (seal `6ad01d1` →
verdict `8f07904`) → **JC-PE1** (`GRTJC_passPE1_report.md`, commit `1a27be3` —
**2 CRITICAL + 8 gaps, NOT CLEAN**; ledger `BRIDGE_ADJUDICATIONS_2026-07-30.md`
entry "J-C PE1", commit `6ed4680`) → **r1 = THIS repair round, STRUCTURAL**
(block below). A repair round is NOT a pass, so the counter stays **0/2**, and
**JC-PE2** — a fresh hostile pass on THIS post-r1 text — is the next acceptance
attempt. No gate fires, none retires; no `.lean` touched; no density/menu/count
statement anywhere.~~

**[r2] S-STATUS (CURRENT; supersedes the r1 status line above, which is kept
struck rather than deleted): attempt grade, acceptance counter 0/2, TWO hostile
passes RUN and TWO repair rounds applied.**

    ARC:  composed (seal 6ad01d1 -> verdict 8f07904)
      ->  JC-PE1  (GRTJC_passPE1_report.md, 1a27be3)   2 CRITICAL + 8 gaps
      ->  r1      STRUCTURAL repair (85d5811/54904cc; mini-seal f45b63c/66263ce)
      ->  JC-PE2  (GRTJC_passPE2_report.md, 4a76d52)   0 CRITICAL + 9 gaps
                  — "the structural repair itself survives a full hostile
                    re-derivation … no false statement"
      ->  r2      THIS round: LABELLING + FOOTPRINT + one new machine leg
      ->  JC-PE3  = the next acceptance attempt (a fresh hostile pass on THIS
                    post-r2 text)

A repair round is NOT a pass, so the counter stays **0/2**. No gate fires, none
retires; no `.lean` touched; no density/menu/count statement anywhere.

**[REPAIR ROUND r1 — 2026-08-08 campaign (wallclock 2026-08-05).** Applied
against JC-PE1. PE1's machine leg reproduced this note's battery **bit-for-bit**
(8,566 scored samples, 0 violations, exit 0, every §9.2 cell identical, runner
md5 identical at both seal commits and at HEAD, instrument re-run clean), so
**no measured quantity moves at r1** and the sealed runner + artifacts are
BYTE-FROZEN (nothing in `grt_jc_checks.py` / `grt_jc_probe.py` or their outputs
is touched at r1). PE1 also re-derived, hostilely and independently, JC-DOM,
JC-GAUGE (unit hypothesis satisfied, TC-1 strictly before TC-2), JC-PER,
JC-FIB, JC-ANCHMON, JC-SCAL, JC-SPAN, JC-LOAD's iff in both directions,
JC-PSIKER's witness computation, W-8's cancellation and JC-F1's algebra —
**all CLEARED**. What failed was one object identification and one quantifier.
Dispositions, each edit carrying a dated `[r1, F#]` (critical) or `[r1, G#]`
(gap) bracket, strike-and-replace (the refuted r0 wording is quoted inside the
bracket that supersedes it, never silently deleted):

* **F1 (CRITICAL 1) — the coordinate calculus was stated on the WRONG OBJECT.**
  §2.10's `(COORD)` ("𝑅_λ : gr_λ(w) → Δ = K_m[y] is a K_m-linear isomorphism")
  and its display ("gr_λ/(𝔦 ∩ gr_λ) ≅ K, a ONE-dimensional K-space") are **FALSE
  on this note's own gr(w)**: the ambient ring is O[x] and w ≥ 0 there, so every
  gr_λ is a FINITE-dimensional K_m-space (explicit slot bound below), and PE1's
  machine counter-instance sits on the battery's own row C2I at the battery's
  own window base. **REPAIRED, inside the note's own machinery**: (COORD),
  (MULT) and TC-3's display are restated on the **post-TC-1 pieces**
  `B_n = ∪_k in(π)^{-k}gr_{n+kE}` (JC-DOM's object), with four new lemmas —
  **JC-LOC** (B ≅ gr_{K[x]}(w): B *is* the object FGMN's theorems speak about),
  **JC-PIINV** (the digit polynomial is π-equivariant, so the colimit coordinate
  is well defined, and ρ is exactly invariant), **JC-BSURJ** (the colimit
  coordinate is ONTO Δ — PROVED from REALIZE-(m), not cited), and the reduction
  of the Δ-module half to a single cited input **(DMULT)** (composite-stage
  residual multiplicativity). **All five PE1-listed consumers RE-DERIVED and
  THROUGH** (§3.1, JC-IND/OB-4, W-7's bijectivity, JC-F1's dimension count,
  (MULT)) — none downgraded; W-7 is in fact STRENGTHENED (𝒜(T) is the whole
  transported ring). New corollary **JC-COB** (u = a_γ·a_{γ′}: the inner factor
  is the anchor-constant coboundary) with its own scored machine family.
* **F2 (CRITICAL 2) — JC-PSIKER's closing sentence was over-quantified.** "TC-3
  has a nonzero kernel on every graded piece" is FALSE for λ < wΦ_NR (all 29
  rows at their own base). The **witness computation is CORRECT** and W-6(v)'s
  fenced wording is CORRECT; only the universal generalization went wrong.
  RE-QUANTIFIED to the exact range (§2.9(ii)(iii)): ZERO for every λ < wΦ_NR,
  NONZERO for every λ ∈ wΦ_NR + W, and — the form §2.10 actually consumes —
  nonzero on **every** graded piece of the POST-TC-1 object B.
* **G1** — W-6(ii)'s interface fixed: `A_ν ≅ B_n` (JC-GAUGE(iii)'s actual
  conclusion), not "the gr_n(w)-piece"; B_n ⊋ gr_n in general.
* **G2** — 𝒜(T)'s "degree-0 component" definition CORRECTED (it contradicted
  the note's own degree-separation proof) and flagged as **FINDING JC-F2**, an
  inherited blueprint/design-note/brief display defect, REVIEW-OWED, the same
  treatment JC-F1 gets.
* **G3** — §9.2's JC8 evidence cell RE-LABELLED honestly (the sealed battery
  filters zeros before the predicate exists, so it does NOT evidence "every
  structure constant is a unit"); the falsifiable version + a skipped-pair
  census live in the NEW r1 script (§9.3, family R1-UNIT + tooth T4).
* **G4** — §7 case 1's g_m labels corrected against the runner (C2I/C4I are the
  two g_m = 2 rows; C2B/C3I are g_m = 1), with the "27 g_m = 1 stages" recount.
* **G5** — §2.8(c)'s "THEOREM" aligned with JC-LOAD's own e_m ≥ 2 fence
  (theorem on the 28 rows with e_m ≥ 2; MEASURED on the top-flat row C4H).
* **G6** — §3.4's SPAN-M census restored to the instrument's own disclosure
  ("606 skipped for non-integrality"), and "no case is owed" re-justified in the
  repaired frame.
* **G7** — §4.1 remark (a)'s two unproved identifications STRUCK, replaced by
  what is provable (the definitional same-line cancellation + JC-COB).
* **G8** — fence hygiene: the battery's own calls to `T.constants` (δ) and
  `T.read` are DISCLOSED, with the non-circularity argument spelled out.

**New machine leg (r1):** `verification/openmath/grt_jc_r1_checks.py` under its
own two-commit mini-seal (sealed UNRUN at `f45b63c`), testing the REPAIRED
statements only. **VERDICT (§9.3): ~~10 families, 10,475 scored samples~~
[r2, G-8: **10 families = 10,330 scored samples + TOOTH-ROW 145 = 10,475 over
the 11-row table** — the r1 headline summed an 11-row table under a 10-family
label], 0 violations, 29 rows, 2.6 s, exit 0; all five teeth fired (1,885
firings)** —
including (DMULT) exact on 2,784 samples, JC-COB's u = a_γa_{γ′} on 869/869
anchor pairs, the corrected PSIKER range in both directions (197 lines below
wΦ_NR with kernel 0; 197 residue classes with a certified nonzero witness), and
G3's missing unit census (869 unit / 0 zero / 0 undefined / 0 out-of-window)
with a planted-zero tooth proving the predicate can fire. The r0 battery, the
instrument, and all their artifacts stay byte-frozen.**]**

**[REPAIR ROUND r2 — 2026-08-08 campaign (wallclock 2026-08-05/06).** Applied
against **JC-PE2** (`GRTJC_passPE2_report.md`, commit `4a76d52`): **0 CRITICAL,
9 gaps**. PE2 re-derived the whole r1 structure hostilely and independently —
JC-LOC, JC-PIINV, JC-BSURJ, (COORD-B)(1)(2), (MULT-B), JC-COB,
JC-PSIKER(ii)(iii) and **all five PE1 consumers** — and found **no false
statement**; it also reproduced both batteries byte-for-byte and verified both
seals. So r2 is a **labelling / footprint / disclosure round with ONE new
machine leg**, not a restatement: **no clause changes grade, no measured
quantity moves, and the r0 battery, the r1 battery, the instrument and all
their artifacts stay BYTE-FROZEN** (r2 adds one new runner and touches nothing
else in `verification/`). Dispositions, each edit carrying a dated `[r2, G#]`
bracket, strike-and-replace:

* **G-1 (the one with content) — `(DMULT)` was labelled "CITED, not proved
  here" in its EXACT (multiplier-1) form, which §0's own transport statement
  cannot deliver.** Split into two honest tiers in §2.10: **(DMULT-w)**, the
  up-to-a-unit-cocycle form, **DERIVED here from §0's transport** (derivation
  displayed), and **(DMULT-s)**, the exact form, **MEASURED (R1-DMULT 2,784/0
  and r2's new R2-BIL/R2-PHI), NOT cited** — the attempt to verify the exact
  form against the sources the note names FAILED in a specific, reportable
  way: (IN-3)'s own transport clause delivers `𝑅 = c·R^{GMN}` only up to a
  line-wise unit, and the corpus's sharpest harness↔literature read
  dictionary, **open lemma TR-3′-GEN** (`GRB_ORDER2_2026-08-05.md` §S3.4), is
  itself stated *"together with per-argument units"* and is OPEN beyond its
  order-≤ 3 closed strata — so no corpus-pinned statement delivers
  multiplier 1 (§2.10 [r2, G-1] quotes both). JC-COB's sharp `u = a_γa_{γ′}`
  is re-fenced to ride **(DMULT-s)** explicitly, at every site.
* **G-2 — R1-DMULT's samples are monomial-dominated and its one
  non-monomial × non-monomial pair was `continue`d UNDISCLOSED.** (a) the
  sample composition and the skip are now disclosed in §9.3 [r2, G-2]; (b) the
  real leg is r2's new runner `verification/openmath/grt_jc_r2_checks.py`
  (§9.4, own two-commit mini-seal), which builds **dense multi-slot digit
  polynomials on BOTH factors** by the JC-BSURJ construction and tests (DMULT)
  on genuinely bilinear input (family **R2-BIL**), scores the r1-skipped pair
  (Φ_{m+1}, Φ_{m+1}) on every row (**R2-PHI**), machine-checks the r1 sample
  composition itself (**R2-MONO**: ≤ 1 multi-slot element per row, every
  r1-tested pair had a single-slot factor), and plants the **cross-term tooth
  U2** — the convolution-killing mutation that is provably SILENT on every
  r1-tested pair (censused at 0 fires there) and must fire on the new dense
  pairs.
* **G-3** — §2.10's stale pre-seal `c_π` quote (`{1, z̄, z̄²}`, a 6-row smoke
  value labelled "across the roster") replaced by the **as-of-r1 roster value
  set** from the committed artifact.
* **G-4** — the `[r1]` bracket leak: every live site still naming the STRUCK
  `(COORD)`/`(MULT)` re-pointed to `(COORD-B)`/`(MULT-B)`, including the two
  honesty defects PE2 named — the **W-7 THEOREM box's OB-4 grade line** (which
  graded OB-4 on the refuted input and denied r1's own machine leg) and §4.1
  remark (b)'s footprint sentence. Re-grepped to fixed point; count reported in
  §9.5.
* **G-5** — (MULT-B)'s and TC-3's all-of-ℤ quantifiers: the window/virtual-anchor
  transport is now an explicit displayed step (§2.10 [r2, G-5]), not a
  parenthesis.
* **G-6** — JC-LOC's identification of the note's own extension of `w` with the
  literature's valuation: **DERIVED** (three displayed steps: the extension is
  forced; §1's min-formula is `π`-homogeneous, so the recursion computes it on
  all of K[x]; it is a valuation), with the **additivity** of the degreewise map
  supplied. The residual tie (§1's recursion = MacLane's inductive valuation) is
  **W-1**, already in §0's stack — not a new input.
* **G-7** — "JC-BOX-4 (unchanged)" corrected at both sites (the box DID change:
  it gained an `[r1]` conditional closure).
* **G-8** — §9.3's headline figure decomposed: **10 families = 10,330 scored
  samples**, plus TOOTH-ROW 145 = **11 rows / 10,475** in the table.
* **G-9** — the one-line ideal transport along JC-GAUGE(iii) written out.

**New machine leg (r2):** `verification/openmath/grt_jc_r2_checks.py` under its
own two-commit mini-seal (commit 1 = the runner, sealed UNRUN at `79611a4`,
prereg in its docstring = §9.4's table; commit 2 = the verdict FROM the
committed artifacts), testing ONLY the bilinearity content of (DMULT) and the
disclosure census. **VERDICT (§9.4): ALL 4 FAMILIES GREEN — 3,655 table rows
(3,597 in-family + TOOTH-ROW 58), 0 violations, 29 rows, exit 0; U1 261/261,
U2 261/261, no silent tooth; (DMULT-s) exact on 261 dense bilinear pairs; the
r1-skipped pair scored on 29/29 (bilinear content on exactly C2I/C4I, the two
g_m = 2 rows); U2 fired 0 times on the r1-tested pairs — the r1 leg had zero
resolution against the cross-term class.** See **§9.4** for the
preregistration and verdict, and **§9.5** for the r2 bracket-sweep
record.**]**

---

## §0. INPUTS AND THE CONDITIONALITY STACK (read before any clause)

Every clause below is stated with its inputs named. There are five, and no
clause is stronger than the weakest input it uses.

**(IN-1) [ILN]† = (ITER-LAW-n), ACCEPTED** (`ITERLAWN_PROOF_2026-08-08.md`,
arc closed 2026-08-03 at the 2-clean model-diverse bar; PC6 CLEAN + PE7 CLEAN).
Scope as accepted: for all n ≥ 1 on the (n+1)-read **standard-lift** harness
class, the closed form for the harness value cocycle

    c_{n+1}(γ,γ′) = z̄^δ · ∏_{j=1}^{n} z_j^{D_j},   δ = ⌊(s_{n+1}(γ)+s_{n+1}(γ′))/e_n⌋,

with residuals: the open engine families (RM-m, m ≥ 2) and (W-MULT-DCX-m), the
fenced corners, and DCX-(n) = ∪_m DCX_m excluded. **In this note c_T denotes
this closed form**, and "the scored stratum" means [ILN]†'s own: all D_j
integral ∧ the pair off DCX. (Instrument census: on its 29-row roster **DCX
pairs 0, non-integral-D pairs 0** — the whole grid sat inside the accepted
stratum.)

**(IN-2) GRB Lemma D-REAL + CARRY-1 + (W-MULT), ACCEPTED-WITH-CONDITIONS**
(`GRB_ORDER2_2026-08-05.md` §S5.2/§S6a; conditional on the GRB §0 ladder
((V1)_{≤i+1}, (KP)_{≤i−1}, (H-CHAIN)) and the §3.3 [T] pins — that
conditionality is inherited here forever). This is the **last-read layer**: the
gauged anchor system at the last read is K_{m+1}[u]/(u^{e_m} − z̄), CARRY-1 is
φ_γφ_{γ′} = φ_{γ+γ′}·ȳ^δ at that layer, and (W-MULT) is
R^{gr}_{γ+γ′}(αβ) = y^{δ}R^{gr}_γ(α)R^{gr}_{γ′}(β). **CONSUMED, NOT RE-PROVED.**
J-C(i) is this layer; §§2–5 below are the composite-stage content.

**(IN-3) The FGMN graded package, CITED LITERATURE, transported by W-1.** As
pinned and quoted in the corpus (`GRB_ORDER2_2026-08-05.md` §S6a verbatim: "Thm
4.2 three times … gr_K(w) is a domain … Thm 4.8 (evaluation at ȳ is an
isomorphism F_r[y] → Δ) … ord_y-additivity from s(gh) = s(g) + s(h), Cor 2.7"):

    (a) w = w_{m+1} is multiplicative: w(fg) = w(f) + w(g);
    (b) gr(w) is a DOMAIN, and in(fg) = in(f)·in(g);
    (c) gr_γ(w) is FREE OF RANK ONE over Δ ≅ K_m[y] on the anchor basis
        in(φ_γ) at attained γ  [Thm 4.2];
    (d) evaluation y ↦ z̄ is an isomorphism K_m[y]/(ψ_m) ≅ K_{m+1}
        [Thm 4.8 / Cor 4.9];
    (e) the minimal on-line Φ_m-abscissa is additive: s(fg) = s(f)+s(g)
        [Cor 2.7].

FGMN state these for types of ARBITRARY order, so the composite-stage instance
is a citation, not an extrapolation by this note — **but the theorem numbering
above is the corpus's pinned quotation, re-verified against no printed source in
this session (citation-precision owed; flagged in JC-BOX-3).** Their transport to
the HARNESS objects (w = v_{m+1} in the sheared frame; R_{m,λ} = c·R_λ^{GMN} with
c a line-wise unit) is **W-1 (J-A), ATTEMPT GRADE**.

**(IN-4) W-2 / J-A / J-B, ATTEMPT GRADE (counter 0/2).** W-2 (the lift junction,
`GRTW2_PROOF_2026-08-08.md`), J-A (the dictionary), J-B (the tree;
`GRTJB_PROOF_2026-08-08.md`, whose JB-BOX-2 conditionality — (VD-m) free only at
m ≤ 1, JA-VDIND at m ≥ 2, JA-BOX-2's (R-coll) at m ≥ 3, the pinned-ℓ orbit,
the shared-key perimeter q ≤ qcap — rides in wherever a print-residual statement
is used). §5's germ display cites J-B's JB-CREAD + JB-EPS and inherits their
fences verbatim.

**(IN-5) The corpus's own construction layer, ACCEPTED as part of [ILN]†:** the
class pin ([ILN]† S0.1: ψ_j monic irreducible with ψ_j(0) ≠ 0, gcd(e_j,h_j) = 1,
g_j ≥ 1), the split/anchor conventions (S0.2), REALIZE-(m) with its R1/R2/R3 laws
(S4.1: deg < deg Φ_m, w = β, read = τ), and the level reads. Everything in §1 is
definition, not claim.

**THE STACK, ONE LINE.** Every clause of §§2–5 rides
`[ILN]† ACCEPTED (scored stratum) + GRB/CARRY-1 ACCEPTED-conditional (§0 ladder) + FGMN (c)(d)(e) CITED + W-1/W-2/J-A/J-B ATTEMPT (0/2)`,
and this note's own arc starts at **0/2**. Nothing here may be consumed at proof
grade before its hostile arc.

---

## §1. OBJECTS (definitions; nothing is claimed in this section)

Fix a complete DVR O with uniformizer π and finite residue field, and a
standard-lift tower T of the [ILN]† class with reads (e_j,h_j,g_j), j = 0..m,
so NR := m+1 reads. Write E := e_0e_1⋯e_m (= E_{m+1} of the blueprint), and:

* **keys** Φ_0 (monic, deg d_0, irreducible mod π), and Φ_{j+1} built by
  REALIZE: Φ_{j+1} = Φ_j^{e_jg_j} + Σ_{k<g_j} C_kΦ_j^{e_jk} with
  deg C_k < deg Φ_j. Hence **deg Φ_{j+1} = e_jg_j·deg Φ_j**.
* **weights** γ_1 = h_0, wΦ_{j+1} = e_jg_jγ_{j+1}, γ_{j+1} = e_jwΦ_j + h_j;
  the MacLane weight w_{j+1}(f) = min_a (e_j w_j(A_a) + aγ_{j+1}) over the
  Φ_j-development f = Σ_a A_aΦ_j^a, and w_0 = the coefficientwise π-valuation.
  **w := w_{m+1}** throughout; gr(w) := ⊕_{γ∈ℤ} P_γ/P_{γ+1}, P_γ := {w ≥ γ},
  and in(f) := the class of f in gr_{w(f)}.
* **residues** K_0 = k_0[x]/(Φ̄_0), K_{j+1} = K_j[y]/(ψ_j) = K_j[z_{j+1}],
  g_j = deg ψ_j; **z̄ := z_{m+1}**, K := K_{m+1}. Note ψ_j(0) ≠ 0 ⟹ z_{j+1} ≠ 0,
  so every letter is a unit.
* **split** γ ↦ (s_1..s_{NR}, u_1) by iterated eq-(12): s_{NR},u_{NR} = eq12(γ,e_m,h_m),
  β_{j-1} = u_j − s_jwΦ_{j-1}, s_{j-1},u_{j-1} = eq12(β_{j-1},e_{j-2},h_{j-2});
  s_{j+1} ∈ [0,e_j) always. **Window** W := {γ : u_1(γ) ≥ 0}.
* **anchors** φ_γ := π^{u_1}∏_{j=0}^{m}Φ_j^{s_{j+1}} for γ ∈ W (Tower.tanch).
* **the level read** at line λ: develop f in Φ_m, keep the digits at abscissas
  a ≡ s_{NR}(λ) (mod e_m) that lie ON the line (weight exactly λ), ε-correct
  them, and pack them as read(λ,f) = Σ_j C_j z̄^{\,j}, **grid slot**
  j := (a − s_{NR}(λ))/e_m. Define the **digit polynomial**

      𝑅_λ(f) := Σ_j C_j y^{\,j} ∈ K_m[y]     (Tower.read_coeffs, packed in y)

  so that **read(λ,f) = 𝑅_λ(f)(z̄) = 𝑅_λ(f) mod ψ_m** — a definitional identity
  of the corpus's own read. By the definition of w as a min, **𝑅_λ(f) = 0 ⟺
  w(f) > λ** (for f with w(f) ≥ λ); so 𝑅_λ is an injective K_m-linear map on
  gr_λ.
* **the scalar lift** Λ_N(c) := realize(NR,c,N) for c ∈ K, N ≡ 0 (mod E) with
  N ≥ wΦ_{NR}: by R2/R3, w(Λ_N(c)) = N and read(N,Λ_N(c)) = c. X_N := Λ_N(1).
* **the TC chain** (blueprint S2.3): TC-1 localize gr(w) at in(π); TC-2 gauge
  π ↦ 1 (the [F.0] weight gauge), collapsing ℤ → ℤ/E; TC-3 the residue quotient
  Δ = K_m[y] ↠ K_m[y]/(ψ_m) = K_{m+1}. ~~**𝒜(T)** := the K-span of the anchor
  classes in the degree-0 component of the TC-transported gr(w).~~ **[r1, G2 —
  the "degree-0 component" reading is WRONG and is replaced; see FINDING JC-F2
  (§5).]** **𝒜(T)** := the K-span of the anchor classes **[φ_{γ_ν}], ν ∈ ℤ/E,
  ACROSS ALL ℤ/E-degrees** of the TC-transported ring 𝒜 = (gr(w)[in(π)^{-1}] /
  (in(π)−1)) / image(in(Φ_{m+1})·gr(w)[in(π)^{-1}]) — equivalently (and now
  PROVED, §2.10 [r1]) **𝒜(T) = 𝒜, the whole transported ring**, since each of
  its E graded pieces 𝒜_ν is the K-line K·[φ_{γ_ν}]. The anchor class of γ sits
  in 𝒜_{γ mod E}, which is the degree-0 component only for ν = 0, so the r0
  wording contradicted this note's own degree-separation argument (§3.4) and
  would have made W-7's Ψ map an E-dimensional carrier onto one K-line.
* **the harness cocycle** c_T(γ,γ′) := z̄^{δ}∏_{j=1}^{m}z_j^{D_j} with δ, D_j the
  [ILN]† recursion data; δ = (s_{NR}(γ)+s_{NR}(γ′) − s_{NR}(γ+γ′))/e_m.
  **Since s_{NR} ∈ [0,e_m) on both arguments, δ ∈ {0,1} always** (used
  constantly below).

---

## §2. CLAUSE W-6 — THE CARRY TARGET EXISTS AT EVERY COMPOSITE STAGE

> **THEOREM W-6.** For every tower T of the [ILN]† class and every level m with
> E > 1: (i) TC-1 and TC-2 are legitimate ring-level operations on gr(w_{m+1});
> (ii) the gauged ring A(T) := gr(w)[in(π)^{-1}]/(in(π) − 1) is **ℤ/E-graded**,
> with ~~A_ν ≅ gr_n(w)-piece for any n ≡ ν~~ **[r1, G1: corrected to JC-GAUGE's
> actual conclusion]** `A_ν ≅ B_n` **for any n ≡ ν, where
> B_n = ∪_{k≥0}in(π)^{-k}gr_{n+kE} is JC-DOM's POST-TC-1 piece** — strictly
> bigger than gr_n in general (the slot bound maxslot(n+kE) of §2.10 grows
> strictly along the ladder infinitely often, so the injective transition maps
> in(π)·gr_{n+kE} ⊆ gr_{n+(k+1)E} are not onto and B_n is the strictly larger
> colimit; PE1's C2I ladder [(0,0),(1,0),(2,1),(3,1),(4,2),…] exhibits it). The
> lemma was always right; the r0 statement quoting it was not, and the
> distinction is load-bearing: B_n, not gr_n, is where Δ ≅ K_m[y] lives (§2.10
> [r1, F1]) — and the surviving index is the
> abscissa-coset index of §1's split (LEMMA JC-FIB); (iii) the anchor map
> γ ↦ [φ_γ] is E-periodic on the nose (LEMMA JC-PER), so it is defined on ℤ/E;
> (iv) **TC-3 is load-bearing exactly on the pairs with δ ≥ g_m** (THEOREM
> JC-LOAD), and the outer factor z̄^δ of c_T is TC-3's image of the graded slot
> shift y^δ — not obtainable from TC-1/TC-2 alone; (v) TC-3 is not a relabeling:
> the level-NR read is non-injective on a graded piece, with the classifier's own
> next key Φ_{m+1} as the kernel witness (COROLLARY JC-PSIKER).
>
> **GRADE: PROVED at general m** on inputs (IN-3)(a)(b)(c)(e) + (IN-5), with the
> single located exception of the **top-flat corner e_m = 1 ∧ g_m = 1** in
> JC-LOAD's sharp form (JC-BOX-4). Attempt grade 0/2.
>
> **[r1] GRADE, post-repair (supersedes the input list only).** Still **PROVED
> at general m**, and on a SMALLER literature footprint: the coordinate calculus
> now rides `(DMULT-w)` **[r2, G-1: the citable tier; the exact tier (DMULT-s)
> is MEASURED-only and carries JC-COB's sharp form alone]** (composite-stage
> residual multiplicativity) instead of
> (IN-3)(c)-on-gr, with (IN-3)(a)(b)(e) + (IN-5) unchanged; clause (ii)'s object
> is B_n (G1); clause (v) is re-quantified (F2). Boxes: ~~JC-BOX-4 (unchanged)~~
> **[r2, G-7: the box DID change at r1 — it gained a CONDITIONAL CLOSURE on
> (DMULT) (the corner is closed for a reader who grants (DMULT-w), open for one
> who wants it FGMN-independent); see JC-BOX-4 [r1]]** and
> JC-BOX-3 **re-cut to box APPLICABILITY, not literature truth**. Attempt 0/2.

### 2.1 LEMMA JC-DOM (TC-1 is legitimate at every stage)

*Statement.* gr(w) is a commutative ℤ-graded domain; in(π) is homogeneous of
degree **E** and is a nonzerodivisor; hence the localization
B := gr(w)[in(π)^{-1}] exists as a ℤ-graded ring, gr(w) ↪ B, and
B_n = ∪_{k≥0} in(π)^{-k}·gr_{n+kE}.

*Proof.* By (IN-3)(a) w is multiplicative, so for f,g ≠ 0,
in(f)in(g) = in(fg) ≠ 0 in gr_{w(f)+w(g)}: gr(w) is a domain ((IN-3)(b), the
same domain property the accepted GRB S6a cancellation uses). For the degree:
w_0(π) = 1 and, since the Φ_j-development of the constant π is A_0 = π,
w_{j+1}(π) = e_jw_j(π); hence **w(π) = e_0e_1⋯e_m = E** by induction. A
nonzerodivisor homogeneous element of a graded domain may be inverted: the
graded localization at the multiplicative set {in(π)^k} is a ℤ-graded ring, with
the stated degree pieces, and the localization map is injective because gr(w) is
a domain. ∎

*Remark (what this settles).* GRW2_TIE_DESIGN's OB-1 asked for exactly this at
the composite stage and recorded "no accepted clause supplies it". The supply is
multiplicativity of w — which is (IN-3)(a), a literature fact for types of every
order, not a last-read-layer accident.

### 2.2 LEMMA JC-GAUGE (TC-2 is legitimate, and the grading collapses ℤ → ℤ/E)

*Statement.* Let B = ⊕_{n∈ℤ}B_n be any commutative ℤ-graded ring containing a
**unit** ϑ ∈ B_E, E ≥ 1. Put A := B/(ϑ−1)B. Then

    (i)  (ϑ−1)B = ⊕_{ν∈ℤ/E} (ϑ−1)B^{(ν)},  B^{(ν)} := ⊕_{n≡ν (E)} B_n,
    (ii) A = ⊕_{ν∈ℤ/E} A_ν  is ℤ/E-GRADED, A_ν := image of B^{(ν)},
         A_νA_{ν′} ⊆ A_{ν+ν′},
    (iii) for each ν and EACH n ≡ ν (mod E) the composite B_n → A_ν is an
          isomorphism of additive groups; in particular A_0 ≅ B_0 as rings.

*Proof.* (i) For homogeneous b ∈ B_n, (ϑ−1)b = ϑb − b has both terms in
B^{(n mod E)}; so (ϑ−1)B is the direct sum of its intersections with the
B^{(ν)}, and B^{(ν)}B^{(ν′)} ⊆ B^{(ν+ν′)}. (ii) is immediate from (i).
(iii) Fix n ≡ ν and define σ: B^{(ν)} → B_n by σ(Σ_k b_{n+kE}) := Σ_k ϑ^{-k}b_{n+kE}
(each summand lands in B_n because ϑ^{-k} has degree −kE). σ is additive and
surjective (restrict to k = 0). σ kills (ϑ−1)B^{(ν)}: for b ∈ B_{n+kE},
σ(ϑb − b) = ϑ^{-(k+1)}ϑb − ϑ^{-k}b = 0. Conversely, modulo (ϑ−1)B^{(ν)} we have
b_{n+kE} ≡ ϑ^{-k}b_{n+kE} (because ϑ^{-k}b·(ϑ^k − 1) ∈ (ϑ−1)B), hence
x ≡ σ(x) for every x ∈ B^{(ν)}; so σ(x) = 0 forces x ∈ (ϑ−1)B^{(ν)}. Thus
ker σ = (ϑ−1)B^{(ν)} and B_n ≅ B^{(ν)}/(ϑ−1)B^{(ν)} = A_ν. ∎

*Application.* Take B from JC-DOM and ϑ := in(π) ∈ B_E (a unit after TC-1, of
degree E by JC-DOM — the harness check w(π) = E the design note wanted). TC-2 is
therefore a legitimate ring-level operation at **every** stage, its output is
ℤ/E-graded, and the design note's C13 objection ("p ↦ 1 is not a graded
homomorphism from TC-1's output alone") is answered in the only way it can be:
the gauge is not a graded map but a **quotient by a non-homogeneous principal
ideal whose ideal splits along the E residue classes**, which is exactly why the
grading survives modulo E and not on the nose.

### 2.3 LEMMA JC-PER (the anchor system is E-periodic on the nose; OB-2)

*Statement.* For every γ ∈ W and k ≥ 0: the split satisfies
s_{j+1}(γ+kE) = s_{j+1}(γ) for all j and u_1(γ+kE) = u_1(γ) + k; hence
**φ_{γ+kE} = π^k·φ_γ as polynomials (byte-for-byte)**, and after TC-2
[φ_{γ+E}] = [φ_γ]. So u_γ ↦ [φ_γ] is well defined on ℤ/E, and (choosing window
representatives) independent of the representative.

*Proof.* By induction down the split. At the top, e_m | E, so
s_{NR}(γ+E) = (l_mγ + l_mE) mod e_m = s_{NR}(γ), and
u_{NR}(γ+E) = u_{NR}(γ) + E/e_m; hence β_{NR-1}(γ+E) = β_{NR-1}(γ) + E/e_m. The
same step at level j (with e_{j-1} | E/(e_j⋯e_m)) gives s_j unchanged and
β_{j-1} increased by E/(e_{j-1}⋯e_m); at the bottom
u_1(γ+E) = u_1(γ) + E/(e_0⋯e_m) = u_1(γ) + 1. The anchor formula then differs by
exactly one factor π. Iterate for k. ∎

*Machine:* instrument **P0-OB2 = 0/285 byte-for-byte** on every anchor of every
row (OB-2/COR-4 exact); this note's own battery re-tests it at k = 1,2,3
(family JC1).

### 2.4 LEMMA JC-FIB (which ℤ/E-indexing survives: the abscissa cosets)

*Statement.* γ ↦ (s_1(γ),…,s_{NR}(γ)) ∈ ∏_{j=0}^{m}ℤ/e_j is E-periodic and
induces a **bijection ℤ/E ≅ ∏_j ℤ/e_j**. Hence the ℤ/E-grading of JC-GAUGE is
indexed equivalently by γ mod E and by the abscissa-coset tuple — the fibred
ℤ/E-indexing of DITER_RESTATE §S3 obligation 1 (design-note G19).

*Proof.* Periodicity is JC-PER. Both sides have E elements, so it suffices to
show injectivity on [0,E). If γ,γ′ have equal tuples then s_{NR} equal forces
γ ≡ γ′ (mod e_m) (as s_{NR} = l_mγ mod e_m with l_m invertible mod e_m), and
then β_{NR-1} − β′_{NR-1} = (γ−γ′)/e_m; descending, equality of s_{NR-1} forces
(γ−γ′)/e_m ≡ 0 (mod e_{m-1}), and so on down to (γ−γ′)/(e_1⋯e_m) ≡ 0 (mod e_0),
i.e. E | γ−γ′. ∎

*Machine:* family **JC2** (tuple injectivity on E consecutive γ + periodicity);
the instrument's P4-DEG (0/29) is its weaker shadow.

### 2.5 LEMMA JC-ANCHMON (the anchor is a single Φ_m-digit)

*Statement.* For γ ∈ W: (a) Σ_{j<m}s_{j+1}·deg Φ_j < deg Φ_m; hence (b) the
Φ_m-development of φ_γ has exactly one nonzero digit, at abscissa s_{NR}(γ);
hence (c) 𝑅_γ(φ_γ) is a nonzero **constant** in K_m (slot set {0}) and
(d) deg φ_γ < (s_{NR}(γ)+1)·deg Φ_m.

*Proof.* (a) s_{j+1} ≤ e_j − 1 and deg Φ_{j+1} = e_jg_j deg Φ_j ≥ e_j deg Φ_j,
so s_{j+1}degΦ_j ≤ e_jdegΦ_j − degΦ_j ≤ degΦ_{j+1} − degΦ_j; summing over
j = 0..m−1 telescopes to ≤ deg Φ_m − deg Φ_0 < deg Φ_m. (b) φ_γ =
(π^{u_1}∏_{j<m}Φ_j^{s_{j+1}})·Φ_m^{s_{NR}} with the parenthesis of degree
< deg Φ_m by (a) — that IS the Φ_m-development. (c) The single digit sits at
abscissa s_{NR}(γ) = the line's base abscissa, so its slot index is 0; it is
nonzero and, being the only digit, is on the line (w(φ_γ) = γ). (d) Immediate
from (a),(b). ∎

### 2.6 LEMMA JC-SCAL (the scalar image: slots 0..g_m−1, and X_N is a constant)

*Statement.* For N ≡ 0 (mod E), N ≥ wΦ_{NR}, and c = Σ_{i<g_m}c_iz̄^i ∈ K
(c_i ∈ K_m, the canonical representative): (a) s_{NR}(N) = s_{NR}(0) = 0 and
the on-line slot set of Λ_N(c) is contained in {0,…,g_m−1}, with slot i digit
the ε-corrected c_i; so **𝑅_N(Λ_N(c)) is the canonical degree-<g_m
representative of c, up to one line-wise unit**; (b) 𝑅_N(X_N) is a nonzero
CONSTANT (slot set {0}); (c) consequently the "scalar image" at line N is
exactly 𝑅_N(X_N)·{K_m-polynomials of degree < g_m}.

*Proof.* s_{NR}(N) = 0 because E | N and s_{NR} is E-periodic with s_{NR}(0) = 0
(JC-PER/JC-FIB). REALIZE's construction (§1, `_realize`) expands
τ = (c_0,…,c_{g_m−1}) as Σ_i child_i·Φ_m^{k_i} with k_i = s_{NR}(N) + i·e_m and
deg child_i < deg Φ_m; hence the abscissas are exactly {i·e_m : c_i ≠ 0}, i.e.
slots i < g_m, and by R3 the packed read is c. For c = 1 only i = 0 survives, so
X_N has slot set {0} and 𝑅_N(X_N) ∈ K_m^*. (c) is (a) + (b). ∎

*Machine:* family **JC4** (slot support of Λ_N(c) and X_N; digit-to-coefficient
match); the instrument's P0-LIFT (0/138) and P0-SCAL (0/293) are its shadows.

### 2.7 THEOREM JC-SPAN (the slot span of an anchor product is the singleton {δ})

*Statement.* Let γ,γ′ ∈ W with γ+γ′ ∈ W, and let δ = δ(γ,γ′) ∈ {0,1} be the top
carry. Assume **e_m ≥ 2**. Then the on-line slot set of φ_γφ_{γ′} at its own
weight γ+γ′ is exactly **{δ}**, i.e.

    𝑅_{γ+γ′}(φ_γφ_{γ′}) = u·y^{δ}  for some u ∈ K_m^*.

If e_m = 1 (so δ = 0), the same argument gives slot set ⊆ {0,1} with 0 attained,
i.e. deg 𝑅 ≤ 1.

*Proof.* **Lower end.** By (IN-3)(e) (Cor 2.7 abscissa additivity) the minimal
on-line abscissa of φ_γφ_{γ′} is s_{NR}(γ) + s_{NR}(γ′), and the line's base
abscissa at λ = γ+γ′ is s_{NR}(λ) = s_{NR}(γ)+s_{NR}(γ′) − δe_m; so the minimal
slot is exactly ((s+s′) − (s+s′−δe_m))/e_m = **δ**, and it is attained.
**Upper end.** By JC-ANCHMON(d), deg(φ_γφ_{γ′}) < (s+1)degΦ_m + (s′+1)degΦ_m,
so the largest abscissa occurring in the Φ_m-development is ≤ s+s′+1. On-line
abscissas are ≡ s+s′−δe_m (mod e_m), so their slots k satisfy
k ≤ (s+s′+1 − (s+s′−δe_m))/e_m = δ + 1/e_m, i.e. **k ≤ δ when e_m ≥ 2**
(and k ≤ δ+1 = 1 when e_m = 1). Combining, the slot set is {δ}: a single
nonzero K_m-coefficient u at slot δ. ∎

*Comment.* This is the composite-stage replacement for CARRY-1
(φ_γφ_{γ′} = φ_{γ+γ′}ȳ^δ, last-read layer, IN-2): at a composite stage the
identity acquires **exactly one extra K_m-unit u**, and the theorem proves that
the extra factor is a unit of K_m — a scalar that TC-3 never touches — while the
y-degree is exactly δ. **The outer/inner split of c_T is therefore structural,
not a coordinate choice**: outer = the slot shift y^δ; inner = u ∈ K_m^*.

*Machine:* family **JC3** — sealed prediction: slot set of φ_γφ_{γ′} == {δ} on
every scored pair with e_m ≥ 2, and ⊆ {0,1} with 0 attained when e_m = 1.

### 2.8 THEOREM JC-LOAD (TC-3 is load-bearing EXACTLY at δ ≥ g_m)

*Statement.* Fix a pair (γ,γ′) as above with e_m ≥ 2, and consider the
**pre-TC-3** (RAW) equation in gr(w) localized and gauged but NOT quotiented by
ψ_m: does there exist c ∈ K^* with

    𝑅(φ_γφ_{γ′}·X_N) = 𝑅(Λ_N(c)·φ_{γ+γ′})   at the line γ+γ′+N ?   (RAW)

Then: **(RAW) is solvable ⟺ δ < g_m.** Equivalently (δ ∈ {0,1}): the pre-TC-3
scalar exists on every pair except those with δ = 1 ∧ g_m = 1, where the
ψ_m-relation — i.e. TC-3 — is unavoidable. Consequently:

    (a) c_T's OUTER factor z̄^δ is the image under TC-3 (y ↦ z̄) of the graded
        slot shift y^δ; it is NOT obtainable from TC-1/TC-2 alone;
    (b) c_T's INNER factor ∏_j z_j^{D_j} lies in K_m^* and needs no quotient;
    (c) the sealed set identity {no pre-TC-3 scalar} = {δ ≥ g_m} of the
        instrument (0/29 set-mismatches, 134/669 pairs) is a THEOREM, not an
        observation.
        [r1, G5 — SCOPED to the theorem's own fence.]  JC-LOAD is stated with
        e_m ≥ 2, so the THEOREM covers the 28 roster rows with e_m ≥ 2; on the
        one top-flat row (C4H, e_m = 1 — the only e_m = 1 row on the roster,
        r1 census R1-CEN) the identity is MEASURED, not proved, and is boxed at
        JC-BOX-4.  So: theorem where proved (28 rows), measured where measured
        (C4H).  The instrument's 0/29 set-mismatch count is unchanged — what is
        corrected is the r0 wording, which implied the theorem covered all 29.

*Proof.* Multiplying by X_N transports lines additively and, by (IN-3)(c) and
JC-SCAL(b), multiplies the digit polynomial by the constant 𝑅(X_N) without
changing its y-degree (offset transport, §4.2; note s_{NR}(N) = 0 so
δ(γ+γ′,N) = 0). So by JC-SPAN the LHS has digit polynomial
𝑅(X_N)·u·y^δ, of exact y-degree δ; by JC-SCAL(a)(c) the RHS ranges exactly over
𝑅(X_N)·{polynomials of degree < g_m} as c ranges over K^*. Since K_m[y] is a
polynomial ring, u y^δ (u ≠ 0) equals a polynomial of degree < g_m iff δ < g_m.
For (a): after TC-3 the class of y^δ is z̄^δ, and by §3.2 the value of the
constant is c_T = z̄^δ·u; the pre-TC-3 object y^δ is not in the K_m-span of
{y^i}_{i<g_m} when δ ≥ g_m, so no relabeling of scalars produces it. ∎

*Honest fence.* The proof of the ⟸ direction rides the offset-transport step
(§4.2), which rides (IN-3)(c); the ⟹ direction (the obstruction) rides only
JC-SPAN + JC-SCAL. The instrument's k-distribution **{0 : 669}** says the
π-clearing ladder is never needed on its roster: the canonical division by
Φ_{m+1} alone discharges TC-3 there.

### 2.9 COROLLARY JC-PSIKER (TC-3 is not a relabeling: the ψ-kernel, witnessed)

*Statement.* At every stage the level-NR read is **non-injective on a graded
piece**: with λ := wΦ_{NR} = e_mg_mγ_{m+1},

    𝑅_λ(Φ_{m+1}) = ψ_m(y) ≠ 0   in K_m[y],  but  read(λ, Φ_{m+1}) = ψ_m(z̄) = 0,

so in(Φ_{m+1}) ≠ 0 in gr_λ lies in the kernel of the read; and (when λ ∈ W, so
that the anchor φ_λ exists — otherwise use the π-translate) Φ_{m+1} + φ_λ and
φ_λ are two elements of gr_λ with equal reads and different classes. ~~Hence
TC-3 has a nonzero kernel on every graded piece (namely ψ_m·Δ under the anchor
coordinate) and **cannot be a relabeling of scalars.**~~

**[r1, F2 — CRITICAL (PE1): that closing sentence is OVER-QUANTIFIED, and is
replaced by the exact range. The witness above is UNCHANGED and correct.]**
PE1's finding, in one line: `𝔦 := in(Φ_{m+1})·gr(w)` is homogeneous with a
single generator of degree wΦ_NR, so its degree-λ part is
`𝔦 ∩ gr_λ = in(Φ_{m+1})·gr_{λ−wΦ_NR}`, and weights are ≥ 0 on O[x] — hence the
kernel is **ZERO whenever λ < wΦ_NR**, which is the case at the window base G0
on **29/29 roster rows** (C2A 4 < 10, C2I 4 < 20, C3G 200 < 222, C4C 312 < 346,
C4H 60 < 81, I4A 156 < 204; PE1 §CRITICAL 2, reproduced as r1 family
R1-PSIK-LO). The corrected statement, in three clauses:

    (i)   [WITNESS — unchanged, PROVED] at λ = wΦ_NR the display above holds:
          𝑅_λ(Φ_{m+1}) = ψ_m(y) ≠ 0 while read(λ,Φ_{m+1}) = ψ_m(z̄) = 0.
    (ii)  [EXACT RANGE on gr] for λ ∈ W, 𝔦 ∩ gr_λ = in(Φ_{m+1})·gr_{λ−wΦ_NR},
          which is ZERO for every λ < wΦ_NR and NONZERO for every
          λ ∈ wΦ_NR + W (the anchor φ_{λ−wΦ_NR} supplies the element, and
          gr(w) is a domain).  Under the note's standing convention that
          gr_γ = 0 off the window (JC-BOX-7) the range is exactly
          W ∩ (wΦ_NR + W).
    (iii) [THE FORM §2.10 CONSUMES — PROVED] after TC-1 the kernel is nonzero on
          EVERY graded piece: 𝔦^B ∩ B_n = in(Φ_{m+1})·B_{n−wΦ_NR} ≅ ψ_m(y)·Δ
          ≠ 0 for every n ∈ ℤ, because in(π) is a unit in B and hence
          B_j ≅ B_{j+E} for all j — no piece of B is zero.  So TC-3 **cannot be
          a relabeling of scalars** on the object TC-3 is actually applied to.

Nothing downstream used the refuted universal form on gr: §2.10 [r1, F1] now
states and consumes (iii). W-6(v)'s own wording ("the level-NR read is
non-injective **on a graded piece**, with the classifier's own next key Φ_{m+1}
as the kernel witness") was already correct as written and stands unamended.

*Machine (r1 §9.3):* **R1-PSIK-LO** (no class at a line λ < wΦ_NR is certified
dead by TC-3, on every row — the zero half, with the certifier's disclosed
one-sidedness) + **R1-PSIK-HI** (the witness Φ_{m+1}·φ_{λ−wΦ_NR} at one line per
residue class ν ∈ ℤ/E: w exact, digit polynomial ∝ ψ_m, read 0, death
certified) + tooth **T1** (the refuted universal claim, which must fire on every
row).

*Proof.* Φ_{m+1} = Φ_m^{e_mg_m} + Σ_{k<g_m}C_kΦ_m^{e_mk} with
w(C_kΦ_m^{e_mk}) = λ for every k with ψ_{m,k} ≠ 0 (REALIZE's construction of
C_k at weight (g_m−k)γ_{m+1}, [ILN]† S0.1) — that is the defining property of the
key polynomial: all its terms sit on the λ-line, its slot digits are the
coefficients of ψ_m, and w(Φ_{m+1}) = λ exactly (the corpus's own wΦ gate). So
𝑅_λ(Φ_{m+1}) = ψ_m(y) ≠ 0 while its evaluation at z̄ is ψ_m(z̄) = 0. The read is
additive on a fixed line, giving the second display. ∎

*Instrument corroboration (independent):* the build-phase disclosure that the
naive class identity [π·Λ_N(c)] = [Λ_{N+E}(c)] is **FALSE** — two weight-(N+E)
lifts with the same read need not be the same class — is the same phenomenon
measured from the other side, and is why the instrument's offset clause (P2-OFF,
0/116) is stated on the CONSTANTS.

*Machine:* family **JC6** (the Φ_{m+1} kernel witness: w exact, read 0, slot
digits = ψ_m's coefficients) + tooth **MJ4**.

### 2.10 [r1, F1] What TC-3 IS in this note, and WHERE the coordinate calculus lives (the post-TC-1 pieces B_n)

**[r1, F1 — CRITICAL (PE1). The r0 text stated the coordinate calculus on
gr_λ(w), where it is FALSE; it is restated here on this note's own B_n, where it
is proved. The struck r0 wording, verbatim:]**

> ~~Two facts fix the coordinate calculus used from here on. Both are named
> inputs, not new claims.~~
>
> ~~**(COORD)** For λ ∈ W the digit map 𝑅_λ : gr_λ(w) → Δ := K_m[y] is a
> K_m-linear **isomorphism**, carrying in(φ_λ) to a nonzero constant
> a_λ ∈ K_m^* (JC-ANCHMON(c)). Injectivity is definitional (§1: 𝑅_λ(f) = 0 ⟺
> w(f) > λ); surjectivity/rank-one is (IN-3)(c) — FGMN Thm 4.2's freeness of
> gr_λ over Δ on the anchor basis.~~

**Why the r0 statement is false (the slot bound).** §1's ambient ring is O[x]:
w_0 is the coefficientwise π-valuation on INTEGRAL polynomials, and the window
W = {γ : u_1(γ) ≥ 0} together with the anchors φ_γ = π^{u_1}∏Φ_j^{s_{j+1}} exist
precisely to keep the π-exponent ≥ 0. Hence every Φ_m-digit A_a of an f in the
ring has w_m(A_a) ≥ 0, so an on-line abscissa at level λ satisfies
e_m·w_m(A_a) + a·γ_{m+1} = λ with w_m(A_a) ≥ 0, i.e. a·γ_{m+1} ≤ λ. Writing

    maxslot(λ) := ⌊(⌊λ/γ_{m+1}⌋ − s_NR(λ))/e_m⌋,

the on-line slot set at λ is contained in {0,…,maxslot(λ)}: **gr_λ is a
FINITE-dimensional K_m-space**, 𝑅_λ is NOT onto K_m[y], and
gr_λ/(𝔦 ∩ gr_λ) is not a 1-dimensional K-space. At this note's own window base
maxslot(G0) = **0 on 29/29 roster rows** (r1 family R1-BND; PE1 §CRITICAL 1
measured the same, and sampled 3,072 integral f with w(f) = 4 on row C2I —
m = 1, E = 4, g_m = 2, e_m = 2, γ_{m+1} = 5, wΦ_NR = 20, G0 = 4 — finding slot
set {0} throughout and 𝔦 ∩ gr_4 = 0, so gr_4 ≅ K_m while [K:K_m] = g_m = 2).

**Why the literature is NOT at fault, and where the repair lives.** FGMN's
Δ ≅ K_m[y] is the degree-0 part of the graded algebra of a MacLane valuation on
**K[x]** — π INVERTED — and that object is exactly what JC-DOM (§2.1) builds one
page earlier: `B := gr(w)[in(π)^{-1}]`, `B_n = ∪_{k≥0}in(π)^{-k}gr_{n+kE}`. So
the coordinate calculus — (COORD-B)/(MULT-B) below — and TC-3 belong strictly
AFTER TC-1, on B **[r2, G-4: this sentence formerly named the struck
(COORD)/(MULT) here]**. Four lemmas do it. Note
that this makes the note's literature footprint SMALLER, not larger: the
surjectivity half becomes a theorem of this note (JC-BSURJ, from REALIZE-(m)),
and the only cited input left in the coordinate calculus is the multiplicativity
(DMULT) **[r2, G-1: in its citable tier (DMULT-w); the exact tier (DMULT-s) is
MEASURED, not cited — see the split below]**.

**LEMMA JC-LOC [r1] (B *is* the object FGMN's theorems speak about).** Write
gr^O(w) for §1's graded ring (built on O[x]) and gr^K(w) for the same
construction on K[x] = O[x][π^{-1}], with w extended by w(π^{-k}g) := w(g) − kE.
Then the degreewise map

    B = gr^O(w)[in(π)^{-1}] → gr^K(w),   in(π)^{-k}·in(g) ↦ in(π^{-k}g),

is an isomorphism of ℤ-graded rings. In particular B_n ≅ gr^K_n(w) for every
n ∈ ℤ, and B_0 ≅ the degree-0 subring of gr^K(w).

*Proof.* Well defined: if in(π)^{-k}in(g) = in(π)^{-k'}in(g′) in B then
in(π^{k'}g) = in(π^{k}g′) in gr^O, i.e. w(π^{k'}g − π^{k}g′) > w(π^{k'}g), which
after dividing by π^{k+k'} is the corresponding statement in gr^K. Graded and
multiplicative by in(fg) = in(f)in(g) ((IN-3)(b)) and w(π) = E (JC-DOM).
Surjective in degree n: any f ∈ K[x] with w(f) = n has π^kf =: g ∈ O[x] for some
k ≥ 0, and then w(g) = n+kE and f's class is the image of in(π)^{-k}in(g).
Injective: in(π)^{-k}in(g) with w(g) = n+kE maps to the class of π^{-k}g, which
is nonzero in gr^K_n because w(π^{-k}g) = n exactly. **[r2, G-6 — additivity of
the degreewise map, previously unchecked (needed because homogeneous elements
are in(f) or 0, and sums can drop degree):** bring two degree-n elements to a
common denominator k; then in(π)^{-k}in(g) + in(π)^{-k}in(g′) is
in(π)^{-k}·(in(g)+in(g′)), and in gr^O the sum in(g)+in(g′) is in(g+g′) if
w(g+g′) = n+kE and 0 if w(g+g′) > n+kE. The image is the class of
π^{-k}(g+g′) in gr^K_n, which by the extension formula is nonzero exactly when
w(g+g′) = n+kE and zero when w(g+g′) > n+kE — the SAME dichotomy, so the map
carries sums to sums in both cases.**]** ∎

**[r2, G-6 — the identification of the extension with the LITERATURE's
valuation, previously asserted by the phrase "the same construction on K[x]";
now derived in three displayed steps, PE2 GAP 6.]** JC-LOC as stated proves
B ≅ gr of *this note's own* extension `w(π^{-k}g) := w(g) − kE`. What licenses
"B *is* the object FGMN's theorems speak about" is that this extension IS the
valuation the literature puts on K[x]:

    (G6-1) THE EXTENSION IS FORCED.  Every f ∈ K[x] is π^{-k}g with g ∈ O[x],
           and any valuation w^K on K[x] restricting to w with w^K(π) = E
           (JC-DOM) must satisfy w^K(π^{-k}g) = w(g) − kE.  Well-defined: if
           π^{-k}g = π^{-k′}g′ (k′ ≥ k) then g′ = π^{k′−k}g, and w(πf) =
           w(π) + w(f) ((IN-3)(a)) gives w(g′) − k′E = w(g) − kE.  So there is
           exactly ONE candidate, the displayed one.
    (G6-2) §1's MIN-FORMULA COMPUTES IT ON ALL OF K[x], i.e. the extension is
           the same MacLane recursion evaluated on K-coefficients: the
           Φ_j-development of π^{-k}g is π^{-k}·(the development of g), and by
           induction on j, w_{j+1}(π^{-k}f) = min_a(e_jw_j(π^{-k}A_a) +
           aγ_{j+1}) = w_{j+1}(f) − k·e_0⋯e_j for every f ∈ O[x] with digits
           A_a (base: w_0 is the coefficientwise π-valuation, which drops by
           exactly k).  At j = m this is the extension formula.  So gr^K(w) is the graded ring of the MacLane
           min-formula valuation on K[x] — the object of FGMN's graded package
           — not of an ad-hoc extension.
    (G6-3) IT IS A VALUATION.  Multiplicative: w(π^{-k}g·π^{-k′}g′) =
           w(gg′) − (k+k′)E by (IN-3)(a) on O[x].  Ultrametric: clear π-powers
           to a common k; on O[x] the min-formula satisfies w(g+g′) ≥
           min(w(g), w(g′)) (developments add termwise and min is
           subadditive), and subtracting kE preserves it.

*Honest residue of this derivation (unchanged input, not a new one).* Steps
G6-1..3 identify the extension with **the min-formula valuation on K[x] in the
harness normalization**. The remaining tie — that §1's recursion (the harness
w = w_{m+1}, sheared frame) is the literature's inductive valuation v_{m+1},
and 𝑅 its residual-polynomial operator up to the line-wise unit — is exactly
**(IN-3)'s W-1 transport clause, already priced in §0's stack** (and the
subject of the open dictionary TR-3′-GEN quoted at [r2, G-1] below). G-6 adds
no new conditionality; it removes the "same construction" hand-wave.

*What this settles.* The r0 text transported FGMN Thm 4.2 to gr^O, where its
conclusion is refuted by §1's own arithmetic; Thm 4.2 is a statement about
gr^K. By JC-LOC the note HAS gr^K — it is TC-1's output — so the citation is
now APPLIED to the object it is about (JC-BOX-3 re-cut accordingly, §8).

**LEMMA JC-PIINV [r1] (the digit polynomial is π-equivariant; the colimit
coordinate is well defined).** For every λ ∈ ℤ and every f ∈ O[x] with
w(f) ≥ λ:

    (a) the on-line abscissas and slot indices at (λ+E, πf) are exactly those
        at (λ, f);
    (b) there is a constant c_π ∈ K_m^*, depending only on T, with
        𝑅_{λ+E}(π f) = c_π·𝑅_λ(f);
    (c) hence, with ρ_λ := 𝑅_λ/a_λ and a_λ := 𝑅_λ(φ_λ) ∈ K_m^* (JC-ANCHMON(c)),
        ρ_{λ+E}(π f) = ρ_λ(f)  EXACTLY, for λ, λ+E ∈ W.

*Proof.* (a) deg(πA) = deg A, so the Φ_m-development of πf is the development of
f multiplied coefficientwise by π; w_m(πA) = w_m(A) + w_m(π) = w_m(A) + E/e_m,
and s_NR(λ+E) = s_NR(λ) because e_m | E (JC-PER). The on-line condition at λ+E
for the digit πA_a, e_m(w_m(A_a) + E/e_m) + aγ_{m+1} = λ+E, is the on-line
condition at λ for A_a; the slot index (a − s_NR)/e_m is unchanged.
(b) By (a) only the digit VALUES can move. §1's digit at slot j is
C_j = ε_m(β_j)·read_m(β_j, A_{a_j}) with β_j the digit's own level-m weight, and
two facts hold by induction down the levels: (i) read_j(β + w_j(π), πA) =
c^{(j)}·read_j(β, A) with c^{(0)} = 1 (at level 0 the residue of πc at the
shifted weight IS the residue of c) and c^{(j)} = embed(δ_{j−1}·c^{(j−1)});
(ii) ε_j(β + w_j(π)) = ε_j(β)·δ_j with δ_j := z_j^{−l_{j−1}w_{j−1}(π)} (and
δ_0 := 1), because ε_j(β) = z_j^{lp_{j−1}s − l_{j−1}u} for (s,u) = eq-(12)(β,
e_{j−1}, h_{j−1}) and shifting β by w_j(π) — a multiple of e_{j−1} — leaves s
fixed and increases u by w_j(π)/e_{j−1} = w_{j−1}(π). Both corrections are
independent of the slot and of β, so the whole digit polynomial is multiplied by
the single constant c_π := δ_m·c^{(m)} ∈ K_m^*. (c) JC-PER gives
φ_{λ+E} = π·φ_λ byte-for-byte, so a_{λ+E} = c_π·a_λ by (b) and c_π cancels. ∎

*Machine (r1 §9.3):* family **R1-PER** — 𝑅_{λ+kE}(π^kf) = c_π^k·𝑅_λ(f) with one
c_π per row and ρ exactly invariant, k = 1,2, on every row (measured
~~c_π ∈ {1, z̄, z̄²} across the roster~~ **[r2, G-3: that was the PRE-SEAL 6-ROW
SMOKE's value set mislabelled "across the roster"; the as-of-r1 ROSTER value
set, from the committed artifact `grt_jc_r1_results.json` (R1-CEN `c_pi`
column), is c_π ∈ {1, z̄, z̄², z̄³, z̄⁴, z̄⁶, z̄⁸} — 1 on 9 rows, z̄ on 9, z̄² on 7,
and z̄³/z̄⁴/z̄⁶/z̄⁸ on the single rows C2G/C3H/C2H/I4C]**: a nontrivial constant,
which is exactly why the ρ-normalization is the one that makes the colimit
well defined).

**LEMMA JC-BSURJ [r1] (the colimit coordinate is ONTO Δ — proved, not cited).**
Fix n ∈ W and p = Σ_{j≤d}c_jy^j ∈ Δ = K_m[y]. For every k with

    (n + kE) − (s_NR(n) + d·e_m)·γ_{m+1}  ≥  e_m·wΦ_m

there is an INTEGRAL f with w(f) = n+kE and 𝑅_{n+kE}(f) = p on the nose; only
finitely many k are excluded. Hence ρ^B_n := colim_k ρ_{n+kE} : B_n → Δ is
SURJECTIVE, while ρ_n itself is not (its image has degree ≤ maxslot(n), which is
0 at every roster row's base).

*Proof.* Put λ := n+kE, s := s_NR(λ) = s_NR(n) (JC-PER), a_j := s + j·e_m and
β_j := (λ − a_jγ_{m+1})/e_m. Each β_j is an INTEGER: γ_{m+1} = e_mwΦ_m + h_m ≡
h_m and λ ≡ s·h_m (mod e_m) by eq-(12), so λ − a_jγ_{m+1} ≡ s h_m − (s+je_m)h_m
≡ 0. The displayed inequality is β_d ≥ wΦ_m, and β_j decreases in j, so
β_j ≥ wΦ_m for all j ≤ d: REALIZE-(m) (IN-5, laws R1/R2/R3) supplies
A_j := realize(m, ε_m(β_j)^{-1}c_j, β_j) with deg A_j < deg Φ_m, w_m(A_j) = β_j,
read_m(β_j,A_j) = ε_m(β_j)^{-1}c_j (skip the j with c_j = 0). Put
f := Σ_j A_jΦ_m^{a_j}. Since deg A_j < deg Φ_m this IS the Φ_m-development of f,
so w(f) = min_j(e_mβ_j + a_jγ_{m+1}) = λ — every digit is ON the line — and the
slot-j digit is ε_m(β_j)·read_m(β_j,A_j) = c_j by §1's read definition. Hence
𝑅_λ(f) = p. Since β_j grows by E/e_m per k-step, all d+1 conditions hold for all
large k. The last clause is the slot bound above. ∎

*Machine (r1 §9.3):* **R1-SURJ** (targets of y-degree 0,1,2 realized at the
predicted k, with 𝑅 equal to the target on the nose, every row) and **R1-BND**
(maxslot(G0) = 0 on 29/29 — the r0 statement's own refutation, and the reason
the k-shift is structural rather than a convenience) + tooth **T2** ("no k-shift
needed", which must fire on every row).

**(COORD-B) [r1 — REPLACES (COORD)].** Fix ν ∈ ℤ/E and n ∈ W with n ≡ ν (mod E);
Δ := K_m[y].

    (1) [PROVED at general m, in this note]  ρ^B_n : B_n → Δ,
        in(π)^{-k}α ↦ ρ_{n+kE}(α), is a well-defined (JC-PIINV(c)), injective
        (§1: 𝑅_λ(f) = 0 ⟺ w(f) > λ, compatibly along the system) and surjective
        (JC-BSURJ) K_m-linear map, with ρ^B_n(in φ_n) = 1.  Moreover in(π) is a
        unit in B of degree E, so B_j ≅ B_{j+E} for EVERY j ∈ ℤ: after TC-1 no
        graded piece is zero and the window restriction disappears.
    (2) [PROVED at general m from (1) + (DMULT-w) — the CITABLE tier suffices,
        [r2, G-1]]  B_0 ≅ Δ as K_m-ALGEBRAS via
        ρ^B_0, and B_n is FREE OF RANK ONE over B_0 ≅ Δ on in(φ_n), with ρ^B_n
        the coordinate of that module structure.

**(DMULT) [r1 — the one cited input of the coordinate calculus] [r2, G-1 —
SPLIT INTO TWO HONEST TIERS; the r1 status line is struck below].** For
f,g ∈ O[x] with λ := w(f), μ := w(g):

    𝑅_{λ+μ}(fg) = y^{δ(λ,μ)}·𝑅_λ(f)·𝑅_μ(g),
    δ(λ,μ) := (s_NR(λ) + s_NR(μ) − s_NR(λ+μ))/e_m ∈ {0,1}.

This is the composite-stage form of (IN-2)'s (W-MULT) — stated there at the
last-read layer — and of Montes/FGMN residual-polynomial multiplicativity; via
JC-LOC it is the content of (IN-3)(c) on the object (IN-3)(c) is about. ~~It is
**CITED, not proved here**~~ **[r2, G-1: PE2 caught that r1 labelled the EXACT
(multiplier-1) display "CITED" while §0's own transport statement can only
deliver it up to a line-wise unit — and simultaneously called the exactness "a
finding of the r1 battery". The honest form is two tiers:]**

**(DMULT-w) [the citable tier — DERIVED from the citation + §0's transport].**
There is a unit ω(λ,μ) ∈ K_m^*, independent of f and g, with

    𝑅_{λ+μ}(fg) = ω(λ,μ)·y^{δ(λ,μ)}·𝑅_λ(f)·𝑅_μ(g).

*Derivation (displayed, the step r1 skipped).* The literature identity is
stated for the FGMN operator R^{GMN}; (IN-3)'s transport clause is
𝑅_λ = c_λ·R^{GMN}_λ with c_λ a LINE-WISE unit (W-1). Substituting,

    𝑅_{λ+μ}(fg) = c_{λ+μ}·R^{GMN}_{λ+μ}(fg)
                = c_{λ+μ}·y^δ·R^{GMN}_λ(f)·R^{GMN}_μ(g)
                = (c_{λ+μ}/(c_λc_μ))·y^δ·𝑅_λ(f)·𝑅_μ(g),

so ω(λ,μ) = c_{λ+μ}/(c_λc_μ) — the 2-coboundary of the line-wise unit system.
That ω depends only on the lines is what the transport gives; nothing gives
ω ≡ 1.

**(DMULT-s) [the exact tier — MEASURED, NOT CITED].** ω(λ,μ) ≡ 1, i.e. the
display at the top holds with multiplier exactly 1. *Status:* **MEASURED**
(R1-DMULT 2,784/0 with tooth T3; §9.3 finding 1 "multiplier exactly 1"; r2's
bilinear leg R2-BIL/R2-PHI, §9.4) and **not cited**: the r2 attempt to locate
a multiplier-1 statement for the harness 𝑅 in the sources the note names
FAILED reportably — (IN-3) itself prices the transport at "c a line-wise
unit", and the corpus's sharpest harness↔literature read dictionary, **open
lemma TR-3′-GEN** (`GRB_ORDER2_2026-08-05.md` §S3.4, statement of record:
*"a level-by-level compatible family of identifications σ_j … together with
per-argument units, under which the FGMN side-read operator corresponds to
the project/GMN-convention R_λ"*), is stated WITH per-argument units even
where closed, and is OPEN beyond {all order-2} ∪ {two order-3 strata}. So no
corpus-pinned citation delivers ω ≡ 1; proving it would mean proving the
ε-kit's unit system multiplicative (c_{λ+μ} = c_λc_μ), which this note does
not do. The standing printed-source Codex leg (JC-BOX-3 item 2) rides
unchanged.

**Who consumes which tier (checked by PE2, GAP 1 blast radius).** (COORD-B)(2),
(MULT-B), JC-CARRY-m, W-8 and JC-BOX-4's [r1] corner closure need only
**(DMULT-w)**, and the mechanism is one line: the normalized coordinate
ρ_λ = 𝑅_λ/a_λ with a_λ = 𝑅_λ(φ_λ) is **invariant under ANY line-wise
rescaling of 𝑅** (the unit c_λ cancels between numerator and denominator), so
the whole ρ-calculus can be run in the R^{GMN} gauge, where the cited identity
is exact; equivalently, ω is absorbed into the anchor cocycle A(λ,μ), and the
monomial-shape/degree-δ statements are ω-blind. Riding **(DMULT-s)** and
downgraded with it: COROLLARY JC-COB's sharp value u = a_γa_{γ′} FOR THE
HARNESS constants a (and its §4.1 restatement and second half) — on (DMULT-w)
alone it degrades to JC-SPAN's already-proved u ∈ K_m^*. No clause GRADE
changes between tiers.

(DMULT-w) is now the ONLY literature input of §§2.10–5's coordinate calculus
(JC-BOX-3). *Machine (r1 §9.3):* family **R1-DMULT** tests the exact-tier
identity (DMULT-s) on sampled pairs on every row, with tooth **T3** (the
y^{δ+1} mutation) — the leg PE1 correctly noted the r0 battery and the
instrument did not have; **[r2, G-2]** its samples are monomial-dominated
(disclosure at §9.3), and the genuinely bilinear leg is r2's **R2-BIL** (§9.4).

*Proof of (2) from (1) + (DMULT-w) [r2, G-1 — re-run on the citable tier].*
Represent t ∈ B_0 at a line kE (so
s_NR(kE) = 0, JC-FIB) and β ∈ B_n at a line n+k′E. Then δ(kE, n+k′E) = 0, so
(DMULT-w) gives 𝑅(tβ) = ω·𝑅(t)𝑅(β) with ω = ω(kE, n+k′E) depending on the
LINES only; dividing by the anchor constants this reads
ρ^B_n(tβ) = κ·ρ^B_0(t)·ρ^B_n(β) with κ := ω·a_{kE}a_{n+k′E}/a_{n+(k+k′)E},
again line-dependent only. **The in-note lemmas pin κ = 1** [r2, G-1]: take
t = in(φ_{kE}) = in(π^k) (the anchor at line kE, JC-PER); then
ρ^B_0(t) = 1 and ρ^B_n(π^kβ) = ρ^B_n(β) EXACTLY by JC-PIINV(c) (proved, not
cited), so κ·1·ρ^B_n(β) = ρ^B_n(β) for a β with ρ^B_n(β) ≠ 0 forces κ = 1 —
for every representative line pair, since κ never saw t or β. Hence
ρ^B_n(tβ) = ρ^B_0(t)·ρ^B_n(β) for the B_0-action on B_n and, at n = 0,
multiplicativity of ρ^B_0 (using a_0 = 𝑅_0(φ_0) = 1, φ_0 = 1, 0 ∈ W). So
ρ^B_0 : B_0 → Δ is a bijective K_m-algebra map
(bijective by (1)), and for β ∈ B_n the element t ∈ B_0 with ρ^B_0(t) = ρ^B_n(β)
satisfies ρ^B_n(t·in φ_n) = ρ^B_0(t)·1 = ρ^B_n(β), hence β = t·in φ_n by
injectivity: B_n = Δ·in(φ_n), free of rank one because ρ^B_n is injective. ∎

~~**(MULT)** in(fg) = in(f)in(g) ((IN-3)(b)) plus (COORD) give a unique **anchor
cocycle** A(λ,μ) ∈ Δ with ρ_{λ+μ}(αβ) = A(λ,μ)·ρ_λ(α)·ρ_μ(β) … for α ∈ gr_λ,
β ∈ gr_μ, λ,μ,λ+μ ∈ W.~~

**(MULT-B) [r1 — REPLACES (MULT); the object is B, and the input is the Δ-MODULE
half, not mere K_m-linearity].** in(fg) = in(f)in(g) ((IN-3)(b)) plus
(COORD-B)(2) give a unique **anchor cocycle** A(λ,μ) ∈ Δ with

    ρ^B_{λ+μ}(αβ) = A(λ,μ)·ρ^B_λ(α)·ρ^B_μ(β),  A(λ,μ) = ρ^B_{λ+μ}(in φ_λ·in φ_μ),

for α ∈ B_λ, β ∈ B_μ and **all λ,μ ∈ ℤ**. ~~(window representatives are used
only to name the anchors; by (COORD-B)(1) every class mod E has one)~~
**[r2, G-5 — the all-of-ℤ quantifier was licensed by a parenthesis; here is
the explicit transport step it stands on.** ρ^B and the anchors are DEFINED
only on the window W (off it, gr_γ = 0 and no anchor exists — JC-BOX-7). The
extension to all of ℤ is two displayed definitions, each k-independent:

    (G5-i)  VIRTUAL ANCHOR.  For λ ∈ ℤ choose k ≥ 0 with λ+kE ∈ W (all large
            k qualify) and set  in φ_λ := in(π)^{-k}·in(φ_{λ+kE}) ∈ B_λ.
            k-independence: for k ≤ k′ with both lines in W, JC-PER gives
            φ_{λ+k′E} = π^{k′−k}·φ_{λ+kE} byte-for-byte, so the two candidates
            differ by in(π)^{-(k′−k)}in(π^{k′−k}) = 1 in B.
    (G5-ii) ρ^B OFF THE WINDOW.  ρ^B_λ := ρ^B_{λ+kE} ∘ (in π)^k (multiply into
            a window line, read there).  k-independence is exactly
            JC-PIINV(c): ρ is π-invariant on the nose.

With (G5-i)/(G5-ii), every statement below quantified over λ, n ∈ ℤ reads the
virtual anchors and the transported ρ^B; on W they agree with the original
definitions (k = 0).**]** By JC-SPAN,
A(λ,μ) = (u/a_{λ+μ})·y^{δ(λ,μ)} with u ∈ K_m^*, so **A is a MONOMIAL of y-degree
exactly δ** (e_m ≥ 2).

*Proof.* Write α = ρ^B_λ(α)·in φ_λ and β = ρ^B_μ(β)·in φ_μ with the coefficients
in Δ ≅ B_0 acting through the module structure of (COORD-B)(2); multiply in the
commutative graded ring B and read off the coordinate at λ+μ. **This is the step
the r0 text skipped**: a K_m-linear isomorphism gr_λ ≅ Δ transports the
multiplication to *some* K_m-bilinear map Δ × Δ → Δ, and only Δ-BILINEARITY —
i.e. compatibility with the degree-0 action, (COORD-B)(2) — makes that map
"multiply and scale by A(λ,μ)". ∎

**[r2, G-4 — the gr-level restriction, recorded once so the proof bodies can
cite it.]** For α ∈ gr_λ ⊆ B_λ and β ∈ gr_μ ⊆ B_μ one has αβ ∈ gr_{λ+μ}
((IN-3)(b)) and ρ^B_λ|_{gr_λ} = ρ_λ (the k = 0 term of the colimit), so
(MULT-B) restricted to the gr-pieces reads ρ_{λ+μ}(αβ) = A(λ,μ)ρ_λ(α)ρ_μ(β) —
the identity the proofs of §3.2, §4.1, §4.2 and §5 apply at gr level. Those
proofs formerly invoked it under the STRUCK name (MULT); every such site is
re-pointed at r2 to **(MULT-B)|gr, this display** (sweep record §9.5).

**COROLLARY JC-COB [r1] (what the slot-δ unit u actually is) [r2, G-1 —
re-fenced onto the EXACT tier].** On ~~(DMULT)~~ **(DMULT-s)**:
A(λ,μ) = (a_λa_μ/a_{λ+μ})·y^{δ(λ,μ)}, i.e. JC-SPAN's unit is
**u = a_λ·a_μ** — the product of the two anchors' own digit constants. Hence the
structure constant of §3.2 is c_{m+1}(γ,γ′) = (a_γa_{γ′}/a_{γ+γ′})·z̄^δ: the
INNER factor is exactly the **coboundary of the anchor normalization**, and (on
[ILN]†'s scored stratum, composing with §3.3) ∏_{j≤m}z_j^{D_j} =
a_γa_{γ′}/a_{γ+γ′}. *Fences [r2, G-1]:* this rides **(DMULT-s), the MEASURED
tier** — on the citable (DMULT-w) alone the sharp values here degrade to
JC-SPAN's u ∈ K_m^* — and the second half additionally rides [ILN]†; it does
NOT trivialize the (CYC) property, which is a statement about
the ANCHOR-INDEXED presentation and is invariant under nothing (§6, JC-F1), and
it re-scores no measured verdict. *Machine (r1 §9.3):* family **R1-COB** tests
𝑅_{γ+γ′}(φ_γφ_{γ′}) == a_γa_{γ′}y^δ exactly on the full anchor grid of every row
— a sharp, falsifiable consequence of ~~(DMULT)~~ **[r2, G-1] (DMULT-s)**: a
failure with the slot set still {δ} would refute only the exact tier (ω ≢ 1),
while a failure of the SLOT-SET half would refute (DMULT-w), (COORD-B)(2) and
with them the repair.

**TC-3 = the quotient by the homogeneous ideal 𝔦^B := in(Φ_{m+1})·B** (this is
exactly what the instrument's certifier operationalizes as division by Φ_{NR}),
taken on B, i.e. **strictly after TC-1**. ~~[r0: "𝔦 := in(Φ_{m+1})·gr(w) … Hence
for every λ ∈ W, gr_λ/(𝔦 ∩ gr_λ) ≅ Δ/(ψ_m) = K, a ONE-dimensional K-space",
with the π-translate hedge "if wΦ_{NR} ∉ W replace Φ_{m+1} by π^kΦ_{m+1}"]~~ —
struck at [r1, F1]: on gr the intersection is 0 below wΦ_NR (§2.9 [r1, F2]) and
the quotient is not a K-line. On B, by (COORD-B)+(MULT-B),

    𝔦^B ∩ B_n = in(Φ_{m+1})·B_{n−wΦ_NR}  corresponds to  ψ_m(y)·Δ,

because ρ^B(in Φ_{m+1}·β) = A·ψ_m(y)·ρ^B(β) with
ρ^B(in Φ_{m+1}) = ψ_m(y)/a_{wΦ_NR} (JC-PSIKER(i)'s computation; **[r2, G-5]**
the line wΦ_NR IS in W — it is attained by Φ_{m+1}, JC-PSIKER's own weight
computation, so the anchor a_{wΦ_NR} exists with no virtual-anchor step —
while the quantifiers "every n" below read the (G5-i)/(G5-ii) transport) and
B_{n−wΦ_NR} ≠ 0 for every n (COORD-B(1)) — the π-translate hedge is no longer
needed, since in(π) is a unit in B. Hence for **every n ∈ ℤ** (via
(G5-i)/(G5-ii), no longer a parenthesis)

    B_n/(𝔦^B ∩ B_n)  ≅  Δ/(ψ_m)  =  K_{m+1} = K       (via y ↦ z̄),

a ONE-dimensional K-space with basis the image of in(φ_n). This is the precise
sense in which TC-3 turns the Δ-coordinate into a K-scalar — and JC-PSIKER(iii)
says its kernel ψ_m·Δ ≠ 0 on every piece of B, so no relabeling can replace it.
Write 𝒜 := (B/(in(π)−1))/image(𝔦^B) for the TC-transported ring; it is
ℤ/E-graded (JC-GAUGE(ii), and 𝔦^B is generated by ONE homogeneous element, so
its image is a graded ideal) with 𝒜_ν = A_ν/(𝔦 ∩ A_ν) ≅ K·[φ_{γ_ν}] and
𝒜_0 = K. **[r2, G-9 — the ideal transport along JC-GAUGE(iii), the one-line
step PE2 found unwritten: 𝒜_ν ≅ K needs JC-GAUGE(iii)'s ADDITIVE isomorphism
σ : A_ν ≅ B_n to carry image(𝔦^B) ∩ A_ν onto 𝔦^B ∩ B_n, which additivity alone
does not give. It does carry it:** with σ(Σ_k b_{n+kE}) = Σ_k ϑ^{-k}b_{n+kE}
(ϑ = in π), σ(𝔦^B ∩ B^{(ν)}) = Σ_k ϑ^{-k}(𝔦^B ∩ B_{n+kE}) ⊆ 𝔦^B ∩ B_n because
𝔦^B is an IDEAL of B and ϑ^{-k} ∈ B; the reverse inclusion is the k = 0 term.
So B_n/(𝔦^B ∩ B_n) ≅ A_ν/(image(𝔦^B) ∩ A_ν) = 𝒜_ν, which is what the display
above and §3.1 consume.**]**

**[r1] THE FIVE CONSUMERS, RE-DERIVED ONE BY ONE.** PE1 listed exactly five
places that consumed the refuted r0 form. Each is re-derived on (COORD-B); none
needed downgrading, and one is strengthened.

| consumer (PE1's list) | what it needs | r1 verdict |
|---|---|---|
| §3.1 "every A_ν is 1-dimensional over K after TC-3" | A_ν ≅ B_n (JC-GAUGE(iii)) + the display above | **THROUGH** — restated in §3.1 on B_n |
| §3.4 THEOREM JC-IND / OB-4 (independence) | ℤ/E degree separation + each 𝒜_ν a K-line with basis [φ_{γ_ν}] ≠ 0 | **THROUGH** — §3.4, with the base-changed module now existing (B_n free rank one over Δ, (COORD-B)(2)) |
| W-7's bijectivity of Ψ | injectivity = JC-IND; surjectivity = spanning | **THROUGH and STRENGTHENED**: dim_K 𝒜 = E, so the K-span of the anchor classes is ALL of 𝒜 — spanning is now a theorem, not a definition (this is also G2's repair) |
| §5 FINDING JC-F1's dimension count | dim_K 𝒜(T) = E | **THROUGH** — E graded K-lines |
| (MULT) for arbitrary α,β | Δ-bilinearity of the multiplication | **THROUGH** as (MULT-B), on (COORD-B)(2) = (1) + (DMULT-w) [r2, G-1] |

Nothing else in §§2–5 used the refuted form: JC-DOM, JC-GAUGE, JC-PER, JC-FIB,
JC-ANCHMON, JC-SCAL, JC-SPAN, JC-LOAD and JC-PSIKER's witness are statements
about integral digit arithmetic and are untouched (PE1 re-derived all of them
independently and found no defect).

---

## §3. CLAUSE W-7 — THE ANCHOR-TRANSPORT ISOMORPHISM Ψ

> **THEOREM W-7.** Fix T of the [ILN]† class, m with E > 1, and window
> representatives γ_0,…,γ_{E−1} ∈ W of the E classes mod E (they exist: all
> large γ lie in W). Let 𝒜(T) be the K-span of the anchor classes [φ_{γ_ν}]
> ~~in the degree-0 component of~~ **[r1, G2]** across all ℤ/E-degrees of the
> TC-transported ring (§1, §2.10 [r1]; by §2.10's consumer table this span is
> the WHOLE transported ring). Then the K-linear
> extension of u_ν ↦ [φ_{γ_ν}] is an isomorphism of K-algebras
>
>     Ψ : (⊕_{ν∈ℤ/E} K·u_ν, u_νu_{ν′} = c_{m+1}(ν,ν′)u_{ν+ν′})  ≅  𝒜(T),
>
> where 𝒜(T)'s multiplication is gr(w)'s OWN (never c_T), and the structure
> constant is
>
>     c_{m+1}(γ,γ′) = (u/a_{γ+γ′})·z̄^{δ}          [always, §3.2 EXISTENCE]
>                   = z̄^{δ}·∏_{j=1}^{m} z_j^{D_j} = c_T(γ,γ′)
>                                                  [on [ILN]†'s scored stratum]
>
> with u = the slot-δ coefficient of JC-SPAN and a_λ = 𝑅_λ(φ_λ) ∈ K_m^* the
> anchor's own digit constant.
>
> **GRADES (per obligation, honestly separated):**
> * **OB-2 (well-defined): PROVED, general m** — JC-PER, byte-exact.
> * **OB-3 EXISTENCE + STRUCTURE (there is a constant, and it is
>   (K_m^*-unit)·z̄^δ): PROVED, general m, on ALL window pairs** — no [ILN]†,
>   no stratum fence (§3.2). Sharp form needs e_m ≥ 2 (JC-BOX-4).
> * **OB-3 VALUE (the unit is ∏_{j≤m}z_j^{D_j}): PROVED, general m, on
>   [ILN]†'s scored stratum** (D integral ∧ off DCX), by transport through W-8
>   + [ILN]† ACCEPTED (§3.3).
> * **OB-4 (independence): PROVED, general m** — degree separation +
>   ~~(COORD)/(IN-3)(c) base change (§3.4); the Δ-rank input is
>   literature-carried, NOT measured (JC-BOX-3)~~ **[r2, G-4: that grade line
>   survived r1 un-superseded inside this THEOREM box — it graded OB-4 on the
>   input PE1 REFUTED and denied r1's own machine leg. As §3.4 [r1] actually
>   states: (COORD-B)(2) base change on B_{γ_ν}, riding (DMULT-w); the
>   Δ-module input IS measured in its equivalent digit form (R1-DMULT
>   2,784/0, R1-COB 869/869; bilinear leg R2-BIL at §9.4), with the exact
>   tier (DMULT-s) measured-not-cited (JC-BOX-3).]**
> * **OB-5 (tautology fence): DISCHARGED as an architecture statement**
>   (§3.5), with the instrument's independent-code leg as its machine bracket.
> * Attempt grade 0/2; the whole clause rides §0's stack.

### 3.1 OB-2 — well-definedness (and representative-independence)

JC-PER gives φ_{γ+kE} = π^kφ_γ as polynomials, so [φ_{γ+kE}] = [φ_γ] after TC-2
(JC-GAUGE gauges in(π) to 1). Hence u_ν ↦ [φ_{γ_ν}] does not depend on which
window representative of ν is chosen, and Ψ is defined on ℤ/E. ~~Every A_ν is
1-dimensional over K after TC-3 (§2.10), so Ψ maps the ν-summand onto A_ν's
K-line.~~ **[r1, F1 — RE-DERIVED on the repaired object.]** By JC-GAUGE(iii) the
gauged piece is A_ν ≅ **B_n** for any n ≡ ν (mod E) — JC-DOM's post-TC-1 piece,
not gr_n (G1) — and by §2.10's repaired display
B_n/(𝔦^B ∩ B_n) ≅ Δ/(ψ_m) = K with basis the image of in(φ_n). So after TC-3
each 𝒜_ν is a 1-dimensional K-space with basis [φ_{γ_ν}], and Ψ maps the
ν-summand ONTO it. The step is now available at every ν and every n ≡ ν, with no
window and no attainment side-condition (COORD-B(1)). **PROVED, general m**, on
(DMULT-w) + (IN-5) [r2, G-1]. *Machine:* JC1 (k = 1,2,3) + the instrument's
P0-OB2 0/285 and P2-REP 0/174; r1 families R1-PER/R1-SURJ/R1-DMULT for the
repaired coordinate itself.

### 3.2 OB-3, EXISTENCE + STRUCTURE — the composite CARRY law (no [ILN]† used)

**THEOREM JC-CARRY-m.** For γ,γ′ ∈ W with γ+γ′ ∈ W and e_m ≥ 2:

    in(φ_γ)·in(φ_{γ′}) = (u/a_{γ+γ′})·y^{δ}·in(φ_{γ+γ′})   in the ρ-coordinate,
    u ∈ K_m^*,  δ = δ(γ,γ′) ∈ {0,1},

and after TC-3 the scalar (u/a_{γ+γ′})·z̄^δ ∈ K^* is the structure constant of
𝒜(T) at (γ,γ′). Pre-TC-3 it is a K-scalar iff δ < g_m (JC-LOAD).

*Proof.* JC-SPAN computes 𝑅_{γ+γ′}(φ_γφ_{γ′}) = u·y^δ with u ∈ K_m^*; divide by
a_{γ+γ′} to pass to ρ, which is the definition of A(γ,γ′) in ~~(MULT)~~
**(MULT-B)|gr [r2, G-4]**. TC-3 sends y ↦ z̄ (§2.10). ∎

**This is the composite-stage generalization of CARRY-1** (IN-2: at the last-read
layer φ_γφ_{γ′} = φ_{γ+γ′}ȳ^δ with NO extra factor). The extra factor at a
composite stage is exactly one K_m-unit, and the theorem locates it: it is the
slot-δ digit coefficient of the anchor product, normalized by the target anchor's
own digit constant. **Three consequences worth displaying separately:**

1. **The outer/inner split is structural.** Outer = y^δ (slot shift, TC-3's
   z̄^δ); inner = a K_m^*-unit (TC-3-blind). No coordinate choice enters. In
   particular the instrument's rival readings H-B (inner dropped) and H-C
   (germ-signed outer) are refuted structurally as well as numerically (H-B
   fails on exactly the 215 pairs with nontrivial inner; H-C on 73).
2. **Existence is unconditional in the window.** The constant exists on EVERY
   window pair, including pairs off [ILN]†'s scored stratum (non-integral D_j,
   DCX pairs) where the closed form c_T is not even defined. This is a STRICT
   extension of the accepted law's scope — with **zero machine support**, since
   the instrument's grid contained 0 DCX and 0 non-integral-D pairs (JC-BOX-2).
3. **δ ∈ {0,1} always**, so "TC-3 load-bearing" ⟺ δ = 1 ∧ g_m = 1: the load
   set is a *geography*, not a growing set — it is empty on every g_m ≥ 2 stage.

### 3.3 OB-3, VALUE — the inner normalization is ∏_{j=1}^{m}z_j^{D_j}

**THEOREM JC-INNER.** On [ILN]†'s scored stratum (all D_j integral, pair off
DCX), for γ,γ′ ∈ W with γ+γ′ ∈ W and e_m ≥ 2:

    c_{m+1}(γ,γ′) = c_T(γ,γ′) = z̄^{δ}·∏_{j=1}^{m}z_j^{D_j},
    equivalently   u = a_{γ+γ′}·∏_{j=1}^{m}z_j^{D_j}  in K_m^*.

*Proof.* By THEOREM W-8 (§4, proved independently of c_T) the gr-side constant
equals the harness ratio: c_{m+1}(γ,γ′) = c_val(γ,γ′) :=
read(γ+γ′,φ_γφ_{γ′})/read(γ+γ′,φ_{γ+γ′}). By [ILN]† (IN-1, ACCEPTED on exactly
this stratum) c_val = c_T. Compose. For the second form, divide by z̄^δ (a unit,
since ψ_m(0) ≠ 0) and use that ∏z_j^{D_j} and u/a lie in K_m, on which
y ↦ z̄ reduction is the injection K_m ↪ K. ∎

**The germ, split honestly (M3, and J-B's fence).** J-B's JB-CREAD gives the
(C-READ) transport constant c_m = ψ_{m,0} = −z_{m+1} at the level-m read, with
the ε-carry cancelling in print coordinates (LEMMA JB-EPS, unconditional). The
instrument measured this in the carrier and split it:

* **CONFIRMED as a value law**: on all **27 eligible (g_m = 1) stages**,
  val(Ĉ_m) = −z̄ = −z_{m+1} exactly, where Ĉ_m := Φ_{m+1} − Φ_m^{e_m} is the
  canonical correction digit (J-B's g_m = 1 well-definedness fence, JB-BOX-4);
  and the carrier-side class constant κ of multiplication by [Ĉ_m] satisfies
  **κ·val(φ_{e_mγ_{m+1}}) = −z_{m+1} on all 27 stages (0 violations)**, with κ
  itself ranging over {1, z̄, z̄², z̄³, z̄⁴}. In this note's coordinates that
  identity is the a_λ-normalization of §3.2: κ is the class constant of the
  correction digit measured against the anchor, so the bare letter appears
  **exactly when the anchor's own digit constant is 1**. The claim
  "c_m = −z_{m+1}" is therefore a statement about the transport constant modulo
  the anchor's value normalization — J-B's fence is honored, not widened (and
  J-B's own scope fences ride: (VD-m) free only at m ≤ 1, JA-VDIND above,
  g_m = 1 for the Ĉ_m instance).
* **REFUTED as OB-3's inner factor**: the brief's literal hypothesis is reading
  H-D (inner letters replaced by −z_{m+1}) and it FAILS on **138 of 669** scored
  pairs. §3.2 explains why structurally: the inner factor is a unit of **K_m**,
  and −z_{m+1} ∉ K_m whenever g_m ≥ 2; on g_m = 1 stages K_{m+1} = K_m and the
  two can coincide numerically without coinciding as laws (the instrument's own
  printer caveat, S6.2).

### 3.4 OB-4 — K-linear independence (Thm 4.2 analogue), and the zero-class genre

**THEOREM JC-IND.** The classes [φ_{γ_0}],…,[φ_{γ_{E−1}}] are K-linearly
independent in 𝒜(T), and each spans its own ℤ/E-graded line; so Ψ is bijective.

*Proof.* By JC-GAUGE the transported ring is ℤ/E-graded and [φ_{γ_ν}] ∈ 𝒜_ν
with ν = γ_ν mod E pairwise distinct (JC-FIB); the TC-3 ideal is generated by one
homogeneous element, so the quotient keeps the ℤ/E-grading and 𝒜_0 = K. A
relation Σ_ν c_ν[φ_{γ_ν}] = 0 with c_ν ∈ K = 𝒜_0 therefore splits into
c_ν[φ_{γ_ν}] = 0 in 𝒜_ν for each ν. ~~By §2.10 each A_ν (after TC-3) is a
1-dimensional K-space with basis [φ_{γ_ν}] — the base change of the free
rank-one Δ-module gr_{γ_ν} along Δ ↠ Δ/(ψ_m) = K.~~ **[r1, F1 — the base-changed
module is now the RIGHT one, and it exists:]** by (COORD-B)(2) the free rank-one
Δ-module is **B_{γ_ν}** (gr_{γ_ν} is not free over Δ — it is a
finite-dimensional K_m-space, §2.10), and JC-GAUGE(iii) gives A_ν ≅ B_{γ_ν}; its
base change along Δ ↠ Δ/(ψ_m) = K is the K-line 𝒜_ν with basis the image of
in(φ_{γ_ν}), which is NONZERO because ρ^B(in φ_{γ_ν}) = 1 ∉ (ψ_m). Hence
c_ν = 0. **[r1, G2/F1 — spanning is no longer definitional:]** by §2.10's
display every 𝒜_ν equals K·[φ_{γ_ν}], so the K-span of the anchor classes is the
whole transported ring and dim_K 𝒜(T) = E. (The r0 text said "spanning is
definitional (design note C18)"; that reading is what G2 corrects.) This is the
composite-stage instance of FGMN Thm 4.2's rank-one freeness, applied — after
JC-LOC — to the object Thm 4.2 is about. ∎

**The case split FROM the census (examples-first).** The instrument's OB-4
censuses give exactly three genres, and each is now accounted for:

| genre (instrument) | count | status here |
|---|---|---|
| anchor classes (P4-DEG) | 29/29 rows bijective | never zero: a_λ ∈ K_m^*, coordinate a unit constant, not divisible by ψ_m |
| monomial perturbations (SPAN-M) | **328 certified / 0 zero-class / 0 FAILED (606 skipped for non-integrality)** — **[r1, G6]** the parenthesis is the instrument's own verdict row, dropped in r0 and restored here | coordinate = (unit)·y^k reducing into K ⟹ certifies; 0 genre rows, so ~~no case is owed~~ **[r1, G6]** no case is owed MATHEMATICALLY — (COORD-B) covers every element of B_n, integral or not — while as MACHINE evidence the census covers only the **328 of 934** perturbations that stayed integral. The 606 skipped are exactly the ones that left O[x]; after the r1 repair they are legitimate elements of B (π is inverted at TC-1), i.e. they lie in the newly covered part of the statement and have **no machine leg**. Disclosed as a resolution limit, and it is the one place r1 leaves a measurement owed |
| weight-matched sums (SPAN-S, unscored) | 435 certified / **60 zero-class** / 0 unexplained | **PROVED AWAY**: a class dies in TC-3 iff its Δ-coordinate ∈ (ψ_m) (§2.10). The 60 are exactly that kernel; they are not anchors and carry no information about OB-4. The two build-phase "failures" were such zero-classes — which is why c = 0 was admitted |

**Honest rider.** ~~The Δ-rank input (IN-3)(c) is *literature-carried*: the
instrument explicitly did NOT measure freeness over Δ before TC-3 (only its
degree-separation shadow and post-TC-3 spanning). If Thm 4.2's composite-order
instance failed, (COORD) and hence §§2.7–3.4 would fail together.~~ **[r1 —
re-stated on the repaired footprint.]** The Δ-module input is now exactly
**(DMULT-w)** **[r2, G-1: the CITABLE tier — the r1 wording said "(DMULT)"
undifferentiated]** (§2.10), applied to B = gr^K(w) (JC-LOC), and it is the
ONLY cited
input of the coordinate calculus: the surjectivity half that r0 also cited is
PROVED here (JC-BSURJ). PE1's observation stands and is now answered on its own
terms — the instrument did not measure Δ-freeness, so **r1 measures its
equivalent digit form**: family R1-DMULT (the exact-tier identity (DMULT-s),
𝑅_{λ+μ}(fg) = y^δ𝑅_λ(f)𝑅_μ(g) with multiplier 1) plus its sharp corollary
R1-COB (u = a_γa_{γ′}, riding (DMULT-s)), with tooth T3, **[r2, G-2]** on
monomial-dominated samples — the genuinely bilinear leg is r2's R2-BIL (§9.4).
If (DMULT-w) failed at composite order,
(COORD-B)(2), (MULT-B) and §§2.7–3.4 would fail together — JC-BOX-3, which r1
re-cuts to box APPLICABILITY and citation precision rather than literature
truth.

### 3.5 OB-5 — the tautology fence: HOW the gr side is computed

The fence demands that 𝒜(T)'s multiplication be computed in gr(w) *before* c_T
is mentioned, and only then compared. This note's chain does exactly that, and
the dependency order is auditable:

1. **gr-side only** (no c_T, no harness read): JC-DOM, JC-GAUGE, JC-PER, JC-FIB,
   JC-ANCHMON, JC-SCAL, JC-SPAN, JC-LOAD, JC-PSIKER, §2.10's ~~(COORD)/(MULT)~~
   **[r1, F1]** (COORD-B)/(MULT-B) with JC-LOC/JC-PIINV/JC-BSURJ/JC-COB,
   JC-CARRY-m, JC-IND. Inputs used: the corpus's definitions of w, split,
   anchors, REALIZE, and FGMN (b)(e) + (DMULT) **[r1: (c) enters only through
   (DMULT), on B]**. **The structure constant's existence,
   its outer/inner shape, its y-degree, and the TC-3 load set are all fixed
   here.**
2. **comparison only** (c_T enters ONCE): §3.3 evaluates the already-computed
   constant against the accepted closed form, through W-8's read identity.
   Deleting §3.3 leaves §§2–3.2 and 3.4 standing.

**Machine bracket for the fence** (the instrument's architecture, quoted): the
gr-side constant is the unique solution of a weight inequality whose decision
procedure calls exactly four primitives — schoolbook O[x] arithmetic, the weight
w by iterated Φ-development, the graded scalar lift REALIZE, and the classifier's
own next key Φ_{NR} — while `Tower.constants` (c_T) and `Tower.read` (the harness
val) are **never called inside the determination or the certification**; all 29
rows ran EXHAUSTIVE over K (zero witness input) with per-pair uniqueness
machine-proved; and the tautology tooth MT3 (one anchor rescaled by a nontrivial
scalar class) was **caught on 197/206 pairs, ≥ 1 per non-skipped row (28/28)**,
while the c_T-defined "check" reports 0 violations by construction. The 9
escapes are disclosed (single-pair, all prime-residue-field rows |K| ∈ {3,5},
planted rescaling coincides with a lawful constant) — they weaken the tooth's
resolution, not the fence's architecture.

**[r1, G8 — fence hygiene: what THIS NOTE's own battery calls, disclosed.]** The
paragraph above is correctly attributed to the *instrument*
(`grt_jc_probe.py`), whose certifier really does call neither primitive. This
note's own battery (`grt_jc_checks.py`) **does call both**, and r0 disclosed only
the c_val half (§9.2). Full disclosure, with the non-circularity argument:
(i) `T.constants(ga, gb)['delta']` supplies the integer δ in families JC3, JC7
and MJ1. This is **not** a c_T read: `constants()` computes
δ = (s_a[NR] + s_b[NR]) // e_m from the SPLIT data alone — byte-identically
§1's definition δ = (s_NR(γ)+s_NR(γ′) − s_NR(γ+γ′))/e_m — and the closed-form
value z̄^δ∏z_j^{D_j} is a different field of the same return dict, never read by
the scored predicates. (ii) `T.read` is called in JC6/JC7/JC8: in JC6 as the
*claim under test* (read(wΦ,Φ_{m+1}) = 0), in JC7/JC8 to build the constant
table, which is by construction the harness ratio c_val — the §9.2 disclosure.
The gr-side quantities the note's theorems are about (slot sets, digit
polynomials, a_λ) come from `T.read_coeffs`, never from `T.constants`. Nothing
circular follows, but a hostile reader should not have to re-derive that: r1
states it. The r1 supplementary battery (§9.3) obeys the same rule and discloses
the same two call sites in its own docstring.

---

## §4. CLAUSE W-8 — HARNESS-VAL = TC-READ (OB-6)

> **THEOREM W-8.** For γ,γ′ ∈ W with γ+γ′ ∈ W, and N ≡ 0 (mod E), N ≥ wΦ_{NR}:
> the gr-side structure constant of §3.2 equals the harness value ratio,
>
>     c_{m+1}(γ,γ′)  =  c_val(γ,γ′) := read(γ+γ′, φ_γφ_{γ′}) / read(γ+γ′, φ_{γ+γ′}),
>
> exactly, with every line-wise normalization cancelling; and the residue chain
> K_0 ⊂ … ⊂ K_{m+1} used by both sides is one and the same tower (J-C(iii)).
> **GRADE: PROVED at general m** on inputs ~~(COORD)+(MULT)~~ **[r1, F1]**
> (COORD-B)+(MULT-B) **on B, i.e. (DMULT-w) [r2, G-1] + the in-note lemmas
> JC-LOC/JC-PIINV/JC-BSURJ** +JC-SPAN+JC-SCAL+R3
> ~~(i.e. FGMN (b)(c)(e) via W-1, ATTEMPT)~~ **[r2, G-4: (i.e. FGMN (b)(e) +
> (c)-ENTERING-ONLY-THROUGH-(DMULT-w)-on-B (§3.5), via W-1, ATTEMPT)]**.
> Attempt 0/2. Machine: the instrument's
> **P5-OB6 0/669** (both sides computed independently per pair).

### 4.1 Proof

Both sides are computed in the ρ-coordinate of §2.10.

*The read is the reduced coordinate.* By §1 (definition), read(λ,f) = 𝑅_λ(f)(z̄).
Hence for any f with w(f) = λ,

    read(λ,f) / read(λ,φ_λ) = 𝑅_λ(f)(z̄)/a_λ = ρ_λ(in f)(z̄)          (†)

(a_λ ∈ K_m^* is a constant, so its reduction is itself). **No unit is
unaccounted for: (†) is an identity of the corpus's own definitions, and the
line-wise ε-kit lives inside 𝑅_λ on both sides of the quotient.**

*The gr-side constant.* Let c := c_{m+1}(γ,γ′) be defined by the fence-clean
equation at the offset line λ+N, λ := γ+γ′:

    in(φ_γ)in(φ_{γ′})in(X_N) = in(Λ_N(c))·in(φ_λ)   in the TC-transported ring.

Apply ρ_{λ+N} and ~~(MULT)~~ **(MULT-B)|gr [r2, G-4]** to both sides.
LHS = A(γ,γ′)·A(λ,N)·ρ_N(in X_N) and
RHS = A(λ,N)·ρ_N(in Λ_N(c)); A(λ,N) ≠ 0 cancels (Δ is a domain), leaving

    ρ_N(in Λ_N(c)) = A(γ,γ′)·ρ_N(in X_N).                              (‡)

*The lift is exactly normalized.* By JC-SCAL(b), 𝑅_N(X_N) is a constant, and by
R3 its reduction is read(N,X_N) = 1; a constant equal to 1 after the injection
K_m ↪ K **is** 1, so 𝑅_N(X_N) = 1 and ρ_N(in X_N) = 1/a_N. By JC-SCAL(a),
𝑅_N(Λ_N(c)) is a polynomial of y-degree < g_m whose reduction is
read(N,Λ_N(c)) = c (R3); the canonical degree-<g_m representative of c is unique,
so **𝑅_N(Λ_N(c)) = c̃(y)** on the nose and ρ_N(in Λ_N(c)) = c̃(y)/a_N.

*Conclusion.* (‡) becomes c̃(y) = A(γ,γ′) = (u/a_λ)y^{δ} (JC-CARRY-m). Reducing
mod ψ_m: c = (u/a_λ)·z̄^{δ}. On the other side, by (†) with f = φ_γφ_{γ′} and
JC-SPAN,

    c_val = ρ_λ(in φ_γ·in φ_{γ′})(z̄) = ((u/a_λ)y^{δ})(z̄) = (u/a_λ)z̄^{δ}.

The two agree. ∎

*Two remarks the design note asked for.* (a) ~~The a_λ's — the anchor's own digit
constants, i.e. the ε-normalization the harness carries — **cancel** because both
reads in c_val sit on the SAME line λ; this is why no coboundary condition is
needed, and it is the general-m form of the ε-collapse J-B proved
unconditionally (JB-EPS).~~ **[r1, G7 — the two identifications inside that
sentence are STRUCK as unproved; W-8 needs neither.]** Struck: (i) the apposition
identifying a_λ = 𝑅_λ(φ_λ) with "the ε-normalization the harness carries", and
(ii) the claim that the cancellation is "the general-m form of" JB-EPS — JB-EPS
is a statement about the print-twist cocycle
(t_m(V+V′) − t_m(V) − t_m(V′) = ε′, GRTJB §5, unconditional at every m ≥ 1) and
so about a different object; importing J-B's authority for this step was
unwarranted. What is TRUE, and all W-8 uses, is: **both reads in c_val are taken
at the SAME line λ = γ+γ′ by the definition of c_val, so the single constant a_λ
cancels in the ratio** — definitional, hence no coboundary condition. What is
additionally ~~PROVED (on (DMULT), ...)~~ **[r2, G-1: PROVED CONDITIONAL ON
(DMULT-s), the MEASURED tier —]** (§2.10 COROLLARY JC-COB) is the sharper
statement the r0 sentence was reaching for: the a's do not merely cancel, they
ARE the inner factor — u = a_γa_{γ′}, so
c_{m+1} = (a_γa_{γ′}/a_{γ+γ′})·z̄^δ, an anchor-normalization coboundary times
z̄^δ, with its own scored machine family (R1-COB) **[r2, G-1: that sharper
statement rides (DMULT-s), the MEASURED tier — see §2.10]**. (b) C15's
separation stands: nothing above uses N-1's
operator-level commuting diagram; what is used is ~~(COORD)+(MULT)~~
**(COORD-B)+(MULT-B) [r2, G-4]**, i.e. the
carrier-level content, which is precisely what C15 said was missing. ~~This note
supplies it from FGMN Thm 4.2 + the corpus's read definition, at the cost of
riding W-1's dictionary for the transport of Thm 4.2 to the harness w.~~
**[r2, G-4: that footprint sentence contradicted r1's own headline (the only
cited input left is (DMULT)) and JC-BOX-3[r1] ("only through the single
statement (DMULT)"). As repaired: this note supplies it from the corpus's read
definition + the single cited identity (DMULT-w) on B (via JC-LOC), with the
surjectivity half PROVED in-note (JC-BSURJ), at the cost of riding W-1's
dictionary for the transport of the residual-multiplicativity citation to the
harness w and 𝑅.]**

### 4.2 The offset-transport lemma (used by JC-LOAD and by (‡))

*Statement.* For λ ∈ W and N ≡ 0 (mod E), N ≥ wΦ_{NR}: s_{NR}(N) = 0,
δ(λ,N) = 0, A(λ,N) is a **constant**, and multiplication by X_N carries ρ_λ
isomorphically onto ρ_{λ+N} up to that constant — in particular it preserves
y-degrees.

*Proof.* s_{NR}(N) = 0 by JC-FIB (E | N); then s_{NR}(λ+N) = s_{NR}(λ)
(JC-PER), so δ(λ,N) = 0 and JC-SPAN gives A(λ,N) constant. Apply ~~(MULT)~~
**(MULT-B)|gr [r2, G-4]** with ρ_N(in X_N) = 1/a_N ∈ K_m^*. ∎

*Machine:* the instrument's **P2-OFF 0/116** (constants independent of the scalar
offset) and **P0-SCAL 0/293** (scalar multiplicativity in gr), plus this note's
family JC4.

### 4.3 J-C(iii) — the residue chain

The chain used on the gr side is K_0 = k_0[x]/(Φ̄_0) and K_{j+1} = K_j[y]/(ψ_j)
(§1), which is the classifier's residual tower `ResidueTower` by construction of
the type: ψ_j is the residual polynomial of Φ_{j+1} at level j, and TC-3's
identification Δ/(ψ_m) ≅ K_{m+1} is (IN-3)(d). Compatibility with (i)/(ii)'s
scalars is the statement that the K_m ⊂ K_{m+1} used by JC-CARRY-m's inner factor
is the same inclusion — true by construction, since the inner unit is literally a
product of the letters z_1..z_m of the same tower. **GRADE: PROVED, general m,
by construction — no independent content beyond the identification (IN-3)(d).**

---

## §5. CLAUSE W-9 — COCYCLE SEMANTICS (the S-priced corollary, composed as one)

> **COROLLARY W-9.** Given W-6, W-7, W-8: (i) c_{m+1} descends to a map
> ℤ/E × ℤ/E → K^* and **is a 2-cocycle**: c(a,b)c(a+b,c) = c(b,c)c(a,b+c) — this
> is [ILN]†'s COR-2, and on the gr side it is nothing but **associativity of
> gr(w)'s multiplication**; (ii) its y-degree part δ satisfies the integer
> cocycle identity δ(a,b) + δ(a+b,c) = δ(b,c) + δ(a,b+c) (the {0,1}-valued
> carry cocycle); (iii) 𝒜(T) is the **twisted group algebra** K^{c}[ℤ/E] of the
> abscissa-coset group over the carry cocycle; (iv) COR-4's monodromy is the
> **gauge period**: φ_{γ+E} = π·φ_γ (JC-PER) is the period, in(π) is the
> gauge unit of degree E (JC-DOM), and the E-fold orbit product
> ζ_T := ∏_{k=1}^{E−1}c(1,k) is exactly the K-scalar by which the E-fold anchor
> product differs from the π-power that TC-2 sets to 1.
> **GRADE: PROVED given W-6..W-8 (general m), S-priced as the blueprint says.**

*Proofs.* (i) Descent is JC-PER. Associativity of gr(w) gives
(in φ_a·in φ_b)·in φ_c = in φ_a·(in φ_b·in φ_c); expanding both with ~~(MULT)~~
**(MULT-B)|gr [r2, G-4]**
yields A(a,b)A(a+b,c) = A(b,c)A(a,b+c) in Δ, and reducing mod ψ_m gives the
K^*-cocycle identity. (ii) Take y-degrees in the same Δ-identity (JC-CARRY-m:
deg A(a,b) = δ(a,b)) — degrees add, so the identity is the additive one. (iii)
Restatement of W-7's Ψ. (iv) With the representative γ_0 = 0 ∈ W we have
φ_0 = 1, and JC-PER gives φ_{kE} = π^k, whose gauged class is 1; iterating
~~(MULT)~~ **(MULT-B)|gr [r2, G-4]** along the orbit of the class 1 gives
[φ_1]^E = ζ_T·[φ_0] = ζ_T. ∎

**FINDING JC-F1 (blueprint display correction, REVIEW-OWED — read with §6).**
(iv)'s computation has a consequence the blueprint's cyclic-fence wording does
not survive as literally stated. Put v := [φ_{γ_1}] (the anchor class of the
residue class 1 ∈ ℤ/E). Then v^k = β_k·[φ_{γ_k}] with β_k := ∏_{i=1}^{k−1}c(1,i)
∈ K^* for k = 1..E−1, so {1,v,…,v^{E−1}} is a K-basis of 𝒜(T) and v^E = ζ_T:

    **𝒜(T) ≅ K[v]/(v^E − ζ_T) as a K-algebra — at EVERY composite stage.**

So "𝒜(T) is NOT F′[u′]/(u′^E − ζ′)" cannot be read as an abstract-isomorphism
claim; it is (and, in its own adjudication procedure, always was) a claim about
the ANCHOR-INDEXED presentation — see §6. Nothing measured is re-scored by this;
what is corrected is a display, exactly as J-B's JB-BOX-1 corrected the J-B(iii)
display.

**[r1, F1 — JC-F1's DIMENSION COUNT re-derived on the repaired object.]** The
argument needs exactly one quantitative input: **dim_K 𝒜(T) = E**. On the r0
text that came from the refuted "each A_ν is a 1-dimensional K-space" on gr_λ;
it now comes from §2.10's repaired display (each of the E pieces
𝒜_ν = B_{γ_ν}/(𝔦^B ∩ B_{γ_ν}) is the K-line K·[φ_{γ_ν}]). With that, the
powers v^k = β_k[φ_{γ_k}] (β_k ∈ K^*) lie in pairwise distinct ℤ/E-degrees, so
they are independent, so {1,v,…,v^{E−1}} is a K-basis; the K-algebra map
K[v]/(v^E − ζ_T) → 𝒜(T) is well defined and surjective, and injective by
comparing dimensions E = E. **THROUGH, general m**, on (DMULT-w) + JC-IND
[r2, G-1].

**FINDING JC-F2 [r1, G2] (blueprint display correction, REVIEW-OWED — the second
inherited-display defect, same treatment as JC-F1).** The corpus defines the
carry-algebra target as "the K-span of the anchor classes **in the degree-0
component** of the TC-transported gr(w)" — verbatim in `GRW2_TIE_DESIGN` §S2.2,
the blueprint §S2.3, the GRTJC brief, and (until r1) §1 and W-7 of this note.
**That reading is wrong, and it contradicts this note's own OB-4 proof:** the
anchor class of γ lives in the ℤ/E-degree γ mod E (JC-GAUGE + JC-FIB), which is
the degree-0 component only for ν = 0; under the literal reading the entire
degree-separation argument of §3.4 is unavailable and W-7's Ψ would map an
E-dimensional carrier onto a single K-line (false for E > 1). r0 used the
CORRECTED reading in its proofs while displaying the inherited one — PE1's GAP 2.
**The correct definition** (now in §1 and W-7): 𝒜(T) := the K-span of the anchor
classes across ALL ℤ/E-degrees of the TC-transported ring, which by §2.10 [r1] is
the whole transported ring, of K-dimension E. Nothing measured moves; no clause's
proof changes. **REVIEW-OWED**: the design note, the blueprint and the brief
carry the defective display and must be corrected there before any downstream
text repeats it (JC-BOX-5's JC-F1 rider now covers JC-F2 as well).

---

## §6. THE CYCLIC FENCE, RESTATED AS A GENRE LAW (and kept consistent with the byte-frozen record)

The blueprint carries the fence as LAW: *at composite stages 𝒜(T) is NOT
F′[u′]/(u′^E − ζ′) (adjudicated NOT-CYCLIC at 22/28 towers, value set
{z₁, z̄, z̄z₁^b}, byte-frozen); only the last-read layer is cyclic.* The
instrument, computing the same adjudication from a completely different side
(gr-side certification instead of the harness value cocycle), returned
**14 NOT-CYCLIC / 6 CYCLIC / 9 UNDECIDED**, with the 6 cyclic rows
C2A/C2E/C2G/C2J/C3A/C4A. Both records stand. Here is the law that has both as
instances.

**(CYC), the property actually adjudicated (definition, quoted from both
runners).** The anchor-indexed presentation is *cyclic* iff
(α) image(c) ⊆ {1, ζ′} for a single ζ′ ∈ K^*, **and** (β) there are integers
σ_r (σ_0 = 0) with σ_r + σ_s = σ_{r+s} + E·carry(r,s) reproducing the table.
This is the **letter-monomial** shape: the anchors are, up to ζ′-power
normalization, the power basis of one generator — precisely the shape D-REAL
supplies one level down (K_{m+1}[u]/(u^{e_m} − z̄), anchors = powers of u).

**LAW JC-CYC (the refinement; each part graded).**

* **(a) [PROVED, general m]** As an abstract K-algebra 𝒜(T) ≅ K[v]/(v^E − ζ_T)
  always (JC-F1). Hence the fence's content is (CYC), not abstract cyclicity, and
  **the operative dead route is the letter-monomial one**: assuming the composite
  carrier is D-REAL's shape with a single letter ζ′ and the carry pattern. The
  design note's S4 dead end ("one-anchor-unit normalization does not trivialize a
  coset progression") is exactly this, and it stays dead.
* **(b) [PROVED, general m — the obstruction direction]** If the measured value
  table has two distinct non-1 values, (CYC) fails by (α). With JC-INNER's law
  image(c) = {z̄^δ∏_j z_j^{D_j}}, this happens as soon as the stage realizes two
  multiplicatively distinct (δ, D)-words — which is the generic composite
  situation and is why 14/29 (instrument) and 22/28 (byte-frozen strata probe)
  come back NOT-CYCLIC.
* **(c) [PROVED, general m — the twist-blind direction]** If |K| = 2 then
  K^* = {1}, so c ≡ 1 and (CYC) holds with ζ′ = 1, σ ≡ 0. Likewise if the table
  has at most one non-1 value AND (β) is solvable, (CYC) holds by definition.
* **(d) [MEASURED, m ≤ 3 — ONE-DIRECTIONAL; corrected by this note's own battery,
  §9.2 finding 1]** On both rosters the cyclic side is CONTAINED in the
  twist-blind/collapse geography: every CYCLIC row has \|K\| = 2 (C4A), or
  g_m = 1 so that K_{m+1} = K_m and z̄ ∈ ⟨z_1⟩ (C2A/C2E/C2G/C3A), or e_0 = 1
  (C2J) — 0 violations of "CYCLIC ⟹ collapse" on 29 rows. **The CONVERSE IS
  FALSE and this note does not claim it**: 13 collapse-geography rows are
  NOT-CYCLIC (C2B, C2C, C2D, C2H, C3D, C3E, C3F, C3H, C3I, C4B, C4G, I4B, I4C),
  by two visible mechanisms — ≥ 2 distinct non-1 values (up to 7 on I4C), or a
  single value whose carry pattern no integer relabeling realizes (C2C, C3I). The
  decidable designated g_m = 2 row came back NOT-CYCLIC (C2I); C4I is UNDECIDED
  at E = 16 (compute fence, not a finding). **The general form of the inclusion —
  CYCLIC ⟹ collapse at every m — is OPEN (JC-BOX-5), and its measured resolution
  is low: only 2 of 29 rows lie off the collapse geography.**
* **(e) Consistency with the byte-frozen record, explicit.** The 22/28
  adjudication and its value set {z₁, z̄, z̄z₁^b} are **unamended**; no row is
  re-scored here; the instrument's 14/6/9 is a different roster and a different
  computation, and it reproduces the same SPLIT SHAPE (cyclic only where the
  twist collapses). The fence's program consequence is unchanged: **any route
  through a letter-monomial cyclic presentation at a composite stage is DEAD**,
  and (b) now says why — the cocycle needs the full inner (δ, D_j) word, not one
  letter.

**Consequence for the case split.** The genre column "cyclic / not-cyclic /
undecided" is carried into §7, and the cyclic side is *not* only the last-read
layer: it includes composite stages whose residual tower collapses (g_m = 1 ⟹
K_{m+1} = K_m). That was the instrument's M5, and it is now a stated law with a
proved obstruction direction.

---

## §7. THE CASE SPLIT (derived FROM the instrument's genre censuses; the case list matches the observed genre list)

| # | genre (as the instrument's censuses name it) | rows / pairs | this note's status |
|---|---|---|---|
| 1 | g_m ≥ 2, δ = 0 | ~~C2B/C2I/C3I/C4I…~~ **[r1, G4: the runner's own per-row print contradicts that list — C2B and C3I have g_m = 1. The g_m ≥ 2 rows are EXACTLY** **C2I** (m = 1, E = 4) **and C4I** (m = 3, E = 16), 2 of 29, the complement of the 27 g_m = 1 stages counted in rows 3/4 and in §3.3 (29 − 2 = 27, consistent); C2B and C3I belong to rows 3/4]; the majority of pairs on those two rows | JC-CARRY-m + JC-INNER; RAW-solvable; canonical outer/inner split (1,z̄,…,z̄^{g_m−1} a K_m-basis) — **PROVED** |
| 2 | g_m ≥ 2, δ = 1 | the carry-boundary pairs on g_m = 2 rows | δ = 1 < g_m ⟹ still RAW-solvable (this is the smoke correction that sharpened the sealed identity from {δ≥1} to {δ≥g_m}) — **PROVED** |
| 3 | g_m = 1, δ = 0 | most pairs on the 27 g_m = 1 stages | K_{m+1} = K_m collapse: value identity holds; the outer/inner split is canonical on the gr side (y-degree) but NOT recoverable from the VALUE alone — **PROVED, with the display fence** (the instrument's printer caveat S6.2) |
| 4 | **g_m = 1, δ = 1 — the TC-3 load set** | **134 of 669 pairs, 0/29 set-mismatches** | THEOREM JC-LOAD: no pre-TC-3 scalar exists; the ψ_m-relation is unavoidable — **PROVED** (this is the case that makes TC-3 load-bearing) |
| 5 | top-flat stage e_m = 1 | C4H (+ any I4x with e_m = 1 — **[r1, G5]** the roster has NONE: C4H is the unique e_m = 1 row, r1 census R1-CEN, which is why §2.8(c)'s theorem covers 28 rows) | δ ≡ 0; JC-SPAN gives deg ρ ≤ 1 instead of the singleton; sharp form **MEASURED not proved** **[r2, G-7: and CONDITIONALLY CLOSED on (DMULT-w) since r1 — the two statuses coexist because they have different footprints]** — JC-BOX-4 |
| 6 | interior-flat legs e_j = 1, j < m | C2J, C3E, C4H | no special role: the split/anchor calculus is uniform in e_j; the [RMG] fenced-corner genre is inherited via J-B, not re-opened — **PROVED (no case owed)** |
| 7 | twist-blind \|K\| = 2 | C4A | c ≡ 1; cyclic by JC-CYC(c); MT3 skipped there (no nontrivial scalar class) — **PROVED** |
| 8 | zero-class genre (SPAN-S) | 60 samples | the TC-3 kernel ψ_m·Δ (§2.10) — **PROVED AWAY**, not a failure genre |
| 9 | DCX / non-integral-D | **0 rows, 0 pairs observed** | existence + structure PROVED (§3.2); the VALUE c_T is not claimed and has no machine support — JC-BOX-2 |
| 10 | prime-residue-field rows (MT3's 9 single-pair escapes) | 9 rows, |K| ∈ {3,5} | a tooth-resolution artifact (planted rescaling coincides with a lawful constant), not a clause genre — disclosed, JC-BOX-7 |
| 11 | UNDECIDED cyclic rows (E > 8) | 9 rows | compute fence on (β)'s relabeling search — no clause depends on them |

---

## §8. HONEST BOXES

* **JC-BOX-1 (proof scope vs machine scope).** Every clause of §§2–5 is stated
  and proved at **general m**; the machine evidence (instrument + §9) covers
  **m ≤ 3, |K| ≤ 25, g_j ≤ 2, d_0 ≤ 3, orders ≤ 4, p ∈ {2,3,5}**, base rings ℤ_p
  and F_p[[t]] (equal-characteristic rows ride construction-identity + machine
  only, no PARI leg). No clause is extrapolated FROM m ≤ 3: where a proof is
  missing the clause is fenced (JC-BOX-2, JC-BOX-4, JC-BOX-5), not extended.
* **JC-BOX-2 (off-stratum).** §3.2's existence/structure statement is strictly
  wider than [ILN]†'s scope (it holds for every window pair, DCX or not,
  D-integral or not); the VALUE statement §3.3 is exactly [ILN]†'s stratum. The
  instrument's grid contained **0 DCX and 0 non-integral-D pairs**, so the wider
  half has **no machine support whatsoever** — it is proof-only, and a hostile
  pass should attack it there first.
* ~~**JC-BOX-3 (the literature leg, and citation precision owed).** (COORD)'s
  surjectivity/rank-one half is FGMN Thm 4.2 at composite order, quoted from the
  corpus's own pinned quotation (`GRB_ORDER2_2026-08-05.md` §S6a) and **not
  re-verified against a printed source in this session**; likewise Thm 4.8 /
  Cor 4.9 (Δ/(ψ_m) ≅ K_{m+1}) and Cor 2.7 (abscissa additivity). Their transport
  to the harness w and R is W-1 (ATTEMPT). If the composite-order instance of
  Thm 4.2 failed, §§2.7–3.4 fail together. The instrument explicitly did NOT
  measure the Δ-rank refinement.~~
* **JC-BOX-3 [r1 — RE-CUT: the box is APPLICABILITY + citation precision, not
  literature truth].** PE1's verdict on the r0 box was that it boxed the wrong
  risk: the danger was never "Thm 4.2 might be false at composite order" but
  that Thm 4.2 (true, and about K[x]) had been transported to the wrong ambient
  object, where its transported conclusion is refuted by §1's own arithmetic.
  Post-r1 the box reads:
  1. **WHICH OBJECT.** The note uses FGMN Thm 4.2 **only on
     B = gr(w)[in(π)^{-1}] ≅ gr_{K[x]}(w)** (LEMMA JC-LOC), never on gr_{O[x]},
     and it uses it **only** through the single statement (DMULT) — **[r2,
     G-1] in its CITABLE tier (DMULT-w) (up to the line-pair unit ω); the
     EXACT tier (DMULT-s) (ω ≡ 1) is MEASURED, not cited, and carries only
     JC-COB's sharp form** — (equivalently:
     B_0 ≅ Δ = K_m[y] as K_m-algebras and B_n free of rank one over B_0 on
     in(φ_n)). The surjectivity half r0 also cited is now PROVED in-note
     (JC-BSURJ, from REALIZE-(m)); Thm 4.8 / Cor 4.9 (Δ/(ψ_m) ≅ K_{m+1}) and
     Cor 2.7 (abscissa additivity, used by JC-SPAN) are unchanged citations.
  2. **CITATION PRECISION — STANDING CODEX LEG (owed, unchanged in status).**
     The numbers "Thm 4.2 / Thm 4.8 / Cor 4.9 / Cor 2.7" come from the corpus's
     own pinned quotation (`GRB_ORDER2_2026-08-05.md` §S6a) and are **still not
     re-verified against a printed source**. That verification is the standing
     adversarial-verification leg for this note (a Codex/printed-source check),
     and r1 does not discharge it. A numbering error would not by itself refute
     (DMULT) — which is standard Montes/FGMN residual multiplicativity and is
     now separately machine-tested (R1-DMULT, R1-COB) — but the note's citation
     would be wrong and must be re-pointed.
  3. **WHAT DIES WITH IT.** If (DMULT-w) failed at composite order,
     (COORD-B)(2),
     (MULT-B), §§2.7–3.4, W-8 and W-9 fail together; if only (DMULT-s) failed
     (ω ≢ 1), JC-COB's sharp values and R1-COB's exact predicate fail while
     the structural clauses stand [r2, G-1]. Transport of the harness
     w and 𝑅 to the FGMN objects is still W-1 (ATTEMPT) — and the corpus's own
     march-level dictionary for that transport, TR-3′-GEN, is OPEN at general
     order and unit-valued where closed (quoted at §2.10 [r2, G-1]).
* **JC-BOX-8 [r1] (what the r1 repair does NOT supply).** Three honest residues
  of this round: (i) the **606 skipped non-integral SPAN-M perturbations** (G6)
  are exactly elements that live in B but not in gr(w) — the repaired statement
  covers them, and there is **no machine evidence** for them on either runner;
  (ii) **R1-PSIK-LO's one-sidedness**: the "kernel is zero below wΦ_NR" half is
  PROVED arithmetically, and the machine leg only confirms that no sampled class
  at such a line is *certified dead* by the (one-sided, canonical-quotient)
  TC-3 certifier — the probe's own disclosed limitation; (iii) **JC-COB's second
  half** (∏_j z_j^{D_j} = a_γa_{γ′}/a_{γ+γ′}) rides [ILN]† in addition to
  (DMULT-s) [r2, G-1], and the identity is displayed, not consumed by any
  clause.
* **JC-BOX-4 (the top-flat corner e_m = 1 ∧ g_m = 1).** JC-SPAN's sharp
  conclusion (slot set = {δ}) is proved for e_m ≥ 2; at e_m = 1 the degree bound
  gives only deg ρ ≤ 1, which suffices whenever g_m ≥ 2 but NOT at
  e_m = 1 ∧ g_m = 1, where deg ρ = 0 is **measured** (C4H: all pairs
  RAW-solvable, 0 violations; family JC3 re-tests it) and unproved. JC-LOAD and
  JC-CARRY-m are therefore stated with e_m ≥ 2 and this corner is boxed OPEN.
  **[r1 — CONDITIONALLY CLOSED, on (DMULT).] [r2, G-1 — tiered: the closure
  needs only (DMULT-w).]** The r0 proof of JC-SPAN is
  e_m-sensitive because it bounds the top abscissa by degrees (JC-ANCHMON(d)).
  The r1 coordinate calculus gives a second, e_m-blind proof: by (DMULT-w) with
  f = φ_γ, g = φ_{γ′}, and since each anchor's digit polynomial is the CONSTANT
  a_γ (JC-ANCHMON(c)),
  𝑅_{γ+γ′}(φ_γφ_{γ′}) = ω·y^{δ}·a_γ·a_{γ′} — a MONOMIAL of degree exactly δ
  whatever the unit ω, with
  no hypothesis on e_m (the sharp coefficient value ω = 1, i.e. u = a_γa_{γ′},
  additionally holds on (DMULT-s) — COROLLARY JC-COB). At e_m = 1 one has
  s_NR ≡ 0 hence
  δ ≡ 0, so the slot set is exactly {0} and JC-LOAD's dichotomy holds trivially
  there (0 = δ < g_m always ⟹ RAW always solvable, which is exactly what C4H
  measures). **So: the corner is CLOSED for a reader who grants (DMULT-w)
  (JC-BOX-3), and stays OPEN for one who wants it independent of the FGMN
  input** — r0's proof and r1's proof have different footprints, and the note
  keeps both. Machine: r1 family **R1-COB scores C4H's 24 grid pairs with the
  sharp form and 0 violations** (§9.3).
* **JC-BOX-5 (the cyclic characterization).** JC-CYC(b)(c) are proved; the
  general form of (d)'s **inclusion** (CYCLIC ⟹ collapse geography) is OPEN, its
  measured resolution is low (only 2 of 29 rows lie off the collapse geography),
  and the **converse is FALSE** — 13 collapse-geography rows are NOT-CYCLIC
  (§9.2 finding 1). The 9 UNDECIDED rows are a compute fence. **JC-F1 (the abstract-cyclicity
  computation) is a blueprint-display correction and is REVIEW-OWED**: it must be
  adjudicated before any text repeats the fence in the abstract-isomorphism
  wording. **[r1, G2] The same rider now covers FINDING JC-F2** (the "degree-0
  component" definition of 𝒜(T), inherited from `GRW2_TIE_DESIGN` §S2.2, the
  blueprint §S2.3 and the brief): also a display correction, also REVIEW-OWED,
  and it must be fixed in those sources before any downstream text repeats it.
* **JC-BOX-6 (inherited conditionality, itemized).** [ILN]† ACCEPTED but with its
  own residuals riding through: the open engine families **(RM-m, m ≥ 2)** and
  **(W-MULT-DCX-m)**, the fenced corners, DCX-(n) excluded, standard-lift only
  (so the **(ITER-LAW-LIFT)** residual — open exactly at g_0 = 1 ∧ δ_1 = 1 —
  is displayed wherever a non-standard lift could enter). GRB/CARRY-1/D-REAL
  ACCEPTED-conditional on the GRB §0 ladder ((V1)_{≤i+1}, (KP)_{≤i−1},
  (H-CHAIN)) + §3.3 [T] pins. W-1/W-2/J-A/J-B at ATTEMPT (0/2), and §3.3's germ
  display additionally rides JB-BOX-2's geography ((VD-m) free only at m ≤ 1;
  JA-VDIND at m ≥ 2; JA-BOX-2's (R-coll) at m ≥ 3; the pinned-ℓ orbit;
  q ≤ qcap) and JB-BOX-4's g_m = 1 fence for Ĉ_m.
* **JC-BOX-7 (standing fences; nothing fires).** Statements are for γ in the
  window W at attained weights (outside, gr_γ = 0 and no anchor exists); E > 1
  throughout; **no gate fires and none retires** — DITERSUP §S3 gate J3b stays
  BLOCKED-ON-CARRIER-TIE (§10 displays the tie it needs), the Asvin P0
  application gate stands; no `.lean` file is touched; no density/menu/count
  statement is made; MT3's 9 single-pair escapes and the 9 UNDECIDED cyclic rows
  are disclosed above; **own acceptance counter 0/2** — nothing here may be
  consumed at proof grade before its hostile arc.

---

## §9. MACHINE BRACKET

### 9.1 SEALED PREDICTIONS (commit 1; battery NOT yet run)

Runner: `verification/openmath/grt_jc_checks.py`, whose docstring carries the
authoritative preregistration and **is part of this seal**. It imports the
instrument's tower/stage construction (`grt_jc_probe.ROSTER`/`Stage`, the same 29
rows) and then tests **this note's clauses**, several of which the instrument
never measured. Deterministic, exact arithmetic, no randomness.

| family | the note's clause it tests | sealed prediction |
|---|---|---|
| EXT-GATE | engine_ext `install()`+`check_pins()`+`agreement_gate()` (standing rule) | **0** |
| JC1 | LEMMA JC-PER + JC-DOM's w(π) = E: φ_{γ+kE} == π^k φ_γ byte-for-byte at k = 1,2,3; s-tuple E-periodic; u_1 ↦ u_1+k | **0** |
| JC2 | LEMMA JC-FIB: the s-tuple map is injective on E consecutive γ (⟹ bijection ℤ/E ≅ ∏ℤ/e_j), s_{j+1} ∈ [0,e_j) | **0** |
| **JC3** | **THEOREM JC-SPAN, the note's NEW sharp prediction**: the on-line slot set of φ_γφ_{γ′} at its own weight is EXACTLY {δ}, δ ∈ {0,1}, slot-δ digit u ≠ 0 in K_m; w(φ_γφ_{γ′}) = γ+γ′ | **0** on e_m ≥ 2 rows |
| JC3-FLAT | the e_m = 1 corner (JC-BOX-4): min slot = 0 is PROVED (scored); "max slot = 0" is the unproved sharp form | **0 scored violations**; census reports the count of pairs with a slot > 0 — **measured, NOT scored** |
| JC4 | LEMMA JC-SCAL + §4.1's normalization: slot set of Λ_N(c) == {i : c_i ≠ 0} ⊆ {0..g_m−1} with slot-i digit == c_i; **𝑅_N(X_N) == 1 exactly** | **0** |
| JC5 | LEMMA JC-ANCHMON: Σ_{j<m}s_{j+1}degΦ_j < degΦ_m; the anchor's Φ_m-development is the single digit at abscissa s_{NR}; slot set {0}; a_λ ≠ 0 | **0** |
| JC6 | COROLLARY JC-PSIKER: w(Φ_{m+1}) == wΦ_{NR}; 𝑅(Φ_{m+1}) == ψ_m coefficientwise; read == 0; and Φ_{m+1}+φ_λ vs φ_λ = equal reads, different classes | **0** |
| JC7 | COROLLARY W-9: the mod-E 2-cocycle identity (E \| G_0 so the classes match), the integer carry identity δ(r,s)+δ(r+s,t) = δ(s,t)+δ(r,s+t), and the E-fold chain c(φ_1^E) == ∏_{k=1}^{E−1}c_val(γ_1,kγ_1) (monodromy = gauge period, two ways; E ≤ 8) | **0** |
| JC8 | LAW JC-CYC + FINDING JC-F1: a CYCLIC verdict ⟹ the collapse geography (\|K\| = 2 ∨ g_m = 1 ∨ e_0 = 1); every structure constant is a UNIT (so JC-F1's power basis exists) | **0** |
| **MJ1** | tooth: "TC-3 is never load-bearing" (a RAW scalar on every pair) | **≥ 1 firing**; and 0 pairs where RAW fails at δ < g_m or succeeds at δ ≥ g_m (either would REFUTE JC-LOAD) |
| **MJ2** | tooth: mutated periodicity φ_{γ+E} == π²φ_γ | **≥ 1 firing per row** |
| **MJ3** | tooth: mutated scalar image "slots ⊆ {0}" | **≥ 1 firing per g_m ≥ 2 row** |
| **MJ4** | tooth: "the read is injective on gr_λ" (read(wΦ,Φ_{m+1}) ≠ 0) | **≥ 1 firing per row** |
| **MJ5** | tooth: mutated span law "slot set == {δ+1}" | **≥ 1 firing per row** |

A silent tooth is a RED. Exit code = (violations + silent teeth).

**BUILD-PHASE SMOKE DISCLOSURE (pre-seal, honest; part of this seal).** One
3-row smoke of this runner (C2A / C2I / C3A — one g_m = 1 wild row, one g_m = 2
row, one m = 2 row) ran during construction, elapsed 0.2 s. Result:
**0 violations in every family (JC1 147, JC2 32, JC3 224, JC4 30, JC5 48,
JC6 12, JC7 81, JC8 99 samples), all five teeth FIRED** (MJ1 8, MJ2 16, MJ3 2,
MJ4 3, MJ5 56 firings). Specifically: JC3's sharp slot-span prediction held on
**56/56** pairs; MJ1 found **8 of 32** tested pairs with no pre-TC-3 scalar and
**all 8 were in the δ ≥ g_m load set** (JC-LOAD's dichotomy, both directions);
JC7's E-fold chain matched the orbit product on all three rows
(C2A z̄¹ = z̄¹, C2I z̄² = z̄², C3A z̄² = z̄²); JC8 returned CYCLIC for C2A and
C3A (both g_m = 1 = collapse geography) and NOT-CYCLIC for C2I (g_m = 2) —
**agreeing row-for-row with the instrument's independent MT2 verdicts**. **No
sealed prediction was changed by the smoke, and no clause of §§2–6 was edited
because of it.** Two construction-time design choices were fixed BEFORE the
smoke and are disclosed: (i) JC7/JC8 use the full E² constant table when E ≤ 8
and the probe's designed subset above it (at E > 8 the adjudicator returns
UNDECIDED, so a truncated table cannot manufacture a CYCLIC verdict);
(ii) per-row tooth obligations are scored as their own family (TOOTH-ROW).

### 9.2 VERDICT (commit 2 — written FROM the artifacts)

**Artifacts:** `verification/openmath/grt_jc_checks_output.txt`,
`grt_jc_checks_results.json` (deterministic; 29 rows, elapsed **2.0 s**; seal
commit `6ad01d1`). **ALL 10 FAMILIES GREEN — 0 violations, every sealed
prediction hit exactly; ALL FIVE TEETH FIRED (no silent tooth).**

| family | the clause | samples | violations | verdict |
|---|---|---|---|---|
| EXT-GATE | engine_ext standing rule | 1 | 0 | GREEN (0 new) |
| JC1 | JC-PER + w(π) = E | 2,594 | **0** | GREEN — π^k-periodicity byte-for-byte at k = 1,2,3, s-tuple periodic, u_1 ↦ u_1+k, w(π) = E on all 29 rows |
| JC2 | JC-FIB | 570 | **0** | GREEN — the s-tuple map is injective on E consecutive γ on every row |
| **JC3** | **JC-SPAN (the note's new sharp prediction)** | 2,484 | **0** | GREEN — **slot set == {δ} on 609/609 pairs** with e_m ≥ 2; δ ∈ {0,1} everywhere; u ≠ 0 everywhere |
| JC3-FLAT | the e_m = 1 corner (JC-BOX-4) | 24 | **0** scored | GREEN; **census: 0 of 24 pairs have a slot > 0** — the unproved sharp form is measured true on the top-flat row (C4H) |
| JC4 | JC-SCAL + the lift normalization | 443 | **0** | GREEN — Λ_N(c)'s slot set == supp(c) ⊆ {0..g_m−1} with slot-i digit == c_i, and 𝑅_N(X_N) == 1 exactly, on every row and every c ∈ K |
| JC5 | JC-ANCHMON | 855 | **0** | GREEN — the telescoping degree bound, the single-digit development, slot set {0}, a_λ ≠ 0 |
| JC6 | JC-PSIKER | 116 | **0** | GREEN — w(Φ_{m+1}) = wΦ_{NR}, 𝑅(Φ_{m+1}) == ψ_m coefficientwise, read == 0, and the equal-read/different-class pair |
| JC7 | W-9 cocycle semantics | 581 | **0** | GREEN — **261 triples** satisfy both the K^*-cocycle identity and the integer carry identity; the **E-fold chain matched the orbit product on all 15 rows with E ≤ 8** |
| JC8 | JC-CYC + JC-F1 | 898 | **0** | ~~GREEN — every structure constant a unit (so JC-F1's power basis exists on every row)~~ **[r1, G3 — RE-LABELLED: this battery does NOT evidence the unit property.]** GREEN for the ONE falsifiable half only: **no CYCLIC verdict off the collapse geography** (29 rows). The unit half is **VACUOUS as coded**: the JC7 block builds the table with `if v is None or K.is_zero(v): continue`, so zeros and undefined constants are filtered out BEFORE the JC8 predicate `if K.is_zero(v)` can see them — the violation branch is unreachable and the skipped pairs were never censused. Mathematically the unit property IS proved (§3.2: u, a_λ ∈ K_m^*, z̄ a unit, so c_{m+1} ∈ K^*), and the E-fold chain leg (15 rows with E ≤ 8) is real evidence for JC-F1's power basis, but it too `break`s silently on a zero. The falsifiable replacement — a full-grid classification (unit / zero / undefined / out-of-window) with the skipped-pair census, plus a planted-zero tooth proving the predicate can fire — is r1 family **R1-UNIT** + tooth **T4** (§9.3) |
| MJ1 | tooth: "TC-3 never load-bearing" | 333 tested | **103 firings** | FIRED — 103 pairs have NO pre-TC-3 scalar and **all 103 lie in the δ ≥ g_m load set**; 0 anomalies in either direction (JC-LOAD's dichotomy, machine-confirmed both ways) |
| MJ2 | tooth: φ_{γ+E} = π²φ_γ | 285 | **285 firings** | FIRED on every row |
| MJ3 | tooth: "Λ_N slots ⊆ {0}" | 6 | **4 firings** | FIRED on every g_m ≥ 2 row (2 of the 6 opportunities are the c's whose slot 1 is genuinely empty) |
| MJ4 | tooth: "the read is injective on gr_λ" | 29 | **29 firings** | FIRED on every row — read(wΦ, Φ_{m+1}) = 0 everywhere |
| MJ5 | tooth: slot set == {δ+1} | 633 | **633 firings** | FIRED on every pair |

**The cyclic split reproduced: CYCLIC 6 / NOT-CYCLIC 14 / UNDECIDED 9**, with the
cyclic rows **C2A / C2E / C2G / C2J / C3A / C4A** — *the same six rows, and the
same 14/6/9 split, as the instrument's MT2*. **Disclosure (resolution, honest):**
this battery's constant table is the harness ratio c_val (via the probe's
`Stage.cval`), whereas the instrument's MT2 used the fence-clean gr-side
certified constant c_gr; the two tables agree because W-8/P5-OB6 says
c_gr = c_val (0/669), so the verdict-identity is a *consistency* check of W-8,
not a second independent measurement of the split. The adjudicator itself is a
fresh transcription.

**TWO BATTERY-DRIVEN FINDINGS, applied above:**

1. **The collapse geography does NOT imply cyclic** (the converse of JC-CYC(d) is
   FALSE): 13 rows sit in the collapse geography and still come back NOT-CYCLIC
   (C2B, C2C, C2D, C2H, C3D, C3E, C3F, C3H, C3I, C4B, C4G, I4B, I4C). Two
   mechanisms are visible in the printed table: **≥ 2 distinct non-1 values**
   (C2B/C2D/C2H/C3D/C3E/C3F/C3H/C4B/C4G/I4B/I4C — up to **7** distinct values on
   I4C) and **a single value whose carry pattern is not realizable by any integer
   relabeling** (C2C, C3I). §6(d) is stated one-directionally because of this,
   and JC-CYC(b)'s obstruction direction is what does the work.
2. **The law's resolution on this roster is low and is disclosed**: only **2 of
   29 rows (C2I, C4I) are OFF the collapse geography**, and both are
   NOT-CYCLIC / UNDECIDED — so "CYCLIC ⟹ collapse" was tested against few
   potential counterexamples. A hostile pass should build g_m ≥ 2 rows with
   small tables.

### 9.3 [r1] THE SUPPLEMENTARY r1 BATTERY (own two-commit mini-seal)

**Runner:** `verification/openmath/grt_jc_r1_checks.py`, whose docstring carries
the authoritative preregistration and **is part of this mini-seal** (commit 1 =
runner + this table, battery NOT yet run; commit 2 = the verdict written FROM the
committed artifacts `grt_jc_r1_output.txt` / `grt_jc_r1_results.json`). It
imports the instrument's roster and stage builder (`grt_jc_probe.ROSTER`/`Stage`
— the same 29 rows) and tests **only the statements r1 introduced or repaired**.
The sealed r0 battery, the instrument, and all their artifacts are untouched.
Fence hygiene as in §3.5 [r1, G8]: `T.constants` is used only for the integer δ,
`T.read`/`T.read_coeffs` supply the digit data that the repaired statements are
*about*.

| family | the r1 statement it tests | sealed prediction |
|---|---|---|
| EXT-GATE | engine_ext `install()`+`check_pins()`+`agreement_gate()` (standing rule) | **0** |
| **R1-BND** | §2.10's slot bound: maxslot(G0) == 0 on every row — i.e. the r0 (COORD)'s surjectivity onto Δ is FALSE at the note's own window base (PE1's counter-instance, reproduced as a scored fact) | **0** violations of "maxslot(G0) == 0"; census printed |
| **R1-PER** | LEMMA JC-PIINV: 𝑅_{λ+kE}(π^kf) == c_π^k·𝑅_λ(f) with ONE c_π per row (independent of f, λ, slot, k), and ρ_{λ+kE}(π^kf) == ρ_λ(f) EXACTLY, k = 1,2 | **0** |
| **R1-INJ** | §1's injectivity, both directions: 𝑅_λ(f) == 0 ⟺ w(f) > λ | **0** |
| **R1-SURJ** | LEMMA JC-BSURJ: for targets p of y-degree 0,1,2 the REALIZE construction at the predicted k gives integral f with w(f) == n+kE and 𝑅(f) == p ON THE NOSE; the minimal k is censused (k > 0 for degree ≥ 1 — the k-shift is structural) | **0** |
| **R1-DMULT** | (DMULT): 𝑅_{λ+μ}(fg) == y^{δ(λ,μ)}·𝑅_λ(f)·𝑅_μ(g) EXACTLY (not merely up to a unit) on sampled pairs — the Δ-module half of (COORD-B), the leg neither prior runner had | **0** |
| **R1-COB** | COROLLARY JC-COB: 𝑅_{γ+γ′}(φ_γφ_{γ′}) == a_γ·a_{γ′}·y^δ on the full anchor grid (a sharp consequence of (DMULT): a failure refutes (COORD-B)(2)) | **0** |
| **R1-PSIK-LO** | JC-PSIKER(ii) lower half: at window lines λ < wΦ_NR no class is certified dead by TC-3 (the kernel is 0 there — one-sided certifier, JC-BOX-8(ii)) | **0** |
| **R1-PSIK-HI** | JC-PSIKER(iii): for EVERY residue ν ∈ ℤ/E, at a line λ ≡ ν with λ−wΦ_NR ∈ W, the witness Φ_{m+1}·φ_{λ−wΦ_NR} has w == λ, digit polynomial == (unit)·y^k·ψ_m(y), read == 0, and its death is certified | **0** |
| **R1-UNIT** | G3's falsifiable replacement: every constant of the FULL E×E grid classified (unit / zero / undefined-denominator / out-of-window); scored = "no zero and no undefined-denominator among in-window pairs", with the skipped-pair census printed | **0**, census printed |
| **T1** | tooth: the REFUTED r0 universal claim "TC-3 has a nonzero kernel on every graded piece of gr" (operationalized at the window base: λ − wΦ_NR ≥ 0 at λ = G0) | **≥ 1 firing per row** |
| **T2** | tooth: "no k-shift is needed" (a y-degree-1 target realizable already at k = 0, i.e. maxslot(G0) ≥ 1) | **≥ 1 firing per row** |
| **T3** | tooth: mutated (DMULT) with the shift y^{δ+1} | **≥ 1 firing per row** |
| **T4** | tooth: a PLANTED ZERO injected into the constant table, to prove R1-UNIT's predicate can fire at all (the exact defect G3 found in JC8) | **≥ 1 firing per row** |
| **T5** | tooth: mutated JC-PIINV "ρ_{λ+E}(πf) == y·ρ_λ(f)" (a slot shift, always false) | **≥ 1 firing per row** |

A silent tooth is a RED. Exit code = (violations + silent teeth).

**PRE-SEAL SMOKE DISCLOSURE (honest, part of this mini-seal).** Two read-only
/tmp scripts were run BEFORE the seal to fix the design and the cost: (a) a
6-row mechanism probe (C2A/C2I/C3A/C3I/C4H/C4I) which found — and is why the
predictions above are stated in this exact form — that c_π is a single row
constant taking values in {1, z̄, z̄²}, that ρ-invariance is EXACT, that (DMULT)
holds with multiplier exactly **1** (so JC-COB's u = a_γa_{γ′} is the right
sharp form), that the REALIZE construction reproduces degree-1 and degree-2
targets on the nose, and that the PSIKER witness behaves as JC-PSIKER(iii) says;
(b) a 29-row cost probe fixing the k-search caps (minimal k ≤ 34 for degree 2,
psiker line offset ≤ 14 steps). No scored predicate was weakened by either probe,
and the two teeth T1/T2 are the r0 text's own refuted claims, fixed before the
probes were written.

**VERDICT (written FROM the committed artifacts
`verification/openmath/grt_jc_r1_output.txt` + `grt_jc_r1_results.json`; runner
md5 `7f896bfa27d06158f95c5987c7299770`, sealed UNRUN at commit `f45b63c`).**
~~**ALL 10 FAMILIES GREEN — 10,475 scored samples**~~ **[r2, G-8 — the split,
displayed: ALL 10 FAMILIES GREEN with 10,330 scored samples (EXT-GATE 1 +
R1-BND 29 + R1-PER 841 + R1-INJ 585 + R1-SURJ 841 + R1-DMULT 2,784 + R1-COB
2,607 + R1-PSIK-LO 591 + R1-PSIK-HI 1,182 + R1-UNIT 869), plus the ELEVENTH
table row TOOTH-ROW 145 (a family by §9.1's own convention) = 10,475 rows
scored over the 11-row table; the r1 headline attached the 11-row total to a
10-family label]**, **0 violations, 29 rows,
elapsed 2.6 s, exit 0; ALL FIVE TEETH FIRED (1,885 firings, no silent tooth,
every per-row obligation met: TOOTH-ROW 145/145).** Every sealed prediction hit
exactly.

| family | the r1 statement | samples | violations | verdict |
|---|---|---|---|---|
| EXT-GATE | engine_ext standing rule | 1 | **0** | GREEN (0 new) |
| **R1-BND** | the slot bound: maxslot(G0) == 0 | 29 | **0** | GREEN — **0 on 29/29 rows**, i.e. the r0 (COORD) is refuted at the note's own base on every row; the ladder census maxslot(G0+kE), k = 0..3, shows the growth that makes B_n ⊋ gr_n (e.g. C2A [0,0,1,1], C2D [0,1,1,1], I4C [0,0,0,0] — slower but unbounded) |
| **R1-PER** | JC-PIINV | 841 | **0** | GREEN — c_π is ONE constant per row (k = 1 and k = 2 consistent, c_π² exact) and ρ is EXACTLY π-invariant; measured c_π = 1 on 9 rows and z̄^a with a ∈ {1,2,3,4,6,8} on the other 20 — so the un-normalized 𝑅 is genuinely NOT π-invariant and the ρ-normalization is doing real work |
| **R1-INJ** | §1 injectivity, both directions | 585 | **0** | GREEN — 𝑅_λ(f) ≠ 0 at λ = w(f), and empty at λ = w(f)−E, w(f)−2E |
| **R1-SURJ** | JC-BSURJ | 841 | **0** | GREEN — every target (degrees 0,1,2 × {all-ones, mixed}) realized on the nose at the predicted k, with REALIZE's R2/R3 laws verified per digit; minimal k for the all-ones targets: degree 0 at k = 0 on 28 rows (k = 2 on C4H), degree 1 at k = 2..16, degree 2 at k = 5..34 — **the k-shift is structural, not a convenience** |
| **R1-DMULT** | (DMULT), the cited input | 2,784 | **0** | GREEN — 𝑅_{λ+μ}(fg) == y^{δ}𝑅_λ(f)𝑅_μ(g) **EXACTLY** (multiplier 1, not merely proportional) on every sampled pair of every row, together with w(fg) = w(f)+w(g). This is the Δ-module leg PE1 recorded as unmeasured |
| **R1-COB** | JC-COB | 2,607 | **0** | GREEN — **u == a_γ·a_{γ′} with slot set exactly {δ} on 869/869 anchor pairs, all 29 rows**, including the e_m = 1 row C4H (0 out-of-window skips) |
| **R1-PSIK-LO** | JC-PSIKER(ii), zero half | 591 | **0** | GREEN — **197 window lines below wΦ_NR**, no class certified dead at any of them (one-sided certifier, JC-BOX-8(ii)) |
| **R1-PSIK-HI** | JC-PSIKER(iii) | 1,182 | **0** | GREEN — **197 residue classes** (all E classes per row, capped at 8) carry a witness Φ_{m+1}·φ_{λ−wΦ_NR} with w exact, digit polynomial == a_ν·y^δ·ψ_m(y) on the nose, read == 0, death CERTIFIED |
| **R1-UNIT** | G3's falsifiable unit check | 869 | **0** | GREEN with the census r0 lacked: **869 unit / 0 zero / 0 undefined-denominator / 0 out-of-window over 869 grid pairs** — and tooth T4 proves the predicate can fire (a planted zero is caught on every row, which the r0 JC8 predicate could not do) |
| TOOTH-ROW | per-row tooth obligations | 145 | **0** | GREEN — all five teeth fire on all 29 rows |

| tooth | mutation | opportunities | firings |
|---|---|---|---|
| T1 | the REFUTED r0 universal kernel claim (λ−wΦ_NR ≥ 0 at λ = G0) | 29 | **29** |
| T2 | "no k-shift needed" (maxslot(G0) ≥ 1) | 29 | **29** |
| T3 | mutated (DMULT), shift y^{δ+1} | 1,392 | **1,392** |
| T4 | planted zero in the constant table (G3's falsifiability check) | 29 | **29** |
| T5 | mutated JC-PIINV, ρ_{λ+E}(πf) == y·ρ_λ(f) | 406 | **406** |

**THREE FINDINGS OF THE r1 BATTERY, applied above.**
1. **(DMULT) holds with multiplier exactly 1**, not merely up to a line-wise
   unit — which is why JC-COB can be stated in the sharp form u = a_γa_{γ′}
   (§2.10) rather than "u is some K_m^*-unit". **[r2, G-1: this measured
   finding IS the exact tier (DMULT-s) — it is the note's evidence FOR that
   tier, not a citation of it.]**
2. **The e_m = 1 corner's sharp form is measured true by R1-COB on C4H** (slot
   set exactly {δ} = {0} on all 24 of its grid pairs), and on (DMULT) it is in
   fact PROVED — see JC-BOX-4 [r1].
3. **c_π ≠ 1 on 20 of 29 rows.** The colimit coordinate would NOT be well
   defined in the un-normalized 𝑅; JC-PIINV(c)'s ρ-normalization is
   load-bearing, not cosmetic.

**[r2, G-2 — INSTRUMENT DISCLOSURE the r1 battery owed: R1-DMULT's sample
composition and its silent skip.]** PE2's code audit of the byte-frozen
`grt_jc_r1_checks.py`, confirmed here against the source: the per-row sample
list has SEVEN elements — up to three anchors φ_r, the scalar lift X_N, one
anchor product φ_0φ_{1 mod E}, (1+π)φ_0, and Φ_{m+1} — of which **six have
SINGLE-SLOT (monomial) digit polynomials** (JC-ANCHMON(c), JC-SCAL(b),
JC-SPAN, and π-scaling; Φ_{m+1}, whose digit polynomial is ψ_m, is the only
multi-slot element), and the DMULT loop **`continue`s the one
non-monomial × non-monomial pair** `(Φ_{m+1}, Φ_{m+1})` — a skip the r1 text
did not disclose. Consequence: on every one of R1-DMULT's 48 ordered pairs
per row, y^δ·𝑅(f)·𝑅(g) is a shift-and-scale of one factor — the identity's
genuinely BILINEAR content (cross-term convolution of two multi-slot digit
polynomials) was **never exercised** by r1 (R1-PSIK-HI's Φ_{m+1}·φ_ν leg is
non-monomial × monomial, still one-sided). The verdict cell above
("on every sampled pair") is therefore true but weaker than it reads. This is
the same defect species r1 repaired in G3/G6, reintroduced in the new leg;
the repair is r2's own machine leg (§9.4): dense multi-slot × multi-slot
pairs (R2-BIL), the skipped pair scored (R2-PHI), the sample-composition
facts above scored rather than asserted (R2-MONO), and the cross-term tooth
U2 that is provably silent on every r1-tested pair.

**Honest scope of this leg.** It measures the r1 statements on the SAME 29-row
roster (m ≤ 3, |K| ≤ 25, g_j ≤ 2, d_0 ≤ 3, p ∈ {2,3,5}), so JC-BOX-1's
proof-scope-vs-machine-scope fence applies verbatim; and it does NOT touch the
one place r1 leaves a measurement owed, the non-integral elements of B
(JC-BOX-8(i)).

### 9.4 [r2] THE SUPPLEMENTARY r2 BATTERY — the bilinearity leg (own two-commit mini-seal)

**Runner:** `verification/openmath/grt_jc_r2_checks.py`, whose docstring
carries the authoritative preregistration and **is part of this mini-seal**
(commit 1 = the runner alone, SEALED and UNRUN, exactly the r1 protocol;
commit 2 = the verdict below, written FROM the committed artifacts
`grt_jc_r2_output.txt` / `grt_jc_r2_results.json`). It imports the
instrument's roster and stage builder (`grt_jc_probe.ROSTER`/`Stage`, the same
29 rows) and the byte-frozen r1 helpers (`grt_jc_r1_checks.Rpoly`/`pmul`/
`surj_build` — imported, not re-typed, so the (DMULT) predicate is the SAME
predicate PE2 audited as independent), and tests **only what G-2 found
missing: the bilinear content of (DMULT-s)**. The r0 battery, the r1 battery,
the instrument, and ALL their artifacts stay byte-frozen. Fence hygiene as in
§3.5 [r1, G8]: `T.constants` only for the integer δ; `T.read_coeffs` supplies
the digit data under test.

| family | the statement it tests | sealed prediction |
|---|---|---|
| EXT-GATE | engine_ext `install()`+`check_pins()`+`agreement_gate()` (standing rule) | **0** |
| **R2-BIL** | (DMULT-s) on genuinely BILINEAR input: both factors built by the JC-BSURJ construction with **dense multi-slot targets** (degree-2 all-coefficients-nonzero "ones" and "mixed" variants on every row — realizable per R1-SURJ's census k ≤ 34; a degree-3 dense pair attempted per row with the same k-cap 80, CENSUSED where realized, not scored where not), every ordered pair tested: w(fg) == w(f)+w(g) and 𝑅_{λ+μ}(fg) == y^δ·𝑅_λ(f)·𝑅_μ(g) EXACTLY (dict equality — the cross-term convolution finally exercised) | **0** |
| **R2-PHI** | the pair r1 silently skipped, scored on every row: f = g = Φ_{m+1}, i.e. w(Φ_{m+1}²) == 2wΦ_NR and 𝑅_{2wΦ_NR}(Φ_{m+1}²) == y^{δ(wΦ,wΦ)}·ψ_m(y)² exactly; the skipped-pair census printed (r1 skipped exactly this 1 pair per row) | **0** |
| **R2-MONO** | §9.3 [r2, G-2]'s disclosure as SCORED fact, not prose: (a) exactly ONE of the r1 sample elements per row has a multi-slot digit polynomial; (b) every r1-TESTED DMULT pair (the skip excluded) has ≥ 1 single-slot factor; (c) the U2 mutation, replayed on the r1-tested pairs, fires **0** times there — machine proof that the r1 leg had zero resolution against it | **0** |
| **U1** | tooth: the y^{δ+1} shift mutation on the new dense pairs (the r1 T3 tooth, re-armed here to prove the r2 predicate is live) | **≥ 1 firing per row** |
| **U2** | tooth: the **CROSS-TERM DROP** — the mutated product keeps only the terms a_ib_j with i ∈ {min, max} of supp 𝑅(f) OR j ∈ {min, max} of supp 𝑅(g), i.e. it deletes exactly the interior×interior convolution terms. PROVABLY equal to the true product whenever either factor has ≤ 2 occupied slots (all its indices are extremal) — hence silent on every r1-tested pair (scored as R2-MONO(c)) — and provably different on a dense deg-2 × dense deg-2 pair over a field (the dropped a₁b₁ ≠ 0 moves the slot-(2+δ) coefficient) | **≥ 1 firing per row** |
| TOOTH-ROW | per-row tooth obligations (U1, U2) | **0** |

A silent tooth is a RED. Exit code = (violations + silent teeth).

**PRE-SEAL SMOKE DISCLOSURE (honest, part of this mini-seal).** One read-only
/tmp design probe ran BEFORE the seal on rows C2A/C2I/C4H to fix the dense
construction and cost (it found: dense degree-2 targets realize within the
R1-SURJ k-range on all three; the U2 mutation fires on the dense pairs and is
silent on the r1 pairs there; per-row cost comparable to r1's). No scored
predicate was weakened by it.

**VERDICT (written FROM the committed artifacts
`verification/openmath/grt_jc_r2_output.txt` + `grt_jc_r2_results.json`;
runner md5 `c02bf06029a72259512ea005bd2562fd`, sealed UNRUN at mini-seal
commit 1 = `79611a4`).** **ALL 4 FAMILIES GREEN — 3,597 scored samples in the
four families (EXT-GATE 1 + R2-BIL 696 + R2-PHI 87 + R2-MONO 2,813) plus
TOOTH-ROW 58 = 3,655 table rows, 0 violations, 29 rows, elapsed 7.4 s, exit
0; BOTH TEETH FIRED ON EVERY OPPORTUNITY (U1 261/261, U2 261/261, no silent
tooth).** Every sealed prediction hit exactly.

| family | result |
|---|---|
| **R2-BIL** | **0 violations on 261 dense multi-slot × multi-slot ordered pairs** (9 per row: the dense set D realized THREE elements on all 29 rows — degree-2 "ones2"/"mix2" at k = 5..34 and, censused, the degree-3 dense "ones3" at k = 7..52, so every row's D is {3,3,4}-slot dense) — **(DMULT-s) holds EXACTLY (dict equality, multiplier 1) on genuinely bilinear input**, cross-term convolution finally exercised, together with w(fg) = w(f)+w(g) on every pair |
| **R2-PHI** | **0 violations on 29/29 rows** for the pair r1 `continue`d: 𝑅(Φ_{m+1}) = ψ_m coefficientwise, w(Φ_{m+1}²) = 2wΦ_NR, and 𝑅(Φ²) = y^δ·ψ_m(y)² exactly (δ = 0 on every row — E \| wΦ_NR forces s_NR(wΦ_NR) = 0). **Census: the skipped pair has genuine bilinear content (occupied interior ψ_m slot) on exactly the two g_m = 2 rows, C2I and C4I** — on the other 27 rows ψ_m is 2-slot and the skip cost nothing; on those two, r1's one true bilinear pair was the skipped one |
| **R2-MONO** | **0 violations**: exactly ONE multi-slot element among the r1 samples on every row (Φ_{m+1}); every r1-TESTED pair has ≥ 1 single-slot factor (29/29 rows); and **U2 replayed on the r1-tested pairs fired 0 times across the whole roster** — machine proof that the r1 leg had zero resolution against the cross-term mutation class |
| **U1 / U2** | U1 (y^{δ+1} shift) 261/261, U2 (cross-term drop) **261/261 — U2 fires on EVERY dense pair and NEVER on an r1-tested pair**, which is exactly the separation the tooth was designed to exhibit |

**What this leg does and does not carry.** It supplies the missing bilinear
evidence for **(DMULT-s)** on the roster (m ≤ 3 machine scope, JC-BOX-1
verbatim); it does NOT convert (DMULT-s) to CITED — the tier split of
§2.10 [r2, G-1] stands, and the non-integral residue JC-BOX-8(i) is still
untouched by every runner.

### 9.5 [r2] THE BRACKET-SWEEP RECORD (G-4: struck names re-pointed to fixed point)

PE2 found the `[r1]` strike system leaking: live text still CONSUMING the
struck `(COORD)`/`(MULT)` at seven sites, worst inside the W-7 THEOREM box.
r2 re-pointed every live consuming site, each with a `[r2, G-4]` (or
`[r2, G-1]`) bracket:

1. W-7 THEOREM box, OB-4 grade line (the honesty defect: graded OB-4 on the
   refuted input and denied r1's own machine leg) — struck and regenerated.
2. §3.2 JC-CARRY-m proof ("the definition of A(γ,γ′) in (MULT)") → (MULT-B)|gr.
3. §4.1 W-8 proof ("Apply ρ_{λ+N} and (MULT)") → (MULT-B)|gr.
4. §4.2 offset-transport proof ("Apply (MULT)") → (MULT-B)|gr.
5. §5 proof (i) ("expanding both with (MULT)") → (MULT-B)|gr.
6. §5 proof (iv) ("iterating (MULT)") → (MULT-B)|gr.
7. §4.1 remark (b) (the second honesty defect: the pre-repair footprint
   sentence "supplies it from FGMN Thm 4.2") — struck and regenerated on the
   (DMULT-w) footprint.
8. (lower weight) §10.1 r0 grade table, W-8 row → (COORD-B)+(MULT-B).
9. (lower weight) W-8 [r1] grade-line tail "(i.e. FGMN (b)(c)(e) via W-1)" →
   (b)(e) + (c)-only-through-(DMULT-w).
10. (courtesy) §2.10's repair narrative "(COORD)/(MULT)/TC-3 belong strictly
    AFTER TC-1" → named the B-restatements instead.

The gr-level restriction that makes sites 2–6 rigorous ((MULT-B)|gr:
ρ^B|_{gr_λ} = ρ_λ, products of gr-elements stay in gr) is recorded ONCE, at
the end of (MULT-B)'s proof [r2, G-4]. **Fixed-point re-grep, protocol and
result:** grep for `(COORD)`/`(MULT)` excluding `-B` forms; every remaining
hit must be (a) inside a `~~…~~` strike, (b) a quotation of the struck r0
wording inside an `[r1]`/`[r2]` bracket, or (c) a reference to the r0 form AS
refuted (R1-BND's rows, the repair-history blocks). Count at r2 close: the
grep returns **22 hit-lines**, classified: **11** inside `~~…~~` strikes or
strike-and-replace brackets (the struck (COORD)/(MULT) displays and their
[r1]/[r2] supersessions), **4** in the r1 repair-history header naming the
struck forms as the objects repaired, **2** R1-BND rows citing the r0 (COORD)
as refuted, **3** in this §9.5 record itself, **2** in [r2, G-4]'s own
quotation brackets (§2.10's narrative line; the (MULT-B)|gr display naming
"the STRUCK name (MULT)") = 22. **0 live consuming sites**;
PE2's seven, plus the two lower-weight §10.1/W-8 sites, all re-pointed.

---

## §10. GRADE BOX, THE CONDITIONALITY STACK, AND CONSUMERS

### 10.1 Per-clause grades

**[r1] GRADE BOX, POST-REPAIR (read this first; the r0 table below stands except
where this block supersedes it).** ~~Arc: **composed (0/2) → JC-PE1: 2 CRITICAL +
8 gaps → r1 (this round, STRUCTURAL) → JC-PE2 next**.~~ **[r2] Arc: composed
(0/2) → JC-PE1 (2 CRITICAL + 8 gaps) → r1 (STRUCTURAL) → JC-PE2 (0 CRITICAL +
9 gaps; "no false statement") → r2 (labelling/footprint/disclosure + the
bilinearity machine leg, §9.4) → JC-PE3 next.** Acceptance counter
**0/2** (a repair round is not a pass). **[r2] Grade deltas at r2: NONE — the
one status that MOVES is (DMULT)'s label (its exact tier from "CITED" to
MEASURED, §2.10 [r2, G-1]), which downgrades no clause grade but re-fences
JC-COB's sharp form onto the measured tier.**

| clause | r0 grade | r1 grade | what changed |
|---|---|---|---|
| **W-6** | PROVED general m | **PROVED general m** | (ii) re-keyed to B_n (G1); (v) re-quantified (F2); ~~box JC-BOX-4 unchanged~~ **[r2, G-7: JC-BOX-4 CHANGED at r1 — it gained the conditional closure on (DMULT-w); the corner is closed for a reader granting that tier, open for one wanting it FGMN-free]** |
| **W-7** | PROVED on stated scopes | **PROVED on stated scopes, one clause STRENGTHENED** | OB-4 re-derived on B (F1); spanning promoted from definition to theorem, so Ψ is onto the WHOLE transported ring (G2/F1) |
| **W-8** | PROVED general m | **PROVED general m** | inputs re-listed as (COORD-B)+(MULT-B)+JC-SPAN+JC-SCAL+R3; remark (a)'s two identifications struck (G7) and replaced by JC-COB |
| **W-9** | PROVED given W-6..W-8 | **PROVED given W-6..W-8** | JC-F1's dimension count now rests on the repaired display; JC-F2 added as a second REVIEW-OWED display correction (G2) |
| cyclic fence | REFINED, not refuted | **unchanged** | no measured verdict moves at r1 |

**Newly PROVED at r1** (all at general m, on the inputs named): JC-LOC,
JC-PIINV, JC-BSURJ, (COORD-B)(1), (COORD-B)(2) from (1)+(DMULT), (MULT-B),
JC-COB, JC-PSIKER(ii)(iii). **Newly boxed:** JC-BOX-8 (r1's three residues).
**Nothing was downgraded to boxed at r1** — every one of PE1's five listed
consumers re-derived through, which is the round's substantive claim and the
first thing JC-PE2 should attack.

| clause | content | grade |
|---|---|---|
| **W-6** | carry-target existence: TC-1 legitimate (JC-DOM), TC-2 legitimate + ℤ→ℤ/E collapse (JC-GAUGE), the surviving fibred index (JC-FIB), OB-2 periodicity (JC-PER), the anchor-monomial and scalar-image lemmas, **THEOREM JC-LOAD** (TC-3 load-bearing exactly at δ ≥ g_m) and **COROLLARY JC-PSIKER** (TC-3 is not a relabeling) | **PROVED at general m**, attempt 0/2, one located box: the top-flat corner e_m = 1 ∧ g_m = 1 (JC-BOX-4) |
| **W-7** | Ψ: OB-2 **PROVED general m**; OB-3 existence/structure (constant = (K_m^*-unit)·z̄^δ) **PROVED general m on ALL window pairs**; OB-3 value (inner = ∏_{j≤m}z_j^{D_j}) **PROVED general m on [ILN]†'s scored stratum**; OB-4 independence **PROVED general m** (Δ-rank input literature-carried); OB-5 fence **DISCHARGED as architecture** | **PROVED on the stated scopes**, attempt 0/2; the germ split displayed honestly (val law CONFIRMED on 27 stages; H-D REFUTED 138/669) |
| **W-8** | harness-val = TC-read (OB-6), with every line-wise normalization cancelling; J-C(iii) residue chain | **PROVED at general m** on ~~(COORD)+(MULT)~~ **(COORD-B)+(MULT-B) [r2, G-4]**+JC-SPAN+JC-SCAL+R3, attempt 0/2 |
| **W-9** | cocycle semantics: descent to ℤ/E, COR-2 = gr-associativity, the {0,1} carry cocycle, the twisted-group-algebra display, COR-4 monodromy = the gauge period | **PROVED given W-6..W-8** (S-priced, as the blueprint priced it), attempt 0/2 |
| **cyclic fence** | LAW JC-CYC: abstract cyclicity always (JC-F1, **review-owed display correction**); the adjudicated (CYC) property is the letter-monomial one; obstruction direction PROVED; twist-blind direction PROVED; the inclusion CYCLIC ⟹ collapse MEASURED (m ≤ 3, 0/29, low resolution) with its general form OPEN and its **converse REFUTED** by this note's own battery (13 collapse rows NOT-CYCLIC) | **REFINED, not refuted**; byte-frozen 22/28 record unamended |

### 10.2 The conditionality stack (one line, then itemized)

**`[ILN]† ACCEPTED (scored stratum; residuals (RM-m ≥ 2), (W-MULT-DCX-m), (ITER-LAW-LIFT), standard-lift only) + GRB/CARRY-1/D-REAL ACCEPTED-conditional (§0 ladder + [T] pins) + FGMN Thm 4.2 / Thm 4.8 / Cor 2.7 CITED (composite order; numbering re-verification owed) + W-1/W-2/J-A/J-B ATTEMPT 0/2 (with JB-BOX-2's (VD-m) geography) ⟹ this note, attempt 0/2.`**

Nothing in §§2–6 is unconditional. ~~The *weakest* links, ranked for a hostile
pass: (1) FGMN Thm 4.2 at composite order + its transport by W-1 — everything
coordinate-based dies with it (JC-BOX-3); (2) the off-stratum existence claim
with zero machine support (JC-BOX-2); (3) the top-flat corner (JC-BOX-4);
(4) JC-F1's display correction (JC-BOX-5).~~

**[r1] The stack, re-stated after the repair.** The FGMN entry is now narrower
and correctly aimed: `(DMULT)` on **B ≅ gr_{K[x]}(w)` (JC-LOC)** replaces
"Thm 4.2 on gr(w)", and the surjectivity half is proved in-note (JC-BSURJ), so
the one-line stack becomes

**`[ILN]† ACCEPTED (scored stratum; residuals (RM-m ≥ 2), (W-MULT-DCX-m), (ITER-LAW-LIFT), standard-lift only) + GRB/CARRY-1/D-REAL ACCEPTED-conditional (§0 ladder + [T] pins) + (DMULT) on B [= FGMN Thm 4.2's content via JC-LOC] + Thm 4.8/Cor 4.9 + Cor 2.7 CITED (numbering re-verification still owed) + W-1/W-2/J-A/J-B ATTEMPT 0/2 ⟹ this note, attempt 0/2 after r1.`**

Weakest links, re-ranked for JC-PE2: (1) **(DMULT) at composite order + W-1's
transport** — everything coordinate-based still dies with it, but it is now a
single named identity with its own machine leg (R1-DMULT/R1-COB) rather than a
mis-aimed citation (JC-BOX-3); (2) the off-stratum existence claim with zero
machine support (JC-BOX-2); (3) the non-integral half of the coordinate
statement, which the repair NEWLY covers and no runner measures (JC-BOX-8(i));
(4) the top-flat corner (JC-BOX-4); (5) the two REVIEW-OWED display corrections
JC-F1/JC-F2 (JC-BOX-5).

**[r2] The stack after the G-1 tier split, for JC-PE3.** The single FGMN entry
divides: **(DMULT-w)** (up to the line-pair unit ω — the citable content,
carrying (COORD-B)(2)/(MULT-B)/JC-CARRY-m/W-8 and JC-BOX-4's closure) stays
CITED with the numbering re-verification owed; **(DMULT-s)** (ω ≡ 1) is
**MEASURED-only** (R1-DMULT + §9.4's bilinear leg), carrying exactly JC-COB's
sharp form. Weakest links, re-ranked for JC-PE3: (1) (DMULT-w) at composite
order + W-1's transport (with TR-3′-GEN, the corpus's march-level dictionary,
OPEN at general order — quoted at §2.10 [r2, G-1]); (2) JC-BOX-2's
off-stratum existence claim (zero machine support, unchanged); (3) the
non-integral residue JC-BOX-8(i) (unchanged); (4) (DMULT-s)'s measured-only
status wherever JC-COB's sharp value is displayed; (5) the top-flat corner
(JC-BOX-4, conditionally closed on (DMULT-w)); (6) JC-F1/JC-F2 REVIEW-OWED
(JC-BOX-5, unchanged).

### 10.3 Consumers — named, with what each may and may NOT take

* **DITERSUP §S3 gate J3b (BLOCKED-ON-CARRIER-TIE).** This note supplies exactly
  the missing item (ii) of J3b's three-item residual list — "the gr(w₂) semantics
  wrapper", i.e. §S3's *missing tie* — at **attempt grade 0/2 and at general m**,
  not only at order 2. **The gate does NOT retire here and this note does not
  retire it**: J3b retires only when (J-C)(ii) survives its own hostile arc, and
  its other legs (BLOCKED-ON-APPLICATION, the (ITER-LAW-LIFT) residual at
  g_0 = 1 ∧ δ_1 = 1, orders ≥ 3 of DITERSUP's own queue) are untouched. **The tie
  is displayed, the gate stands.**
* **`Scaffold/HDischarge/H1/DIterCarrier.lean` — JS1 / JS2.** JS1
  (`gateJS1_cocycle_assoc`, PROVED with the honest `hTrack : D.OuterTrackAdd`
  hypothesis) is the harness-side 2-cocycle/associativity gate; §5's COROLLARY
  W-9(i)(ii) is its **semantic home**: the cocycle identity is gr-associativity,
  and the outer-track additivity JS1 needed as a hypothesis is §5(ii)'s integer
  carry-cocycle identity on the δ-part. JS2 (`gateJS2_dreal_degeneration`,
  PROVED, no added hypotheses) is the e_0 = 1 D-REAL degeneration, which §6's
  genre law places in the *collapse geography* (flat control rows). **No Lean
  hypothesis is discharged by this note** — the compiled file's `hTrack` still
  needs a Lean-level supplier, and this note is not it (attempt grade, no Lean
  layer exists for gr(w_{m+1})).
* **MOVES B2-DEF.** Its accepted induction gains its intended **semantic home**:
  the level-indexed carry data B2-DEF manipulates is, by W-7/W-8, the structure
  constant of the anchor basis in gr(w_{m+1}) — the outer slot shift plus the
  inner K_m-unit. Display only; B2-DEF's own statements and grade are unchanged.
* **The (H1)(a) GR-B carry side.** §§3–4 give the composite-stage carry law that
  the (H1)(a) package's carry side asks for, on the scored stratum and at attempt
  grade, riding GRB's own §0 ladder. It does **not** discharge (H1) — the
  faithfulness handoff is J-D1 (W-12), not composed here.
* **The MOVES B2-FINAL bridge and bare-interface discharges stay DEAD** (brief
  fence 3): nothing above routes through them, and the option-(ii) vacuity trap
  (P1-FLAG-1/J3B-FLAG-1) is not re-opened.
