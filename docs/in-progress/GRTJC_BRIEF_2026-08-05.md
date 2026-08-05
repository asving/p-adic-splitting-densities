# GRTJC dispatch brief — the carry-algebra junction (W-6..W-9), instrument phase first

**Status: BRIEF (orchestrator-authored, 2026-08-05). Not a result. Drafted during the
API outage for dispatch when the LIFT-r1/JB-PE1 pair lands.**

## Position in the program

The GRT weld (docs/in-progress/GRT_WELD_BLUEPRINT_2026-08-08.md) ties the accepted
harness/carry-algebra corpus to the actual Okutsu–Montes classifier. Composed at
attempt grade: W-0/W-1 (J-A, the dictionary), W-3/W-4/W-5 (J-B, the tree; note
GRTJB_PROOF_2026-08-08.md), W-2 (the lift junction; GRTW2_PROOF_2026-08-08.md).
Per the blueprint's dependency order (S3.1), the J-C block W-6 → W-7 → W-8 → W-9 is
NEXT; J-D (W-10..W-12) after. J-C carries three of the four **L**-priced rows — it is
the hardest remaining weld content, and per the blueprint's break-analysis its failure
mode is HIGH for the program (J3b permanently blocked; standing obligation 2's Lean
layer unbuildable as designed) though NIL for existing texts.

## The claim to be composed (blueprint S2.3, verbatim source)

(J-C)(ii), the open content: for every level m with E_{m+1} := e₀⋯e_m > 1, the fibred
carrier (⊕_{γ ∈ ℤ/E_{m+1}} K_{m+1}·u_γ, u_γ·u_{γ′} = c_{m+1}(γ,γ′)·u_{γ+γ′}) built
from the canonical D(T)/c_T of GRT-1 is isomorphic, via u_γ ↦ [φ_γ]_{TC} through the
localize–gauge–quotient chain TC-1/TC-2/TC-3, to the K_{m+1}-span 𝒜(T) of the anchor
classes in the degree-0 component of the actual graded ring gr(w_{m+1}) — with 𝒜(T)'s
multiplication gr's OWN, never c_T (the tautology fence). Plus (iii): the residue
chain K₀ ⊂ … ⊂ K_{m+1} IS the classifier's residual tower (`ResidueTower`),
identification compatible with (i)/(ii)'s scalars. (i) — the last-read layer — is
ACCEPTED precedent (GRB Lemma D-REAL, conditional on the GRB §0 ladder); consume, do
not re-prove.

The order-2 instance of (ii) is EXACTLY the GRW2_TIE_DESIGN obligation package
OB-1..OB-6: target exists (W-6) / map well-defined (OB-2) / multiplicativity including
the INNER z₁ normalization factor (OB-3) / rank-one K-linear independence, Thm 4.2
analogue (OB-4) / tautology fence (OB-5) / harness-val = TC-read (OB-6, W-8). W-9
(cocycle semantics: [ILN]†'s c_{n+1} = the classifier's graded carry cocycle;
COR-2 = gr-associativity; COR-4 monodromy = the gauge period) is S-priced GIVEN
W-6..W-8.

## The germ (new since the blueprint — from J-B)

GRTJB_PROOF_2026-08-08.md, JB-CREAD + its J-C fence: in print coordinates the carry
contribution CANCELS (Lemma JB-EPS), and the (C-READ) transport constant is
c_m = ψ_{m,0} = −z_{m+1} — the NEXT residual letter. Working hypothesis for OB-3: the
inner normalization factor at general m is this letter (the order-2 instance's z₁
factor generalizing to z_{m+1} at stage m). The instrument MUST measure this before
the composer assumes it.

## Standing fences (LAW — violating any is an automatic finding)

1. **The cyclic fence**: at composite stages 𝒜(T) is NOT F′[u′]/(u′^E − ζ′)
   (adjudicated NOT-CYCLIC at 22/28 towers, value set {z₁, z̄, z̄z₁^b}, byte-frozen).
   Only the last-read layer is cyclic. Any route through a cyclic presentation at a
   composite stage is DEAD (design-note S4).
2. **The tautology fence**: 𝒜(T)'s multiplication must be computed IN gr(w_{m+1}) —
   independently of c_T — and then compared. Defining it BY c_T proves nothing.
3. **Dead routes** (lean/quarantine + blueprint break-analysis): the MOVES B2-FINAL
   bridge (NOT accepted, 5C/2G structural); bare-interface discharges (the option-(ii)
   vacuity trap, P1-FLAG-1/J3B-FLAG-1). Do not re-attempt.
4. "Nearly automatic" was REFUTED for this junction — OB-4 (independence) and OB-6
   (val = TC-read) are the two legs that killed the shortcut. Budget effort there.

## Phase 0 — MANDATORY instrument (examples-first directive, Asvin 2026-08-05)

Before ANY composition: a sealed probe (two-commit discipline — seal the preregistered
predictions + runner FIRST, then run) measuring, on ≥ 24 constructed towers spanning
m ∈ {1, 2, 3}, p ∈ {2, 3, 5}, d₀ ∈ {1, 2, 3}, mixed (e_j) with E_{m+1} > 1 (include
e_j = p wild legs, g_j > 1 branching, and the 22/28 NOT-CYCLIC roster's genres —
engine_ext.py lifts the capability walls; import + install() + agreement_gate()
in-unit):

  P1. build gr(w_{m+1}) degree-0 and the anchor span 𝒜(T) concretely; multiply anchor
      classes IN gr (tautology-fence-clean); tabulate the structure constants.
  P2. build the fibred carrier from GRT-1's D(T)/c_T; tabulate ITS structure constants;
      compare after the TC-1/TC-2/TC-3 transport — the candidate iso on the nose,
      per (γ, γ′) pair, exact arithmetic.
  P3. measure the inner normalization factor per stage; test the germ hypothesis
      (= −z_{m+1} / the next residual letter) against the measured value.
  P4. rank-one independence (OB-4): numeric rank of the anchor classes over K_{m+1}
      at every tower — any rank drop is a genre, tabulate it.
  P5. harness-val vs TC-read (OB-6): both sides computed independently per anchor.
  P6. teeth: at least 3 planted-wrong controls (wrong letter in the normalization,
      cyclic presentation at a composite stage, c_T-defined multiplication) that MUST
      fire.

The composer derives its case split FROM the observed genres (case list must match the
table's genre list). If any P-leg shows violations, the composer boxes the exact
obstruction instead of forcing the claim — a measured obstruction here is a program
finding, not a failure.

## Deliverables & grading

Instrument: GRTJC_PROBE_2026-08-08.md + verification/openmath/grt_jc_probe.py
(+ output/json), two-commit seal. Composer (only after the instrument's verdict):
GRTJC_PROOF_2026-08-08.md + grt_jc_checks.py, W-6/W-7/W-8/W-9 as separate boxed
clauses, each graded honestly (attempt 0/2 at composition; the note rides W-2/J-A/J-B
at attempt and [RMG]/GRB D-REAL as accepted-with-conditions — display the full
conditionality stack). Consumers to name: DITERSUP §S3 gate J3b (retires only when
(ii) survives its hostile arc); Scaffold/HDischarge/H1/DIterCarrier.lean (JS1/JS2, the
harness-side carrier); MOVES B2-DEF's semantic home; the (H1)(a) GR-B carry side.
