# ITERLAW3 hostile pass PE — Fable execution + content leg (F2c from-note reimplementation + diag re-run + full hostile content read)

**Pass:** ITERLAW3-PE (Fable leg; execution + content; model-diverse counterpart to
the concurrent Codex content pass PC). **Target:**
`lean/notes/openmath/ITERLAW3_PROOF_2026-08-08.md` (the (ITER-LAW-3) proof compose,
attempt grade; acceptance bar: PE + PC both CLEAN, counter 0/2 at pass start).
**Statement of record:** `ITERLAWR_PROBE_2026-08-08.md` S1 primary display —
verified VERBATIM against the note's S0.4 theorem display (δ₃/D₂/Σ/D₁ constants
character-identical; class pin carries no E₃ floor on either side). **Discipline:**
quote-and-classify; CRITICAL = breaks a logical chain / false claim of record,
GAP = unproved-but-assumed step, verify downstream; nothing fixed. F2c ordering
honored STRICTLY: `verification/openmath/iterlaw3_pe_reimpl.py` was written and run
to green from the note text ALONE; `iterlaw3_proof_diag.py` was opened only
afterwards. Findings below were frozen before consulting any concurrent-pass
artifact. **Wallclock:** 2026-08-03 (campaign date 2026-08-08).

## VERDICT BLOCK

**FINDINGS: 1 critical, 1 gap (+ 3 nits).**
**VERDICT: NOT-CLEAN.**

Both findings live OUTSIDE the main proof chain (S2/S3/S4.2–S4.6/S5 verified sound
by hand and by machine): the critical is a false unconditionality claim in the
COR-3 display (S6.3) with a declared consumer at risk; the gap is an induction-
measure defect in DEV-1's stated generality at a corner no downstream use reaches.
The theorem-off-DCX, W-MULT-(3), the case partition, the DCX locus, and the DCX
honesty display all SURVIVED full hostile execution: 3,344 fresh-tower pairs /
55,186 checks / 0 violations, all 6 mutation controls fired, diag re-run
byte-exact, case censuses reconciled exactly.

### FINDING 1 [CRITICAL — scoped to the COR-3 conditionality display; main
### theorem chain untouched]

S6.3 header (line 713):

> ### S6.3 COR-3: degenerations (sealed G6; all unconditional — DCX needs δ₁ = 1 ∧ g₀ = 1 ∧ e₀ ≥ 3, none of which survives the respective degeneration)

The justification is FALSE for the e₂ = 1 (CX) and e₁ = 1 (CW) bullets, and with it
the "all unconditional" claim. The DCX predicate (S0.4/S4.7) has NO e₂ condition,
and none of δ₁ = 1, g₀ = 1, e₀ ≥ 3 is negated by e₂ = 1 or e₁ = 1. Worse, at
e₁ = 1 the track condition s₂(γ) = s₂(γ′) = e₁−1 = 0 trivializes, ENLARGING the
locus — and the note itself displays the e₁ = 1 DCX flavor in S4.7 (line 643:
"or slot 1 = e₁ (Case II-3 at e₁ = 1)"), so S6.3 contradicts S4.7. Executed
witnesses (this pass):

* **CX witness:** tower (3,2,1)(2,1,1)(1,1,1) over ℤ₅ — an e₂ = 1 tower —
  realizes **4 DCX pairs** per W₁×W₁-equivalent block (census I 84 / II-1 24 /
  II-2 8 / II-3 24 / DCX 4). On those 4 pairs the e₂ = 1 field-level clause
  "c₃ = the ACCEPTED law verbatim" is exactly as conditional on (W-MULT-3-DCX) as
  the theorem (instance-true 4/4, Q¹ ≠ 0 4/4, naive-E₀ re-overflow 4/4 — but no
  proof coverage from this note).
* **CW witness:** battery tower TW2 = (4,1,1)(1,3,1)(2,1,1) over F₃[[t]] — an
  e₁ = 1 tower — realizes **48 DCX pairs** (census below); same conditionality
  for the CW display on those pairs.

Consumer at risk (declared by the note itself, S9 line 858): the ITERLAW4 unit
"may cite this note's S6.3 (e₂ = 1 embedding proved) once accepted" — the cite
would inherit the false unconditionality on DCX-live e₂ = 1 towers. What IS
unconditional in COR-3: the integer-level reductions (δ₃ = 0, β₂(γ) = γ, D₂ = δ₂,
Σ = γ₂δ₂, D₁ = the accepted exponent at e₂ = 1; D₂ = 0, Σ = δ₃γ₃ at e₁ = 1;
D₁ = 0 at e₀ = 1) — machine-checked 64/0 per family on TW5/TW6 and 144/0 on the
CX witness — and the CV bullet in full (e₀ = 1 does contradict e₀ ≥ 3, and DCX
needs S₁ ≥ e₀+1 ≥ 2 > 0 = S₁|_{e₀=1}; also its own e₀ ≥ 3 clause). Fix is a
one-line re-scope: CX/CW field-level clauses hold on the proved perimeter
(S6-preamble convention), unconditionally once (W-MULT-3-DCX) closes; the S0.4
status-table COR-3 row's "(conditionalities displayed per-item)" then becomes
accurate.

### FINDING 2 [GAP — DEV-1's stated generality; no downstream use affected]

S4.1, DEV-1 induction step (line 409):

> All children have Φ₀-exponent ≤ e₀(g₀−1) + j − e₀g₀ + 1 = j − e₀ + 1 ≤ j − 1 < j (e₀ ≥ 1) and

The chain "j − e₀ + 1 ≤ j − 1" requires **e₀ ≥ 2**, not e₀ ≥ 1 as displayed. At
e₀ = 1 the junkΦ⁽ᵍ⁰⁻¹⁾ child has Φ₀-exponent exactly j, and the strong induction
on j does not terminate as written (the child's line rises by h₀ each round, so
no j-descent occurs). The corner is live only at e₀ = 1 ∧ d₀ ≥ 2 ∧ j ≥ g₀: at
d₀ = 1 the DIGIT-SPLIT Y-cofactor vanishes identically (deg αβ ≤ 2d₀−2 = 0 <
d₀ = 1 forces Y = 0), so junkΦ ≡ 0. NO use of DEV-1 in this note reaches the
corner: S4.5's inputs G_m have Φ₀-exponent J + me₀ with J = S₁ + s(γ₂) ≡ 0 at
e₀ = 1 (all eq-(12-int) s-values vanish), i.e. exponent m ≤ g₀−1 < e₀g₀ — base
case only; S4.6 requires g₀ = 1 ∧ δ₁ = 1, forcing e₀ ≥ 2. So the theorem chain
is unaffected; DEV-1 AS STATED (all e₀ ≥ 1, all j < 2e₀g₀) has an unproved
corner. Fix: either restrict DEV-1's hypothesis (e₀ ≥ 2 ∨ j < e₀g₀ — everything
consumed survives verbatim), or repair the measure (at e₀ = 1 the only
non-descending child is the junkΦ chain, whose coefficient π-depth strictly
grows; a secondary induction on target-relative depth closes it, but that
argument is NOT in the note).

### Nits (no logic touched)

* **N1** (S2 WINDOW case (i), line 282): leftover self-correction artifact in the
  proof text: "then s₂″ = S₂−δ₂e₁ = S₂ wait — at δ₃ = 0, ...". The content after
  the dash is correct; the false start "= S₂" plus the literal "wait" should not
  survive in a proof of record.
* **N2** (S6.6, lines 764–765): rung indexing collides with the section title —
  title says "(ITER-LAW-n) at n = 3, derived", body says "n = 1 accepted [IL],
  n = 2 this note". One convention counts reads, the other carries; pick one
  (the ledger's ITERLAW3-PC-adjudicated bracket counts READS for names).
* **N3** (S4.6 Case II-2, slot k+2 parenthetical, line 602): the "on-grid-above-
  line at e₁ = 2" branch is vacuous in the proved region — Q¹ ≠ 0 with
  k+2 ≤ e₁−1 forces e₁ ≥ 3 (at e₁ = 2, Q¹ ≠ 0 lands in DCX). Harmless
  defensive text; could be flagged as such.

### What was verified SOUND (hand + machine, the full charged surface)

* **DEV-1 sign/collision bookkeeping** (S4.1 outside the F2 corner; S4.5/S4.6):
  the b = π^{w₀(b)}b′ factorization behind the child display, the three-child
  lines λ/λ+e₀/λ+h₀, read additivity under cancellation (res kills consistent
  excess), the ψ₀(z₁) = 0 telescope with the (j−e₀g₀−s*)/e₀ intermediate
  exponent (final abscissas ≥ s* proved via j ≡ s* (mod e₀) ∧ j ≥ 0 ⟹ j ≥ s*),
  the −Rem⁰ sign through C₀ = ε₁(β*)c₀τz₁^{ε′} = c₀c₁ε₁(B₁) = z₂z₁ε₁(B₁), the
  e₁ = 2 slot-collision in II-3 (Q¹ above-line inside the colliding digit leaves
  exact-w₀ residues unchanged — verified in TW1/TW5/TW7 where such collisions
  occur), and the II-2 grid-off/grid-above dichotomy.
* **Case exhaustiveness** (S4.3): inner dichotomy is exact (g₀ ≥ 2 ⟹ S₁ ≤
  2e₀−2 < e₀g₀; g₀ = 1 splits by δ₁); top trichotomy matches the deg-A criterion
  — machine: INNER-DICHOT 3,344/0, CASESPLIT-DEG 3,344/0 (predicate ⟺
  deg A < deg Φ₂ on every pair including DCX).
* **Consumption legality of the accepted L7 on the inner digit**: the S0.3
  dictionary is exact (verified symbol-by-symbol: [IL] γ ↦ β₂(γ), γ₁ ↦ β₁,
  z̄ ↦ z₂, W-membership ⟺ γ ∈ W₃); the digit A IS the level-2 anchor pair
  product on the nose; the consumed displays (both L7 value forms + the Case
  I/II development shapes + the single-coefficient-at-slot-δ₂ read clause) are
  all proven displays of the ACCEPTED note; weights are re-derived, not
  consumed. Machine: I-R2vA/I-w2A/I-dev 2,328/0 each.
* **Class pinning**: the note's class = the sealed ITERLAWR S0 pin on the nose
  (per-read conditions, no E₃ floor both sides; roster E₃ ≥ 4 disclosed both
  sides; the VC36b lesson applied correctly this time).
* **DCX honesty**: predicate empty ⟺ e₀ ≤ 2 (3e₀−3 < 2e₀); DCX ⊆ II-2 ∪ II-3
  with the e₁-split exactly as displayed; the proved/open boundary sits exactly
  where the II-2/II-3 provisos fail (k+2 = e₁ ∧ Q¹ ≠ 0, resp. e₁ = 1 ∧ Q¹ ≠ 0);
  Q¹ ≠ 0 ⟺ ω ≥ e₀ confirmed on every probed pair (the note claims only ⟸,
  which is all it needs); instance evidence labeled as such throughout.
* **Corollary derivations**: COR-1 = the D-INTs; COR-2 both proofs (δ₃ is a
  2-cocycle via L1 associativity; slotwise telescopes symmetric); COR-4 shift
  arithmetic + ρ-monodromy via EXP-KIT(a); COR-5 closed monomial form, H²-class
  honestly left cited-measured; COR-6 substitution reproduces the recursion;
  COR-7 = W-MULT second display. Only COR-3's conditionality header fails
  (Finding 1).
* **Integer layer + EXP-KIT** (S2/S3): every displayed identity re-derived by
  hand (incl. the 1−ℓ₁γ₂ = e₁(ℓ₁′−ℓ₁w₁Φ₁) Bézout step and the WINDOW case-(iii)
  recombination) and machine-checked: 3,344 pairs/0 per family + 20,000/0
  symbolic draws (random (e,h)-triples, γ ∈ [−3000,3000), field-free).
* **L6-(3)** (S4.2): degree bound, dictionary consumption of accepted L6,
  on-line slot-0 read, w₃(φ_γ) = γ — machine 638/0.
* **WELL-DEF** (S4.0): u(gp) > (g₀−1)h₀ display verified algebraically; C_k
  degree/line/weight/read invariants machine-checked on all 10 towers (10/0;
  includes the g₁ = 1 exact two-term form Φ₂ = Φ₁^{e₁} + Ĉ, asserted
  polynomially at build time).

## EXECUTION ACTUALS

### A. From-note reimplementation (verifier-owned; F2c genre)

`verification/openmath/iterlaw3_pe_reimpl.py` — written from the note text alone
(fields, DVR arithmetic, developments, reads, anchors, case predicates all
reimplemented; NO harness import). Seed 20260803. Exit 0, **ALL GREEN, first
full run**: **3,344 pairs / 55,186 checks / 0 violations** across 56 check
families (full table in `iterlaw3_pe_reimpl_output.txt` +
`iterlaw3_pe_reimpl_results.json`). 10 fresh towers, none in any sealed roster;
rings ℤ₂/ℤ₃/ℤ₅/F₂[[t]]/F₃[[t]]/F₅[[t]] (ℤ₅, F₅[[t]] new to the genre); d₀ up to
2, g₀/g₁/g₂ up to 2, e₁ ∈ {1,2,3}, e₂ ∈ {1,2,3}; π-perturbed Φ₀ on 4 towers
(in-class: S0.1 pins only monic + w₀ = 0 + irreducible reduction — no
perturbation sensitivity found, confirming the proof's Φ₀-lift-freeness); two
windows per tower (W1 ∪ W1+M·E₃, M ∈ [2,9] seeded), all four mixed blocks
paired (COR-4 descent exercised implicitly: the residue-computed display matched
the measured c₃ on every block).

Tower roster + census (DCX counted separately from its host case, diag-style):

| tower | ring | (e,h,g)×3 | E₃ | block | I | II-1 | II-2 | II-3 | DCX |
|---|---|---|---|---|---|---|---|---|---|
| TW1-Z5-DCX | ℤ₅ | (3,2,1)(2,1,1)(2,1,1) | 12 | 576 | 336 | 96 | 32 | 96 | 16 |
| TW1b-F5t-DCX | F₅[[t]] | same | 12 | 576 | 336 | 96 | 32 | 96 | 16 |
| TW2-F3t-DCX-e1is1 | F₃[[t]] | (4,1,1)(1,3,1)(2,1,1) | 8 | 256 | 160 | 0 | 0 | 48 | 48 |
| TW3-Z3-g1is2 | ℤ₃ | (2,1,1)(2,1,2)(3,1,1) | 12 | 576 | 576 | 0 | 0 | 0 | 0 |
| TW4-F2t-g0is2 | F₂[[t]] | (2,1,2)(2,1,1)(2,1,1) | 8 | 256 | 192 | 64 | 0 | 0 | 0 |
| TW5-Z3-e2is1 | ℤ₃ | (2,1,1)(2,1,1)(1,2,1) | 4 | 64 | 40 | 12 | 4 | 8 | 0 |
| TW6-Z5-e0is1 | ℤ₅ | (1,2,1)(2,1,1)(2,1,1) | 4 | 64 | 48 | 16 | 0 | 0 | 0 |
| TW7-Z2-d0is2 | ℤ₂ | (2,1,1)(2,1,1)(2,1,1), d₀=2 | 8 | 256 | 160 | 48 | 16 | 32 | 0 |
| TW8-F2t-g2is2 | F₂[[t]] | (3,2,2)(1,1,1)(2,1,2) | 6 | 144 | 144 | 0 | 0 | 0 | 0 |
| TW9-Z5-e1is3 | ℤ₅ | (2,1,1)(3,1,1)(2,1,1) | 12 | 576 | 336 | 144 | 48 | 48 | 0 |

**DCX locus meter:** predicate-live exactly on the three constructed
(e₀ ≥ 3 ∧ g₀ = g₁ = 1)-with-track towers, measure 16/576 = 0.0278, 16/576,
48/256 = 0.1875; ZERO DCX pairs on every e₀ ≤ 2 tower and on both e₀ = 3
towers with g₀ = 2 (TW8) — the proved/open boundary is exactly where the note
says. **DCX instance data (open lemma, NOT counted as violations): 80 pairs —
theorem display holds 80/80, all three W-MULT clauses hold 80/80, Q¹ ≠ 0
80/80, naive-E₀ re-overflow 80/80** (the S4.7 breakdown mechanism is real on
every DCX pair; instance evidence for (W-MULT-3-DCX), proof stays open).

**Degenerations:** e₂ = 1 (TW5): the accepted order-2 law re-measured by an OWN
level-2 cocycle (R2v-based, no level-3 objects) and compared: CX-accepted-law-c2
64/0 and c₃ = emb(c₂) 64/0, plus all integer reductions 64/0 each (and 144/0
each on the Finding-1 CX witness tower). e₁ = 1 (TW2, TW8): CW-D2is0 /
CW-Sig 400/0. e₀ = 1 (TW6): CV-D1is0 / CV-S1is0 64/0.

**Mutation controls (6, on the law's constants; field-level visibility verified
in a pre-pass BEFORE any measurement, all > 0):**

| mutation | visible | violations | of which non-integral |
|---|---|---|---|
| M1 drop top carry (z̄^{δ₃} → 1) | 868 | 868 | 0 |
| M2 γ₃ → γ₃+1 inside D₂ | 768 | 768 | 768 |
| M3 Σ drops the δ₃γ₃(ℓ₁′−ℓ₁w₁Φ₁) term | 464 | 464 | 64 |
| M4 naive Σ = γ₂δ₂ (the ITERLAWR distinguished alternative) | 720 | 720 | 416 |
| M5 D₂ → D₂+δ₂ (internal-carry leak) | 784 | 784 | 0 |
| M6 ℓ₀ → ℓ₀′ in D₁ | 1288 | 1288 | 752 |

All fired (violations = visible on every mutation: the law separated from each
mutant at every field-visible point). Disclosure: M2 fires exclusively through
the integrality clause (ℓ₁ ∤ e₁-shifts at δ₃ = 1) — integrality is part of the
displayed law, so this is a legitimate detection channel; M3/M4/M6 fire through
both channels; M1/M5 purely field-level.

**Symbolic integer layer:** 20,000 random draws (e ≤ 6, h ≤ 11, g ≤ 3,
γ ∈ [−3000, 3000)) of L1/L2-(3a)/(3b)/D₂-INT/D₁-INT/EXP-KIT(a) integrality/
EXP-KIT(c) closed-form at both levels/WINDOW: **0 bad**.

### B. Diag re-run + semantic diff

`iterlaw3_proof_diag.py` re-run (opened only after A was green): **exit 0,
byte-exact reproduction** of `iterlaw3_proof_diag_output.txt` (diff empty) —
aggregate census I 912 / II-1 368 / II-2 40 / II-3 88 / DCX 16 over 1,424
pairs, 0 identity violations, matching the note's S8 bracket exactly.
**Semantic diff of case predicates:** my from-note predicates, run on the
diag's 5 tower shapes (integer layer only; census is window-independent by
COR-4 descent), reproduce the diag's per-row censuses EXACTLY (DGA 48/16 ·
DGB 84/24/8/24/4 · DGC 84/36/12/12 · DGD 24/8/4 · DGE 216/108) and the
aggregate. One implementation difference, value-identical: the diag's
`classify` tests top-slot overflow via `top = S2+1 if innerII else S2` against
e₁−1 where mine tests S₂ ≥ e₁ / S₂ = e₁−1 branchwise — algebraically the same
partition (verified by the exact census match plus my CASESPLIT-DEG family:
predicate ⟺ deg A < deg Φ₂ on all 3,344 pairs).

### C. Finding-1 witness run (labeled verifier diagnostic, post-battery)

Tower (3,2,1)(2,1,1)(1,1,1)/ℤ₅ (e₂ = 1, DCX-live): census I 84 / II-1 24 /
II-2 8 / II-3 24 / **DCX 4**; 3,532 checks / 0 violations on the non-DCX
perimeter; theorem instance-true on the 4 DCX pairs (Q¹ ≠ 0 and naive-E₀
overflow on all 4). This is the CX counterexample of Finding 1.

## PROVENANCE APPENDIX (verbatim slices of every load-bearing cite)

* Note S0.4 THEOREM display vs sealed ITERLAWR S1 — both read, constant for
  constant:
      δ₃ := ⌊(s₃(γ)+s₃(γ′))/e₂⌋ ∈ {0,1}
      D₂ := (s₂(γ)+s₂(γ′)−s₂(γ+γ′) + ℓ₁·γ₃·δ₃)/e₁ ∈ ℤ
      Σ  := D₂·γ₂ + δ₃·γ₃·(ℓ₁′ − ℓ₁·w₁Φ₁) ∈ ℤ
      D₁ := (s₁(γ)+s₁(γ′)−s₁(γ+γ′) + ℓ₀·Σ)/e₀ ∈ ℤ
      c₃(γ,γ′) = z̄^{δ₃} · z₂^{D₂} · z₁^{D₁}
  (ITERLAWR_PROBE_2026-08-08.md S1 "[THE PRIMARY CANDIDATE]"; note lines
  146–151. VERBATIM MATCH.)
* Finding 1 slice (note line 713): "### S6.3 COR-3: degenerations (sealed G6;
  all unconditional — DCX needs δ₁ = 1 ∧ g₀ = 1 ∧ e₀ ≥ 3, none of which
  survives the respective degeneration)"
* S4.7 e₁ = 1 DCX display contradicting it (note lines 642–643): "on DCX the
  DEV-1 carry Q¹ ≠ 0 lands at Φ₁-slot k+2 = e₁ (Case II-2 at S₂ = 2e₁−2) or
  slot 1 = e₁ (Case II-3 at e₁ = 1)"
* Consumer-at-risk slice (note lines 857–858): "its F0/F-SUB legs may cite
  this note's S6.3 (e₂ = 1 embedding proved) once accepted"
* Finding 2 slice (note lines 408–409): "All children have Φ₀-exponent ≤
  e₀(g₀−1) + j − e₀g₀ + 1 = j − e₀ + 1 ≤ j − 1 < j (e₀ ≥ 1) and < 2e₀g₀"
* Nit N1 slice (note lines 282–283): "(i) δ₃ = 0, δ₂ = 0: then s₂″ = S₂−δ₂e₁
  = S₂ wait — at δ₃ = 0, β₂″ = B₂ and L1 at (e₁,h₁) gives s₂″ = S₂ − δ₂e₁
  directly"
* Nit N2 slices (note S6.6 title + lines 764–765): "COR-6: the exponent
  recursion — (ITER-LAW-n) at n = 3, derived" vs "Confirmed rungs of
  (ITER-LAW-n): n = 1 accepted [IL], n = 2 this note (off DCX)"
* Nit N3 slice (note lines 601–602): "slot k+2 (only if Q¹ ≠ 0): line ≥
  e₁(β*−2e₀h₀)+(k+2)γ₂ = B₂+2h₁ > B₂ (off-grid at e₁ ≥ 3; on-grid-above-line
  at e₁ = 2 — read 0 either way)."
* Accepted-base citation in the note header — PASTED-from-ledger block
  verified verbatim against `lean/notes/BRIDGE_ADJUDICATIONS_2026-07-30.md`
  "ITER-LAW ACCEPTED — 2026-08-03": "Scope as accepted: the harness tower
  class (superset of DITER_RESTATE §S2's E₂ > 1 pin; on-the-nose coincidence
  restricted to E₂ > 1); residuals: (ITER-LAW-LIFT) open exactly at g₀ = 1 ∧
  δ₁ = 1; gr(w₂) wrapper rides the accepted GRB retarget; orders ≥ 3
  untouched."
* Class pin cross-check (ITERLAWR_PROBE S0 "Class pin"): "reads (e₀,h₀,ψ₀),
  (e₁,h₁,ψ₁), (e₂,h₂,ψ₂) with gcd(eᵢ,hᵢ) = 1, ψᵢ monic irreducible with
  ψᵢ(0) ≠ 0; E₃ := e₀e₁e₂; ... All roster rows have E₃ ≥ 4." (No E₃ floor in
  the pin; matches the note's S0.1 class-coincidence display.)

**Pass files (this unit's whole write set):** `iterlaw3_pe_reimpl.py`,
`iterlaw3_pe_reimpl_output.txt`, `iterlaw3_pe_reimpl_results.json`, this
report, the ledger append. Sealed artifacts, the note, the diag, and all
iterlaw4* files byte-untouched by this pass.

— ITERLAW3-PE, Fable verifier leg, wallclock 2026-08-03.
