# MOVESD REV-7 CONFIRMATION AUDIT — fresh Fable #6 (via workflow)

- **Date:** 2026-07-28 (campaign date)
- **Auditor:** fresh Fable instance #6, spawned by the workflow orchestrator; no prior
  conversation state; read-and-judge only, nothing fixed.
- **Scope:** REV 7 closing confirmation of `MOVESD_LEAN_BLUEPRINT_2026-07-28.md`
  (1439 lines, read in full) — the certificate completion (hh/hcop/species/gamTie/
  anchorTie), the piecewise NP vs L12, the binding sweep, SW1's extended sketch, the
  gate recomputation, six-plus spot-checks, the 48-unit sweep.
- **Ground truth:** `MOVES_2026-07-24.md` §D4-R rev 9 (lines 4580–5435; DUAL-ACCEPTED
  record lines 6783–6831) + `lean/LeanUrat/MovesC/Defs.lean` (Node/HistoryCoherent/
  TransitionAdmissible read in full for the mirrored clauses).
- **Method:** per the campaign calibration ("Fable auditors have repeatedly
  under-tested adversaries — run MORE than the listed ones"), the certificate, the
  gate ledger, and the adversaries were executed as an independent computational
  replica (Python, exact rationals) of the §3.1/§3.3 definitions, NOT hand-waved.
  Transcript: `/tmp/movesd_rev7_audit.py` (reproduced in summary below).

## 1. The completed certificate — adversaries re-run + two NEW ones

The §3.1 certificate (ShapeRead Prop fields + ShapeWF clauses incl. the REV-7
`gamTie`/`anchorTie`, `bezT`) was re-implemented independently from the blueprint's
displayed definitions and run against ALL listed adversaries plus two invented ones:

| adversary | data | failed clause (computed) | blueprint claim |
|---|---|---|---|
| A-i (Fable#5) | root wSide = 10, n = 3 | `root_box` | ✓ match |
| A-ii (Fable#5) | monicTop, s0+wSide = 2 ≠ 3 | `MonicTie@r0` | ✓ match |
| A-iii (Fable#5) | monicTop at depth 1 | `hmonicRoot` (record unbuildable) + `MonicTie@r1` | ✓ match ("hmonicRoot/species") |
| A-iv (Codex#5) | one-read root, h = 0 | `hh` — the RECORD is unbuildable | ✓ match |
| A-v (rev 7) | (e, h) = (2, 4) | `hcop` | ✓ match |
| **A-vi (NEW)** | consistent (e,h) = (1,1), u* = 0, span [0,3], declared γ = 5 (true γ = 3) | **`gamTie@r0`** | — (charge-demanded γ-tie violator: KILLED) |
| **A-vii (NEW)** | e = 2, h = 1, u* = 1 ⟹ γ = 4, true a = (0 − 1·4)/2 = −2; declared a = 0 | **`anchorTie@r0`** | — (charge-demanded wrong-Bézout anchor: KILLED) |

A-vii control: the same shape with the CORRECT anchor a = −2 passes every clause —
so `anchorTie` is exact, not over-restrictive, at e = 2 (the first e > 1 probe of the
certificate; both blueprint positives have e ≡ 1).

`bezT` verified as THE canonical Bézout coefficient on 7 (e,h) pairs: bezT(e,h) ∈
[0,e), h·bezT ≡ 1 (mod e), and UNIQUE in the window whenever gcd(e,h) = 1 (`hcop`);
bezT(1,h) = 0 (the D.5 (P2) base — a = s0 at e = 1, exactly the positives' pattern);
bezT(2,1) = 1. Against MovesC: `Node.hbezCanon` (0 ≤ t < e) + `hbez` (e·s + h·t = 1)
+ `Node.hcop` force Node.t = bezT e h — SW1's "small in-unit lemma" is genuine.

Positives, every clause checked computationally:
- **P̂*** ∈ Shape 3: PASS, all clauses. γ₀ recomputed from the tie = 1·(1·0) + 3·1
  = **3** = the seal's (L3's γ = e·u* + j*·h at u*₀ = 0, j*₀ = 3); γ₁ = 1·(1·1) +
  1·3 = **4** ✓; anchor a = s0 = 0 both reads (bezT = 0 at e = 1) ✓.
- **P̂₀** ∈ Shape 4: PASS. γ₀ = 0 + 4·1 = 4 ✓; a = 0 = s0 ✓. BONUS cross-check the
  blueprint did not claim: the §3.3 replica computes **A(P̂₀) = 14** — exactly the
  note's D4R.1 rev-6 check value ("A(P̂₀) = 14: 4 cluster + 6 below-line + 4
  on-line pins"), from definitions written for a different shape. Strong evidence
  the band replica is the note's inventory.

MovesC mirror fidelity: `hh`/`hcop` = Node's "genuine polygon side: e, h ≥ 1,
coprime (lowest terms)" verbatim (Defs.lean:398–401); `hspecInc`/`hspecRec` =
Node's species laws verbatim (:451–454); `gamTie` = HistoryCoherent's γ-tie clause
verbatim (:640–643) with strS for strFrame (D6a's transport); `anchorTie` =
`hAnchor : e·a = s0 − t·gam` (:441) at t = bezT. NOTE-SCALE REMARK (verified, not a
finding): §D4-R L3's display "γ_r := e_r·u*_r + j*_r·h_r" omits the stretch, but it
cites "§C's DERIVED list", and §C rev 14's formula (per the dual-audited MovesC
formalization, Node.gam docstring) is γ = e·(STR·u*) + j*·h with u* ABSOLUTE-scale —
the scale Matches ties `ShapeRead.ustar` to. The STR-carrying tie is the only one
SW1 can transport (the STR-free tie is FALSE for genuine histories with stretch
> 1); at both gates STR = 1, so the gates cannot distinguish them. The blueprint
documents the choice ("at the chain stretch"). Faithful.

No universe loss: every new clause is a Node law (hh/hcop/hspecInc/hspecRec) or a
coherence/Node consequence (gamTie/anchorTie via hAnchor + hbezCanon), so every
matched coherent history's shape still carries the certificate — SW1's claim, and
its extended sketch closes (item 4 below).

## 2. NP piecewise vs L12 (charge item 2)

L12 quoted from the note (:5138–5139): "N(P̂) := max_{η ∈ Pref(P̂)} N(η,⊤) if
Pref(P̂) ≠ ∅, N(P̂) := 1 if Pref(P̂) = ∅". Blueprint: `Shape.NP P pol := if Nonempty
(PrefIdx n pol P) then NPband else 1`.

- **Pref-conditional, pol-dependence:** PrefIdx nonempty ⟺ PrefSet ≠ ∅; PrefSet
  carries `IsCanonPres` = the note's canonical-lift clause, so the conditional is
  pol-dependent exactly as L12's own (the note's Pref is defined at THE canonical
  policy). Docstring says so explicitly. ✓
- **Empty clause UNCONDITIONAL on the band:** verified — a Pref-empty shape with
  nonempty band gets NP = 1 through the else-branch regardless of NPband; the
  docstring quotes the note's "realizability can remove every value assignment"
  mechanism (one-word quote elision, see OBS-A). ✓
- **NP_stab scoping:** `[Nonempty (PrefIdx n pol P)]` instance-scopes stability to
  the inhabited branch (NP = NPband); soundness re-derived: every band coordinate
  has ℓ ≤ htS ≤ line ≤ intercept < Nshape, hence lies inside the range-Nshape grid,
  hence ℓ ≤ NPband − 1 — so A n N is constant for N ≥ NPband. The empty branch never
  consumes stability. ✓
- **D4R4_all's empty branch at full strength:** on the empty branch NP = 1, so
  ∀ N ≥ NP is L12's "for EVERY N ≥ 1" EXACTLY; conclusion ∑ᶠ over the empty index
  = 0 = CD·p^{nN} (CD = 0 by hne + card of the empty PrefIdx) ∧ 0 ≤ 0 — L12's
  displayed empty-clause arithmetic; the set-display S(P̂,⊤) = ∅ ∧ C = 0 is carried
  by D14b at every N ≥ 1 with explicit hN. Full strength GIVEN the corpus-wide
  declared presentation boundary (Threshold's jets, HC-2) — the standing, repeatedly
  adjudicated conditionality, not a new drop. ✓
- **Max-η identification softened:** the docstring claims only NP_stab + range as
  theorems; the NPband = max_η N(η,⊤) reading is documented semantics. Matches
  Codex#5 c.2's second half. ✓
- One residual corner: the EMPTY SHAPE (finding G-2 below) — values coincide, branch
  routes differ.

Gate: NP(P̂*) = NPband = 1 + 4 = **5** computed (band levels within the Nshape-grid:
{0..3} ∪ {4 at (4, c₀)}, {3 at (3, c₁)} — the note's "largest pinned base level = 4,
at c₀" verbatim). ✓

## 3. Binding sweep (charge item 3)

Every subtype-taking def re-checked by eye against the §14 row-3 list: PrefIdx,
PresentNorm, reprOf, Shape.CD, PrefOpt, Presented, Threshold, D4R_CYL,
ClassFiberWelldef, PrefSet, PrefSetAny all bind `P : Shape n` ✓; raw-type utilities
(EtaData/etaData/EtaGalEq/etaDataO/NPband + the §3.3 replicas) stay on ShapePrefix
with explicit coercions ✓; §3.0's order puts Shape.NP in group (4) after PrefIdx ✓;
unit specs use the §4 common binder {P : Shape n} with the Q := ↑P convention ✓;
SW1's {Q : ShapePrefix} is deliberate (it PRODUCES the certificate) ✓. ONE residue
found: finding G-1 (the fiber/event/mult section-variable line — displayed nowhere).

## 4. SW1's extended sketch (charge item 4)

- `gamTie`: HistoryCoherent clause 3 gives ((ν.gam:ℤ):ℚ) = ν.e·(strFrame i·ν.ustar)
  + (ν.s0+ν.wSide)·ν.h; Matches ties e/h/s0/wSide/ustar/gam (all present in the
  §3.2 Matches list, heights INCLUDED); D6a converts strFrame → strS under
  MatchesHist (equal lengths + e-clauses). Transports. ✓
- `anchorTie`: hAnchor (e·a = s0 − t·γ at the node's recorded t) + the uniqueness
  lemma Node.t = bezT e h (from hbezCanon's window + hbez's Bézout identity + hcop;
  verified numerically §1). Transports. ✓
- The other clauses' sources unchanged from rev 6 (root_iff, coherence window/width
  chain, E4/E5, hEdvd, InBox, hmt) — re-checked against Defs.lean, all present. ✓

## 5. Gate recomputation on rev-7 definitions (charge item 5)

All from the independent replica of the blueprint's displayed defs (exact rationals):

| quantity | computed | sealed/note |
|---|---|---|
| W(P̂*) | 7 (= 1·3 + 2·2; d₀ = 3 via monicTop, d₁ = 2) | 7 ✓ |
| M(P̂*) | 1 (⌊3/2⌋·⌊1/1⌋) | 1 ✓ |
| Nshape(P̂*) | 5 (intercepts 3, 4 computed from lineS) | 5 ✓ |
| A(P̂*) | 11 at N = 5, 6, 9 (9 read-0 + 2 read-1 band coords; stable) | 11 ✓ |
| NP(P̂*) | 5 (inhabited branch; sup level 4 at c₀) | N(P̂*) = 5 ✓ |
| C_P̂*(2) | 3 — §0.6's enumeration re-walked: 1 tuple (0,0,1) × 1 ψ × pinned root × forced d′₁ × 3 free d′₀; rev-7 clauses constrain SHAPE fields only, so class data untouched (structural) | 3 ✓ |
| C_P̂*(3) | 48 = 6 root tuples (3 quadratics × r ∈ {1,2}) × 8 | 48 ✓ |
| mult_P̂* | ≡ 1 (per-cell eligible quadratic unique: deg R₀ = 3 < 2g₀μ₀ = 4; R₁ linear — the note's FACTOR SELECTION line; conjugate pair merged by canonRoot since rev 4) | ≡ 1 ✓ |

Plus the unclaimed cross-check A(P̂₀) = 14 = the note's number (§1).

## 6. Spot-checks (charge item 6) — all faithful

1. **D10** vs D4R.1-SUM/D4R.4-SUM: division-free ∑ᶠ over the INDEX type, no
   disjointness, constant = card PrefIdx (= CD via hne + CD_eq with S's hnorm);
   quantifier via hA, packaged at the note's threshold by D4R4_all. ✓
2. **D13** vs "count-equality ⟺ mult ≡ 1 POINTWISE on the event": pointwise ∀ x ∈
   event, mult x = 1. ✓
3. **D14b** vs L12's empty case: hemp/hN/hm explicit; S.event = ∅ ∧ CD = 0 ∧ the
   0 = 0 law. ✓ (Presented exists on this branch under the honest policy: empty jet
   function; hnorm vacuous since note-Pref = ∅ ⟺ PrefSetAny = ∅ under L1-totality
   — the declared pin, no new assumption.)
4. **W3/D3a** vs D4R.2′ "C ≤ M·p^W, M ≤ n^{|P̂|}": the display PAIR, hnorm carried;
   the ∅-shape display owned by D14a per the rev-4 adjudication. ✓
5. **D9** vs L9: totalPins = A(P̂), division-free, via mstar_eq/band/grid chain. ✓
6. **F3** vs "Pref(∅) = {∅}": PrefOpt(∅) = {none} literal; CD_correspondence
   uniform. ✓
7. **NPu**: NP_pos both branches; NP_le_Nshape (sup < Nshape shown above; empty
   branch 1 ≤ Nshape). ✓
8. **rootHalt_iff** root-species filter: non-root children of `none` are inert
   (mem_single requires History.root_iff), so the filter is the faithful L2 clause
   at the ∅-root. ✓

48-unit sweep: manifest re-added = 48 exactly (D0a–c, E1–E9, D1c, D2a, F1, F3, SW1,
W1′–W3, NPu, D3a–b, D4a–b, D5a–b, D6a–e, D7a–c, D8, D9, L9s, D10, D4R4_all(+TW),
D11a–b, D12, D13, D14a–b, T1a, D15); 13 AUX (E1–E8, D1c, D4a, D4b, D5a, L9s) ✓.
hypothesis_fields list hnorm on E9/D2a/F1/D3a/W3 as claimed ✓; §7 item 7 = "jet +
hnorm" ✓; the stale rev-5 TW construction line is gone ✓; VerdictModel's
hCellFin/cell_local/vdict_cell/rootVdict_cell present, typed OPEN, consumed by
nothing ✓ (cell_local does kill cellOf := id under a proper envelope — checked;
`Cell := Box` passes hCellFin alone since Box is finite, but dies at cell_local, so
the docstring's non-degeneracy claim holds through the PAIR).

## 7. Findings

**G-1 (GAP — displayed-skeleton elaboration; binding-sweep residue).** Quote
(§3.2, the block's only variable line, line 429): "`variable {p : ℕ} [Fact p.Prime]
{F : Type*} [Field F] [Finite F]`"; then (lines 608–612): "`def Presented.fiber
{P : Shape n} (S : Presented p F n N m pol P) …` / `def Presented.event (S :
Presented p F n N m pol P) …` / `def Presented.mult (S : …)`". The identifiers
`n N m pol` (and `P` in event/mult) are bound by NO displayed binder or variable
line (Mathlib sets autoImplicit false), so the skeleton as displayed does not
elaborate — against REV 7's own claims "the skeleton elaborates as displayed"
(header item 3) and §14 row 3's "the fiber/event/mult section variables" (no such
variables are displayed). Repair is one line (`variable {n N m : ℕ} {pol :
CanonPolicy p F} {P : Shape n}` before the trio); zero semantic content at stake —
the §4 unit binders are complete and correct. NON-BLOCKING.

**G-2 (GAP — documentation corner on Shape.NP's conditional).** Quote (§3.3):
"`if Nonempty (PrefIdx n pol P) then (P : ShapePrefix).NPband n else 1`" vs L12:
"N(P̂) := max_{η ∈ Pref(P̂)} N(η,⊤) if Pref(P̂) ≠ ∅". At the EMPTY SHAPE the two
conditionals route differently: the note has Pref(∅) = {∅} ≠ ∅ (max branch, value
N(∅,⊤) = 1 — T(∅,⊤) has no equations, §C C.2's 1 + empty max), while the Lean
PrefIdx(∅) is empty (History has no empty chain), taking the else-branch (value 1;
NPband(∅) = 1 also). ALL routes give 1, and every consumer is safe (D14a uses
explicit hN, never NP; D4R4_all carries hne), so this is value-exact — but the
docstring's "L12 QUOTED VERBATIM" glosses a representation deviation that the
sibling deviation (CD's dispatch) earned an explicit display and a machine-checked
bridge (F3). One docstring sentence ("at the ∅-shape both branches give L12's
N(∅) = 1; the branch-condition deviation is F3's History-has-no-empty-chain, value-
exact") closes it. NON-BLOCKING.

**OBS-A (not counted).** The NP docstring's quote "realizability can remove every
assignment" elides one word of the note's "realizability can remove every value
assignment" (:5142) — inside quotation marks; meaning identical.

**OBS-B (not counted).** The γ-tie scale reconciliation (§1's NOTE-SCALE REMARK):
the blueprint's STR-carrying form is the faithful one (MovesC/§C rev 14; SW1
requires it); the note L3's STR-free display is its abbreviation of "§C's DERIVED
list". Recorded so the discrepancy is on the record; gates blind to it (STR = 1).

## 8. Verdict

**ACCEPT (0 crit / 2 gap, both non-blocking one-line repairs).** The rev-7
certificate is COMPLETE and computationally confirmed: all five listed adversaries
plus two new ones (a consistent-(e,h) γ-tie violator; a wrong-Bézout anchor at
e = 2 — the first e > 1 probe) each fail a NAMED clause, and the correct-anchor
control passes; both positives pass every clause with γ₀ = 3, γ₁ = 4 recomputed
from the tie. NP is L12's piecewise threshold with the empty clause unconditional
on the band and D4R4_all's empty branch at L12's full N ≥ 1 range; NP_stab is
correctly scoped. The binding sweep is complete except one displayed section-
variable line (G-1). SW1's extended sketch closes from coherence's γ-tie + hAnchor
+ the verified bezT-uniqueness. All seven-plus sealed gate values recomputed exactly
on the rev-7 definitions (W = 7, M = 1, Nshape = 5, A = 11, NP = 5, C₂ = 3,
C₄₈ = 48, mult ≡ 1), plus the unclaimed A(P̂₀) = 14 cross-check. Both gaps are
writer's-next-touch repairs, not statement defects: no unit says anything different
from, weaker than, or stronger than its quoted display.
