# MOVESD BLUEPRINT REV 8 — FRESH-INSTANCE ACCEPTANCE AUDIT (Fable #7, 2026-07-28)

VERDICT: **NOT ACCEPTED — 0 critical / 2 justification gaps**, both in ONE unit (SW1)
with one root cause: REV 8 grew `ShapeWF` by `w0`/`wchain` (its own item (1)) but did
not extend SW1's hypotheses or sketch to cover them, so the closing claim "the
genuinely underivable residue … is the [ONE] named encoding gap ENC-MONIC" is
overstated. Everything else audited — the seven charge items, the full gate
(Python-replicated), the six-adversary block, the ∅ dispatch arithmetic, the §3.0
order walk, the TreeModel/VerdictModel teeth, and a 48-unit sweep — verified CLEAN.
The architecture stands; the repair is local (SW1 + §2 ledger + §15 row 2).

Auditor: fresh Fable instance. Read in full: the blueprint
(`MOVESD_LEAN_BLUEPRINT_2026-07-28.md`, 1552 lines), the source §D4-R rev 9
(`MOVES_2026-07-24.md` 4580–5435 + the dual-acceptance record 6783–6831), and
`lean/LeanUrat/MovesC/Defs.lean` (979 lines) plus the `Moves` defs SW1's new legs
would consume (`Stage`, `TransitionData`, `IsRecentering`, `nextField`,
`HistoryCoherent`). Role: read and judge; nothing fixed.

---

## 1. Charge item (1) — w0/wchain vs the note's dictionary: PASS (as certificate clauses)

The note's dictionary: L3 retains "residue degrees w_r" as shape data; read r's
digits range in the pool F_{Q_r}, Q_r = p^{w_r} (L8/L11) — the pool is the frame
field. §D4-R.6 supplies both data points verbatim: the root read's "Side digits
(pool F_p)" (w₀ = 1) and "F₁ := F_p[z]/(ψ) = F_{p²}, w₁ = 2" (w₁ = w₀·g₀, g₀ = 2).
The tower law F_{r+1} = F_r[z]/(ψ_r), deg ψ_r = g_r (recenterings g = 1, field
unchanged — `IsRecentering`'s `σ'.K = σ.K` in the Lean corpus, `TransitionData`'s
`child_field : σ'.K = σ.nextField zbar` otherwise) gives exactly the blueprint's one
uniform law `w_{r+1} = w_r·g_r`. As SHAPE-CERTIFICATE clauses, `w0`/`wchain` are
note-faithful: every note shape is dictionary-image of a §C history whose frame
fields obey the tower, so nothing of the note's universe is excluded.

Adversary A-vi re-run (root-only record, node (1,1,1,2,0), full span, w = 2, n = 4):
fails `ShapeWF.w0` and nothing else — replicated in Python (below), exactly the
blueprint's ✗. Predecessor's full block re-run: A-i → root_box ✗ (also MonicTie —
consistent, the blueprint names root_box); A-ii → MonicTie ✗; A-iii →
hmonicRoot ✗; A-iv (h = 0) → `hh` unbuildable ✗; A-v → hcop ✗. Positives: P̂* passes
every clause including w0 (w₀ = 1) and wchain (w₁ = 1·2 = 2, the note's "w₁ = 2");
P̂₀ passes (w₀ = 1, wchain vacuous). ✓

BUT: the clauses' consumption in SW1 is where the two gaps live — §8 below.

## 2. Charge item (2) — ENC-MONIC's honesty: PASS for MonicTie; the "ONE gap" claim FAILS for ShapeWF

The Matches clause checked at the source (§3.2): `(R.monicTop = true →
ν.sideDigit R.len = 1)` — a one-directional implication about the digit VALUE.
Verified underivable in both directions of the root residue:
- (→) `monicTop₀ = true → s0+wSide = n` is NOT derivable: Matches yields only
  `sideDigit ℓ₀ = 1`, a value fact; a sub-span root read whose top digit happens to
  equal 1 (allowed — `hpatTop` says ≠ 0 only) matches a `monicTop = true` record.
- (←) `s0+wSide = n → monicTop₀ = true` is NOT derivable: at `monicTop = false` the
  Matches clause is vacuous, so a genuinely full-span monic-box history matches a
  `monicTop = false` record (the blueprint's own sentence, confirmed).
The derivable part IS derivable exactly as claimed: `monicTop = true → species =
root` (`hmonicRoot`) + Matches' species equality + `History.root_iff` give
`monicTop_r = false` for all r ≥ 1, settling MonicTie at every non-root read; the
root read's biconditional is then precisely `hmt0`. So `hmt0` is the exact residue —
the weakest sufficient hypothesis FOR MONICTIE, and its ENC-MONIC framing
(encoding-correctness duty, owner = D4-n3 gate + menu wave) is honest.

HOWEVER, `hmt0` is NOT sufficient for SW1's CONCLUSION `ShapeWF n Q`, because the
rev-8 certificate also contains `w0`/`wchain`, neither covered by SW1's hypotheses
or sketch — the two findings, §8.

## 3. Charge item (3) — the ∅ dispatch: PASS (computed)

- `D4R2'` at reads = []: `Shape.CD` takes the if-branch, CD = 1 (the note's own
  definition-level Pref(∅) = {∅} dispatch). `Mfac(∅)` = empty `List.prod` = 1;
  `W(∅)` = empty sum = 0. The theorem instance IS `1 ≤ 1·p⁰ = 1` — the note's C_∅
  arithmetic (L12: C_∅ = 1; D4R.2′ at the empty prefix), a theorem, not a 0-bound.
  `D4R2'_full` adds `Mfac(∅) = 1 ≤ n⁰ = 1`. ✓
- The empty ShapePrefix IS a Shape (every ShapeWF clause quantifies over r <
  0 or 0 < length — vacuous), so the ∅ instance genuinely lives in the domain. ✓
- E9's `encTargetP_empty`: `EncTargetP` at reads = [] is a Pi over `Fin 0` — a
  singleton type, `Nat.card = 1` = C_∅. The singleton-to-unit display is exact. ✓
- PresentNorm at ∅ is trivially true (PrefSetAny(∅) = ∅: MatchesHist needs length 0,
  `History.nonempty` forbids it), so the hnorm hypothesis is satisfiable there —
  no vacuity smuggled. ✓
- Cross-check of the NP ∅-routing docstring (REV 8, Fable#6 G-2): NPband(∅) =
  1 + sup ∅ = 1; Shape.NP(∅) = else-branch = 1; the note's MAX branch gives
  N(∅,⊤) = 1 (§C C.2 with zero equations). All routes value-exact, deviation
  displayed = F3's. ✓

## 4. Charge item (4) — §3.0 declaration order: PASS (walked)

Group (1): `strS` now precedes `ShapeWF` (the Codex#6 g.4 hoist) — `gamTie`'s
`P.strS r` resolves; `bezT` precedes `anchorTie`; `MonicTie` precedes `monic`;
`ShapeRead.w` precedes `w0`/`wchain`. Group (2) is self-contained on group (1)
(lineS…bandS → A → Nshape → A' → NPband → Anet, each consuming only earlier names).
Group (3): selRank's deps (pool, fieldEnum, lexLt, RanchImage, ψImage,
poolSubfield, EligibleImage) all earlier in the group; canonRoot (group 4) consumes
ψImage (group 3) ✓ — the §3.2 order note agrees. Group (4): EtaGalEq after EtaData;
Shape.NP after PrefIdx (the piecewise form's consumption); PresentNorm after
PrefIdx and EtaGalEq; Threshold after Shape.NP and Presented. Group (5): D4R_CYL
after Presented (fiber); VerdictModel after TreeModel. Every forward reference
resolved; the list elaborates.

Two non-blocking observations: (i) the §3.2 DISPLAY places the section's
`variable {pol : CanonPolicy p F}` line above `structure CanonPolicy` — fine only
because §3.0 is normative and the display declared thematic; an implementer must
open that section after group (4)'s CanonPolicy. (ii) `Presented.fiber/event/mult`
are absent from the §3.0 list (their §3.2 position after Threshold is the obvious
placement, before group (5)'s D4R_CYL which consumes fiber). Neither blocks.

## 5. Charge item (5) — TreeModel `child_iff` vs L2; VerdictModel `cellOf := id`: PASS

L2's display: "the children of a chain η ∈ T_can(f) … are ALL next-node data ν =
(side s, its digit tuple, ψ, canonical lift) where s is an eligible side … and ψ
ranges over the eligible factors". The typed law `child_iff : mem o x → (child o ν x
↔ eligible o ν x)` is the all-and-only content conditioned exactly on η ∈ T_can(f)
(= `mem o x`), with `eligible`'s semantics (cell data, kernel-(b)) an OPEN named
field — the dependency is a field, not prose, as claimed. Faithful. ✓

`cellOf := id` kill, constructed: take `Cell := Box p m`, `cellOf o x := x`. By
`hlevel` at ℓ := capBound (`hcapB : capBound < N` makes it eligible) there is
c₀ : Fin m with `levelOf c₀ = capBound`; by `hcapU`, no v has `levelOf c₀ < cap v`,
so c₀ is OUTSIDE the envelope. Take x, x' equal everywhere except at c₀ (ZMod p has
p ≥ 2 elements): `cell_local`'s hypothesis holds, its conclusion `x = x'` fails —
the instance is unbuildable. ✓ (`hCellFin` alone would not kill it — Box is finite;
the teeth is `cell_local` + the rev-8 cap fields, exactly as documented.) The
constant-verdict caveat is stated, not hidden. ✓

## 6. Charge item (6) — the gate on rev-8 defs: PASS (hand + Python, `/tmp/movesd_rev8_check.py`)

The rev-8 §3.1/§3.3 definitions were re-implemented independently in Python
(lineS/kappaS/innerslotS/htS/staircaseS/floorS/prevRimS/bandS/A/Nshape/NPband/W/
Mfac/bezT + the full certificate incl. w0/wchain/gamTie/anchorTie). Output:

- P̂* (n = 3): ShapeWF fails: NONE (P̂* ∈ Shape 3, all clauses incl. w₀ = 1,
  w₁ = 2, γ₀ = 3, γ₁ = 4, bezT = 0 at e = 1 hence a = s0 = 0).
  **W = 7 ✓ · Mfac = 1 ✓ · Nshape = 5 ✓ · NPband = 5 ✓ (NP = 5, inhabited branch)
  · A = 11 ✓ (N-stable: A(n,9) = 11 ✓) · A_net = 4 ✓ · d₀ = 3, d₁ = 2 ✓.**
- C counts by direct enumeration of the note's realizability display
  (R₀ = ψ·(z−r), ψ irreducible quadratic, r ∈ F_pˣ, × the free d'₀ ∈ F_{p²}ˣ):
  **C_P̂*(2) = 3 ✓, C_P̂*(3) = 48 ✓** — the sealed counts.
- mult ≡ 1: the §0.6 factor-uniqueness argument re-checked (deg R₀ = 3 < 2·g₀·μ₀
  = 4 forces the unique eligible quadratic per cell; R₁ linear) — unchanged by the
  rev-8 deltas, which constrain shape fields only. ✓
- **A(P̂₀) = 14 ✓** (root-only, n = 4, full span, u*₀ = 0: band count 5+4+3+2 —
  the note's 4 cluster + 6 below-line + 4 on-line), P̂₀ ∈ Shape 4 with w₀ = 1,
  Mfac(P̂₀) = 2 = the note's m̄₀ = ⌊4/2⌋ (the F1 multiplicity instance). ✓
- Adversaries: A-i…A-vi all fail exactly as tabled (§1 above). ✓

## 7. Charge item (7) — spot-checks (>6 run) + the 48-unit sweep

Unit count re-verified: 48 exactly (D0a–c, E1–E9, D1c, D2a, F1, F3, SW1, W1′, W2,
W3, NPu, D3a–b, D4a–b, D5a–b, D6a–e, D7a–c, D8, D9, L9s, D10, D4R4_all(+TW),
D11a–b, D12, D13, D14a–b, T1a, D15). Spot-checks against the note's displays:

1. **D10** vs D4R.1-SUM/D4R.4-SUM: division-free transcription exact (×p^A both
   sides); the level quantifier via `hA : A n N = A' n` covers L12's ∀ N ≥ N(P̂)
   through NP_stab/L9s; constants (card PrefIdx, A') N-free; no disjointness. ✓
2. **D13** vs the L12 pointwise upgrade: at fixed level the fibers ARE box subsets,
   so the note's positive-mass-overlap step is the finite double count; cancel p^{A'}
   (p ≥ 2). "iff mult ≡ 1 POINTWISE on the event" carried verbatim. ✓
3. **D14a** vs the empty dispatch: card univ = p^{nN} = 1·p^{nN−0}; A'_nil; hN = 1 ≤ N
   = L12's "for EVERY N ≥ 1"; the CD-carries-the-dispatch honesty display intact. ✓
4. **E6** vs L11's m̄: distinct monic irreducibles coprime, ∏q^μ ∣ Ranch, k·g·μ ≤
   ℓ = deg Ranch (E4, `hOrd`, `hψdeg`) — "each contributes g_r·μ_r". ✓
5. **D9/L9s** vs L9: the shape replicas checked field-by-field against MovesC —
   lineS reproduces `hLineU` (at((s0+wSide)·D) = u*) + the coherence slope law;
   bandS's third conjunct is the ROUND-6 FINE-slot boundary
   `line.at((b/Dwidth)·Dwidth)` = `slotVal ∘ fineSlot` (NOT the coarse lineStep) ✓;
   floorS = the coarse `childWidth` staircase fold = `floorH` ✓; prevRimS ✓. The
   A-transport chain (mstar_eq → band → D8 → D4b grid count) is exact. ✓
6. **D4R4_all/TW/NPu** vs L12: quantifier ∀ N ≥ NP with SUM ∧ EV; empty branch =
   L12's every-N ≥ 1 clause at full strength; NP_stab's inhabited-branch scoping
   sound (band levels ≤ NP−1 by the sup; [Nshape, N) band-free by the intercept
   bound; NP ≤ Nshape both branches). PRESENT-EXIST consumed only in TW. ✓
7. **F3**: both branches machine-checkable as stated (PrefOpt_empty = {none};
   CD_correspondence via `some`-injectivity). ✓ · **T1a** derivable from
   mem_snoc/mem_single + root_iff (appended nodes non-root). ✓ · **D15** exact on
   hcyl + hwd. ✓ · **W1′/W2/W3** chains close (ℓ_{r+1} ≤ s0'+wSide' ≤ μ_r ≤ g·μ ≤
   ℓ_r; m̄ ≤ ℓ ≤ n). ✓ · **D3b** gets hnorm through S.hnorm. ✓

Sweep residue (non-blocking observations): (i) §6's build order predates the rev-6
additions — SW1, NPu, F3, W3, D4R4_all are missing from the waves (stale, carried
through two accepted revs; should be refreshed at implementation). (ii) E9's
`hnorm` hypothesis is not consumed by the literal injection argument (the chain
closes from Matches + node Props alone); it is documented as the semantic pin —
harmless. (iii) A-i also fails MonicTie besides root_box — the table's single-cause
labels are minimal causes, fine.

---

## 8. THE TWO FINDINGS (both SW1; one root cause)

**Quoted claim under audit** (REV 8 header item (2), §15 row 2, SW1's spec block):
"SW1 now DERIVES MonicTie's derivable clauses …; the genuinely underivable residue
— the ROOT read's monicTop ↔ (s0+wSide = n) — is the named encoding gap ENC-MONIC
…, kept as SW1's weakest sufficient hypothesis `hmt0`." SW1's statement:
`ShapeWF_of_matches (hM) (hcoh) (hbox) (hmt0) : ShapeWF n Q`, sketch = "transport
each certificate clause from the matched history: species_iff …; window/dchain …;
gmu …; edvd …; root_box …; gamTie …; anchorTie …". difficulty "medium".

The conclusion `ShapeWF n Q` at rev 8 CONTAINS `w0` and `wchain`. The sketch names
neither, and the hypothesis set does not support one of them:

**G-1 (justification gap — SW1's `w0` leg has no derivation path; the "ONE
underivable clause" claim is overstated).** `w0` demands `reads[0].w = 1`; Matches
pins `Nat.card ↥ν₀.σ.K = p^{w₀}`, so the leg needs card(root frame field) = p.
Checked against the consumed interfaces: `HistoryCoherent`'s only root clause is
`(H.nodes[0]).σ.Φ.natDegree = 1`; `Stage` requires merely `FQ ≤ K`; `InBox`,
`Realizable` (not even a hypothesis of SW1), `IsCanonPres` say nothing about the
root residue field. NO clause on SW1's hypothesis path pins the root pool to F_p.
The transport therefore does not close: a Lean-`HistoryCoherent` history over a
root stage with K ⊋ (prime field) — if such a Stage exists — matches only w₀ ≥ 2
records, refuting SW1 as stated. I checked whether the Stage laws exclude such a
stage: plausibly YES, but only via a genuinely novel interface argument (at
deg Φ = 1 the coefficients are constants; Hom(ℤ_pˣ, ℤ) = 0 forces units to weight
0; `hRmul`/`hRadd`/`hS5` force the fixed-weight digit scalars into a single
(prime-field)ˣ-coset of order p−1, and `hS6b` demands ALL of Kˣ — contradiction for
card K > p). That is a hard, unsketched, research-grade lemma about `Stage` — in no
sense the spec'd "transport … medium". HONEST FIXES (either): (a) a second named
hypothesis on SW1 — `hw0 : Nat.card ↥(H.nodes[0]'h0).σ.K = p` — a second
ENC-style residue (root pool = F_p, §D4-R.6's "Side digits (pool F_p)"), with its
own §2 ledger row and owner, and §15 row 2 / the header claim corrected from "the
one underivable clause" to two; or (b) the hS6b-coset obstruction as a new named
AUX unit (hard). Discharged on the note's universe either way — the subtype
architecture and the universe-loss guard survive intact; nothing downstream
consumes SW1 in the build DAG. Gap, not critical.

**G-2 (justification gap — SW1's `wchain` leg unsketched and un-depped).** The leg
IS derivable, but from sources SW1's spec never names: non-recentering steps via
`TransitionData.child_field : σ'.K = σ.nextField zbar` (= `Subfield.closure
(K ∪ {z̄})`) plus a finite-field extension-degree card argument — minpoly of z̄ over
↥σ.K is the parent's ψ (`hψirr` + `hψmonic` + `hψdeg` + `hzbarRoot`), so
card σ'.K = (card σ.K)^g, whence p^{w_{r+1}} = p^{w_r·g_r} and exponent-injectivity
(p ≥ 2) closes; recentering steps via `IsRecentering`'s `σ'.K = σ.K` + the node's
`hspecRec` (g = 1). This is E3-grade field theory (arguably the hardest new step in
SW1, likely its own AUX unit), absent from the sketch and from deps (E4, E5 only).
One-paragraph spec repair; flagged because the campaign standard is that unit
sketches name their mechanisms, and because it shares the root cause of G-1.

---

## 9. Verdict

**NOT ACCEPTED: 0 critical / 2 gaps** (G-1, G-2 — both SW1; root cause: ShapeWF
grew at rev 8, SW1's spec did not). Everything else is clean at the acceptance
standard: the gate is exact on the rev-8 definitions (independently replicated:
C(2) = 3, C(3) = 48, mult ≡ 1, NP = 5, Nshape = 5, A = 11, W = 7, M = 1, and
A(P̂₀) = 14), the six adversaries die at exactly the tabled clauses, the ∅
arithmetic is now theorems (1 ≤ 1 computed at D3a/W3; card 1 at E9), ENC-MONIC is
honest for MonicTie with `hmt0` the exact residue, the §3.0 order elaborates, the
TreeModel law is L2-faithful, and `cellOf := id` is dead by construction. REV 9
needs: SW1's w0 hypothesis (or the hard obstruction unit) + ledger row + the
"one underivable clause" claim corrected + wchain's sketch leg; opportunistically,
the §6 build-order refresh.
