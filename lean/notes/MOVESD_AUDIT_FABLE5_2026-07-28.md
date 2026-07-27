# MOVESD blueprint audit — fresh Fable #5 (rev 6, domain-subtype confirmation)

- **Date:** 2026-07-28
- **Auditor:** fresh Fable instance #5 (zero prior context; read-only; fixes nothing)
- **Scope:** `MOVESD_LEAN_BLUEPRINT_2026-07-28.md` REV 6 — the domain-subtype ruling
  (`Shape n := {P // ShapeWF n P}`), audited as a CONFIRMATION of the cure for Codex
  FINAL#4's findings 1–3 (the one-disease diagnosis), plus the full charge list.
- **Ground truth:** `MOVES_2026-07-24.md` §D4-R rev 9 (lines 4580–5435) + the
  dual-acceptance/kernel-status record (lines 6783–6831); `LeanUrat/MovesC/Defs.lean`
  (read in full — Node/History/HistoryCoherent/Realizable/JetSetup/SHZ/totalPins/
  mstar_eq and all node Props verified present as consumed).
- **Verdict: REJECT (0 crit / 2 gap).** The domain-subtype cure itself is CONFIRMED
  on every mandated check (all seven below PASS); both gaps are mechanical
  incomplete-propagation defects of the rev-6 text, repairable in one sweep without
  changing any unit statement's meaning.

## 1. ShapeWF vs the note's L3 dictionary + three adversaries — PASS

Clause inventory vs L3/§C laws: `species_iff` (History.root_iff), `root_box` (the
degree-n box / InBox), `window` (coherence's s₀'+w' ≤ μ), `gmu` (ψ^μ ∥ R_anch ⟹
gμ ≤ ℓ, E4/E5), `edvd` (Node.hEdvd), `dchain0`/`dchain` (deg Φ₀ = 1 + the width
chain), `monic` (MonicTie, the §0.5-adjudicated slot-set reduction). Every clause is
a dictionary-image law; ShapeRead retains the full rev-9 L3 field list including the
height pair (ustar, gam) — pass-10 F1's u* retention faithfully mirrored (lineS's
intercept consumes ustar).

**Adversary A (junk — must fail).** (i) root read wSide = 10, n = 3: fails
`root_box` (0+10 ≤ 3 false) — the rev-5 W2-rider shape is no longer in the domain.
(ii) monicTop = true at a non-full-span root (s0+wSide = 2 ≠ 3): fails `MonicTie`
(the "artificially smaller W" faker — d shrinks by 1, W by w₀ — is not a Shape).
(iii) monicTop = true at depth 1: `hmonicRoot` forces species = root there, which
`species_iff` kills (and non-root species can't even build the ShapeRead). All three
previously trivialized/violated mass-law units (vacuous PrefSet or false M-bound);
all three now FAIL the certificate. ✓

**Adversary B (real shapes — must pass).** P̂* (n = 3): species root/recentering ✓;
root_box 0+3 ≤ 3 ✓; window 0+1 ≤ μ₀ = 1 ✓; gmu 2·1 ≤ 3, 1·1 ≤ 1 ✓; edvd 1∣3, 1∣1 ✓;
dchain0 D₀ = 1 ✓; dchain D₁ = 1·2·1 = 2 ✓; MonicTie: read 0 true ↔ (0 ∧ 3 = 3) ✓,
read 1 false ↔ false ✓. P̂* ∈ Shape 3. The menu-wave shape P̂₀ (the D4-m2/F1-check
shape, n = 4, root-only (1,1,1,2,0), full span (0,4)–(4,0), u* = 0, monicTop = true):
all clauses check (gmu 1·2 ≤ 4; root_box 0+4 ≤ 4; MonicTie true ↔ (0 ∧ 4 = 4));
P̂₀ ∈ Shape 4, d₀ = 4 = the note's 4-digit cell tuples. ✓

**Adversary C (∅ boundary).** ⟨[]⟩: every ShapeWF clause quantifies over r < 0 or
0 < 0 — vacuously true, so the empty shape IS in Shape n (necessary: the η = ∅
dispatch lives on it). Threading: PrefSet(∅) = ∅ (MatchesHist needs length 0 vs
History.nonempty — D14a's honesty display), CD's if-branch = 1 = C_∅, A'(∅) = 0,
NP(∅) = 1 (empty band), emptyFiber = the full box, and F3's `PrefOpt_empty` gives
the literal Pref(∅) = {none} with `CD_correspondence` transporting the count — the
∅ convention threads the subtype consistently with the bridge. ✓

## 2. SW1 — no universe loss — PASS (with one explicit-hypothesis note)

Walked clause-by-clause: species_iff ⟵ Matches.species + root_iff (indices via
hlen); root_box ⟵ InBox + Matches s0/wSide; window ⟵ HistoryCoherent's containment;
gmu ⟵ E5 (hOrd/hψdeg) + E4 (hRanch/hpatTop) transported by Matches e/g/μ/wSide;
edvd ⟵ hEdvd; dchain0 ⟵ coherence's deg Φ₀ = 1 + hDwidth; dchain ⟵ coherence's
width chain + Matches. All deps exist in MovesC/Defs.lean as fields/Props. MonicTie
enters as the EXPLICIT hypothesis `hmt` — it is the encoding-correctness clause (the
monicTop bit is shape data, not history data), satisfied by construction on every
correctly-encoded note shape; nothing silent. Every note shape (= shape of a
matched coherent in-box chain, correctly encoded) carries the certificate: the
subtype loses nothing of the note's universe. Conversely, certificate-passing
member-free shapes only ever receive true-or-trivial laws (W1′/W2/W3/NPu verified
sound on bare certificate data; empty-Pref laws are the note's own L12 dispatch). ✓

## 3. NP vs L12 verbatim + the circularity check — PASS

L12: "N(P̂) := max_{η ∈ Pref(P̂)} N(η,⊤) if Pref(P̂) ≠ ∅ … N(P̂) := 1 if Pref(P̂) = ∅
… for EVERY N ≥ N(P̂): D4R.4-SUM/EV". The defined `ShapePrefix.NP = 1 + sup(band
levels)` matches: each N(η,⊤) = 1 + largest constrained level (§C C.2); constrained
coordinates = the fresh band exactly (fresh_band + fresh_cover + mstar_eq, grid-read
via D8/D4b), and the band is shape data — the max over η collapses, the note's own
gate remark ("identical for every η"). NO CIRCULARITY: NP's definition and NPu's
three lemmas consume only §3.3 shape defs + L9s (band levels < Nshape from κ ≥ 0,
slope ≥ 0, intercept ceiling — checked); D9 (the Lean L9) is nowhere in NPu's
dependency cone, and D9 itself never consumes NP. Dependency order Defs → NPu →
D4R4_all (which also uses D10/D12 → D9) is acyclic. Empty convention: band-empty ⟹
NP = 1; the Pref-empty-but-band-nonempty case is carried at full L12 strength
(every N ≥ 1) by D14b, so no range is lost by the corpus (see OBS-2). D4R4_all's
range ∀ N ≥ NP is exactly L12's, constants CD/A′ N-free, no ∃-over-presentations in
the conclusion; TW consumes PRESENT-EXIST restated at NP. ✓

## 4. The five hnorm-gated units (D2a, F1, E9, D3a, W3) — PASS

The note's domain IS normalized presentations: its Pref(P̂) is intrinsically
canonical-lift η's (L3), and the classes ↔ η dictionary is the typed `PresentNorm`
(totality from the policy-free PrefSetAny + Galois uniqueness — note-supported via
L1 kernel-(a, discharged math-side), the L6 corollary, and the Fable#2 equivariance/
rigidity analysis; Lean discharge = HC-2, ledgered). With hnorm the five statements
remain the note's 'always' claims over the note's own universe (Shape n ×
PresentNorm, the latter note-true on all of it); without it PrefIdx-emptiness could
be a policy artifact — exactly Codex#4 f.2. hnorm is satisfiable (∅-shape trivially;
gate shape per §0.6), never dropped elsewhere (D10/D12/D13/D14b consume it through
`Presented.hnorm`; D3b gets it from its S binder). On CD_eq/card_classes the rider
is logically superfluous (definitional equalities) — harmless, meaning-carrying. ✓

## 5. Gate recomputed over the subtype from the rev-6 definitions — PASS (exact)

From §3.1/§3.3 defs at P̂* ∈ Shape 3: strS = (1,1); lineS₀ = ⟨3, 1⟩ (through (3,0));
lineS₁ = ⟨4, 3/2⟩ (u*₁ = 1 + (3/2)·2 = 4, through (0,4)/(2,1)); κ = (1,3);
childWidthS = (2,2); prevRimS = (3,2). Band read 0: {b < 3, ℓ ≤ 3−b} = 4+3+2 = 9
cells; band read 1: floor 3 < ℓ + (b mod 2) ≤ 4 on b < 2 = {(4,0),(3,1)} = 2 cells.
**A = 11 ✓** (matches the note's 11-pin cross-check: level-4-at-c₀ = (4,0),
level-3-at-c₁ = (3,1)). **W = 1·3 + 2·2 = 7 ✓** (d₀ = 3+0, d₁ = 1+1). **Mfac =
⌊3/2⌋·⌊1/1⌋ = 1 ✓**. **Nshape = 1 + max(⌈3⌉,⌈4⌉) = 5 ✓**. **NP = 1 + 4 = 5 ✓** = the
note's N(P̂*) via its own derivation. Classes at p = 2: unique ψ = z²+z+1, r = 1 ⟹
tuple (0,0,1) ×1; zbar₀ pinned to canonRoot ×1; d′₁ (HV)-forced ×1; d′₀ ∈ F₄ˣ ×3 ⟹
**C = 3 ✓**; p = 3: 3 quadratics × 2 roots × 8 ⟹ **C = 48 ✓**. mult ≡ 1: per
realized cell the eligible quadratic is unique (deg R₀ = 3 < 2g₀μ₀ = 4) and R₁
linear; the rev-3 conjugate pair is one class under IsCanonPres ⟹ **mult ≡ 1 ✓**,
EV-equality — the note's gate re-derivation verbatim. All eight numbers exact. ✓

## 6. VerdictModel's typed fields vs D4R.0-K(c) — PASS

Kernel (c) per the dual-acceptance record: "alphabet V + halting rule τ + the
UNIFORM per-class detection cap". Typed: V/hVfin/hVne; vdict + halt_iff (L2's leaf
clause, both directions, no `leaf := False` instance); cap/cap_law + levelOf/
levelOf_lt (the uniform per-class cap against vdict); vdict_local (finite-level
shadow of VP-2). REV-6 additions match Codex#4 f.5's demand: rootVdict/rootHalt_iff
(the ∅-root (ns) verdict — L5 (ns) + L2's leaf clause at the root) and
Cell/cellOf/vdict_cell/rootVdict_cell (τ factors through cell data — typed, OPEN,
semantics documented as the HC-2/MovesT pin). Consumed by nothing in MovesD;
instantiable (non-vacuous as a type); no silent discharge claimed. ✓ (OBS-1 below.)

## 7. Spot-checks (6) + fresh sweep of all 48 units — PASS except the two gaps

Spot-checked in depth: D0b (division-free C(b) at ⊤, numPinned 0 ✓), E6 (coprime
monic irreducibles, k·gμ ≤ deg Ranch ✓), D5b (intercept from hLineU + slope law —
u* enters exactly as L9 rev 9 says ✓), D13 (pointwise iff, p-power cancellation,
hne present ✓), D14b (L12 empty display verbatim, hN/hm explicit, hnorm via S ✓),
T1a (snoc-peeling with root_iff giving hν ✓). Also walked: E9's full-tuple recovery
(monic digit via Matches.hmonic; RanchImage from digits; ψImage from rank via E8),
D3b's hnorm-through-S, D8's three-conjunct band transfer (fine-slot upper edge
mirrors ROUND 6's inFreshBand exactly), D9/L9s/D10/D12 chain, D11a/b, D14a, D15
(hcyl + hwd both explicit hypotheses; D4R_CYL nowhere a field), F3, W1′/W2/W3, NPu,
D4a/D4b, D5a, D6a–e, D7a–c, D1c, D2a, F1, E1–E8, D0a/D0c, D4R4_all/TW. Checklist
§7: rev-9 L3 retained ✓; no disjointness consumed ✓; kernel citations correct ✓;
EV pointwise + hA quantifier ✓; A/A′/CD definitions with the ∅ dispatch at
definition level ✓; E1–E9 consume only MovesC Props + Matches ✓; assumed structure
fields = jet + hnorm only (ledger row correct; §7 item 7's "ONLY jet" wording is
stale — cosmetic). No new axioms anywhere. 48 units confirmed (+SW1, +NPu).

## FINDINGS

**GAP 1 (Defs soundness — the rev-6 re-binding not swept through the §3.2/§3.4
displays; one disease, several sites).** Quote: `def PrefSet (n : ℕ) (pol :
CanonPolicy p F) (P : Shape n) : Set (History p F)` vs `def PrefIdx (n : ℕ) (pol :
CanonPolicy p F) (P : ShapePrefix) : Type := ↥(etaData P '' PrefSet n pol P)`.
PrefSet/PrefSetAny/Threshold bind `P : Shape n` while PrefIdx, PresentNorm
(`PrefSetAny n P` with `P : ShapePrefix`), CD, Presented, PrefOpt, D4R_CYL, and
ClassFiberWelldef retain rev-5's `P : ShapePrefix` and call the Shape-n-binding
defs. No coercion exists ShapePrefix → Shape n, so the skeleton as displayed does
not typecheck; the blanket "(coercions elided below)" only covers the ↑P direction.
The ruling text ("ALL downstream defs/units re-bind {P : Shape n}") pins the
intent, and BOTH mechanical repairs (re-bind the seven, or revert PrefSet/PrefSetAny
to ShapePrefix while units keep the Shape-n quantification) leave every unit
statement's meaning identical on the quantified domain. Classification: GAP
(underspecified/inconsistent Defs dependency; charge item 4's "typing plausible in
Lean 4" fails as displayed). The repairer must pick ONE binding convention and
sweep §3.2/§3.4 + the D4R4_all `(P : ShapePrefix).CD` usages.

**GAP 2 (stale rev-5 construction in D4R4_all's spec).** Quote: "`TW`: Nshape is
the CONSTRUCTIVE WITNESS (NP := Nshape, hstab := L9s, jets := hex via choice)".
At rev 6 `Threshold` has no NP or hstab field (NP is defined, hstab derived — the
spec's own header says so), so the parenthetical assigns fields that no longer
exist and, read literally, contradicts NP ≤ Nshape (in general strict). The TW
STATEMENT itself is clean (sole field jets := choice on hex at every N ≥ NP);
prose-only defect. Classification: GAP (ambiguity — unswept rev-5 residue).

**OBS-1 (uncounted).** `rootHalt_iff` quantifies `∀ ν : Node p F` without the
species filter its depth-≥1 twin `halt_iff` carries (`hν : species ≠ root`): junk
`child none ν x` facts at non-root-species ν (untied by mem_single, whose History
requires species = root) could force rootVdict = none in a degenerate instance.
Instance-avoidable, no MovesD consumer; recommend restricting the quantifier to
root-species ν at the repair sweep. Not counted.

**OBS-2 (uncounted).** The NP docstring's "L12's empty convention … falls out of
the formula" holds only for band-empty shapes; a Pref-empty shape with nonempty
band gets NP > 1, while the note assigns N(P̂) := 1 — the every-N ≥ 1 law there is
carried at full strength by D14b, so the corpus loses no content. Docstring
precision only. Not counted.

**OBS-3 (uncounted).** §7 checklist item 7 ("`Presented.jet` is the ONLY assumed
structure field") is stale against the §2 ledger's correct "two assumed structure
fields" (jet + hnorm). Cosmetic.

## COUNTS AND VERDICT

Criticals: 0. Gaps: 2 (both mechanical rev-6 text-propagation defects; neither
touches any unit statement's semantics, the certificate design, the gate, or the
open-surface ledger). The domain-subtype cure is CONFIRMED: junk shapes fail the
certificate by type, the note's shapes (P̂*, P̂₀, ∅) pass, SW1 closes the universe,
NP is L12's formula non-circularly, the five hnorm riders are the note's domain,
and every gate number recomputes exactly over the subtype.

**VERDICT: REJECT (0 crit / 2 gap)** — repair = one textual sweep (binding
convention + stale TW parenthetical), then this auditor expects a clean pass.
