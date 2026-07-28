# MovesT blueprint (rev 1) — fresh-instance FABLE audit (2026-07-28)

ARTIFACT: `lean/notes/MOVEST_LEAN_BLUEPRINT_2026-07-28.md` (1382 lines, read in full).
GROUND TRUTH: `MOVES_2026-07-24.md` §T-ASSEMBLY rev 7 (6970–7761, read in full);
`MovesD/Defs.lean` + `MovesSp/Defs.lean` + MovesC signatures (every cited name
spot-verified); MovesD blueprint §2.5 (W4-1…W4-4); MovesS §W4-SYNC (S-1…S-11) + the two
ratification addenda (`MOVESS_RATIFICATION_CODEX_2026-07-28.md` findings 1 and 7); HC2
blueprint Walls A/B + the clause-(vi) §7.6 note; the sealed gate records
(`CASE_SIB_SEALED_PREDICTIONS.md`, `CASE_TN3_SEALED_PREDICTIONS.md` 21/21 PASS,
`FABLE_CONFIRM_TASM_REV6` p=2 census line 65) and the acceptance record MOVES 9189–9227.
CHARGE: `CAMPAIGN_AUDIT_CHARGE_2026-07-28.md` + the six wave-4 hardest items.
Calibration: verify by computation and display. I fix nothing.

## VERDICT: **REJECT (5 crit / 8 gap)**

---

## 0. What checks out (recorded so the repairer doesn't re-litigate it)

* **Citations/names.** Every consumed Lean name exists with the claimed shape:
  MovesD `Box`/`topLocus`/`ShapeRead`/`ShapePrefix`/`ShapeWF`/`Shape`/`CanonPolicy`/
  `PrefSet`/`PrefIdx`/`reprOf`/`Presented.fiber|event|mult`/`Threshold`/`TreeModel`
  (structural fields only, as claimed)/`D4R_CYL`/`ClassFiberWelldef`/`History.snoc`/
  `History.IsPrefixOf`/`Nshape`/`NPband`/`Shape.NP`/`ShapeWF_of_matches` (SW1)/
  `D4R4_all`/`D4R1_SUM` (D10)/`band_shape` (D8)/`chart_count` (D4b); MovesSp `Species`/
  `StageLaws`/`Coherent` (G1–G6, G6 = sel=none ↔ W=1)/`RootStage`/`CatalogueWord.hLast`
  (W=1 convention)/`CanTreeModel`; MovesC `C4_conditionalMass` (T-E3's display is its
  verbatim signature incl. `Sigma.mass`), `C6_thmC_b`, `AdmissibleZ`, `SHZ`, `totalPins`,
  `boxMass`, `HistoryCoherent`, `Realizable`, `JetSetup`, `Locus`.
* **Note-line citations.** All spot-checked moves_refs are accurate, including the
  acceptance record (9215–9227), the rev-6 JOINT-D1→Montes-L1 repair (9196–9201, matches
  T-S3's record verbatim), the ns-null four-verification claim (9222–9223), and the p=2
  confirm census N(fiber)=8=2^{9−6}, 0/10,000 (FABLE_CONFIRM_TASM_REV6 line 65).
* **§0 ledger.** The conditionality rows match the note's §T.5 perimeter; both refutation
  records (TB-CAP(ns) literal duty FAILS 7189–7202; raw-count limit FALSE 7237–7240) are
  correctly carried: no unit states an (ns) cap, no unit claims a raw-count limit,
  T-E8/E11 exclude (ns) by `hdet`, T-C8/E12 are normalized-only.
* **Quantifier honesty (charge item 2).** TB-CAP(irr) is stated per (P, i) — never
  joined; `VTree.thr` is a per-tree max (7562–7566); no cap uniform over cells appears
  anywhere. SIBLING INDEXING honored (member-indexed Finset, no ordering, no symmetry
  factor); the multinomial scope is correctly NOT claimed (T-E10 docstring duty).
* **ns-null chain structure (charge item 3).** C3=(ns-lump)/C4=ladder/C5=Z_M
  construction+freeness+count/C6=C(b) pricing/C7=limit/C8=consequences maps the displayed
  rev-2 proof 7203–7247 clause-for-clause; the (ZC)/B(iii)/C(b) consumptions ride as
  hypotheses with the right owners. (One gap on the profinite face, GAP-4.)
* **Q1/Q2 fences (charge item 4): PASS.** No unit among the 51 consumes the re-keyed
  child value or the vertex pin; `CellAssign.child_cell` is keyed to `T.child`; G3 is
  spec-only `fenced-Q1`; `CellAssign` carries no vertex field. No critical here.
* **Decide-gate numbers (charge item 5).** All quoted integers re-verified: 78,125² =
  15,625·390,625 = 6,103,515,625; 5^{22−14} = 390,625; marked 64 / per-f 58 / gap 6 and
  6·390,625 = 2,343,750 match the T-n3 seal (C=64/E=58/GAP=6 in the seal file); the p=2
  target 8 = 2^{9−6} matches the confirm. T-E8's exponent law verified EXACT against both
  censuses (F1: 5⁶·5^{4+12} = 5²²; p=2: 8·2^{3+3} = 2⁹). T-E11's form verified on F1.
  (Feasibility of `by decide` is GAP-6.)
* **Seam map (charge item 1), non-critical rows.** W4-1 (CellAssign/eligibleT + T-D1/T-D2
  honor the tie-demand union: defined-over-cell-vocabulary, no eligible:=child vacuity,
  cell-data-never-f-data), W4-2 (both directions: VdAt n concrete + non-constant-vdict
  gate; cell_local rebuilt per-state with T-D4's falsifier; ns cap-free per the
  refutation record; caps N-free hence cross-level), W4-4 (T-D7 from
  mstar_eq+fresh_band/fresh_cover+D8/D4b, deletes D4R4_all's pointer), S-1/S-2/S-3/S-4/
  S-5/S-7/S-8/S-9/S-10/S-11, both MovesS addenda (the W1-circularity disposition is
  honest: MovesT supplies TREE-EXP/TREE-N/ONE-F as separate named theorems so MovesS's
  re-key can derive RS.1-SH non-circularly; the derivation and the pin restructuring stay
  MovesS's; W1m's ledger is MovesS's real object, T-D12 types only the [3t] premises),
  Wall A (eligibleT↔SideReads reconciliation with the clause-(vi) pointer, verified
  against HC2 §7.6/lines 1471–1475), Wall B (correctly NOT widened; jets ride as
  hypothesis fields on exactly the listed units) — all faithful to their recorded
  contracts. W4-3 is CRIT-4 below; S-6's deliverable pointer is part of GAP-2.
* **Unit census.** 51 units = 12 easy / 29 medium / 10 hard checks against the specs;
  the hard list matches; pre-approved splits recorded.

---

## CRITICAL findings

**CRIT-1 · §2.6 `SibCount` (consumed by T-S1/S3, T-E5/E7/E8/E10/E11, T-D12): the
conditioning event Σc is quantified over ARBITRARY subsets — the typed kernel is FALSE
for the intended models, i.e. silently STRENGTHENED into an unsatisfiable hypothesis.**
Quote:
```
∀ (o …) (Σc : Set (Box p m)) (B : Finset (Node p F)) (S : …),
    2 ≤ B.card →
    (∀ x ∈ Σc, T.mem o x ∧ ∀ ν ∈ B, T.child o ν x) → …
```
The note's display 7284–7292 conditions on THE cell event Σ_c ("c a digit cell of Σ …
conditionally on the cell event Σ_c"). The blueprint's only Σc-hypothesis is
Σc ⊆ {x : mem ∧ all B-children} — satisfied by EVERY subset of the cell. Computation at
the note's own F1 cell (S₁, S₂ the two RAM leaf events, censused 78,125 each on the
390,625-member cell, joint 15,625): take Σc := (S₁ Δ S₂) ∩ cell. Then
Nat.card(Σc ∩ S₁ ∩ S₂)·card(Σc)^1 = 0, while ∏ = 62,500² ≠ 0. So `SibCount T χ` is FALSE
for every model with one genuine branching cell: all `hsib`-premised units become
vacuous-by-inconsistency (the V10/Q1 failure class), the conditionality perimeter "GIVEN
(SIB)" is misrepresented (the Lean (SIB) ≠ the note's (SIB)), and T-G1's `toy_sib …
:= by decide` claim ("provable ON THE TOY") is internally contradicted — over all
subsets Σc the pair law fails on any toy whose two continuation events differ (take
Σc = a mixed pair). FIX SHAPE: pin Σc to the site's cell event (SiteCell/CellAssign
fiber), exactly the display's Σ_c.

**CRIT-2 · T-E4 `JCmulti`: Σc is a free variable with NO tie to the site — the typed
open kernel is unsatisfiable at any multi-side site with positive fresh exponent.**
Quote:
```
∀ (o …) (Σc cell : Set (Box p m)) (k : ℕ) (sides : Fin k → …),
    2 ≤ k → IsMultiSideSite T o cell sides →
    Nat.card ↥(cell ∩ Σc) * p ^ (∑ j, freshExp (sides j)) = Nat.card ↥Σc
```
`IsMultiSideSite T o cell sides` does not mention Σc, so Σc ranges over ALL sets: take
Σc := {x₀} with x₀ ∈ cell — LHS = p^E ≠ 1 = RHS for E ≥ 1. The note's display 7473–7483
prices jvol(c_s │ Σ) at the entrance STATE Σ. The doctrine ("obligations may be open,
but their TYPES must pin their content") is violated in the load-bearing direction: the
type pins FALSE content, and `hjcm`-premised units (T-E7/E8/E10/E11) go vacuous on any
model with a multi-side site. Same fix shape as CRIT-1.

**CRIT-3 · T-E5 `fiber_root_split`: the displayed identity is arithmetically FALSE —
the sibling power is off by one; it fails the note's own F1 integers and the p=2 confirm
census.** Quote:
```
Nat.card ↥{x | Tr.fiberAt T χ x} * (Nat.card ↥(rootCell χ g)) ^ (numTracks htracks - 1)
      * p ^ n
      = p ^ m * ∏ i ∈ trackIdx htracks, Nat.card ↥(rootCell χ g ∩ trackEvent Tr T χ i)
```
The display 7485–7495: μ(fiber) = p^{−n}·∏_i μ(S_{T_i}│Σ₀). Division-free with
card(Σ₀)·p^n = p^m this is card(fiber)·card(Σ₀)^t·p^n = p^m·∏_i card(Σ₀∩S_i) —
exponent **numTracks**, not numTracks − 1. Computation at t = 1 (any single-cluster
tree, F1 included): the blueprint's form forces card(fiber)·p^n = p^m·card(Σ₀∩S₁), i.e.
5^{10} = 5^{28} at F1 (card(fiber) = card(Σ₀∩S₁) = 5⁶ in B22), and 64 = 4096 on the
p=2 confirm census. The exponent bracket is NOT E-phase-flagged (E5's bracket covers
only `RootSplitData` packaging — contrast T-E7, which flags its bookkeeping). Note
T-E8's exponent form is CORRECT (verified both censuses) — the defect is E5-local, but
E5 is a dependency of E8's induction, so the repair must land before E-phase.

**CRIT-4 · T-D5/T-D6 (the W4-3 seam row): `hkey`'s ∀-J-INSIDE-the-iff form cannot
discharge D4R_CYL/ClassFiberWelldef — the claimed implication is false, and the
"jet-independence … supplied INSIDE hkey's ∀-J quantifier" remark is a quantifier
error.** Quote (T-D5):
```
(hkey : ∀ (H …) (hH : H ∈ PrefSet n pol P) (x : Box p m),
      (∀ J : JetSetup H n N m, x ∈ J.SHZ (topLocus p m)) ↔ T.mem (some H) x) :
    D4R_CYL S T
```
`D4R_CYL S T` demands `x ∈ (S.jet i).SHZ ⊤ ↔ T.mem (some (reprOf i)) x` per class. The
⇐ leg follows; the ⇒ leg needs ∀-J from ONE J — exactly same-history jet-independence,
which is (part of) `ClassFiberWelldef`, NOT assumed. Counter-model: H with two jets
J₁ ≠ J₂ of different loci (this is precisely what CFW leaves open — MovesD's own
`Presented` docstring calls it "HC-2 semantic content"), T.mem := the loci intersection
(extendable to a lawful `TreeModel`: define mem/child by snoc-recursion, restrict to
coherent histories for `mem_realizable`): hkey holds, D4R_CYL fails at a Presented with
jet := J₁. T-D6 inherits ("hkey both ways" is used per-J in its sketch). FIX SHAPE: move
the ∀ J OUTSIDE the iff — `∀ H hH x J, x ∈ J.SHZ ⊤ ↔ T.mem (some H) x` — which is also
the honest per-jet RUN-KEY surface HC-2 would actually prove; then both units go
through and CFW's same-H face falls out. As written, the SEAM-DISCHARGE row "W4-3 …
T-D5 + T-D6" does not discharge its recorded contract ("become wave-4 THEOREMS over the
MovesT tree").

**CRIT-5 · T-V5 `tau_disjoint`: the displayed statement is vacuously satisfiable
(`… ∨ True`) — it does not say what 7104–7111 says.** Quote:
```
theorem tau_disjoint … : ¬ (IrrHalts H ∧ NsHalts T (some H) x) ∨ True
```
`Or.inr trivial` closes it. The real duty (mutual exclusivity by domain stratification)
sits only in the unit's prose ("state as `IrrHaltsAsChild T o ν x → ¬ NsHalts T o x`"),
and `IrrHaltsAsChild` is itself undefined in the Defs skeleton. Since T-D3's `halt_iff`
and T-E9's leaf-agreement both consume T-V5's content, an E-phase transcription of the
displayed block would silently hollow the (c2) mutual-exclusivity slot. Per the charge's
own classification ("vacuously satisfiable relative to the note's display") this is
CRITICAL; the repair is already drafted inline — promote the prose form to the statement
field and define `IrrHaltsAsChild` in §2.

---

## GAP findings

**GAP-1 · §5 COUNT line: the seam-entry arithmetic is internally inconsistent.**
"4 (MovesD) + 11 + 2 addenda (MovesS) + 2 (HC-2 walls) + 2 (Q1/Q2) = 19" sums to 21;
the §5 tables contain 21 rows. Either the total or the roster (Q1/Q2 as seam entries vs
queue items) must be corrected — this line is quoted by acceptance records.

**GAP-2 · The site-exponent vocabulary is absent from the Defs skeleton though consumed
by statements and promised by a seam row.** `siteExp`, `windowSites`, `SiteLedger`
(T-E8's STATEMENT — the corpus centerpiece), `freshExp` (T-E4/E6), `IsMultiSideSite`/
`OneSideSite` (T-E4/E6), `AofTr` (T-E11, unflagged), `siteLevel` (T-D4's `hlev`) appear
nowhere in §2; yet seam row S-6 claims the deliverable "Defs §2.5 (sites/siteExp)" —
§2.5 defines only `VTree.sites` and `SiteCell`. The charge's DEFS-SOUNDNESS item
requires these typed (or bracket-flagged as E-phase with content pinned, as C5's
`IsLumpLocus`/`M₀`/`pinCount` correctly are).

**GAP-3 · T-E6: the spectator event E lacks its level-separation premise in the
statement.** As displayed the identity is false for adversarial E (take E := the child
event). The omission is NOT silent (the sketch defers it: "E-phase adds the standard
level-separation premise") — hence gap, not critical — but the hypothesis is
load-bearing and must appear in the statement field.

**GAP-4 · ns-null is delivered ONLY as the finite-level normalized face; the seam re-key
must record the weakening.** The note's (ns-null) display is μ((τ-ns) class │ Σ) = 0
(7210–7231, continuity from above); T-C7 states the truncated-ratio limit (a legitimate,
declared corpus design — "the profinite class never enters"). But T-D12 re-keys
`XRBPackage.ns_null := (T-C7's statement)` into a field MovesS tags "[3t] §T.2, CLOSED"
— i.e. the note's measure statement. The S-2 row should carry an explicit
finite-face rider so wave-5 consumers cannot silently read the profinite claim. Also
T-C7's `(hlumps : …)` is a bare ellipsis hypothesis (content named only in a comment).

**GAP-5 · T-F2's hypothesis set is plausibly insufficient for the stated count
identity.** The bijection classes-with-mark ↔ chains needs, for the surjectivity leg
(chain H of Tr matching P̂ ⟹ its class i has x ∈ S.fiber i): membership
eta-invariance (ETA-LOC/`heta`, or a per-history CYL form) — `hcyl` is quantified at
representatives only and `hwd` gives locus-equality only for PrefSet members, while
H ∈ PrefSet additionally needs `InBox n H`, which `TreeModel.mem_realizable` does not
supply. Add the missing hypothesis fields (they are already named in §0's ledger) or
re-scope the count.

**GAP-6 · The decide gates are not typing-plausible as displayed.** `toy_sib : SibCount
… := by decide`, `toy_gate` (via `fiberAt`), T-S2, T-D2, T-D4's falsifier all place
`decide` on statements quantifying over `Set (Box p m)`, `History p F`, `Node p F` —
types carrying `Polynomial ℤ_[p]` data (not finite, no Decidable instances). The gates
need finite reformulations (enumerated node rosters/decidable surrogates) specified at
blueprint level, since the day-one toy gate is the corpus's declared non-vacuity
mechanism.

**GAP-7 · T-E4's branching corollary is weaker than its display.** The note: "k sides
⟹ ≥ k branches" (7481–7483); the blueprint concludes only `2 ≤ (CA.branchSetOf …).card`
under `2 ≤ k`. State `k ≤ card`.

**GAP-8 · Statement-precision sweep (minor, batched).** (i) T-V3's statement contains
the metavariable `?g_of` (selection-threading deferred — the one E-phase hole inside a
`statement` field's formula); (ii) T-E1's display parses as `⋃ g, (rootCell χ g ∧
Pairwise …)` — the partition conjunction is mis-bracketed; (iii) T-E7's RHS exponent `?`
is deferred (flagged — acceptable, recorded here for the E-phase checklist); (iv) VTree
uses `IsMaximalIn` before its definition (declaration order); (v) T-C2's NPband cutoff
is provable only via the ⊆ half of NP-ID (= T-D7a), which is in-corpus but absent from
T-C2's deps — add the dep or the D8-route note.

---

## Disposition

The corpus architecture is sound and the honesty apparatus (refutation records, Q1/Q2
fences, ownership tags, quantifier honesty) is the best of the wave — but the two
central hypothesis Props (SIB count face, JC-multi) are typed FALSE-for-intended-models
by the same unpinned-conditioning-event slip, one hard unit (E5) displays an identity
refuted by the note's own committed integers, and the W4-3 seam discharge rests on a
quantifier error. All five criticals have mechanical fix shapes (pin Σc to the cell
event; exponent numTracks; ∀-J outside the iff; promote V5's prose form). REJECT
(5 crit / 8 gap); a rev-2 addressing these plus the Defs-vocabulary gaps should
re-audit clean.
