/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Scaffold.DictIII.Hyps
import LeanUrat.Scaffold.DictIII.GMNReader
import LeanUrat.Scaffold.DictIII.Locality
import LeanUrat.Scaffold.DictIII.Window
import LeanUrat.HC2.Defs
import LeanUrat.MovesT.V9_irrSat
import LeanUrat.MovesT.V3_accKeyDeg

/-!
# Scaffold/DictIII/CU1 — Theorem CU-1 (BP_III §1.8)

E-phase target file for units III-U1..U8 (module §1.8, Theorem CU-1 +
Corollary CU-1-LVL).  Source of record: CU1 §2 Thm CU-1.

Status at hand-off (units III-U5 and III-U7, 2026-08-01): BLOCKED — see the
records below.  No declaration is landed; the verbatim blueprint statement is
preserved in the commented block (transcribing it weakened, or with invented
placeholder carriers for other units' owned definitions, would be a statement
change).

Status at hand-off (unit III-U2, 2026-08-01): LANDED — `InteriorChain` (the
§1.8 signature, verbatim) with fieldwise access lemmas, + the CU-1 base case
k = 0 (`cu1_base_rootTrack`, `cu1_base_reductionFactor`), proved, Lean-core
footprint.  Source of record: `CU1_phaseB_verifybrief_rev5.md` §2 (clause
(i)'s k = 0 reading; V27 finding 3a — REALIZED is NOT asserted at the empty
history) and §3 "Base k = 0".  Dep: unit III-C9 (`ConsF`,
`DictIII/GMNReader.lean`).  This lands the FIRST of the four missing
identifiers recorded in the III-U5 block below; `CU1Pins`/`machineProj`/
`StateBinding` remain open there.

Rendering note for III-U2 (division-lead review; the III-C3 precedent in
Carriers.lean): BP_III §1.8 displays for this unit only the def SIGNATURE
`def InteriorChain (H : EHist p F) : Prop` with its docstring ("all nodes
continuing, non-complete (μ_i ≥ 2), a₀ ≥ 2"), and NO Lean statement for the
base case (unit-table row 805 describes it in words).  The def BODY and the
two base-case theorems are therefore this unit's renderings — flagged, not
fenced.  Body sources: "continuing" = `sel ≠ none` (the (C1) docstring's
`sel = none` ⇔ terminal); "non-complete" = μ ≥ 2 at the selected pair (CU1
rev-5 §2: "EVERY node non-complete: μ_i ≥ 2 for all 1 ≤ i ≤ k"); `2 ≤ H.a0`
verbatim from the docstring.  ord_{ψ̂₀}(f̄) is carried at the §1.2
ι-interface as the (c0) read — `ConsF`'s first conjunct `R.rootOrd = H.a0`
with `R.rootOrd_spec : R.rootOrd = D.rootOrder`; the scaffold constructs no
GMN objects (§1.2 header), so the base clause is stated against the reader.

Status at hand-off (unit III-A5, 2026-08-01): BLOCKED — record at the end of
the file.  The `MovesT` imports pin that unit's quarry
(`V9_irrSat`/`V3_accKeyDeg`, landed and green — this file's compile gate
certifies they resolve at HEAD); the unit's re-keyed statement has no
blueprint display, and its statement site (coherent `machineProj`, unit
III-U1) is unlanded.

Status at hand-off (unit III-U6, 2026-08-01): BLOCKED — record below (between
the III-U5 and III-U7 blocks; the same elision class as III-U7, plus a
statement defect inherited from the III-T14 seam).  One support lemma IS
landed and PROVED (`nstarMaj_readCeil_le`, the (N\*-MAJ) consumption leg over
the landed III-H4 row), Lean-core footprint — the `Locality`/`Window` imports
pin its `readCeil` cite and the III-T14 census.
-/

namespace LeanUrat.Scaffold.DictIII

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-! ## Unit III-U2, def half — the interior scoping (BP_III §1.8, signature verbatim) -/

/-- Interior scoping: all nodes continuing, non-complete (μ_i ≥ 2), a₀ ≥ 2. -/
def InteriorChain (H : EHist p F) : Prop :=
  2 ≤ H.a0 ∧
    ∀ (i : ℕ) ν, H.nodes[i]? = some ν →
      ν.sel ≠ none ∧ ∀ gμ ∈ ν.sel, 2 ≤ gμ.2

/-- Fieldwise access, a₀-clause: an interior chain has a₀ ≥ 2 (CU1 rev-5 §2's
    standing hypothesis; at nonempty chains this is also W3's second leg). -/
theorem InteriorChain.a0_ge_two {H : EHist p F} (h : InteriorChain H) :
    2 ≤ H.a0 :=
  h.1

/-- Fieldwise access, continuing-clause: every node of an interior chain is
    continuing (`sel ≠ none`; terminal records are CU-2t's seam, excluded by
    the scoping — CU1 rev-5 §2 scope note (2)). -/
theorem InteriorChain.sel_ne_none {H : EHist p F} (h : InteriorChain H)
    {i : ℕ} {ν : ENodeData} (hν : H.nodes[i]? = some ν) :
    ν.sel ≠ none :=
  (h.2 i ν hν).1

/-- Fieldwise access, non-complete-clause: every selected multiplicity of an
    interior chain has μ ≥ 2 (complete last nodes, μ_k = 1, are the leaf seam
    routed by CU1 rev-5 §4's split — excluded here). -/
theorem InteriorChain.mu_ge_two {H : EHist p F} (h : InteriorChain H)
    {i : ℕ} {ν : ENodeData} (hν : H.nodes[i]? = some ν)
    {g μ : ℕ} (hsel : ν.sel = some (g, μ)) :
    2 ≤ μ :=
  (h.2 i ν hν).2 (g, μ) hsel

/-- Fieldwise access, selected-pair form of the continuing-clause: every node
    of an interior chain carries a selected pair, with μ ≥ 2 (the ∃-form the
    induction step consumes). -/
theorem InteriorChain.exists_sel {H : EHist p F} (h : InteriorChain H)
    {i : ℕ} {ν : ENodeData} (hν : H.nodes[i]? = some ν) :
    ∃ g μ, ν.sel = some (g, μ) ∧ 2 ≤ μ := by
  cases hsel : ν.sel with
  | none => exact absurd hsel (h.sel_ne_none hν)
  | some gμ => exact ⟨gμ.1, gμ.2, rfl, h.mu_ge_two hν hsel⟩

/-! ## Unit III-U2, base half — CU-1 base case k = 0 (CU1 rev-5 §2/§3 "Base k = 0")

The brief's clause (i) at k = 0 reads (V27 finding 3a — REALIZED is not
defined at the empty history, so NO REALIZED claim is made): "the track root
state o_𝐇 of ψ̂₀ exists on f, i.e. ord_{ψ̂₀}(f̄) = a₀ ≥ 2, with reduction
factor ψ̂₀^{a₀}".  At the ι-interface the displayed equation is the (c0)
read.  Consumed: (c0) + the interior scoping's a₀ ≥ 2 — the brief's
"[Consumed: (c0); …]" list restricted to this unit's clause; ROOT-M is NOT
yet needed here, per the same list. -/

/-- CU-1 base case k = 0, clause (i) (CU1 rev-5 §3 "Base k = 0"): the root
    track of ψ̂₀ exists on f — the (c0)-read root order (ord_{ψ̂₀}(f̄) read
    through the ι-interface) equals a₀ and is ≥ 2.  No `H.nodes = []`
    hypothesis is consumed: (c0) is `ConsF`'s level-free first conjunct, so
    the k = 0 instance is the literal statement, and the root clause stays
    available along the whole chain (the assembly III-U5 uses it at its
    `List.rec` base). -/
theorem cu1_base_rootTrack {f : Polynomial ℤ_[p]} {H : EHist p F}
    {D : GMNData f (Theta H)} {R : GMNReader f (Theta H) D}
    (hint : InteriorChain H) (hcons : ConsF f H D R) :
    R.rootOrd = H.a0 ∧ D.rootOrder = H.a0 ∧ 2 ≤ D.rootOrder := by
  have h1 : R.rootOrd = H.a0 := hcons.1
  have h2 : D.rootOrder = H.a0 := R.rootOrd_spec.symm.trans h1
  exact ⟨h1, h2, hint.a0_ge_two.trans_eq h2.symm⟩

/-- CU-1 base case k = 0, the reduction factor (CU1 rev-5 §3 "Base k = 0":
    "f̄ has the repeated irreducible factor ψ̂₀^{a₀} (a₀ ≥ 2), so the track
    of ψ̂₀ exists with root state o_𝐇, reduction factor ψ̂₀^{a₀}"): at the
    ι-interface the reduction factor's exponent is the (c0)-read root order —
    ψ̂₀^{ord_{ψ̂₀}(f̄)} = ψ̂₀^{a₀}, with exponent ≥ 2 (repeated, so the track
    exists).  The polynomial lives over the carrier's root level `H.base`;
    monicity and irreducibility of ψ̂₀ itself are `H.hpsi0`. -/
theorem cu1_base_reductionFactor {f : Polynomial ℤ_[p]} {H : EHist p F}
    {D : GMNData f (Theta H)} {R : GMNReader f (Theta H) D}
    (hint : InteriorChain H) (hcons : ConsF f H D R) :
    H.psi0 ^ D.rootOrder = H.psi0 ^ H.a0 ∧ 2 ≤ D.rootOrder := by
  obtain ⟨-, h2, h3⟩ := cu1_base_rootTrack hint hcons
  exact ⟨by rw [h2], h3⟩

/-! ## Unit III-U5 — `cu1` (BP_III §1.8): BLOCKED on missing dependencies

The verbatim blueprint statement is preserved in the commented block below; it
is NOT weakened or partially landed.  Status at hand-off (2026-08-01):

* -- BLOCKED(III-U5): four identifiers in the verbatim statement do not exist
  in the corpus, so the statement cannot compile as written.  Transcribed
  VERBATIM (only this file's standing `variable {p} [Fact p.Prime] {F} [Field F]
  [Finite F]` line supplying the ambient binders, as in every DictIII module),
  `lake env lean` reports, per identifier:
    - `InteriorChain` (line `(hint : InteriorChain H)`):
        "The identifier `InteriorChain` is unknown" — unit III-U2, not landed
        anywhere in `LeanUrat/` (grep over the corpus: zero declarations);
    - `CU1Pins` (line `(hpins : CU1Pins p F)`):
        "The identifier `CU1Pins` is unknown" — unit III-H3 is itself BLOCKED
        (Hyps.lean §III-H3: statement defect in row `frEQ`, `HC1.ReadFrame`
        arity/sort mismatch, fenced above unit authority); the structure exists
        only inside Hyps.lean's commented block, so it is not an available
        declaration;
    - `machineProj` (conclusion clause `(machineProj M hM).1 = H`):
        "The identifier `machineProj` is unknown" — unit III-U1, not landed;
    - `StateBinding` (conclusion clause `StateBinding M H hlift`):
        "The identifier `StateBinding` is unknown" — unit III-U3a, not landed.
  (All other vocabulary resolves: `EHist`/`EWF`/`Theta` from Carriers, `GMNData`/
  `GMNReader`/`ConsF` from GMNReader, `GRB`/`FRESH`/`LiftFn`/`OL1`/`OL6` from
  Hyps, `MovesC.History`/`MovesC.HistoryCoherent`/`MovesJ.ReadsOf` from the
  corpus.)
* Beyond statement elaboration, the assembly proof this unit owns ("List.rec on
  nodes; U2 base, U3b/c + U4 step") consumes the base and step lemmas of units
  III-U2, III-U3b, III-U3c, III-U4 — none landed.  Wave-4 order of record:
  III-U1, III-U2, III-U3a..c, III-U4 (and the III-H3 `frEQ` blueprint repair)
  must land before III-U5 can be attempted.

```
/-- THEOREM CU-1 (N-free realization + state binding), over the displayed rows:
    order-≤1 instances of GD-2/GD-3(min)/GD-6 outright; orders ≥ 2 via hGRB; plus
    hFRESH, the pins, OL6. Conclusion (i): a machine history M with
    machineProj M = 𝐇 and ReadsOf f M; (ii): the state frame after M equals the
    [F.0] stage data over Theta 𝐇 (key = Lift, width = μ_k). -/
theorem cu1 {n : ℕ} {f : Polynomial ℤ_[p]} (H : EHist p F) (hwf : EWF H)
    (hint : InteriorChain H)
    (D : GMNData f (Theta H)) (R : GMNReader f (Theta H) D)
    (hcons : ConsF f H D R)
    (hGRB : GRB p F) (hFRESH : FRESH p F) (hpins : CU1Pins p F)
    (hOL6 : OL6 f (Theta H) D R)
    (hlift : LiftFn p F) (hOL1 : OL1 (Theta H) hlift) :
    ∃ M : MovesC.History p F,
      ∃ hM : MovesC.HistoryCoherent M,
        (machineProj M hM).1 = H ∧
        MovesJ.ReadsOf p F n f M ∧ StateBinding M H hlift
```
-/

/-! ## Unit III-U7 — `cu1_spanTotal` (BP_III §1.8): BLOCKED — no verbatim
statement exists, and the construction it quantifies over is unlanded

STATEMENT-PROVENANCE RECORD (same discipline as the Window.lean §1.7 records):

* -- BLOCKED(III-U7): BP_III §1.8 displays this unit's theorem ONLY as the
  ellipsis
  ```
  /-- Interior adequacy (per-site SPAN totality; the ADEQ interior half). -/
  theorem cu1_spanTotal …
  ```
  (blueprint lines 585–586) — there is NO verbatim blueprint statement to
  transcribe (REV2 finding 1 left §1.8's `cu1_lvl` and `cu1_spanTotal`
  displays elided; the same finding class as Window.lean's §1.7 records).
  Unit row (line 812): proof sketch = "per-site totality from the SAME
  harvest construction", deps = III-U3c, src = CU1 §4.
* Unlike III-T11a (Window.lean), NO displayed constraint pins this statement
  byte-for-byte to landed corpus declarations: the object whose per-site
  totality the unit asserts is unit III-U3c's harvest construction
  ("harvest realizes ν̂_{i+1}, creation-first"), and III-U3c is UNLANDED
  (grep over `LeanUrat/`: zero declarations; this file held no declaration
  at hand-off — unit III-U5's record above lists the missing Wave-4 chain
  III-U1/U2/U3a/H3 as well).  Elaborating a fresh statement from the CU1 §4
  prose would invent this unit's quantified object AND duplicate III-U3c's
  owned construction — a statement change plus a seam conflict, both fenced.
* Mathematical content of record, for the eventual elaboration (source: CU1
  rev-5 brief `lean/notes/openmath/CU1_phaseB_verifybrief_rev5.md` §4,
  Corollary CU-1-ADEQ, per-step rescope of V27 finding 6a): for a well-formed
  all-continuing Cons_f prefix 𝐇_{≤i} (a₀ ≥ 2, every node non-complete) and
  EVERY interior GMN child (S, ψ) of ι(Θ(𝐇_{≤i})) — interior meaning
  μ := ord_ψ(R_λ(f)) ≥ 2 — the constructed node ν(S, ψ) with the displayed
  fields
      (e, h) := lowest-terms pair of −λ;  ℓ := d(S);
      (s, u) := initial point of S;  sel := (deg ψ, μ);
      inc := 1 iff e·deg ψ ≥ 2;  dressing ψ̂ := ψ
  extends 𝐇_{≤i} to a well-formed all-continuing non-complete Cons_f chain
  that Theorem CU-1 realizes.  "Per-site SPAN totality" = the ∀-(S, ψ)
  quantifier over interior children at the site (the ADEQ interior half; the
  μ = 1 leaf half is O5triple's, routed OUTSIDE CU-1 by the §4 split — no
  leaf clause belongs in this unit's statement).
* Unblock order: III-U3c's construction lands first (it fixes the node-builder
  vocabulary this statement binds); then this unit states totality over it and
  fires `cu1` (III-U5, itself BLOCKED above) for the realization clause.
  Statement elaboration requires division-lead ratification (nothing to be
  verbatim to). -/

/-! ## Unit III-A5 — the `(accE, accF)` tie + saturation ⇔ ω = 1 at coherent
`machineProj` (BP_III §2 row 768, MOVED TO WAVE 4 after III-U1): BLOCKED

Charge (BP_III §2, line 768): "`(accE, accF)` tie + saturation ⇔ ω = 1 at
coherent `machineProj` | corpus telescope `V9_irrSat` + `V3_accKeyDeg`;
quarry only, not a verbatim alias | deps III-U1, corpus MovesT | EASY |
O2a §5 (B); ROOT Step 7".  Probed 2026-08-01 (BP_III.md at HEAD, 1011
lines; Lean 4.31, this pin).  No declaration is landed, on two independent
grounds, per the BLOCKED(III-A4/A7/A8) precedent (`O2aOrder1.lean`) and the
III-U5/III-U7 records above:

1. NO Lean statement exists in the blueprint for this unit, so there is
   nothing to transcribe, and statement invention is forbidden.  Grep audit
   over BP_III.md: `III-A5`/`A5` hit the §2 Wave-2 prose row (line 768),
   the §3.2 corpus-reuse row (line 871: "the (accE,accF) tie is largely
   PROVED — re-key, don't re-prove"), the §4 wave-plan prose (lines 921,
   928: "U1→A5"), and the REVISION-2 rows 12 and 26 (lines 993, 1007) —
   all prose, none a signature.  The §1.8 block for THIS module (lines
   553–587) displays `machineProj`, `InteriorChain`, `cu1`, `cu1_lvl`,
   `cu1_spanTotal` only — no III-A5 display; no other §1 block mentions
   the unit.  REVISION-2 finding 26 pins the unit as "quarry-only, not a
   verbatim alias", so re-exporting the corpus theorems verbatim is ALSO
   out of scope by the blueprint's own ruling: the unit's content is a
   RE-KEY of the quarry at `machineProj`, and no display of the re-keyed
   signature exists (the III-U7 record's failure class, not III-T11a's).

2. The sole Lean dependency, III-U1's
   `machineProj (M : MovesC.History p F) (hM : MovesC.HistoryCoherent M) :
   {H : EHist p F // EWF H}` (§1.8 display), is UNLANDED at HEAD: grep over
   `LeanUrat/` finds zero declarations (the name occurs only in BLOCKED
   records — the III-U5 block above, which lists `machineProj` among its
   four missing identifiers and which the III-U2 landing note above leaves
   open, and `O2aOrder1.lean`'s BLOCKED(III-A8) ground 3).  The unit
   charge's scheduling premise ("runs immediately after III-U1") is false
   at probe time, and the statement site "at coherent `machineProj`" has
   no carrier: without III-U1 there is no map from the quarry's carrier to
   the Θ-side chain carrier, and dressing one up here would be a NEW
   definition owned by another unit (the III-U5 record's fence, verbatim).

Quarry status (pinned by this file's `MovesT` imports, so the compile gate
certifies it resolves at HEAD): the corpus telescope IS landed and green,
on the `MovesC.History p F` carrier —
  * `MovesT.acc_childWidth` (`MovesT/V9_irrSat.lean`): under
    `HistLawful p n H` and `H.nodes ≠ []`,
    `accE H * accF H = (H.nodes.getLast?).elim 1 fun ν => ν.childWidth`
    — the `(accE, accF)` tie (Dwidth-chain telescope);
  * `MovesT.irr_iff_mu_one` (same file): under `HistLawful p n H` at
    `H.nodes.getLast? = some ν`, `IrrHalts H ↔ ν.μ = 1` — the saturation
    ⇔ ω = 1 leg (the row's ω is the note's μ; MOVES 7078–7080
    parenthetical, per that file's header);
  * `MovesT.accEF_keyDeg` (`MovesT/V3_accKeyDeg.lean`): the E·F =
    key-degree species leg.
The re-key target carrier is `EHist p F` (`H.nodes : List ENodeData`),
while `MovesT.accE`/`accF` have domain `MovesC.History p F` — the exact
carrier seam already on record at BLOCKED(III-A7) ground (a)
(`O2aOrder1.lean`: application type mismatch, `H.nodes : List ENodeData`
where `MovesC.History ?p ?F` is expected; no coercion exists).
`machineProj` is the blueprint's sanctioned bridge across that seam —
REVISION-2 finding 12 moved this unit after III-U1 for exactly this
reason.

Cure (in order): land III-U1 (`machineProj`, §1.8 display) → architect
displays the III-A5 re-keyed signature in a §1 block for this module (the
tie + saturation ⇔ ω = 1 stated through `(machineProj M hM).1`, consuming
the quarry rows above) → III-A5 re-runs as a re-key, NOT a re-proof
(BP §3.2 row 871). -/

end LeanUrat.Scaffold.DictIII

-- Footprint audit (unit III-U2 gate): expect Lean core only.
#print axioms LeanUrat.Scaffold.DictIII.cu1_base_rootTrack
#print axioms LeanUrat.Scaffold.DictIII.cu1_base_reductionFactor
