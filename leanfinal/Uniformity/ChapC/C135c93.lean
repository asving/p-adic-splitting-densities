/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C131ag
import Uniformity.ChapC.C131w
import Uniformity.ChapC.C150rb3
import Uniformity.ChapC.C150rb5
import Uniformity.ChapC.C132sg3
import Uniformity.ChapC.C26

/-!
# Uniformity.ChapC.C135c93 — Chapter C, NODE C.93's `C93Census` manifest, transcribed

Unit C93T. The signed node (`leanspec/Leanspec/ChapC.lean`, `section C93Census`, currently
lines 4024–4032 — the file is under concurrent edit by unit A22E, so line numbers are as of
this read and may drift) is a documentation `#check` suite over exactly seven already-signed
names, one per HYP.82 census item (GENTOW-1 through GENTOW-5, plus the two-way split of item
(6)). Per `docs/in-progress/CAPSTONE_SUPPLY_MAP_2026-08-26.md`'s `[CHA 2026-08-28]` section and
`runs/wave-c/verdict_CHA.md`, this census is `GenhnTow1At`'s (I.07's, `n ≥ 8` field) named next
node: `Tow1CensusAt`'s seven conjuncts must instantiate, IN ORDER, exactly these seven leanspec
names, and `docs/in-progress/TOWER_INSTANTIATION_FREEZE_V2_2026-08-24.md` §I.07 records that at
its writing "these names exist only in the leanspec census ... they are not declarations in
`leanfinal`", making `Tow1CensusAt` untypeable. This file transcribes the census.

## Verdict: PARTIAL — 4 of 7 landed (one under a corrected name), 1 half-landed, 2 open

**[A-C.23 UPDATE, 2026-08-28, unit A23E — now 5 of 7]:** item (2)'s BLOCKED row below is
SUPERSEDED. `runs/wave-c/verdict_RB3R.md` proved (codex-confirmed 5/5) that the then-signed
`IsTestKey` conjunct was a statement-level overclaim of the source `EFF.GENTOW1.28`
(unprovable-and-unrefutable under the opaque `k2Coord`; false under the faithful read);
amendment A-C.23 re-signed the conclusion to the source-faithful M4 package (leanspec
`ChapC.lean` NODE C.56, full record there; pre-amendment text archived at commit
`523c8a7b`), and the re-signed statement is now a LANDED THEOREM, byte-identical premises
and conclusion: `Uniformity.Density.Tower.refine_invariants`
(`Uniformity/ChapC/C150rb5.lean`, Lean-core footprint). The `#check` below is live. The
original C93T row text is retained verbatim beneath as the pre-amendment record.

Per name (leanspec node, leanspec `axiom` line as of this read):

* `towerLocus_iff_budget` (C.52, `:2059`) — **LANDED**, `Uniformity.Density.Tower
  .towerLocus_iff_budget` (`C131ag.lean:147`). Byte-verified against the leanspec text
  (modulo `axiom → theorem`): identical binder list and conclusion.
* `refine_invariants` (C.56, `:2163`) — **BLOCKED, unchanged**. `C150rb3.lean`'s own dispatch
  note (unit RB3) already gives the exact gap: `composedKey` (C.43) is landed, clearing the
  ONLY blocker its predecessor note named, but the theorem's real content is a one-step
  Newton–Hensel refinement of `composedKey T` against a `μ₂`-th-power residual — no landed
  lemma transports a witness `f`'s dv2-residual pattern to `composedKey T`'s own residual at
  the refinement slope, nor is there a landed "subtract the digit lift, the key stays
  monic/right-degree/`IsTestKey`" step lemma. `C150rb3.lean` sizes this at ~200–900 new lines
  (the scale of `composedKey_isTestKey` or `shadow_floor`), not a wrap. Re-verified here:
  `rg -n "k2DigitLift.*Monic\|refine_invariants" Uniformity/ChapC/*.lean` outside `C150rb3.lean`
  finds no attempt. Cited, not re-derived.
* `shadow_floor` (C.72, `:3507`) — **LANDED**, `Uniformity.Density.Tower.C131w.shadow_floor`
  (`C131w.lean:851`). Byte-verified: identical binder list and conclusion (the landed copy
  fully qualifies `ResidueField`; no other difference).
* `partial_floor_and_datum` (C.76, `:3604`) — **HALF-LANDED (new this unit)**. The conclusion
  is a conjunction of two clauses: (a) `ℓ * ((F.e₁ * F.f₁) * F.h) < u` (the frame-opening
  floor — genuinely open, needs `hopen`, unexamined per `runs/wave-b/verdict_CCUR.md`'s
  "unattempted" row) and (b) the residual datum
  `(dvResPoly …).coeff 0 ≠ 0 ∧ (dvResPoly …).natDegree = dvSideDeg …`. Clause (b) is EXACTLY
  the already-landed `natDegree_dvResPoly` (C.26, `C26.lean:394`) — same `dvResPoly` term,
  same two conjuncts (swapped order), and `F.Pin H₀` is definitionally `KeyFrame.Pin`'s
  `npHgt … = H₀` equation that `natDegree_dvResPoly`'s `hpin` argument expects (`C14a.lean:214`,
  noted definitionally-equal at `C51.lean:54`) — so it applies with no adaptation. Landed below
  as `partial_floor_and_datum_of_floor`: the exact signed binder list plus one new explicit
  hypothesis `hfloor` supplying clause (a) directly (the `gentow5w_one_shape_of_letter_tie`
  genre: signed type + one named carried hypothesis, distinct name, not the signed name itself
  since clause (a) is not yet unconditional). `hf`/`hsq`/`hkey`/`hopen`/`hdeg`/
  `[IsAdicComplete …]` are UNUSED in the proof (clause (b) needs none of them) — kept verbatim
  for signed-shape parity, matching the `budget_of_mem_towerLocus` (`C131ag.lean`) precedent
  for unused range binders.
* `window_band1` (C.58, `:2232`) — **LANDED**, `Uniformity.Density.Tower.window_band1`
  (`C150rb3.lean:93`). Byte-verified: identical binder list and conclusion.
* `towerLocus_depth3_floor` (C.55, `:2113`, item (6)(β), census comment "DISCHARGED into (1)")
  — **BLOCKED, and the census's own annotation does not hold as stated**. The signed axiom
  carries NEITHER `hh : 1 ≤ F.h` NOR `[Finite (ResidueField O)]` — but EVERY route from
  `towerLocus_iff_budget` (item (1)) to a `dv2Pin`/`dv2SideSet` floor goes through the C.54
  node-floor family (`towerLocus_node_floor` et al.), and every landed instance of that family
  (`towerLocus_dev_strict_floor`, `C131af.lean:364`, which IS `towerLocus_node_floor` up to
  unfolding `dv2Pin := dv2Hgt ∘ dev`, `C11.lean:136`) REQUIRES both `hh` and `[Finite
  (ResidueField O)]`. So "discharged into (1)" cannot literally mean "derived from
  `towerLocus_iff_budget` plus the landed node-floor family" under this signature — whatever
  pin-lattice argument the informal source uses (the docstring's "already signed at the gate
  as the pin-lattice arithmetic") must be independent of the budget-floor value entirely, and
  no landed lemma proves that generic `dv2Supp`/`dv2SideSet` argmin fact. Recorded as a review
  flag, not bridged: this is new mathematics (the CCUR survey's "BLOCKED, same C.54/C.55
  node-floor family, no `C55.lean`" verdict stands, sharpened by the hypothesis-mismatch
  observation above).
* `gentow5_key_certificate` (C.90, `:3945`, item (6)(α)) — **LANDED, under a corrected name**.
  The CURRENT leanspec text is the A-C.21 (2026-08-27, amendment ANORM) re-signed form: `hres`
  reads `Rgr (e' * ((f' - t) * u')) …` (the cleared grade) and `hW : Wle W e' f' u' I r` where
  leanspec's own `Wle`/`GENTOW5W` were edited in place to the cleared semantics
  (`ChapC.lean:3863–3869`, confirmed by direct read). `C107ac14.lean`'s `gentow5_key_certificate`
  — the name that bare-matches the census — is the **PRE-A-C.21 carrier, retained verbatim only
  because the do-not-edit refutation record `C132sg2.lean` states its own theorems against it**
  (`C107gt5.lean`'s docstring: "SUPERSEDED CARRIER... FALSE at the honest μ₃ instance"; machine
  proof `C132sg3.s2Mu3_gentow5w_old_refuted`). The TRUE byte-faithful twin of what leanspec signs
  today is `Uniformity.Density.Tower.C132sg3.gentow5_key_certificate_cleared` (`C132sg3.lean:259`,
  its own docstring: "byte-faithful to the amended leanspec axiom") — checked below under its
  full name, deliberately NOT via `open C107ac14`, so the correction stays visible at the call
  site rather than silently resolving to the stale name.

## Disposition

Per the parent CLAUDE.md statement-fence and the `C106m.lean`/GT5 precedent (a signed manifest
with some names unlanded is reported as a real partial assembly, never silently matched or
padded): this file `#check`s the four names that land under their signed bare name or a
documented-correct qualified name, comments out the three that do not exist as leanfinal
declarations (with the audited reason inline), and lands one new conditional theorem
(`partial_floor_and_datum_of_floor`) for the item that split cleanly into a proved half and an
open half. No `sorry`, no new `axiom`, no `unsafe`, no statement weakening, no edit to
`leanspec/` or any other landed file.

## DEPENDS

C131ag (`towerLocus_iff_budget`) · C131w (`shadow_floor`) · C150rb3 (`window_band1`) · C132sg3
(`gentow5_key_certificate_cleared`) · C26 (`natDegree_dvResPoly`) — all landed, imported.

## Status

Sorry-free. The four `#check`s elaborate declarations whose own axiom footprints are Lean core
only (printed in their home files); nothing here adds to that. The one new theorem
(`partial_floor_and_datum_of_floor`) is proved directly from `natDegree_dvResPoly`; its own
footprint is printed below.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower

open Uniformity.Density.Tower.C131w

/-! ## The `C93Census` manifest, transcribed -/

section C93Census

-- item (1), C.52 — LANDED (`C131ag.lean`, `Uniformity.Density.Tower`)
#check @towerLocus_iff_budget

-- item (2), C.56 — LANDED [A-C.23 UPDATE, 2026-08-28, unit A23E; supersedes the C93T
-- BLOCKED row — see the docstring's dated update block]: the A-C.23 re-signed statement
-- (M4-package conclusion) is the theorem `Uniformity.Density.Tower.refine_invariants`
-- (`C150rb5.lean`, imported above), byte-identical to leanspec's re-signed NODE C.56(i).
#check @refine_invariants

-- item (3), C.72 — LANDED (`C131w.lean`, `Uniformity.Density.Tower.C131w`, opened above)
#check @shadow_floor

-- item (4), C.76 — HALF-LANDED: clause (a) (the frame-opening floor) is open (see
-- docstring); clause (b) (the residual datum) is landed below as
-- `partial_floor_and_datum_of_floor`'s conclusion, unconditionally, via C.26's
-- `natDegree_dvResPoly`. The bare signed name `partial_floor_and_datum` does not exist
-- (clause (a) is still a carried hypothesis, not yet a theorem).
-- #check @partial_floor_and_datum

-- item (5), C.58 — LANDED (`C150rb3.lean`, `Uniformity.Density.Tower`)
#check @window_band1

-- item (6)(β), C.55 — BLOCKED: the census's "DISCHARGED into (1)" note does not hold
-- under this signature (no `hh`/`[Finite (ResidueField O)]`; see docstring). No leanfinal
-- declaration; needs the still-unlanded C.54 node-floor family or a genuinely new
-- hypothesis-independent lattice argument.
-- #check @towerLocus_depth3_floor

-- item (6)(α), C.90 — LANDED under the CORRECTED name: the bare `gentow5_key_certificate`
-- (`C107ac14.lean`) is the SUPERSEDED pre-A-C.21 carrier (retained only for the
-- do-not-edit refutation record `C132sg2.lean`); the current signed axiom's byte-faithful
-- twin is `C132sg3.gentow5_key_certificate_cleared` (see docstring). Checked fully
-- qualified, deliberately not via `open C107ac14`.
#check @Uniformity.Density.Tower.C132sg3.gentow5_key_certificate_cleared

end C93Census

/-! ## Item (4)'s open half, as an explicit carried hypothesis

`partial_floor_and_datum`'s clause (a) — the frame-opening floor `ℓ * ((F.e₁*F.f₁)*F.h) < u`
— is not derivable from any landed lemma (unattempted per `verdict_CCUR.md`, and out of the
transcription scope of this unit). Clause (b) is landed unconditionally: `natDegree_dvResPoly`
(`C26.lean:394`) IS exactly clause (b)'s two conjuncts (in swapped order) for the identical
`dvResPoly` term, needing none of `hf`/`hsq`/`hkey`/`hopen`/`hdeg`/`[IsAdicComplete …]`. -/

set_option linter.unusedVariables false in
/-- **NODE C.76, `partial_floor_and_datum`, conditional form.** The exact signed binder list
plus one new explicit hypothesis `hfloor` supplying clause (a) directly; the conclusion is the
signed statement byte-unchanged. `hfloor` is exactly the open frame-opening floor — when a
future unit derives it from `hopen` (and `hf`/`hsq`/`hkey`/`[IsAdicComplete …]`), this becomes
one application away from the unconditional `partial_floor_and_datum`. -/
theorem partial_floor_and_datum_of_floor {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {π : O} {F : KeyFrame O π} {H₀ : ℕ} (hpin : F.Pin H₀)
    (hπ : Irreducible π)
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    {f : Polynomial O} (hf : f.Monic) (hsq : Squarefree f) (hkey : ¬ F.key ∣ f)
    (hopen : (((f.natDegree / (F.e₁ * F.f₁)) * ((F.e₁ * F.f₁) * F.h) : ℕ) : ℕ∞)
      < dvHgt F f 0)
    {u ℓ : ℕ} (hℓ : 0 < ℓ) (hcop : Nat.Coprime u ℓ)
    (hne : (dvSideSet F f u ℓ).Nonempty) (hdeg : 0 < dvSideDeg F f u ℓ hne)
    (hfloor : ℓ * ((F.e₁ * F.f₁) * F.h) < u) :
    ℓ * ((F.e₁ * F.f₁) * F.h) < u ∧
    ∀ (M₀ : ℕ) (hp : dvHgt F f (dvSideMin F f u ℓ hne) = (M₀ : ℕ∞)),
      (dvResPoly F H₀ hpin f u ℓ hne M₀ hp).coeff 0 ≠ 0 ∧
      (dvResPoly F H₀ hpin f u ℓ hne M₀ hp).natDegree = dvSideDeg F f u ℓ hne :=
  ⟨hfloor, fun M₀ hp =>
    ⟨(natDegree_dvResPoly F hπ H₀ hpin hℓ hcop hne hp).2,
     (natDegree_dvResPoly F hπ H₀ hpin hℓ hcop hne hp).1⟩⟩

end Uniformity.Density.Tower

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.partial_floor_and_datum_of_floor

end AxCheck
