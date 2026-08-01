/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.MovesU.BridgeD7_canonical
import LeanUrat.MovesU.BridgeD4_vtLaws

/-!
# Scaffold/HDischarge/H9/NsfKeyProp — the (H9) = (NSF) compiled conformance units
[HDISCHARGE_H9 Wave 1]

Transcription of `lean/blueprints/HDISCHARGE_H9.md` §6 (all five statements and
proof bodies VERBATIM, compile-probed against built HEAD at the blueprint
session). (H9) = (NSF) is the ns-routing interface row (ROOT §3.1, NEW at
REVISION 10, r11). Provenance of record: the (NSF-KEY) member is RETIRED by the
executed Unit C per (NSF-KEY-RET) — ledger `BRIDGE_ADJUDICATIONS_2026-07-30.md`,
entry "H9 LEAD ADJUDICATION"; the units here are CONFORMANCE/WITNESS theorems
(the blueprint's ground (b) CORROBORATION and the §2.2 compiled conformance
faces), carrying NO retirement weight of their own.

Units (file order = blueprint wave order):
* `nsFree_of_maximal_irrHalts` (H9-U2) — §4B claim (i)'s Lean face at a
  `fiberAt` witness: the (q-3) leaf guard forces mark-freeness.
* `nsFree_iff_maximal_irrHalts` (H9-U3) — at `fiberAt` witnesses the guard's
  MARK COMPONENT in the two vocabularies coincides (NOT billed as the full
  (q-3) package).
* `nsLeaf_nsHalts_of_fiberAt` (H9-U4) — marks RECORD NsHalts events at the
  built carrier (the marks-vocabulary premise's compiled conformance face).
* `nsfKey_prop` (H9-U1) — THE compiled (NSF-KEY) proposition (§1.1 verbatim in
  as-built vocabulary): label ⟹ carried ns-free fibering tree within threshold.
* `bridgeVt_maximal_irrHalts` (H9-U5) — every CARRIED tree satisfies the
  CHAIN-LEAF component of the (q-3) guard (all maximal chains IrrHalts), via
  the carrier's own `RealizedSelf` witness. NOT billed as the full guard
  package: complete/finite/canonical are `VTree` structural fields,
  realizability is the carrier's `RealizedSelf` clause, and (τ-hen) content is
  the `henV` payload (`hhen`'s (1,g)-shape), not a chain.

## NON-claims (blueprint §5.2, verbatim)

No compiled element of `bridgeTree n p σ` exists at HEAD (post-Unit-C the
former paper-witness V₀ is expelled BY DESIGN; realization of a positive
witness is blocked on the same seam as always: `canPolicy` designer-sorried;
nearest assets = the G1_toyGate toy trees + the M18/IFK-U6 probes).
Consequence displayed honestly: H9-U1/U5 and `count_tie` at the guarded
instance are implications over the carrier and would be vacuously satisfiable
at an empty carrier — their VALUE as conformance witnesses is real (they pin
the wiring's shape) but they are NOT existence claims. Non-vacuity belongs to
the realization/instantiation seam ([3t]/TreePin), tracked there. This module
declares NO element of `bridgeTree` (blueprint gate g-5).
-/

set_option linter.style.longLine false
set_option maxHeartbeats 1000000

namespace LeanUrat.Scaffold.HDischarge.H9

open LeanUrat.MovesU

/-- H9-U2: §4B claim (i)'s Lean face at a `fiberAt` witness — the (q-3) leaf
    guard (all maximal chains IrrHalts) forces mark-freeness. Consumes
    `hns_leaf` (marks only at maximal chains) + `fiberAt` clause (2)'s
    dichotomy. -/
theorem nsFree_of_maximal_irrHalts {p : ℕ} [Fact p.Prime] {F : Type*}
    [Field F] [Finite F] {n N m : ℕ} {pol : MovesD.CanonPolicy p F}
    (Tr : MovesT.VTree p F) (T : MovesD.TreeModel p F n N m pol)
    (χ : Fin n → Fin m) (x : MovesD.Box p m)
    (hfib : Tr.fiberAt T χ x)
    (hirr : ∀ H ∈ Tr.chains, MovesT.IsMaximalIn Tr.chains H → MovesT.IrrHalts H) :
    MovesT.NsFree Tr := by
  intro H hH hns
  obtain ⟨hmem, hmax⟩ := Tr.hns_leaf H hns
  rcases hfib.2.1 H hmem hmax with h1 | h2
  · exact h1.2.1 hns
  · exact h2.2.1 (hirr H hmem hmax)

/-- H9-U3 [billing per HDISCHARGE_H9 Codex review finding 6]: at `fiberAt`
    witnesses, the guard's MARK COMPONENT in the two vocabularies coincides —
    `NsFree`/`hdet` (mark vocabulary) ⟺ all-maximal-chains-IrrHalts (the
    chain-leaf component of (q-3)'s vocabulary). NOT billed as the full (q-3)
    package (complete/finite/canonical = `VTree` structural fields;
    realizability = `RealizedSelf`; (τ-hen) content = the `henV` payload).
    Consumed by the (K1-CANON) warrant note at C1-3, under exactly this
    billing. -/
theorem nsFree_iff_maximal_irrHalts {p : ℕ} [Fact p.Prime] {F : Type*}
    [Field F] [Finite F] {n N m : ℕ} {pol : MovesD.CanonPolicy p F}
    (Tr : MovesT.VTree p F) (T : MovesD.TreeModel p F n N m pol)
    (χ : Fin n → Fin m) (x : MovesD.Box p m)
    (hfib : Tr.fiberAt T χ x) :
    MovesT.NsFree Tr ↔
      ∀ H ∈ Tr.chains, MovesT.IsMaximalIn Tr.chains H → MovesT.IrrHalts H := by
  constructor
  · intro hnf H hmem hmax
    rcases hfib.2.1 H hmem hmax with h1 | h2
    · exact h1.1
    · exact absurd h2.2.2.1 (hnf H hmem)
  · exact nsFree_of_maximal_irrHalts Tr T χ x hfib

/-- H9-U4: marks RECORD NsHalts events at the built carrier — the
    marks-vocabulary premise's compiled conformance face (blueprint §4).
    (`History` lives in `MovesC`.) -/
theorem nsLeaf_nsHalts_of_fiberAt {p : ℕ} [Fact p.Prime] {F : Type*}
    [Field F] [Finite F] {n N m : ℕ} {pol : MovesD.CanonPolicy p F}
    (Tr : MovesT.VTree p F) (T : MovesD.TreeModel p F n N m pol)
    (χ : Fin n → Fin m) (x : MovesD.Box p m)
    (hfib : Tr.fiberAt T χ x)
    (H : MovesC.History p F) (hns : Tr.nsLeaf H) :
    MovesT.NsHalts T (some H) x := by
  obtain ⟨hmem, hmax⟩ := Tr.hns_leaf H hns
  rcases hfib.2.1 H hmem hmax with h1 | h2
  · exact absurd hns h1.2.1
  · exact h2.1

/-- H9-U1 — THE compiled (NSF-KEY) proposition (blueprint §1.1 verbatim in
    as-built vocabulary): if the wired classifier labels `f`
    (`bridgeCanonical … N f = some σ`) then `f` fibers a carried tree of the
    σ-carrier satisfying `MovesT.NsFree` at threshold ≤ N. The (NSF-KEY)
    adjudication's ground (b) — a WITNESS of the retired state, carrying no
    retirement weight of its own. At the generic `boxeq` binder (the pin
    theorem's own generality); the wired instance specializes it. -/
theorem nsfKey_prop (n p : ℕ) [Fact p.Prime]
    (boxeq : ∀ N : ℕ, Box p n N ≃ MovesD.Box p (n * N))
    (N : ℕ) (f : Box p n N) (σ : SplittingType n)
    (h : bridgeCanonical n p boxeq N f = some σ) :
    ∃ (hN : 0 < N) (T : bridgeTree n p σ),
      bridgeThr n p σ T ≤ N ∧
      (bridgeVt n p σ T).fiberAt (bridgeTm p n N) (bridgeChart n N hN)
        (boxeq N f) ∧
      MovesT.NsFree (bridgeVt n p σ T) := by
  rcases Nat.eq_zero_or_pos N with hN0 | hN
  · subst hN0
    rw [bridgeCanonical_level0] at h
    exact absurd h (by simp)
  · obtain ⟨T, hthr, hfib⟩ := (bridgeCanonical_pin n p boxeq N hN f σ).mp h
    exact ⟨hN, T, hthr, hfib, bridgeVt_nsFree n p σ T⟩

/-- H9-U5 [billing per HDISCHARGE_H9 Codex review finding 6]: every CARRIED
    tree satisfies the CHAIN-LEAF component of the (q-3) guard (all maximal
    chains IrrHalts), via the carrier's own `RealizedSelf` witness — the
    as-built input to the (K1-CANON) warrant note's C1-3. NOT billed as the
    full guard package: complete/finite/canonical are `VTree` structural
    fields, realizability is the carrier's `RealizedSelf` clause, and (τ-hen)
    content is the `henV` payload (`hhen`'s (1,g)-shape), not a chain. -/
theorem bridgeVt_maximal_irrHalts (n p : ℕ) [Fact p.Prime]
    (σ : SplittingType n) (T : bridgeTree n p σ) :
    ∀ H ∈ (bridgeVt n p σ T).chains,
      MovesT.IsMaximalIn (bridgeVt n p σ T).chains H → MovesT.IrrHalts H := by
  obtain ⟨x, hfib⟩ := bridgeVt_realizedSelf n p σ T
  exact (nsFree_iff_maximal_irrHalts _ _ _ _ hfib).mp (bridgeVt_nsFree n p σ T)

end LeanUrat.Scaffold.HDischarge.H9
