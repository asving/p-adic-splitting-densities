/-
Unit U17b.galois_normalize  (HC-2 campaign, E-phase — blueprint §5 Layer C)
moves_ref: MovesD `EtaGalEq`/`canonRoot` defs; §0.6 root-normalization gate.
deps: mathlib finite-field Galois (Frobenius closure), MovesD `fieldEnum`.
difficulty: hard — PRE-SPLIT (blueprint): U17b-1 single-read root swap; U17b-2 tower
composition; U17b-3 data transport. The E-phase renderings below are the elaborator's
typeable carriers (flagged in MANIFEST; prover refinement authorized — a full Node/Stage
transport definition is NOT authorized in the Defs layer, so U17b-3 is stated in
∃-transported form).  hypothesis_fields: none.
-/
import Mathlib
import LeanUrat.HC2.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesJ
open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- U17b-1 — single-read root swap: some ambient automorphism fixes the frame subfield
pointwise and carries the recorded residue root to the canonical one (both are roots of
the same `ψImage`, irreducible over the frame field; Frobenius power). -/
theorem galois_root_swap (ν : Node p F) :
    ∃ φ : F ≃+* F, (∀ x ∈ ν.σ.K, φ x = x) ∧
      φ ((ν.zbar : Fˣ) : F) = canonRoot ν := by
  sorry

/-- U17b-3 — data transport: an ambient automorphism transports a coherent realizable
history to a coherent realizable history with φ-conjugated η-data and φ-mapped roots
(a ring-iso commutes with every clause in Node's Prop fields — mechanical but long). -/
theorem galois_transport (φ : F ≃+* F) (H : History p F)
    (hcoh : HistoryCoherent H) (hreal : Realizable H) :
    ∃ H' : History p F,
      HistoryCoherent H' ∧ Realizable H' ∧
      H'.nodes.length = H.nodes.length ∧
      (∀ P : ShapePrefix, P.MatchesHist H → P.MatchesHist H') ∧
      (∀ P : ShapePrefix, P.MatchesHist H →
        ∀ r : Fin P.reads.length,
          ((etaData P H' r).1 = fun k => φ ((etaData P H r).1 k)) ∧
          ((etaData P H' r).2 = fun k => φ ((etaData P H r).2 k))) ∧
      (∀ (r : ℕ) (hr : r < H'.nodes.length) (hr' : r < H.nodes.length),
        (((H'.nodes[r]'hr).zbar : Fˣ) : F) = φ (((H.nodes[r]'hr').zbar : Fˣ) : F)) := by
  sorry

/-- U17b-2 — tower composition: normalize the roots of the first `i` reads (induction
carrier; the automorphism group of a finite field is cyclic, extension over the recorded
subfield tower is elementary Galois theory of finite fields). -/
theorem galois_normalize_upTo {n : ℕ} {P : Shape n} (H : History p F)
    (hm : (P : ShapePrefix).MatchesHist H) (hcoh : HistoryCoherent H)
    (hreal : Realizable H) (hbox : InBox n H) (i : ℕ) :
    ∃ H' : History p F,
      (P : ShapePrefix).MatchesHist H' ∧
      EtaGalEq (etaData (P : ShapePrefix) H) (etaData (P : ShapePrefix) H') ∧
      HistoryCoherent H' ∧ Realizable H' ∧ InBox n H' ∧
      (∀ (r : ℕ) (hr : r < H'.nodes.length), r < i →
        (((H'.nodes[r]'hr).zbar : Fˣ) : F) = canonRoot (H'.nodes[r]'hr)) := by
  sorry

/-- U17b assembled — GALOIS NORMALIZATION: every matched coherent realizable in-box
history has a fully root-normalized Galois class-mate. -/
theorem galois_normalize {n : ℕ} {P : Shape n} (H : History p F)
    (hm : (P : ShapePrefix).MatchesHist H) (hcoh : HistoryCoherent H)
    (hreal : Realizable H) (hbox : InBox n H) :
    ∃ (φ : F ≃+* F) (H' : History p F),
      (P : ShapePrefix).MatchesHist H' ∧
      (∀ (r : ℕ) (hr : r < H'.nodes.length),
        (((H'.nodes[r]'hr).zbar : Fˣ) : F) = canonRoot (H'.nodes[r]'hr)) ∧
      (∀ r : Fin (P : ShapePrefix).reads.length,
        ((etaData (P : ShapePrefix) H' r).1
            = fun k => φ ((etaData (P : ShapePrefix) H r).1 k)) ∧
        ((etaData (P : ShapePrefix) H' r).2
            = fun k => φ ((etaData (P : ShapePrefix) H r).2 k))) ∧
      EtaGalEq (etaData (P : ShapePrefix) H) (etaData (P : ShapePrefix) H') ∧
      HistoryCoherent H' ∧ Realizable H' ∧ InBox n H' := by
  sorry

end LeanUrat.MovesJ
