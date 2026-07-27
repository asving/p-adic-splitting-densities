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

open Classical in
/-- `canonRoot ν` really is a root of `ψImage ν` as soon as `ψImage ν` has a root in `F`
(the `fieldEnum`-least element of a nonempty root set is a member of that set). -/
private lemma canonRoot_mem_roots (ν : Node p F)
    (hne : ((ψImage ν).roots.toFinset.image (fieldEnum F)).Nonempty) :
    canonRoot ν ∈ (ψImage ν).roots.toFinset := by
  classical
  set T := (ψImage ν).roots.toFinset.image (fieldEnum F) with hT
  have hmin : T.min = (↑(T.min' hne) : WithTop (Fin (Nat.card F))) :=
    (Finset.coe_min' hne).symm
  have hcanon : canonRoot ν = (fieldEnum F).symm (T.min' hne) := by
    rw [canonRoot, ← hT, hmin]; rfl
  rw [hcanon]
  obtain ⟨x, hx, hxeq⟩ := Finset.mem_image.mp (T.min'_mem hne)
  rw [← hxeq, Equiv.symm_apply_apply]
  exact hx

open Classical in
/-- U17b-1 — single-read root swap: some ambient automorphism fixes the frame subfield
pointwise and carries the recorded residue root to the canonical one (both are roots of
the same `ψImage`, irreducible over the frame field; Frobenius power). -/
theorem galois_root_swap (ν : Node p F) :
    ∃ φ : F ≃+* F, (∀ x ∈ ν.σ.K, φ x = x) ∧
      φ ((ν.zbar : Fˣ) : F) = canonRoot ν := by
  classical
  set K := ν.σ.K with hKdef
  set z : F := ((ν.zbar : Fˣ) : F) with hzdef
  set r : F := canonRoot ν with hrdef
  letI : Algebra ↥K F := K.subtype.toAlgebra
  haveI : Finite ↥K := inferInstance
  -- z is a root of the K-irreducible ψ
  have hzaeval : (Polynomial.aeval z ν.ψ : F) = 0 := ν.hzbarRoot
  have hminz : minpoly ↥K z = ν.ψ :=
    (minpoly.eq_of_irreducible_of_monic ν.hψirr hzaeval ν.hψmonic).symm
  -- ψImage ν is monic (hence nonzero) and has z as a root, so its root set is nonempty
  have hψImg_ne : ψImage ν ≠ 0 := (ν.hψmonic.map ν.σ.K.subtype).ne_zero
  have hz_root_img : (ψImage ν).eval z = 0 := by
    show (ν.ψ.map ν.σ.K.subtype).eval z = 0
    rw [Polynomial.eval_map]; exact ν.hzbarRoot
  have hz_mem : z ∈ (ψImage ν).roots.toFinset := by
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hψImg_ne]; exact hz_root_img
  have hne : ((ψImage ν).roots.toFinset.image (fieldEnum F)).Nonempty :=
    ⟨fieldEnum F z, Finset.mem_image.mpr ⟨z, hz_mem, rfl⟩⟩
  -- r = canonRoot ν is a root of ψImage ν too
  have hr_mem : r ∈ (ψImage ν).roots.toFinset := canonRoot_mem_roots ν hne
  have hr_root_img : (ψImage ν).eval r = 0 := by
    have h := Multiset.mem_toFinset.mp hr_mem
    rw [Polynomial.mem_roots hψImg_ne] at h; exact h
  have hraeval : (Polynomial.aeval r ν.ψ : F) = 0 := by
    have h1 : (ψImage ν).eval r = Polynomial.aeval r ν.ψ := by
      show (ν.ψ.map ν.σ.K.subtype).eval r = _
      rw [Polynomial.eval_map]; rfl
    rw [← h1]; exact hr_root_img
  have hminr : minpoly ↥K r = ν.ψ :=
    (minpoly.eq_of_irreducible_of_monic ν.hψirr hraeval ν.hψmonic).symm
  -- z and r are conjugate roots over K; a normal (finite ⇒ Galois) extension supplies φ
  have hconj : IsConjRoot ↥K r z := by
    show minpoly ↥K r = minpoly ↥K z
    rw [hminr, hminz]
  obtain ⟨φ, hφ⟩ := hconj.exists_algEquiv
  refine ⟨φ.toRingEquiv, ?_, ?_⟩
  · intro x hx
    have key : φ (algebraMap ↥K F ⟨x, hx⟩) = algebraMap ↥K F ⟨x, hx⟩ := φ.commutes ⟨x, hx⟩
    rw [AlgEquiv.coe_ringEquiv]
    exact key
  · rw [AlgEquiv.coe_ringEquiv]; exact hφ

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
  -- Normalize every read (`i := #reads`); the Galois witness of `EtaGalEq` is the `φ` sought.
  obtain ⟨H', hM', hEta, hcoh', hreal', hbox', hnorm⟩ :=
    galois_normalize_upTo H hm hcoh hreal hbox ((P : ShapePrefix).reads.length)
  obtain ⟨hlen', hmatch'⟩ := hM'
  obtain ⟨φ, hφ⟩ := hEta
  exact ⟨φ, H', ⟨hlen', hmatch'⟩,
    (fun r hr => hnorm r hr (hlen' ▸ hr)), hφ, ⟨φ, hφ⟩, hcoh', hreal', hbox'⟩

end LeanUrat.MovesJ
