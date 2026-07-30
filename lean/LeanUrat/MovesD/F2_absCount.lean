/-
Unit F2.absCount  (MovesD campaign, ratification repair D3, 2026-07-28)
[Finding D3: core OVERRULED (EtaData/PrefIdx/PresentNorm IS the faithful η-granularity
design — REV 4 Fable#2 C1: the note's η carries digits+ψ, everything else is
shape-pinned/derived/policy-determined; zbar is NOT η data — the normalization kills
conjugate-presentation overcounting; PresentNorm(ii) IS the typed anti-collapse law);
residue ACCEPTED — the conditionality is made visible as a REAL THEOREM here.]
moves_ref: L3 "Pref(P̂) := { η : shape(η) = P̂, η realizable, canonical lifts }, C_P̂(p) :=
#Pref(P̂) … a literal finite count of realized value prefixes — no quotient". The ratifier
worried PrefIdx (an etaData-image) adds normalization + an image quotient. THIS unit:
under the typed dictionary pin `PresentNorm` (the corpus's standing hypothesis on every
C-consuming law), the normalized-class count EQUALS the count of the POLICY-FREE Galois
setoid classes of `PrefSetAny` — i.e. the image/normalization construction counts exactly
one class per policy-free η up to conjugate presentation, nothing collapsed, nothing
added. PresentNorm (i) totality gives surjectivity, (ii) uniqueness gives injectivity.
deps: Defs, F1 (reprOf_mem, etaData_reprOf).
sketch: EtaGalEq is an equivalence (RingEquiv group: refl/symm/trans); the map
i ↦ ⟦reprOf i⟧ is the bijection.  difficulty: easy-medium (finite plumbing).
hypothesis_fields: `hnorm : PresentNorm n pol P` on `card_classes_abs` (the typed pin —
exactly the conditionality the ratifier asked to see).
-/
import Mathlib
import LeanUrat.MovesD.Defs
import LeanUrat.MovesD.F1_enum

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesD
open LeanUrat.Moves LeanUrat.MovesC

section
variable {F : Type*} [Field F]

/-- `EtaGalEq` is reflexive (φ = id). -/
theorem EtaGalEq.refl {P : ShapePrefix} (d : EtaData F P) : EtaGalEq d d :=
  ⟨RingEquiv.refl F, fun _ => ⟨rfl, rfl⟩⟩

/-- `EtaGalEq` is symmetric (φ ↦ φ⁻¹). -/
theorem EtaGalEq.symm {P : ShapePrefix} {d d' : EtaData F P}
    (h : EtaGalEq d d') : EtaGalEq d' d := by
  obtain ⟨φ, hφ⟩ := h
  refine ⟨φ.symm, fun r => ⟨?_, ?_⟩⟩
  · rw [(hφ r).1]; funext k; simp
  · rw [(hφ r).2]; funext k; simp

/-- `EtaGalEq` is transitive (composition). -/
theorem EtaGalEq.trans {P : ShapePrefix} {d d' d'' : EtaData F P}
    (h : EtaGalEq d d') (h' : EtaGalEq d' d'') : EtaGalEq d d'' := by
  obtain ⟨φ, hφ⟩ := h
  obtain ⟨φ', hφ'⟩ := h'
  refine ⟨φ.trans φ', fun r => ⟨?_, ?_⟩⟩
  · rw [(hφ' r).1, (hφ r).1]; rfl
  · rw [(hφ' r).2, (hφ r).2]; rfl

end

section
variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F] {n : ℕ}
  {pol : CanonPolicy p F} {P : Shape n}

/-- **The policy-free Galois setoid** on the policy-free realizable prefix set: two
histories are related iff their η-class data are conjugate presentations (`EtaGalEq` of
their `etaData`). This is the note's own granularity BEFORE any policy/normalization:
one class = one η up to the Galois relation between conjugate presentations. -/
def etaGalSetoid (n : ℕ) (P : Shape n) : Setoid ↥(PrefSetAny (p := p) (F := F) n P) where
  r H H' := EtaGalEq (etaData (P : ShapePrefix) H.1) (etaData (P : ShapePrefix) H'.1)
  iseqv := ⟨fun _ => EtaGalEq.refl _, EtaGalEq.symm, EtaGalEq.trans⟩

/-- PrefSet ⊆ PrefSetAny (drop the canonical-presentation conjunct). -/
theorem prefSet_subset_any {H : History p F} (hH : H ∈ PrefSet n pol P) :
    H ∈ PrefSetAny n P :=
  ⟨hH.1, hH.2.1, hH.2.2.1, hH.2.2.2.1⟩

/-- **The absolute-count theorem (the ratification-residue repair)**: under the typed
dictionary pin `PresentNorm`, the normalized-class count `#PrefIdx` (what `CD` counts on
nonempty shapes) EQUALS the number of POLICY-FREE Galois classes of `PrefSetAny` — L3's
"literal finite count" read at the η-granularity with conjugate presentations identified.
So the image construction neither collapses distinct η's (PresentNorm (ii) uniqueness =
the anti-collapse law) nor misses any (PresentNorm (i) totality); the normalization
`zbar = canonRoot` selects exactly one presentation per class. The conditionality is now
a THEOREM hypothesis, not a comment. -/
theorem card_classes_abs (hnorm : PresentNorm n pol P) :
    Nat.card (PrefIdx n pol P) = Nat.card (Quotient (etaGalSetoid (p := p) (F := F) n P)) := by
  refine Nat.card_congr (Equiv.ofBijective
    (fun i => Quotient.mk (etaGalSetoid n P)
      ⟨reprOf i, prefSet_subset_any (reprOf_mem i)⟩) ⟨?_, ?_⟩)
  · -- INJECTIVE: Galois-related normalized classes coincide (PresentNorm (ii)).
    intro i j hij
    have hrel : EtaGalEq (etaData (P : ShapePrefix) (reprOf i))
        (etaData (P : ShapePrefix) (reprOf j)) := Quotient.exact hij
    have heq : etaData (P : ShapePrefix) (reprOf i) = etaData (P : ShapePrefix) (reprOf j) :=
      hnorm.2 (reprOf i) (reprOf j) (reprOf_mem i) (reprOf_mem j) hrel
    apply Subtype.ext
    rw [← etaData_reprOf i, ← etaData_reprOf j, heq]
  · -- SURJECTIVE: every policy-free prefix has a normalized class-mate up to Galois
    -- (PresentNorm (i)).
    intro c
    induction c using Quotient.inductionOn with
    | h H =>
      obtain ⟨i, hi⟩ := hnorm.1 H.1 H.2
      refine ⟨i, Quotient.sound ?_⟩
      change EtaGalEq (etaData (P : ShapePrefix) (reprOf i)) (etaData (P : ShapePrefix) H.1)
      refine EtaGalEq.symm ?_
      rw [etaData_reprOf i]; exact hi

end

end LeanUrat.MovesD
