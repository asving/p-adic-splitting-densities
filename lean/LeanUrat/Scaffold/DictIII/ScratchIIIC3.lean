-- SCRATCH (prover III-C3) — standalone test copy; DELETE before unit completion.
import Mathlib

namespace ScratchIIIC3

structure ENodeData where
  (e h ℓ : ℕ)
  (s u : ℕ)
  sel : Option (ℕ × ℕ)
  inc : Bool
  he : 1 ≤ e
  hh : 1 ≤ h
  hcop : Nat.gcd e h = 1
  hl : 1 ≤ ℓ
  hsel : ∀ gμ ∈ sel, 1 ≤ gμ.1 ∧ 1 ≤ gμ.2 ∧ gμ.2 * gμ.1 ≤ ℓ

structure EHist (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Finite F] where
  base : Subfield F
  psi0 : Polynomial ↥base
  hpsi0 : psi0.Monic ∧ Irreducible psi0
  a0 : ℕ
  ha0 : 1 ≤ a0
  nodes : List ENodeData
  fld : ℕ → Subfield F
  psihat : (i : ℕ) → Polynomial ↥(fld i)
  hpsihat : ∀ i, (psihat i).Monic ∧ Irreducible (psihat i) ∧
    psihat i ≠ Polynomial.X

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

structure EWF_dress (H : EHist p F) : Prop where
  w4dress : ∀ i ν g μ, H.nodes[i]? = some ν → ν.sel = some (g, μ) →
          (H.psihat i).Monic ∧ Irreducible (H.psihat i) ∧
          (H.psihat i).natDegree = g ∧ H.psihat i ≠ Polynomial.X

structure EWF_rows (H : EHist p F) : Prop where
  w1a : ∀ (i : ℕ) ν, H.nodes[i]? = some ν → ν.sel ≠ none → ν.ℓ = 1 → 2 ≤ ν.e → ν.inc = true
  w1b : ∀ (i : ℕ) ν, H.nodes[i]? = some ν → ν.sel ≠ none → ν.ℓ = 1 → ν.e = 1 → ν.inc = false
  w2  : ∀ (i : ℕ) ν g μ, H.nodes[i]? = some ν → ν.sel = some (g, μ) →
          (ν.inc = true ↔ 2 ≤ ν.e * g)
  w3  : (∀ i ν, i + 1 < H.nodes.length → H.nodes[i]? = some ν →
          ∀ gμ ∈ ν.sel, 2 ≤ gμ.2) ∧ (H.nodes ≠ [] → 2 ≤ H.a0)
  w5  : ∀ i ν, i + 1 < H.nodes.length → H.nodes[i]? = some ν → ν.sel ≠ none

structure EWF_tower (H : EHist p F) : Prop where
  towerBase : H.base ≤ H.fld 0
  towerStep : ∀ i, H.fld i ≤ H.fld (i + 1)
  towerBaseDegree :
    Nat.card ↥(H.fld 0) = (Nat.card ↥H.base) ^ H.psi0.natDegree
  towerStepDegree : ∀ i ν g μ,
    H.nodes[i]? = some ν → ν.sel = some (g, μ) →
    Nat.card ↥(H.fld (i + 1)) = (Nat.card ↥(H.fld i)) ^ g

structure EWF (H : EHist p F) : Prop extends EWF_rows H, EWF_dress H, EWF_tower H

def EHist.continuingPart (H : EHist p F) : EHist p F :=
  { H with nodes := H.nodes.takeWhile fun ν => ν.sel.isSome }

theorem EWF.of_prefix {H : EHist p F} (hwf : EWF H) {P : List ENodeData}
    (hpre : P <+: H.nodes) : EWF ({ H with nodes := P } : EHist p F) := by
  have hget : ∀ {i : ℕ} {ν : ENodeData}, P[i]? = some ν → H.nodes[i]? = some ν := by
    intro i ν hg
    obtain ⟨hi, -⟩ := List.getElem?_eq_some_iff.mp hg
    obtain ⟨t, ht⟩ := hpre
    rw [← ht, List.getElem?_append_left hi]
    exact hg
  have hlen : P.length ≤ H.nodes.length := hpre.length_le
  have hne : P ≠ [] → H.nodes ≠ [] := fun hP h0 => hP (List.prefix_nil.mp (h0 ▸ hpre))
  refine { w1a := ?_, w1b := ?_, w2 := ?_, w3 := ⟨?_, ?_⟩, w5 := ?_,
           w4dress := ?_, towerBase := hwf.towerBase, towerStep := hwf.towerStep,
           towerBaseDegree := hwf.towerBaseDegree, towerStepDegree := ?_ }
  · intro i ν hg hsel hl he2
    exact hwf.w1a i ν (hget hg) hsel hl he2
  · intro i ν hg hsel hl he1
    exact hwf.w1b i ν (hget hg) hsel hl he1
  · intro i ν g μ hg hsel
    exact hwf.w2 i ν g μ (hget hg) hsel
  · intro i ν hi hg gμ hmem
    exact hwf.w3.1 i ν (lt_of_lt_of_le hi hlen) (hget hg) gμ hmem
  · intro hP
    exact hwf.w3.2 (hne hP)
  · intro i ν hi hg
    exact hwf.w5 i ν (lt_of_lt_of_le hi hlen) (hget hg)
  · intro i ν g μ hg hsel
    exact hwf.w4dress i ν g μ (hget hg) hsel
  · intro i ν g μ hg hsel
    exact hwf.towerStepDegree i ν g μ (hget hg) hsel

theorem EWF.continuingPart {H : EHist p F} (hwf : EWF H) :
    EWF H.continuingPart :=
  hwf.of_prefix (List.takeWhile_prefix _)

end ScratchIIIC3

#print axioms ScratchIIIC3.EWF.continuingPart
