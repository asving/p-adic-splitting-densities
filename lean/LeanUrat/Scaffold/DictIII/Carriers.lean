/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib

/-!
# Scaffold/DictIII/Carriers — 𝔈 carriers (BP_III §1.1)

E-phase transcription of `lean/blueprints/BP_III.md` §1.1 (Carriers block).
This file currently holds units III-C1 (`ENodeData`), III-C2a (`EHist`),
III-C5 (`ChainData`), and III-C2b1 (`EWF_rows`: the W1/W2/W3/W5 laws of the
blueprint's `EWF` display, E-phase split per §1.1), transcribed VERBATIM.
Source of record: O2a r5 §2 (C1), (C2); W-laws O2a (C1) W1–W5.

Design note (BP_III §5, D-R1): the residue tower is carried CORPUS-STYLE — an
ambient finite field `F` with each level a `Subfield F`. The `Subfield` carrier
is the contract; an `AdjoinRoot` swap would be a breaking revision.

Display adjustment (III-C2b1, applied uniformly to every node lookup in this
file; same sanctioned convention as the III-C1 paren note below): the §1.1
display writes node lookups as `H.nodes.get? i`, but `List.get?` was REMOVED
from the Lean-4.31/Mathlib environment pinned here (exact error:
"Invalid field `get?`: The environment does not contain `List.get?`"). The
surviving spelling of the SAME function is `H.nodes[i]?` (`getElem?`, of which
`List.get?` was the deprecated alias); the propositions are unchanged. No other
token differs from the display. -/

namespace LeanUrat.Scaffold.DictIII

/-- O-2a (C1): one node record ν = (e,h,ℓ,s,u,sel,inc). `sel = none` ⇔ terminal.

Display adjustment (III-C1; same sanctioned convention as the Spine.lean header):
the §1.1 display writes the ℕ field lines bare (`e h ℓ : ℕ`), but in Lean 4.31
structure-field syntax a bare multi-identifier line parses as ONE field with
function binders (`e : (h : _) → _ → ℕ`; the later row `hcop : Nat.gcd e h = 1`
then fails with "Application type mismatch: The argument e has type
(h : ?m.1) → ?m.3 h → ℕ but is expected to have type ℕ"). The parenthesized
form `(e h ℓ : ℕ)` is the unique well-typed reading — it declares exactly the
displayed fields `e h ℓ s u : ℕ` (checked: `ENodeData.e : ENodeData → ℕ`,
..., `ENodeData.hcop : ∀ self, self.e.gcd self.h = 1`); no other token changes. -/
structure ENodeData where
  (e h ℓ : ℕ)
  (s u : ℕ)                    -- (C1) REV 2: declared domains ℤ≥0
  sel : Option (ℕ × ℕ)         -- some (g, μ)
  inc : Bool
  he : 1 ≤ e
  hh : 1 ≤ h
  hcop : Nat.gcd e h = 1
  hl : 1 ≤ ℓ
  hsel : ∀ gμ ∈ sel, 1 ≤ gμ.1 ∧ 1 ≤ gμ.2 ∧ gμ.2 * gμ.1 ≤ ℓ

/-- 𝔈 carrier: root datum (ψ̂₀, a₀) + node list + Subfield tower dressing. -/
structure EHist (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Finite F] where
  base : Subfield F                              -- F_q
  psi0 : Polynomial ↥base                        -- monic irreducible, f₀ := deg
  hpsi0 : psi0.Monic ∧ Irreducible psi0
  a0 : ℕ
  ha0 : 1 ≤ a0
  nodes : List ENodeData
  fld : ℕ → Subfield F                           -- F_1, F_2, … (tower levels)
  psihat : (i : ℕ) → Polynomial ↥(fld i)         -- the dressing ψ̂_i (junk off-range)
  hpsihat : ∀ i, (psihat i).Monic ∧ Irreducible (psihat i) ∧
    psihat i ≠ Polynomial.X

/-- 𝔗 (C2): formal chain data — slopes in lowest terms + dressing; NO admissibility. -/
structure ChainData (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Finite F] where
  base : Subfield F
  psi0 : Polynomial ↥base
  hpsi0 : psi0.Monic ∧ Irreducible psi0
  slopes : List (ℕ × ℕ)                          -- (e_i, h_i), λ_i = −h_i/e_i
  hcop : ∀ eh ∈ slopes, 1 ≤ eh.1 ∧ 1 ≤ eh.2 ∧ Nat.gcd eh.1 eh.2 = 1
  fld : ℕ → Subfield F
  psihat : (i : ℕ) → Polynomial ↥(fld i)
  hdress : ∀ i, i < slopes.length → (psihat i).Monic ∧ Irreducible (psihat i) ∧
             psihat i ≠ Polynomial.X

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-- O-2a (C1) W4: the dressing laws as one Prop structure (unit III-C2b2) —
    the `w4dress` row of the blueprint's `EWF` display, split out per the
    E-phase note at BP_III §1.1 (`EWF_rows`/`EWF_tower`/`EWF_dress`). -/
structure EWF_dress (H : EHist p F) : Prop where
  w4dress : ∀ i ν g μ, H.nodes[i]? = some ν → ν.sel = some (g, μ) →
          (H.psihat i).Monic ∧ Irreducible (H.psihat i) ∧
          (H.psihat i).natDegree = g ∧ H.psihat i ≠ Polynomial.X

/-- O-2a (C1) W1/W2/W3/W5: the well-formedness laws as one Prop structure
    (unit III-C2b1) — the `w1a`/`w1b`/`w2`/`w3`/`w5` rows of the blueprint's
    `EWF` display, split out per the E-phase note at BP_III §1.1
    (`EWF_rows`/`EWF_tower`/`EWF_dress`).

    Display adjustment (III-C2a repair pass, same class as the header's `[i]?`
    note): in `w1a`/`w1b`/`w2` the index `i` occurs ONLY in `H.nodes[i]?`, so
    after the `get?` → `[i]?` swap nothing pins `i : ℕ` and elaboration fails
    ("Invalid field notation: Type of ν is not known"). The blueprint's
    `List.get?` spelling forced `i : ℕ` by itself; the binder annotation
    `(i : ℕ)` restores exactly that reading — propositions unchanged. `w3`/`w5`
    need no annotation (`i + 1 < H.nodes.length` pins `i`). -/
structure EWF_rows (H : EHist p F) : Prop where
  w1a : ∀ (i : ℕ) ν, H.nodes[i]? = some ν → ν.sel ≠ none → ν.ℓ = 1 → 2 ≤ ν.e → ν.inc = true
  w1b : ∀ (i : ℕ) ν, H.nodes[i]? = some ν → ν.sel ≠ none → ν.ℓ = 1 → ν.e = 1 → ν.inc = false
  w2  : ∀ (i : ℕ) ν g μ, H.nodes[i]? = some ν → ν.sel = some (g, μ) →
          (ν.inc = true ↔ 2 ≤ ν.e * g)
  w3  : (∀ i ν, i + 1 < H.nodes.length → H.nodes[i]? = some ν →
          ∀ gμ ∈ ν.sel, 2 ≤ gμ.2) ∧ (H.nodes ≠ [] → 2 ≤ H.a0)
  w5  : ∀ i ν, i + 1 < H.nodes.length → H.nodes[i]? = some ν → ν.sel ≠ none

/-- O-2a (C1) tower: base/step inclusions + both cardinal-power degree laws
    (REV2 finding 4) as one Prop structure (unit III-C2b3) — the `towerBase`/
    `towerStep`/`towerBaseDegree`/`towerStepDegree` rows of the blueprint's
    `EWF` display, split out per the E-phase note at BP_III §1.1
    (`EWF_rows`/`EWF_tower`/`EWF_dress`). -/
structure EWF_tower (H : EHist p F) : Prop where
  towerBase : H.base ≤ H.fld 0
  towerStep : ∀ i, H.fld i ≤ H.fld (i + 1)
  towerBaseDegree :
    Nat.card ↥(H.fld 0) = (Nat.card ↥H.base) ^ H.psi0.natDegree
  towerStepDegree : ∀ i ν g μ,
    H.nodes[i]? = some ν → ν.sel = some (g, μ) →
    Nat.card ↥(H.fld (i + 1)) = (Nat.card ↥(H.fld i)) ^ g

/-- Well-formedness W1–W5 + W4 dressing laws + tower-degree laws, as one Prop
    structure (split into three ≤40-line units at E-phase: EWF_rows, EWF_tower,
    EWF_dress). Unit III-C2b4: the assembly — fields only, extending the three
    E-phase rows; together the inherited fields are VERBATIM the blueprint's
    `EWF` display (BP_III §1.1). -/
structure EWF (H : EHist p F) : Prop extends EWF_rows H, EWF_dress H, EWF_tower H

/-! ## Unit III-C4 — row classifiers T1–T5 + `dCert` (O2a r5 §2 (C1) rows)

O2a r5 §2 (C1): "Rows: T1 (ℓ ≥ 2), T2 (ℓ = 1, e ≥ 2, h ≥ 2), T3 (ℓ = 1, e ≥ 2,
h = 1), T4 (ℓ = 1, e = 1), all with sel ≠ ⊥; T5 = terminal. A continuing node is
CERTIFIED iff it is T1 with inc = 1, or T2; dCert(𝐇) := #certified nodes."
The classifiers are Props with `Decidable` instances — the decidable case split
on (ℓ, e, h, sel, inc). Only T1/T2 rows (which force `sel ≠ none`) can be
certified, so counting over all of `H.nodes` agrees with counting over the
continuing part. `EHist.dCert`'s signature is VERBATIM BP_III §1.1 line
`def EHist.dCert (H : EHist p F) : ℕ  -- #certified (T1∧inc, or T2)`. -/

/-- Row T1 (O-2a (C1)): ℓ ≥ 2, continuing (`sel ≠ none`). -/
def ENodeData.isT1 (ν : ENodeData) : Prop :=
  2 ≤ ν.ℓ ∧ ν.sel ≠ none

/-- Row T2 (O-2a (C1)): ℓ = 1, e ≥ 2, h ≥ 2, continuing. -/
def ENodeData.isT2 (ν : ENodeData) : Prop :=
  ν.ℓ = 1 ∧ 2 ≤ ν.e ∧ 2 ≤ ν.h ∧ ν.sel ≠ none

/-- Row T3 (O-2a (C1)): ℓ = 1, e ≥ 2, h = 1, continuing. -/
def ENodeData.isT3 (ν : ENodeData) : Prop :=
  ν.ℓ = 1 ∧ 2 ≤ ν.e ∧ ν.h = 1 ∧ ν.sel ≠ none

/-- Row T4 (O-2a (C1)): ℓ = 1, e = 1, continuing. -/
def ENodeData.isT4 (ν : ENodeData) : Prop :=
  ν.ℓ = 1 ∧ ν.e = 1 ∧ ν.sel ≠ none

/-- Row T5 (O-2a (C1)): terminal (`sel = none`). -/
def ENodeData.isT5 (ν : ENodeData) : Prop :=
  ν.sel = none

instance : DecidablePred ENodeData.isT1 := fun ν =>
  inferInstanceAs (Decidable (2 ≤ ν.ℓ ∧ ν.sel ≠ none))

instance : DecidablePred ENodeData.isT2 := fun ν =>
  inferInstanceAs (Decidable (ν.ℓ = 1 ∧ 2 ≤ ν.e ∧ 2 ≤ ν.h ∧ ν.sel ≠ none))

instance : DecidablePred ENodeData.isT3 := fun ν =>
  inferInstanceAs (Decidable (ν.ℓ = 1 ∧ 2 ≤ ν.e ∧ ν.h = 1 ∧ ν.sel ≠ none))

instance : DecidablePred ENodeData.isT4 := fun ν =>
  inferInstanceAs (Decidable (ν.ℓ = 1 ∧ ν.e = 1 ∧ ν.sel ≠ none))

instance : DecidablePred ENodeData.isT5 := fun ν =>
  inferInstanceAs (Decidable (ν.sel = none))

/-- O-2a (C1): a continuing node is CERTIFIED iff it is T1 with `inc = true`,
    or T2. (T1/T2 force `sel ≠ none`, so no terminal node is certified.) -/
def ENodeData.certified (ν : ENodeData) : Prop :=
  (ν.isT1 ∧ ν.inc = true) ∨ ν.isT2

instance : DecidablePred ENodeData.certified := fun ν =>
  inferInstanceAs (Decidable ((ν.isT1 ∧ ν.inc = true) ∨ ν.isT2))

/-- The rows T1–T5 exhaust every node: the case split on (ℓ, e, h, sel) is
    total, using the carrier laws e ≥ 1, h ≥ 1, ℓ ≥ 1. -/
theorem ENodeData.rows_exhaustive (ν : ENodeData) :
    ν.isT1 ∨ ν.isT2 ∨ ν.isT3 ∨ ν.isT4 ∨ ν.isT5 := by
  have he := ν.he
  have hh := ν.hh
  have hl := ν.hl
  unfold ENodeData.isT1 ENodeData.isT2 ENodeData.isT3 ENodeData.isT4 ENodeData.isT5
  by_cases hsel : ν.sel = none
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr hsel
  · rcases Nat.lt_or_ge ν.ℓ 2 with hl2 | hl2
    · rcases Nat.lt_or_ge ν.e 2 with he2 | he2
      · exact Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨by omega, by omega, hsel⟩
      · rcases Nat.lt_or_ge ν.h 2 with hh2 | hh2
        · exact Or.inr <| Or.inr <| Or.inl ⟨by omega, he2, by omega, hsel⟩
        · exact Or.inr <| Or.inl ⟨by omega, he2, hh2, hsel⟩
    · exact Or.inl ⟨hl2, hsel⟩

/-- #certified (T1∧inc, or T2). -/
def EHist.dCert (H : EHist p F) : ℕ :=
  H.nodes.countP fun ν => decide ν.certified

/-! ## Unit III-C6a — prefix operations `EHist.take` / `ChainData.take`
(BP_III §1.1; O2a r5 §2 (C3)) -/

/-- Prefix operations owned by III-C6a. Off-range tower dressing is retained. -/
def EHist.take (H : EHist p F) (k : ℕ) : EHist p F :=
  { H with nodes := H.nodes.take k }

/-- Display adjustment (III-C6a; same sanctioned convention as the III-C1 and
III-C2b1 notes above): the §1.1 display updates only `slopes` and `hcop`,
leaving `hdress` to the `{ c with ... }` copy — but `hdress`'s TYPE depends on
`slopes`, so the copied proof fails to elaborate (exact error: "Type mismatch:
c.hdress has type ∀ i < c.slopes.length, (c.psihat i).Monic ∧ … but is expected
to have type ∀ i < (List.take k c.slopes).length, (c.psihat i).Monic ∧ …").
The forced reading — stated by the display's own comment "Off-range tower
dressing is retained" — supplies the SAME retained proof restricted along
`(c.slopes.take k).length ≤ c.slopes.length`. The `hdress` row below is exactly
that restriction; it fills a Prop field (proof-irrelevant), so the def's data
content is token-identical to the display. No other token differs. -/
def ChainData.take (c : ChainData p F) (k : ℕ) : ChainData p F :=
  { c with
    slopes := c.slopes.take k
    hcop := by
      intro eh heh
      exact c.hcop eh (List.mem_of_mem_take heh)
    hdress := by
      intro i hi
      exact c.hdress i (lt_of_lt_of_le hi (c.slopes.length_take_le' k)) }

/-! ## Units III-C3 / III-C6b / III-C7a — 𝐇°, Θ, `theta_continuing`
(O2a (C1) last ¶ + (C3)); the III-C3/III-C6b dep declarations are transcribed
here by III-C7a since they had not yet landed anywhere in the corpus. -/

/-- 𝐇°: drop a terminal last node (unit III-C3; signature VERBATIM BP_III §1.1).
    Design note (III-C3 body freedom, recorded): the blueprint gives a signature
    only. Realized as `takeWhile (sel ≠ none)`: on well-formed histories (W5:
    only the last node may be terminal) this is exactly "drop a terminal last
    node", and it is idempotent on ALL of 𝔈 — which the unconditional statement
    `theta_continuing` (VERBATIM, no `EWF` hypothesis) requires; a bare
    "`dropLast` if last is terminal" body would make that statement FALSE on
    non-WF histories with two trailing terminal nodes. -/
def EHist.continuingPart (H : EHist p F) : EHist p F :=
  { H with nodes := H.nodes.takeWhile fun ν => ν.sel.isSome }

/-- (C3): Θ re-indexes the continuing part. Dressing follows from `EHist.hpsihat`.
    (Unit III-C6b, transcribed VERBATIM from BP_III §1.1.) -/
def Theta (H : EHist p F) : ChainData p F :=
  { base := H.base
    psi0 := H.psi0
    hpsi0 := H.hpsi0
    slopes := H.continuingPart.nodes.map fun ν => (ν.e, ν.h)
    hcop := by
      intro eh heh
      rcases List.mem_map.mp heh with ⟨ν, hν, rfl⟩
      exact ⟨ν.he, ν.hh, ν.hcop⟩
    fld := H.fld
    psihat := H.psihat
    hdress := by
      intro i hi
      exact H.hpsihat i }

/-- Helper (III-C7a): `continuingPart` is idempotent — `List.takeWhile_idem`
    pushed through the structure update (the Prop rows ride by proof
    irrelevance). -/
theorem EHist.continuingPart_idem (H : EHist p F) :
    H.continuingPart.continuingPart = H.continuingPart :=
  congrArg (fun l => ({ H with nodes := l } : EHist p F)) List.takeWhile_idem

/-- Helper (III-C7a): the `Theta` body as a builder fully parametric in the
    node list, so that list rewrites stay well-typed (the proof rows' TYPES
    mention the list; `Theta`'s extracted proofs pin it, blocking `rw`). Both
    `Theta H` and `Theta H.continuingPart` are definitionally `thetaAux H` of
    their respective node lists, by iota-reduction + proof irrelevance. -/
private def thetaAux (H : EHist p F) (l : List ENodeData) : ChainData p F :=
  { base := H.base
    psi0 := H.psi0
    hpsi0 := H.hpsi0
    slopes := l.map fun ν => (ν.e, ν.h)
    hcop := by
      intro eh heh
      rcases List.mem_map.mp heh with ⟨ν, hν, rfl⟩
      exact ⟨ν.he, ν.hh, ν.hcop⟩
    fld := H.fld
    psihat := H.psihat
    hdress := by
      intro i hi
      exact H.hpsihat i }

/-- Owned by III-C7a; proved by unfolding `Theta` and `continuingPart`. -/
theorem theta_continuing (H : EHist p F) :
    Theta H = Theta H.continuingPart :=
  calc Theta H
      = thetaAux H H.continuingPart.nodes := rfl
    _ = thetaAux H H.continuingPart.continuingPart.nodes :=
        (congrArg (thetaAux H) List.takeWhile_idem).symm
    _ = Theta H.continuingPart := rfl

/-! ## Unit III-C7b — `theta_truncation` (O2a r5 §2 (C3)) -/

/-- Owned by III-C7b; proved from `List.map_take`. -/
theorem theta_truncation (H : EHist p F) (k : ℕ) :
    (Theta H).take k = Theta (H.take k) := by
  simp only [Theta, ChainData.take, EHist.take, EHist.continuingPart,
    List.take_takeWhile, ← List.map_take]

/-! ## Unit III-C3 (lemma half) — prefixes of WF ending continuing are WF
(O2a (C1) last ¶: "Prefixes of well-formed histories ending at a continuing
node are well-formed."). The unit's def half `EHist.continuingPart` landed
above (III-C7a's dep transcription; body design note there). The blueprint
displays NO Lean statement for this lemma (only the def signature is displayed
in §1.1; the unit-table row describes the lemma in words), so the rendering
below is this unit's — flagged for division-lead review, not fenced. -/

/-- Unit III-C3 lemma, general form: EVERY nodes-prefix of a well-formed
    history is well-formed. The source row reads "prefixes of WF ending
    continuing are WF" (O2a (C1) last ¶); the "ending at a continuing node"
    hypothesis is not needed: every `EWF` row is guarded by a node lookup
    `H.nodes[i]?` or an interior bound `i + 1 < H.nodes.length`, both of which
    transport along any prefix, and the tower/base rows do not mention
    `nodes` (the prefix keeps `a0`, `fld`, `psihat`). The blueprint's named
    case — the prefix ending at the last continuing node — is
    `EWF.continuingPart` below. -/
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

/-- Unit III-C3 lemma at the blueprint's named prefix: the continuing part 𝐇°
    (= "drop a terminal last node" on well-formed histories, per the def note
    above) of a well-formed history is well-formed. `takeWhile` prefixes are
    prefixes, so this is `EWF.of_prefix` at `List.takeWhile_prefix`; the
    `dropLast`-vs-identity case split of the blueprint sketch is subsumed by
    the prefix transport. -/
theorem EWF.continuingPart {H : EHist p F} (hwf : EWF H) :
    EWF H.continuingPart :=
  hwf.of_prefix (List.takeWhile_prefix _)

end LeanUrat.Scaffold.DictIII

-- Footprint audit (unit III-C7b gate): expect Lean core only.
#print axioms LeanUrat.Scaffold.DictIII.theta_truncation

-- Footprint audit (unit III-C3 gate): expect Lean core only.
#print axioms LeanUrat.Scaffold.DictIII.EWF.continuingPart
