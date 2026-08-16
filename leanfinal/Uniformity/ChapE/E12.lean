/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapE.E11
import Mathlib.Data.Nat.GCD.Basic

/-!
# Uniformity.ChapE.E12 — `RungInterface`, T2's five HE7.A clause families as fields

**Chapter E, NODE E.12** [def] (`blueprint/CHAP-E_sigma_ladder.md` §4, **as REPAIRED by
amendment A-E.1/E-D6**), ENV-E2 (the carrier arena: the bundle `O`, the label field `K`, a slot
carrier `C : SlotCarrier O K` from E.10 and a block `B : BlockData C` from E.11).

Over a slot carrier and a block, the **rung interface** carries the side/residual numerical data
together with THEOREM HE7.A's five hypothesis families at exactly corpus strength (`EFF.T2.39`:
*"The theorem assumes the explicit quantitative consequences `(ACCOUNT)`, `(RES-DEG)`,
nonemptiness, exhaustion, and root-preserving continuation. These are source obligations, not
conclusions obtained merely by naming a carrier."*):

1. the **sides** `(u_λ, ℓ_λ)` in lowest terms with their lengths — `hside_cop`, `hside_node`
   (the cleared `λ > T`), `hlen_pos`, and `(HULL-LENGTH)` `hlen_sum : Σ len = μ` (SUPPLIED, not
   derived: its derivation is polygon geometry owned below E);
2. the per-side **residual shadow** (D-E2) `linFac`/`hiFac` with `(RES-DEG)` `hresdeg`
   (`EFF.T2.12`'s `e′ Σ m_{λ,r′} deg r′ = L_λ`);
3. `(ACCOUNT)` at its consumed jump form `(SIDE-COUNT)` — `rootCount` with
   `haccount : rootCount λ = D · len λ` (see D-E3 below);
4. **nonemptiness** `hnonempty` and the local **forcing** shadow `hforce` (`EFF.T2.30`'s
   divisibilities `e_𝒞 e′ ∣ e`, `f_𝒞 deg r′ ∣ f`, in their count form `|orbit| ≥ D e′ deg r′`);
5. **exhaustion** `hexhaust` (the classes are disjoint and fill the side's root count) and
   **root-preserving continuation** — the `(SEC-RANK)` carrier `W`, `wf`, `σRank` (`EFF.T2.26`).

σ-valued outputs NEVER live here (GC-4: they exit through §7's dictionary).

## The three universes (A-E.1/E-D6) — named here, once, for the whole chapter

`RungInterface` is universe-polymorphic in **three** parameters, IN THIS ORDER:
`uO` (the ring `O`), `uK` (the field `K`), `uW` (the `(SEC-RANK)` rank carrier `W`). The first
two are inferable at every use site (they occur in `C`/`B`); `uW` occurs ONLY in the structure's
own body, so ANY declaration that QUANTIFIES over a `RungInterface` inside a `Prop` must bind
`uW` explicitly and write `RungInterface.{uO, uK, uW}` — otherwise Lean reports "Failed to infer
universe levels in type of binder" / "contains universe level metavariables" (the hard errors
the stage-0e gate hit at E.24, E.39, E.40, E.44 before the repair).

The blueprint grants spelling latitude here: `{O : Type*} … W : Type*` and the fully explicit
`{O : Type uO} … W : Type uW` elaborate to the identical signature and the identical parameter
order. **The explicit form is what landed** — it makes the FROZEN order `⟨O, K, W⟩` structural
rather than incidental, and it gives the `universe` line above the structure a use. Re-probed at
landing: both forms print
`{O : Type u_1} → [CommRing O] → {K : Type u_2} → [Field K] → (C : SlotCarrier O K) →
BlockData C → Type (max u_2 (u_3 + 1))`.

`W := ℕ` was NOT adopted, per the node's own instruction (`EFF.T2.52` licenses a well-foundedness
form an instance "may discharge either way"; an `ℕ`-valued rank would silently strengthen).
The scoping consequence recorded at honesty **E-12** stands: `LB1Carrier.{uO, uK, uW}` and the
other Display-A conjunct carriers quantify only over interfaces whose rank carrier lives in
universe `uW`, so those carriers are universe-SCOPED and chapter I must consume them
universe-polymorphically.

## ⚠ DECISION D-E3 — `(ACCOUNT)` is carried at its consumed jump form

`EFF.T2.16`'s integral `(ACCOUNT)` (`Σ_ρ min(w_ρ, κ) = D Σ_λ L_λ min(λ, κ)` for `κ > T`) is
consumed by the master ONLY through its two jump consequences `(SIDE-COUNT)` `n_λ = D·L_λ` and
`(DEG-SUM)` (`EFF.T2.29`: "Comparing the jumps of the two piecewise-linear sides at λ yields
`(SIDE-COUNT)`"). The field `haccount` carries `(SIDE-COUNT)` directly; the κ-sampled integral
identity and its jump derivation are the INSTANCES' obligation (level 1: HE6-ACCOUNT via B/C;
level 2: `EFF.HE7.41`'s `(†₂-count)` + HE6-3's sampling), recorded per instance at E.22/E.23.
Rationale: the sampling/elimination derivation quantifies over rational `κ` in gaps, which under
GC-2's no-ℚ rule would force a cleared two-variable sampling layer E does not own and no
E-theorem consumes — E.14–E.16 need exactly `(SIDE-COUNT)`. **This is the chapter's largest
transcription-strength call** (flagged for the cross-read, §14); the original integral display is
quoted in full at E.22's instance-obligation list so no strength is silently lost.

## ⚠ `(RISE)`/`(WINDOW)` are deliberately NOT fields

`(RISE)` (`EFF.T2.19`: "a carrier hypothesis, not an open ledger obligation") and
`(WINDOW)`/proxy-safety enter as hypotheses OF THE TRANSITION THEOREMS (E.17/E.18) at the exact
step that consumes them, not as standing structure fields — a rung that never recenters never
owes `(RISE)`. This matches `EFF.T2.19`'s per-step scoping and keeps minimal binding (GC-6.4).

NO-IRR fence (`EFF.T2.43`/`.44`, binding on every §4 signature): nothing here carries an
irreducibility hypothesis on `Φ`; residual LABELS and emitted boundary factors may be
irreducible.

Definitional, no proof obligation. The structure body is reused verbatim from the gate-verified
leanspec stub (`leanspec/Leanspec/ChapE.lean`, `LeanspecE`) — only the universe spelling of the
three `Type` binders differs, per the latitude quoted above. The blueprint's SPLIT-MANDATE
(land as `E12` + `E12a` "if elaboration or universe plumbing on `W` fights") was NOT triggered:
with the explicit universes the single structure elaborates in one pass, and the E-D6 quantifier
pattern is exercised in the gate below.

DEPENDS: E.10 (`SlotCarrier`), E.11 (`BlockData`) · mathlib `WellFoundedRelation`,
`Multiset.map`, `Multiset.sum`, `Finset.sum`, `Nat.Coprime`.

SOURCE: `EFF.T2.12` (`(RES-FACT)`/`(RES-DEG)`); `EFF.T2.15` (the seven test-package clauses —
clauses 3/4/5/6 are the `hnonempty`/`hexhaust`/`hforce` shadows; clauses 1/2/7 are instance
obligations, E.22); `EFF.T2.16` (`(ACCOUNT)` — via D-E3); `EFF.T2.26` (`(SEC-RANK)` verbatim:
well-founded `W_𝒞`, strict decrease at product-1 linear recenterings ONLY, "Nothing is required
of `σ_𝒞` at any other transition"); `EFF.T2.29` (`(SIDE-COUNT)`/`(DEG-SUM)`); `EFF.T2.30` (the
forcing divisibilities, of which `hforce` is the count shadow `|orbit| ≥ D e′ deg r′`);
`EFF.T2.39` (the hypothesis-suite architecture); `EFF.T2.52` (the rank carrier's form).

TEETH: S7 Pass 2 missing-`(RES-DEG)` refusal → structural (a consumer without `hresdeg` cannot
elaborate). S7 well-founded-but-root-losing mutant (`EFF.T2.27`) → `hexhaust` and `haccount` are
separate fields from the rank, so rank descent alone proves nothing; the mutant's route is closed
by construction and E.20 states the theorem only from BOTH.

ENVIRONMENT: ENV-E2.

## Status

Sorry-free. Every declaration reports at most the Lean-core triple
`{propext, Classical.choice, Quot.sound}`. Types checked against the signed SIGNATURE
declaration by declaration (field names, field order, and every field's statement unchanged).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Ladder

-- The three universes E.12's `RungInterface` carries: `uO` (the bundle), `uK` (the label field)
-- and `uW` — the `(SEC-RANK)` carrier's universe, which every declaration that QUANTIFIES over
-- a `RungInterface` inside a `Prop` must bind explicitly (defect A-E.1/E-D6).
universe uO uK uW

/-- The **rung interface**: T2's carrier hypothesis suite as fields (`EFF.T2.39`'s five
quantitative families + the side/residual numerical shadow). σ-valued outputs NEVER live
here (GC-4: they exit through §7's dictionary). -/
structure RungInterface {O : Type uO} [CommRing O] {K : Type uK} [Field K]
    (C : SlotCarrier O K) (B : BlockData C) where
  sides : Finset (ℕ × ℕ)
  hside_cop : ∀ p ∈ sides, Nat.Coprime p.1 p.2 ∧ 1 ≤ p.2
  hside_node : ∀ p ∈ sides, p.2 * B.T < p.1                     -- λ > T (clause 1 half)
  len : ℕ × ℕ → ℕ
  hlen_pos : ∀ p ∈ sides, 1 ≤ len p
  hlen_sum : ∑ p ∈ sides, len p = B.μ                           -- (HULL-LENGTH)
  linFac : ℕ × ℕ → Multiset (K × ℕ)                             -- (root s, mult m)
  hiFac : ℕ × ℕ → Multiset (ℕ × ℕ)                              -- (deg ≥ 2 …, mult)
  hresdeg : ∀ p ∈ sides,                                        -- (RES-DEG)
      p.2 * (Multiset.sum ((linFac p).map Prod.snd)
        + Multiset.sum ((hiFac p).map fun q => q.1 * q.2)) = len p
  rootCount : ℕ × ℕ → ℕ
  haccount : ∀ p ∈ sides, rootCount p = C.D * len p             -- (SIDE-COUNT) form
  classCount : ℕ × ℕ → K × ℕ → ℕ                                -- per linear factor
  classCountHi : ℕ × ℕ → ℕ × ℕ → ℕ                              -- per higher factor
  hnonempty : ∀ p ∈ sides, (∀ q ∈ linFac p, 1 ≤ classCount p q) ∧
      (∀ q ∈ hiFac p, 1 ≤ classCountHi p q)                     -- nonemptiness
  hforce : ∀ p ∈ sides, (∀ q ∈ linFac p, C.D * p.2 ≤ classCount p q) ∧
      (∀ q ∈ hiFac p, C.D * p.2 * q.1 ≤ classCountHi p q)       -- local forcing
  hexhaust : ∀ p ∈ sides,                                       -- exhaustion
      Multiset.sum ((linFac p).map (classCount p))
        + Multiset.sum ((hiFac p).map (classCountHi p)) = rootCount p
  /-- root-preserving continuation: the `(SEC-RANK)` carrier (`EFF.T2.26`). -/
  W : Type uW        -- this field's universe IS `uW` (third parameter; see the note above)
  wf : WellFoundedRelation W
  σRank : W                                                     -- the state's rank

/-! ## Gate (executed `example`s, not blueprint declarations)

Two things a definitional node can get wrong silently, checked here rather than asserted.

**(a) The E-D6 quantifier pattern elaborates.** The defect the amendment fired on is not visible
at the structure's own declaration — it appears only at a `Prop` that quantifies over an
interface. The gate reproduces exactly that shape (E.24/E.39/E.40/E.44's), so a regression in the
universe plumbing fails HERE, in E.12's own file, rather than four nodes downstream.

**(b) The count fields do not collide.** `hresdeg`, `haccount`, `hforce`, `hnonempty` and
`hexhaust` are five simultaneous constraints on the same numbers; if they were jointly
unsatisfiable every consumer of `RungInterface` would be vacuous. A FULL instance (a real
`SlotCarrier`/`BlockData` with polynomial data) is E.22/E.23's obligation, and is deliberately
NOT attempted here — what the gate checks is the arithmetic shadow those five fields impose on
one side, which is where a collision would live.

The second example is the sharper one: on a side carrying one linear and one degree-2 residual
factor, `hforce`'s lower bounds and `hexhaust`'s total are **saturated** — the two class counts
are pinned to exactly `D·ℓ` and `2·D·ℓ`. So `hforce` is not slack decoration bolted onto
`hexhaust`; the two together determine the counts. -/

section Gate

-- (a) the E-D6 pattern: a `Prop` quantifying over an interface, with `uW` bound explicitly.
example : Prop :=
  ∀ {O : Type uO} [CommRing O] {K : Type uK} [Field K] (C : SlotCarrier O K) (B : BlockData C),
    Nonempty (RungInterface.{uO, uK, uW} C B)

-- (b) shadow consistency: one side, one linear residual factor of multiplicity 1. Reading
-- `ℓ = p.2`, `hresdeg` is `ℓ·1 = len`, `haccount` is `rootCount = D·len`, `hnonempty` is
-- `1 ≤ classCount`, `hforce` is `D·ℓ ≤ classCount`, `hexhaust` is `classCount = rootCount`.
example : ∃ D ℓ len rootCount classCount : ℕ,
    1 ≤ D ∧ 1 ≤ ℓ ∧ ℓ * 1 = len ∧ rootCount = D * len ∧
      1 ≤ classCount ∧ D * ℓ ≤ classCount ∧ classCount = rootCount :=
  ⟨2, 3, 3, 6, 6, by norm_num⟩

-- (b′) saturation: with a linear factor and a degree-2 factor on one side, `hresdeg` gives
-- `len = 3ℓ` and `haccount` gives `rootCount = 3·(D·ℓ)`; `hforce`'s two bounds plus `hexhaust`
-- then force equality in both, so no slack is available anywhere.
example (c a b : ℕ) (hfa : c ≤ a) (hfb : 2 * c ≤ b) (hex : a + b = 3 * c) :
    a = c ∧ b = 2 * c := by omega

end Gate

end Uniformity.Density.Ladder

/-! ## Axiom footprint

Definitional node. The structure former asserts nothing about its fields, so the five clause
families are printed one by one alongside the type former and its constructor. -/

section AxCheck

#print axioms Uniformity.Density.Ladder.RungInterface
#print axioms Uniformity.Density.Ladder.RungInterface.mk
#print axioms Uniformity.Density.Ladder.RungInterface.hlen_sum
#print axioms Uniformity.Density.Ladder.RungInterface.hresdeg
#print axioms Uniformity.Density.Ladder.RungInterface.haccount
#print axioms Uniformity.Density.Ladder.RungInterface.hnonempty
#print axioms Uniformity.Density.Ladder.RungInterface.hforce
#print axioms Uniformity.Density.Ladder.RungInterface.hexhaust
#print axioms Uniformity.Density.Ladder.RungInterface.wf

end AxCheck
