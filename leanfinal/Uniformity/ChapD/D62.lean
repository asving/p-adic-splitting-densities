/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapD.D04
import Uniformity.ChapD.D07

/-!
# Uniformity.ChapD.D62 — `HVarthetaRes`, the sitewise `(H-VARTHETA-RES)_i` carrier

**Chapter D, NODE D.62** [def] [fresh], at the **A-D.2 / DECISION D-2 RE-SIGNED signature**
(`blueprint/CHAP-D_gauge_tchain.md` §9, amendment A-D.2, 2026-08-16). ENV-D2 + ENV-D3.
Landed by unit OM-8 (`docs/openmath-campaign/OM-8_deep-twist_2026-08-16.md`), byte-matching
the leanspec landing (`leanspec/Leanspec/ChapD.lean` §9, commit d420f112) modulo the
namespace (`Uniformity.Density.Gauge` per GC-6.2, not the leanspec wrapper).

*The `(H-VARTHETA-RES)_i` carrier, SITEWISE.* The corpus's fence (`EFF.T1.09` R9-2): at
depth `i ≥ 3` every consumer of `ϑ_{i,s}`/`Θ_i(t)` carries

  `(H-VARTHETA-RES)_i : res(n̂_i(u_{i+1})^s / n̂_i(su_{i+1})) ∈ K_i   (s ≥ 0)`.

The Lean carrier is that display verbatim, over the level's height data `(N, v)` and a GIVEN
ambient residue datum `ρ : ker v →* Lˣ` (`L` the ambient residue field, `K = K_i` the level
field embedded in it), at the level's fixed use-height `q = u_{i+1}` (a parameter — exactly
source scope): every ϑ-quotient `n̂(q)^s/n̂(sq)` has value zero AND its ambient residue is
(the image of) a `K_i`-unit.

## Faithfulness

**⚠ Mandatory, trust-boundary definition.** Three points:

* *This is the A-D.2 form ONLY.* The COMMITTED existential form
  `HVarthetaResVoided G K N v := ∃ A : GaugeArena G K N, A.v = v` was machine-REFUTED as a
  carrier (defect D-D12: it is discharged by the trivial hom and provably equivalent to the
  exact-height fact). Per CHAP-I I.10's dated consumption note item 2, **no consumer or
  discharge may cite the voided form**; it is deliberately NOT re-landed in this tree — the
  permanent refutation record stays at `leanspec/Leanspec/ChapD.lean` (named-and-voided) and
  `verification/om4_shadow_vacuity.lean` / `om4_resign_nontriviality.lean`.
* *Non-fabricability.* With `ρ` GIVEN the trivial-hom trick dies: the carrier's truth depends
  on where `ρ` sends the ϑ-quotients — machine-certified FALSE at a concrete instance
  (`verification/om4_resign_nontriviality.lean`), and FALSE at REAL tower exponents under an
  adversarial `ρ` (`verification/om8_vartheta_deep.py` LEG D2). It is NOT a theorem of
  exact-height arithmetic; discharging it at an instance is exactly supplying the letter law
  for the canonical residue read (D62w's reduction + the OM-8 unit note §3.1).
* *The D-H3 direction, restored honestly* (`hvarthetaRes_of_arena_agree` below): an arena
  whose `res` AGREES with `ρ` through the level-field embedding discharges the sitewise
  carrier — `GaugeArena`-as-THEOREM-HYPOTHESIS is formally stronger, in exactly that sense
  and no other.

DEPENDS: D.01, D.04 (`varthetaEl`), D.07 (`GaugeArena`, for the proved lemma). The
kernel-membership fact `GaugeArena.varthetaEl_mem_ker` is D.08's; D.08 has not landed in
this tree, so the fact is PROVED here (not axiomatized) and D.08 may later re-export it.

SOURCE: `EFF.T1.09` (the fence + the displayed hypothesis), `EFF.T5.10` (the carry at every
`i ≥ 3` `Θ`-use); DECISION D-2 grounds 1–3. Consumed by E (ladder displays at `i ≥ 3`) and I
(Display A's `∀ i ≥ 3` conjunct, via D.63) — at THIS form only.

## Status

Sorry-free, axiom-free (Lean core only).
-/

namespace Uniformity.Density.Gauge

/-- **D.08's kernel-membership fact** (proved here because D.08 has not landed in this tree):
the ϑ-element `n̂(q)^s·n̂(sq)⁻¹` has value zero at any arena — exact-height arithmetic
(`EFF.T1.09`'s CONDITIONALITY line: "The quotient and residue exist from exact-height
arithmetic"). -/
theorem GaugeArena.varthetaEl_mem_ker {G K : Type*} [CommGroup G] [Field K]
    {N : NormSection G} (A : GaugeArena G K N) (q : ℤ) (s : ℕ) :
    N.varthetaEl q s ∈ MonoidHom.ker A.v := by
  rw [MonoidHom.mem_ker, NormSection.varthetaEl, map_mul, map_inv, map_pow,
    A.exact_height, A.exact_height, ← ofAdd_nsmul]
  simp

/-- The Lean carrier of `(H-VARTHETA-RES)_i` (`EFF.T1.09` R9-2 fence), SITEWISE against a
GIVEN ambient residue datum [RE-SIGNED: A-D.2 / DECISION D-2]. Consumed by E (ladder
displays at `i ≥ 3`) and I (Display A's `∀ i ≥ 3` conjunct, via D.63) — at THIS form only;
the pre-A-D.2 existential form is `HVarthetaResVoided` (leanspec, VOID — not re-landed). -/
def HVarthetaRes (G : Type*) [CommGroup G] (K : Type*) [Field K] (L : Type*) [Field L]
    [Algebra K L] (N : NormSection G) (v : G →* Multiplicative ℤ)
    (ρ : MonoidHom.ker v →* Lˣ) (q : ℤ) : Prop :=
  ∀ s : ℕ, ∃ (h : N.varthetaEl q s ∈ MonoidHom.ker v) (u : Kˣ),
    ((ρ ⟨N.varthetaEl q s, h⟩ : Lˣ) : L) = algebraMap K L (u : K)

/-- [PROVED at A-D.2] The D-H3 direction, restored honestly: an ambient-agreeing arena
discharges the sitewise carrier. -/
theorem hvarthetaRes_of_arena_agree {G : Type*} [CommGroup G] {K : Type*} [Field K]
    {L : Type*} [Field L] [Algebra K L] {N : NormSection G} (A : GaugeArena G K N)
    (ρ : MonoidHom.ker A.v →* Lˣ)
    (hagree : ∀ x : MonoidHom.ker A.v, ((ρ x : Lˣ) : L) = algebraMap K L ((A.res x : Kˣ) : K))
    (q : ℤ) : HVarthetaRes G K L N A.v ρ q :=
  fun s => ⟨A.varthetaEl_mem_ker q s, A.res ⟨_, A.varthetaEl_mem_ker q s⟩, hagree _⟩

end Uniformity.Density.Gauge

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Gauge.GaugeArena.varthetaEl_mem_ker
#print axioms Uniformity.Density.Gauge.HVarthetaRes
#print axioms Uniformity.Density.Gauge.hvarthetaRes_of_arena_agree

end AxCheck
