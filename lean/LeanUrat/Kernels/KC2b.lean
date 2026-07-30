/-
Kernels/KC2b — BP4-c5 E-phase skeleton for unit KC2b: the `DomProj` named law
+ the derivation attempt from the XHDd law fields
(BRIDGE_BP4_KERNELS_2026-07-30.md REV 2, §3.C + §4 KC2b; risk R4;
adjudications per BRIDGE_ADJUDICATIONS_2026-07-30.md BP4 block).

FILE PLACEMENT (recorded resolution): the blueprint's KC home
Kernels/HmcReduction.lean exists (sibling cluster BP4-c2: KC2a/KC3/KC4) and
may not be modified; per its file-scope note the named `DomProj` def is
KC2b's and lands here.  <UnitId>.lean naming.

GATE SEQUENCING (REV 2, F5): KC2a — the DomProj countermodel attempt — is ON
RECORD as a sorried skeleton at Kernels/HmcReduction.lean and is SEQUENCED
BEFORE this unit's prover.  The gate is a scheduling constraint, not an
import: this file imports only MovesV.Defs.

RECORDED RESOLUTION (the "conditional on KC2a's outcome" clause): the
UNRESTRICTED derivation target `∀ TE D, DomProj TE D` is NOT stated in this
file.  Reason: it is already dead in-corpus — KC1's leg (iii)
(Kernels/KC1.lean, `hmcToy_proj_dir_fails_deep`) records that `HmcToy`
violates the DomProj implication at deep tails (γ composite, h₂ = 0), so a
sorried bare universal would be engineered to coexist with a compiled
negation witness once KC1 lands — the cross-area M1-soundness rule forbids
exactly that.  The surviving derivation surface, minimal against the XHDd/
TmplEvents law fields, is the ONE-STEP-TAIL scope: there `tmark_last_surj`/
`tmark_lastT_surj` (surjectivity of the mark map, available ONLY at one-step
templates) convert combinatorial chain projections into census positivity,
and no_stray/no_orphan close the loop.  The two scoped attempts below carry
that route; `DomProj` itself stays the ⚑ named hypothesis (Q4-sanctioned
shape: hypothesis of reduction theorems, NEVER a new field on the frozen
`XHDd`), consumed by KC5.

deps: KC2a (CM gate — sequenced first), MovesV.Defs vocabulary.
difficulty: hard-fable, ~50 ln.  [ATTEMPT with pre-declared fallback: if the
scoped derivations also stall, DomProj stays a bare named hypothesis and the
obstruction record names the failing law step — never a silent sorry.]

Build: cd lean && lake build LeanUrat.Kernels.KC2b
-/
import LeanUrat.MovesV.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false

namespace LeanUrat.Kernels

open LeanUrat.MovesV

/-- Fin-append splitter identity (private re-derivation; the original
`hpt_take_append` is `private` in MovesV/V4_naming.lean, hence not
importable). -/
private lemma hpt_take_append {D₁ D₂ : ℕ} (h₁ : Hpt D₁) (h₂ : Hpt D₂) :
    Hpt.take (Hpt.append h₁ h₂) = h₁ := by
  funext i; simp only [Hpt.take, Hpt.append, Fin.append_left]

/-- Fin-append splitter identity (private re-derivation, as above). -/
private lemma hpt_drop_append {D₁ D₂ : ℕ} (h₁ : Hpt D₁) (h₂ : Hpt D₂) :
    Hpt.drop (Hpt.append h₁ h₂) = h₂ := by
  funext j; simp only [Hpt.drop, Hpt.append, Fin.append_right]

/-- KC2b — `DomProj`, the ⊆/projection leg of HMC as a NAMED law (⚑ Q4
named-law ratification): a realized composite history realizes its steps —
composite domain membership at an appended height point projects to the two
factor memberships.  Binder shape mirrors `MovesV.HMC` (Defs.lean:1180) and
the sibling `MarkCompose` (Kernels/HmcReduction.lean) verbatim; HMC TE D is
then definitionally DomProj ∧ MarkCompose pointwise (KC5's assembly).
Consumers: KC5 (`hmc_of_domProj_markCompose`), the KC2a gate record.
Instance facts on record once KC1 lands: DomProj FAILS at `HmcToy` (deep
tails — KC1 leg (iii)); its depth-2 restriction holds there (KC1 leg (ii)). -/
def DomProj {n : ℕ} {S : StepSys n} (TE : TmplEvents n S)
    (D : XHDd n S TE) : Prop :=
  ∀ {α β : S.Cell} (m : S.Move α β) (γ : Template n S β)
    (h₁ : Hpt (S.dim m)) (h₂ : Hpt γ.D),
    (D.dom (.cons m γ)).Mem (Hpt.append h₁ h₂) →
      (D.dom (.last m)).Mem h₁ ∧ (D.dom γ).Mem h₂

/-- KC2b [ATTEMPT] — the scoped derivation, `.last`-tail leg: at one-step
tails the projection direction follows from the law fields alone.  Sketch:
`no_stray` at the composite (with a pool `q₀ ∈ S.Pools` from `S.pools_ne`
and a zc history from `S.zc_ne`) gives 0 < Tgam at the appended point; a
mark's chain (`tmark`) is a Σ-pair: a head assignment at `Hpt.take (append
h₁ h₂) = h₁` and a tail chain at `Hpt.drop (append h₁ h₂) = h₂`; head:
`Nonempty (Assign m x h₁)` + `tmark_last_surj` ⟹ 0 < Tgam (.last m) x h₁ ⟹
`no_orphan` gives the first membership; tail: the extended history
(`S.ext`, zc by `ext_zc`) + `tmark_last_surj` at `.last m₂` gives the
second.  FALLBACK (pre-declared): if the take/append identities or the
surjectivity plumbing stall, record the exact law step and leave DomProj a
bare hypothesis. -/
theorem domProj_lastTail_of_laws {n : ℕ} {S : StepSys n}
    (TE : TmplEvents n S) (D : XHDd n S TE)
    {α β β' : S.Cell} (m : S.Move α β) (m₂ : S.Move β β')
    (h₁ : Hpt (S.dim m)) (h₂ : Hpt (S.dim m₂))
    (hmem : (D.dom (.cons m (.last m₂))).Mem (Hpt.append h₁ h₂)) :
    (D.dom (.last m)).Mem h₁ ∧ (D.dom (.last m₂)).Mem h₂ := by
  -- pool + zc history supply
  obtain ⟨q₀, hq₀⟩ := S.pools_ne
  obtain ⟨x, hzc⟩ := S.zc_ne q₀ hq₀ α
  -- `no_stray` at the composite: census positivity at the appended point
  have hpos : 0 < Tgam TE (.cons m (.last m₂)) x (Hpt.append h₁ h₂) :=
    D.no_stray _ _ hmem hq₀ x hzc
  obtain ⟨b, hb⟩ := Finset.card_pos.mp hpos
  -- a mark's chain is a Σ-pair: head assignment at `take`, tail chain at `drop`
  have hchain : Σ a : S.Assign m x (Hpt.take (Hpt.append h₁ h₂)),
      Chains S (.last m₂) (S.ext m x (Hpt.take (Hpt.append h₁ h₂)) a)
        (Hpt.drop (Hpt.append h₁ h₂)) :=
    TE.tmark (.cons m (.last m₂)) x (Hpt.append h₁ h₂) ⟨b, hb⟩
  obtain ⟨a, c⟩ := hchain
  have hzc' : S.zc (S.ext m x (Hpt.take (Hpt.append h₁ h₂)) a) :=
    S.ext_zc m x _ a hzc
  constructor
  · -- head leg: `tmark_last_surj` converts the assignment into census positivity
    rw [← hpt_take_append h₁ h₂]
    obtain ⟨b₁, -⟩ := TE.tmark_last_surj m x (Hpt.take (Hpt.append h₁ h₂)) hq₀ hzc a
    exact D.no_orphan _ x _ hq₀ hzc (Finset.card_pos.mpr ⟨b₁.1, b₁.2⟩)
  · -- tail leg: same route at the extended (zc, by `ext_zc`) history
    rw [← hpt_drop_append h₁ h₂]
    obtain ⟨b₂, -⟩ := TE.tmark_last_surj m₂
      (S.ext m x (Hpt.take (Hpt.append h₁ h₂)) a)
      (Hpt.drop (Hpt.append h₁ h₂)) hq₀ hzc' c
    exact D.no_orphan _ _ _ hq₀ hzc' (Finset.card_pos.mpr ⟨b₂.1, b₂.2⟩)

/-- KC2b [ATTEMPT] — the scoped derivation, `.lastT`-tail leg: same route
with `tmark_lastT_surj` on the terminal tail. -/
theorem domProj_lastTTail_of_laws {n : ℕ} {S : StepSys n}
    (TE : TmplEvents n S) (D : XHDd n S TE)
    {α β : S.Cell} {v : VLabel n} (m : S.Move α β) (mT : S.MoveT β v)
    (h₁ : Hpt (S.dim m)) (h₂ : Hpt (S.dimT mT))
    (hmem : (D.dom (.cons m (.lastT mT))).Mem (Hpt.append h₁ h₂)) :
    (D.dom (.last m)).Mem h₁ ∧ (D.dom (.lastT mT)).Mem h₂ := by
  obtain ⟨q₀, hq₀⟩ := S.pools_ne
  obtain ⟨x, hzc⟩ := S.zc_ne q₀ hq₀ α
  have hpos : 0 < Tgam TE (.cons m (.lastT mT)) x (Hpt.append h₁ h₂) :=
    D.no_stray _ _ hmem hq₀ x hzc
  obtain ⟨b, hb⟩ := Finset.card_pos.mp hpos
  have hchain : Σ a : S.Assign m x (Hpt.take (Hpt.append h₁ h₂)),
      Chains S (.lastT mT) (S.ext m x (Hpt.take (Hpt.append h₁ h₂)) a)
        (Hpt.drop (Hpt.append h₁ h₂)) :=
    TE.tmark (.cons m (.lastT mT)) x (Hpt.append h₁ h₂) ⟨b, hb⟩
  obtain ⟨a, c⟩ := hchain
  have hzc' : S.zc (S.ext m x (Hpt.take (Hpt.append h₁ h₂)) a) :=
    S.ext_zc m x _ a hzc
  constructor
  · rw [← hpt_take_append h₁ h₂]
    obtain ⟨b₁, -⟩ := TE.tmark_last_surj m x (Hpt.take (Hpt.append h₁ h₂)) hq₀ hzc a
    exact D.no_orphan _ x _ hq₀ hzc (Finset.card_pos.mpr ⟨b₁.1, b₁.2⟩)
  · rw [← hpt_drop_append h₁ h₂]
    obtain ⟨b₂, -⟩ := TE.tmark_lastT_surj mT
      (S.ext m x (Hpt.take (Hpt.append h₁ h₂)) a)
      (Hpt.drop (Hpt.append h₁ h₂)) hq₀ hzc' c
    exact D.no_orphan _ _ _ hq₀ hzc' (Finset.card_pos.mpr ⟨b₂.1, b₂.2⟩)

end LeanUrat.Kernels
