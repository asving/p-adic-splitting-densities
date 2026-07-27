/-
Unit U17c.presentNorm_total  (HC-2 campaign, E-phase — blueprint §5 Layer C)
moves_ref: MovesD `PresentNorm` clause (i) — TOTALITY.
deps: U17a + U17b + membership bookkeeping (H' ∈ PrefSet → its class is a PrefIdx
member); the assembled `presentNorm_polOM` additionally consumes U18.
difficulty: medium.  hypothesis_fields: inherits U17a's stage supplier (`StageTransHyp`).
-/
import Mathlib
import LeanUrat.HC2.Defs
import LeanUrat.HC2.U17a_liftSwap
import LeanUrat.HC2.U17b_galois
import LeanUrat.HC2.U18_unique

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesJ
open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

/-- The TOTALITY clause of `PresentNorm n (polOM p F) P`: every policy-free realizable
prefix has a normalized class-mate up to Galois. -/
theorem presentNorm_total {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    {n : ℕ} {P : Shape n} (hst : StageTransHyp p F) :
    ∀ H : History p F, H ∈ PrefSetAny n P →
      ∃ i : PrefIdx n (polOM p F) P,
        EtaGalEq (etaData (P : ShapePrefix) H) i.1 := by
  intro H hH
  -- U17a `lift_swap`: canonical-lift (`IsCanon`), same-η class-mate.
  obtain ⟨H', hMatch', hEta', hCanon', hcoh', hreal', hbox'⟩ := lift_swap hst H hH
  -- U17b `galois_normalize`: root-normalize (`canonRoot`) up to a Galois automorphism.
  obtain ⟨φ, H'', hMatch'', hRoot'', hTrans'', hGal'', hcoh'', hreal'', hbox''⟩ :=
    galois_normalize (P := P) H' hMatch' hcoh' hreal' hbox'
  -- Membership bookkeeping: `H'' ∈ PrefSet` ⟹ its η-class is a `PrefIdx` member.
  have hmem : H'' ∈ PrefSet n (polOM p F) P := by
    refine ⟨hMatch'', hcoh'', hreal'', hbox'', ?_, hRoot''⟩
    -- OBSTRUCTION (unprovable from the current dependency STATEMENTS; not a proof gap in
    -- this unit).  Remaining goal, verified by the LSP:  `⊢ (polOM p F).IsCanon H''`.
    -- `PrefSet` membership needs `IsCanonPres = IsCanon ∧ canonRoot` on ONE history.
    -- ESCALATION RECORD (2nd prover, 2026-07-27): BOTH composition orders verified blocked,
    -- each by a missing output clause in a DIFFERENT dependency, and each post-hoc repair is
    -- barred STRUCTURALLY by a coherence clause that pins the swapped field at interior nodes:
    -- • THIS order (lift_swap → galois_normalize): `galois_normalize` (U17b) exposes NO
    --   `.lift`/polOM-canonicity clause, so `hCanon'` cannot transport to `H''`.  Post-hoc
    --   lift surgery on `H''` (set `lift := polOM.liftOf`; legal — no Node Prop field, no
    --   Matches/etaData/InBox/Realizable clause reads `.lift`) fails at interior RECENTERING
    --   nodes: `HistoryCoherent → IsRecenteringCore → IsRecentering` pins
    --   `σᵢ₊₁.Φ = σᵢ.Φ − liftᵢ` (Moves/Defs.lean:264), and the choice-defined
    --   `polOM.liftOf νᵢ` ≠ the recorded `σᵢ.Φ − σᵢ₊₁.Φ` in general (the spec's realizers
    --   form a coset — higher-valuation freedom — so no uniqueness rescue).  Repair = rebuild
    --   all downstream stages = U17a's own HARD content (StageTransHyp), not bookkeeping.
    -- • REVERSED order (galois_normalize → lift_swap): the canonRoot VALUES survive —
    --   `etaData H₂ = etaData H₁` + Matches (`g = R.g`) + `hψdeg`/`hψmonic` pin
    --   `ψImage ν₂ᵣ = ψImage ν₁ᵣ` coefficientwise, so `canonRoot ν₂ᵣ = (ν₁ᵣ.zbar : F)` —
    --   but the recorded `zbar₂ᵣ` is unconstrained by U17a's statement.  Post-hoc zbar
    --   surgery (`zbar₂ᵣ := zbar₁ᵣ`; `hzbarRoot`/`hspecRecCenter` survive) fails at interior
    --   nodes: `TransitionCoreL.child_dig` (Moves/DefsCore.lean:228-231) forces
    --   `(c' : F) = σ.digPrime zbar B · (zbar^m : F)` with `c'` pinned by the RECORDED child
    --   stage's `σ'.R B`, and `TransitionData.child_field` pins `σ'.K = σ.nextField zbar`
    --   (Moves/DefsT.lean:152) — a conjugate root needs the child stages φ-rebuilt = U17b-3's
    --   own content.  (Only the LAST node's zbar is coherence/realizability-free.)
    -- • No third source: U24 `readsOf_canonical` gives `IsCanonPres` only from a run
    --   (`ReadsOf f H` — no `f` exists for the transported mate); U25 `polOM_total`/
    --   `polOM_liftOf_spec` assert spec-realizer existence, never equality with the recorded
    --   lift; U18/OmUniqHyp are uniqueness, circular here.
    -- The mathematics is sound; the gap is a MISSING OUTPUT CLAUSE.  MINIMAL AMENDMENTS
    -- (statement-fence → needs sign-off), either suffices:
    -- (A) U17b [recommended]: add `((polOM p F).IsCanon H → (polOM p F).IsCanon H')` to
    --     `galois_transport`/`galois_normalize_upTo`/`galois_normalize`.  Sound by the
    --     intended construction: the transport fixes ℤ_p[X]-side data (`.lift`, `σ.Φ`, `σ.w`)
    --     and φ-conjugates residue data (K, center, R); `RecenterLiftSpec ν tL` is then
    --     INVARIANT (φ injective on the R-identity), so the choice-defined `polOM.liftOf`
    --     is unchanged node-by-node while the lift field is untouched — `IsCanon` transports
    --     verbatim.  Consumption here: one line (the clause applied to `hCanon'`).
    -- (B) U17a: add `∀ r hr hr', (H'.nodes[r]'hr).zbar = (H.nodes[r]'hr').zbar` to
    --     `lift_swap` (sound per the blueprint's own U17a sketch: "transport the remaining
    --     reads — their data are development-side, unchanged").  Consumption here: reversed
    --     order + the ψImage-from-η extraction above (≈40 lines).
    sorry
  refine ⟨⟨etaData (P : ShapePrefix) H'', ⟨H'', hmem, rfl⟩⟩, ?_⟩
  -- η(H') = η(H) and EtaGalEq (η H') (η H'') ⟹ EtaGalEq (η H) (η H'').
  rw [← hEta']
  exact hGal''

/-- ASSEMBLED (U17c + U18): the full typed dictionary pin `PresentNorm` at `polOM` —
U15/U16's `hnorm` discharger. -/
theorem presentNorm_polOM {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    {n : ℕ} {P : Shape n} (hst : StageTransHyp p F) :
    PresentNorm n (polOM p F) P :=
  ⟨presentNorm_total hst, presentNorm_unique⟩

end LeanUrat.MovesJ
