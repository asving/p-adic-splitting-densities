/-
Unit U18.presentNorm_unique  (HC-2 campaign, E-phase — blueprint §5 Layer C)
moves_ref: MovesD §3.2 clause (ii) "UNIQUENESS (embedding rigidity)"; the note's
§D4-R L3 prefix-identity display and §B2-DEF D.10.
deps: MovesD canonRoot/ψImage; MovesC HistoryCoherent tower (child_field /
IsRecentering); mathlib.  difficulty: hard.

REV 3 = U18-ADJUDICATION (2026-07-28, the note read — supersedes the K3 rev 2 form,
which was REFUTED: `lean/scratch_U18_adjacent_refuted.lean` compiles green and kills the
`AdjacentReads`-guarded statement; `lean/scratch_U18_unique_false.lean` had already killed
the unguarded rev-1/`OmUniqHyp` form. Both scratches stand as machine records).

VERDICT OF THE NOTE READ: **BLUEPRINT-OVERSTRENGTH** — the refuted strength was
introduced at MOVESD blueprint REV 5 (PresentNorm clause (ii), sourced to audit finding
Fable#2 C1), NOT asserted by the note. The note's displays:
* §D4-R L3 (MOVES_2026-07-24.md ~4747-4753): "Prefix order: η ⪯ η′ iff η is an initial
  segment of the chain η′ (LITERAL NODE-DATA + LIFT EQUALITY) … Pref(P̂) := { η :
  shape(η) = P̂, η realizable, canonical lifts }, C_P̂(p) := #Pref(P̂)" — η-identity is
  literal value data in the tower; the note NEVER quotients η's by an ambient Galois
  action (it has no ambient field at all).
* §B2-DEF D.10 (~2592, 2608-2611): "the classifier's recentering datum is a center
  c̃ ∈ Fˣ" — the center is free η-data (distinct centers = distinct η's); the ONLY
  (v, dig)-style identification the note makes is LIFT independence: "Everything below
  depends on t only through [t] ∈ gr_v(A), i.e. through (v(t), dig(t))" — lifts only,
  and polOM already normalizes lifts away.
* §C LIFT-TRANSLATION REMARK (~3480-3488) + C.0.5 (~3558): the unitriangular/conjugating
  transports carry strata of one history onto strata of the TRANSPORTED history ("with
  downstream data held literally fixed, NO CORRESPONDENCE IS CLAIMED") — equal masses
  between distinct η's, never an identification.
The clause-(ii) charge (audit Fable#2 C1's repair direction) is: "each note-η has
exactly ONE canonical presentation chain". Two ambient presentations of ONE note-η are
related by an ambient automorphism transporting the FULL per-read value data — the
tower-embedding witnesses `zbar` INCLUDED — over a pointwise-FIXED base frame (the
audit's own witness conjugated the stage maps and both zbar choices, φ "fixing the
prime-field root data"). `EtaGalEq` (the rev-5 typing) relates only the etaData
PROJECTION, which FORGETS the embedding witnesses — a strictly coarser relation. Both
refutation witnesses live exactly in the gap: they conjugate the LAST node's values over
a SHARED, PINNED node-0 (same zbar₀), producing presentations of two DISTINCT note-η's
(centers c̃ vs φ(c̃)) that the note COUNTS SEPARATELY (C_P̂* gate: 3 classes, not 2).
Collapsing them (as clause (ii) as typed demands) would UNDERCOUNT the note's C.

THE RESTATED UNIQUENESS (this file, note-supported): Galois transport of the FULL
presentation — base frame field pointwise fixed, per-read transport of the residue root
`zbar`, the ψ-image, and the side digits (`HistGalTransport`) — between normalized
(PrefSet) members forces EQUAL η-data. This is embedding RIGIDITY proper: the least-root
normalization pins the root at every read (zbar' = canonRoot' = canonRoot = zbar forces
φ(zbar) = zbar), and the coherence tower (`child_field : σ'.K = K⟮z̄⟯`; recenterings:
`σ'.K = σ.K`) then propagates pointwise φ-fixedness up the frame fields, so ALL recorded
values are φ-fixed and the transported η-data coincide. PROVED sorry-free below (Lean
core axioms only).

BOTH REFUTATIONS DIE against this form: for the scratch witnesses, `HistGalTransport φ`
at the shared node 0 forces φ(zbar₀) = zbar₀, and the tower then forces φ to fix
σ₁.K ∋ center pointwise — contradicting the witnesses' `hmove` ((center)² ≠ center).
Formally: this theorem is PROVED, so no witness can satisfy its hypotheses and deliver
distinct η-data; the scratch pairs simply fail `HistGalTransport` (their φ = Frobenius
moves zbar₀ — a root of the degree-2 ψ₀ forced by hmove through the tower — while the
transport clause at the shared node 0 demands it be fixed).

CONSEQUENCE FOR CONSUMERS (unchanged from K3 scope record): `PresentNorm`'s clause (ii)
and `OmUniqHyp` AS TYPED remain conditionally refuted (`omUniqHyp_refuted_by_witness`);
the K3 fence on `presentNorm_polOM` stands. The wave-4 dictionary negotiation should
retype clause (ii) to THIS transport-keyed form (a MovesD-blueprint designer-round
event, out of this unit's scope). The `hbr`-drop standing probe (blueprint §3 P-3)
remains permanent.
hypothesis_fields: φ + HistGalTransport (U18-ADJ; the K3 hadj/hadj' guards are
REMOVED — refuted as insufficient, superseded by the transport keying).
-/
import Mathlib
import LeanUrat.HC2.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesJ
open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

/-- The fixed subfield of an ambient field automorphism (the rigidity target: frame
fields land here pointwise, up the tower). -/
def galFixedSubfield {F : Type*} [Field F] (φ : F ≃+* F) : Subfield F where
  carrier := {x : F | φ x = x}
  zero_mem' := map_zero φ
  one_mem' := map_one φ
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, map_add] at *
    rw [ha, hb]
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, map_mul] at *
    rw [ha, hb]
  neg_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq, map_neg] at *
    rw [ha]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq, map_inv₀] at *
    rw [ha]

@[simp] lemma mem_galFixedSubfield {F : Type*} [Field F] {φ : F ≃+* F} {x : F} :
    x ∈ galFixedSubfield φ ↔ φ x = x := Iff.rfl

/-- Tower step: if `φ` fixes the frame field pointwise and fixes the adjoined residue
root, it fixes the next frame field `K⟮z̄⟯` pointwise (D.6/D.7(v) growth is by ONE
generator). -/
lemma nextField_le_galFixed {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    {σ : Stage p F} {zbar : Fˣ} {φ : F ≃+* F}
    (hK : ∀ x ∈ σ.K, φ x = x) (hz : φ ((zbar : Fˣ) : F) = ((zbar : Fˣ) : F)) :
    σ.nextField zbar ≤ galFixedSubfield φ := by
  refine Subfield.closure_le.mpr ?_
  rintro y (hy | hy)
  · exact hK y hy
  · rw [Set.mem_singleton_iff] at hy
    subst hy
    exact hz

/-- `canonRoot` is a function of the ψ-image alone. -/
lemma canonRoot_congr {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    {ν ν' : Node p F} (h : ψImage ν' = ψImage ν) :
    canonRoot ν' = canonRoot ν := by
  unfold canonRoot
  rw [h]

/-- **FULL-HISTORY GALOIS TRANSPORT** (the U18-ADJUDICATION relation — "H and H' are
ambient presentations of ONE note-η"): the base frame field is pointwise `φ`-fixed (the
note's tower starts at a FIXED base — the residue field of the ground field; re-rooting
freedom lives in the DESCEND steps, D.6/D.7, never at the base), and at every read `φ`
transports the FULL value data: the recorded residue root `zbar` (the tower-embedding
witness — exactly what `EtaGalEq` forgot), the ψ-image, and the side digits. -/
def HistGalTransport {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (φ : F ≃+* F) (H H' : History p F) : Prop :=
  (∀ (h0 : 0 < H.nodes.length) (x : F), x ∈ (H.nodes[0]'h0).σ.K → φ x = x) ∧
  H'.nodes.length = H.nodes.length ∧
  ∀ (r : ℕ) (hr : r < H.nodes.length) (hr' : r < H'.nodes.length),
    (((H'.nodes[r]'hr').zbar : Fˣ) : F) = φ (((H.nodes[r]'hr).zbar : Fˣ) : F) ∧
    ψImage (H'.nodes[r]'hr') = (ψImage (H.nodes[r]'hr)).map (φ : F →+* F) ∧
    ∀ k : ℕ, (H'.nodes[r]'hr').sideDigit k = φ ((H.nodes[r]'hr).sideDigit k)

/-- UNIQUENESS, TRANSPORT-KEYED (U18-ADJUDICATION restatement): normalized presentation
classes are RIGID — two PrefSet members related by a full-history Galois transport (one
note-η, two tower embeddings over the fixed base) have EQUAL η-data. The least-root
normalization pins the residue root at every read; the coherence tower propagates the
base's pointwise φ-fixedness through every frame field; hence every recorded value is
φ-fixed and the transport clauses collapse to equality. -/
theorem presentNorm_unique {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    {n : ℕ} {P : Shape n} :
    ∀ H H' : History p F,
      H ∈ PrefSet n (polOM p F) P → H' ∈ PrefSet n (polOM p F) P →
      (∃ φ : F ≃+* F, HistGalTransport φ H H') →
      etaData (P : ShapePrefix) H = etaData (P : ShapePrefix) H' := by
  intro H H' hH hH' hT0
  obtain ⟨φ, hbase, hlen, hT⟩ := hT0
  obtain ⟨hMatch, hCoh, hReal, hBox, hCanon, hZbar⟩ := hH
  obtain ⟨hMatch', hCoh', hReal', hBox', hCanon', hZbar'⟩ := hH'
  classical
  -- (1) TOWER RIGIDITY: φ fixes every frame field pointwise, by induction up the tower.
  have key : ∀ (r : ℕ) (hr : r < H.nodes.length),
      ∀ x : F, x ∈ (H.nodes[r]'hr).σ.K → φ x = x := by
    intro r
    induction r with
    | zero => exact fun hr x hx => hbase hr x hx
    | succ r ih =>
      intro hr1 x hx
      have hr : r < H.nodes.length := by omega
      have hr' : r < H'.nodes.length := by omega
      -- φ fixes the read-r ψ-image (its coefficients live in the φ-fixed frame field)
      have hψfix : (ψImage (H.nodes[r]'hr)).map (φ : F →+* F) = ψImage (H.nodes[r]'hr) := by
        ext k
        rw [Polynomial.coeff_map]
        refine ih hr _ ?_
        show ((H.nodes[r]'hr).ψ.map (H.nodes[r]'hr).σ.K.subtype).coeff k ∈ _
        rw [Polynomial.coeff_map]
        exact SetLike.coe_mem _
      obtain ⟨hz, hψ, -⟩ := hT r hr hr'
      have hψeq : ψImage (H'.nodes[r]'hr') = ψImage (H.nodes[r]'hr) := by
        rw [hψ, hψfix]
      -- BOTH normalized ⟹ φ fixes the read-r residue root (least-root rigidity)
      have hzfix : φ (((H.nodes[r]'hr).zbar : Fˣ) : F) = (((H.nodes[r]'hr).zbar : Fˣ) : F) := by
        rw [← hz, hZbar' r hr', canonRoot_congr hψeq, hZbar r hr]
      -- the coherence tower step carries φ-fixedness to the next frame field
      obtain ⟨-, -, -, hchain⟩ := hCoh
      have hstep := hchain r hr1
      by_cases hrec : (H.nodes[r]'hr).species = ReadSpecies.recentering
      · -- recentering: no residue growth (IsRecentering: σ'.K = σ.K)
        have hrc := hstep.1 hrec
        obtain ⟨-, -, -, -, -, -, -, -, -, -, hKK, -⟩ := hrc.base
        have hKK' : (H.nodes[r + 1]'hr1).σ.K = (H.nodes[r]'hr).σ.K := hKK
        exact ih hr x (hKK' ▸ hx)
      · -- increment/root species: child field = K⟮z̄⟯ (TransitionData.child_field)
        have hTC := (hstep.2.1 hrec).2
        have hcf : (H.nodes[r + 1]'hr1).σ.K
            = (H.nodes[r]'hr).σ.nextField (H.nodes[r]'hr).zbar := hTC.base.child_field
        exact nextField_le_galFixed (ih hr) hzfix (hcf ▸ hx)
  -- (2) η-DATA EQUALITY: every recorded value is φ-fixed; the transport collapses.
  obtain ⟨hlenP, -⟩ := hMatch
  funext r
  have hrH : (r : ℕ) < H.nodes.length := by rw [hlenP]; exact r.isLt
  have hrH' : (r : ℕ) < H'.nodes.length := by omega
  obtain ⟨-, hψ, hdig⟩ := hT (r : ℕ) hrH hrH'
  have hψfix : (ψImage (H.nodes[(r : ℕ)]'hrH)).map (φ : F →+* F)
      = ψImage (H.nodes[(r : ℕ)]'hrH) := by
    ext k
    rw [Polynomial.coeff_map]
    refine key _ hrH _ ?_
    show ((H.nodes[(r : ℕ)]'hrH).ψ.map (H.nodes[(r : ℕ)]'hrH).σ.K.subtype).coeff k ∈ _
    rw [Polynomial.coeff_map]
    exact SetLike.coe_mem _
  have hψeq : ψImage (H'.nodes[(r : ℕ)]'hrH') = ψImage (H.nodes[(r : ℕ)]'hrH) := by
    rw [hψ, hψfix]
  have e1 : H.nodes[(r : ℕ)]? = some (H.nodes[(r : ℕ)]'hrH) :=
    List.getElem?_eq_getElem hrH
  have e1' : H'.nodes[(r : ℕ)]? = some (H'.nodes[(r : ℕ)]'hrH') :=
    List.getElem?_eq_getElem hrH'
  simp only [etaData, e1, e1', Option.elim_some]
  congr 1
  · funext k
    rw [hdig (k : ℕ)]
    exact (key _ hrH _ (SetLike.coe_mem _)).symm
  · funext k
    have hc := congrArg (fun q : Polynomial F => q.coeff (k : ℕ)) hψeq
    simp only [ψImage, Polynomial.coeff_map] at hc
    exact hc.symm

-- axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms presentNorm_unique

end LeanUrat.MovesJ
