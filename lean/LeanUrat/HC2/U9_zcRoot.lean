/-
Unit U9.zc_root  (HC-2 campaign, E-phase — blueprint §5 Layer B, the (ZC) base)
moves_ref: §C C.2 proof "initialized at the root (C.1.5's base = D.8 + D.11 at ν₀)".
deps: U7, D6/D7, S.zcSeed, U11.  difficulty: hard — PRE-SPLIT (mandatory): U9a downset ⊆,
U9b ⊇, U9c interior_zero (the two `ZCData` fields, split).
hypothesis_fields: S.zcSeed.
RESTATED-POST-DEFS-REPAIR (2026-07-27): statement stands on the REPAIRED ZCSeedLaws.downsets_literal (chart-coverage guard added; box-truncation refuted by scratch_U9_presentSeed_false — blueprint §2.2 DC-1). Sorries retained for the next fleet round.
ESCALATION RECORD (2026-07-28, second prover): U9a PROVED (case split on the
`IsFreshAttach` witness existence: the no-witness branch degenerates to `topLocus`
(no pins, vacuous); the witness branch reads pins off `pinTransportSystem_spec`
clause (2) and transports the band's upper edge through the root floor bridge —
`κ₀ = slope·Dwidth`, `ustar` cancels, `root_height`/U11 NOT needed).
U9b / U9c / zc_root: STOP — unprovable as stated; the exact obstructions are recorded
at each sorry below. Headline: the F-7 "inlinable ∃-witness" premise is FALSE —
`IsFreshAttach` clauses (1)+(3) jointly force `S.Theta 0`'s unitriangular corrections
to vanish at every strip coordinate on the fresh locus, which no `PresentSeed` law
supplies (the same obstruction re-blocks U7.mkSigma_recursion despite DC-2).
DC-3 ADDENDUM (2026-07-28, K2 kernel round; statements byte-unchanged, the records
below kept as history): `IsFreshAttach` clauses (3)/(4) repaired to Θ-COMPOSED zeros
(Defs DC-3 — the untransported-coordinate bug, same class DC-2 fixed in clause (1));
the U7 machine refutation is DEAD and the ∃-witness EXISTS at i = 0 for every seed
(U7.freshAttach_exists + mkSigma_recursion_zero — no pins before the root read).
Status shift: U9b's existence obstruction is DISCHARGED — its route re-opens as the
recorded backwards run of the U9a machinery (witness branch now total; pins off spec
clause (2)). U9c: obstruction (i) is discharged, obstruction (ii) STANDS, and the
literal-zero leg now needs the Θ-normalization zcSeed law (post-DC-3 the chosen
system's strip solves are −corr, zero exactly when the correction vanishes — the
C.1.5 "No carries occur in valuation content" residue, landing as a named seed law
per D5's fence exactly as the blueprint's residue rule predicted; the dead
countermodel's badSeed now witnesses U9c-as-stated false pending that law). Both U9c
legs remain designer sign-off items (N-queue).
-/
import Mathlib
import LeanUrat.HC2.Defs
import LeanUrat.HC2.U7_sigmaRec
import LeanUrat.MovesC.C2_floorH_succ
import LeanUrat.MovesC.C2_floorH_root

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesJ
open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]

/-! ### Escalation helpers (the U9a route)

`valueClause_support` re-exports the `hVal` step of `mkFreshClauses_disj` (the value
clause's support IS its slot's level set — `C1_TYP_toClause`'s support law; the private
`card_fin_fun` is replicated inline, the two `choose`s agree by proof irrelevance).
`root_ht_le_floor` is the root floor bridge: at an interior coordinate,
`htH 0 ≤ slotVal (fineSlot b)` (the fresh band's upper edge) IS `htH 1 ≤ floorH 1` —
`slotVal` and the staircase read the same root line, the coherence slope law at
`STR₀ = 1`, root `Dwidth = 1` gives `κ₀ = slope`, and the div/mod defect telescopes;
the intercept (hence `ustar`) cancels, so U11/`root_height` is not consumed. -/

private lemma valueClause_support {n N : ℕ} {H : History p F} {keys : ℕ → Polynomial ℤ_[p]}
    (S : PresentSeed p F H n N keys) (vOf : VOf p (n * N))
    (i : ℕ) (hi : i < H.nodes.length) (j : ℕ) (hsp : (H.nodes[i]'hi).spanSlot j) :
    (valueClause H n N S vOf i hi j hsp).support = levelSet H n N i (H.nodes[i]'hi) j := by
  classical
  have hcard : Nat.card (Fin (levelSet H n N i (H.nodes[i]'hi) j).card → ZMod p)
      = p ^ (levelSet H n N i (H.nodes[i]'hi) j).card := by
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    simp [Nat.card_eq_fintype_card, ZMod.card]
  exact (C1_TYP_toClause
    (S.typObj i hi (levelSet H n N i (H.nodes[i]'hi) j)
      ⟨j, hsp, fun c => Iff.intro
        (fun hc => (Finset.mem_filter.mp hc).2)
        (fun hc => Finset.mem_filter.mpr ⟨Finset.mem_univ c, hc⟩)⟩)
    (vOf i j (levelSet H n N i (H.nodes[i]'hi) j))
    (levelSet H n N i (H.nodes[i]'hi) j).card
    hcard).choose_spec.1

private lemma root_ht_le_floor {H : History p F}
    (hcoh : HistoryCoherent H) (h0 : 0 < H.nodes.length) (c : Coord)
    (hb : c.2 < (H.nodes[0]'h0).μ * (H.nodes[0]'h0).childWidth)
    (hht : (c.1 : ℚ) ≤ (H.nodes[0]'h0).slotVal ((H.nodes[0]'h0).fineSlot c.2)) :
    ((H.htH 1 c : ℚ) : WithBot ℚ) ≤ H.floorH 1 c.2 := by
  have hD : (H.nodes[0]'h0).Dwidth = 1 := by
    rw [(H.nodes[0]'h0).hDwidth]; exact hcoh.1 h0
  have hstrN : H.strFrame 0 = 1 := rfl
  have hnode : H.nodes[0]? = some (H.nodes[0]'h0) := by
    rw [List.getElem?_eq_getElem]
  have he0 : ((H.nodes[0]'h0).e : ℚ) ≠ 0 := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mp (H.nodes[0]'h0).he
  -- the coherence slope law at the root: slope · e = h  (STR₀ = 1, Dwidth = 1)
  have hslope' : (H.nodes[0]'h0).line.slope * ((H.nodes[0]'h0).e : ℚ)
      = ((H.nodes[0]'h0).h : ℚ) := by
    have h' := hcoh.2.1 0 h0
    rw [hstrN, hD] at h'
    simpa using h'
  -- κ₀ = slope
  have hkap : H.kappaH 0 = (H.nodes[0]'h0).line.slope := by
    have hk : H.kappaH 0 = ((H.nodes[0]'h0).h : ℚ)
        / (((H.nodes[0]'h0).e : ℚ) * ((H.strFrame 0 : ℕ) : ℚ)) := by
      unfold History.kappaH
      rw [hnode]
      rfl
    rw [hk, hstrN, ← hslope']
    push_cast
    rw [mul_one]
    exact mul_div_cancel_right₀ _ he0
  -- the level-0 inner slot at root width 1 is the childWidth remainder
  have hinner : H.innerslotH 0 c.2 = c.2 % (H.nodes[0]'h0).childWidth := by
    unfold History.innerslotH
    rw [hnode]
    show (c.2 % (H.nodes[0]'h0).childWidth) / (H.nodes[0]'h0).Dwidth = _
    rw [hD, Nat.div_one]
  -- htH 1 = level + remainder · slope
  have hht1 : H.htH 1 c = (c.1 : ℚ)
      + ((c.2 % (H.nodes[0]'h0).childWidth : ℕ) : ℚ) * (H.nodes[0]'h0).line.slope := by
    unfold History.htH
    rw [Finset.sum_range_one, hinner, hkap]
  -- the band edge at root width 1 is the line at the base index itself
  have hslot : (H.nodes[0]'h0).slotVal ((H.nodes[0]'h0).fineSlot c.2)
      = (H.nodes[0]'h0).line.at c.2 := by
    unfold Node.slotVal Node.fineSlot
    rw [hD, Nat.div_one, mul_one]
  rw [hslot] at hht
  -- the step-1 floor is the root staircase (interior branch)
  have hfl : H.floorH 1 c.2 = (H.nodes[0]'h0).staircase c.2 := by
    have hf := C2_floorH_succ H 0 h0 c.2
    rw [C2_floorH_root] at hf
    rw [show (0 + 1 : ℕ) = 1 from rfl] at hf
    rw [hf, max_eq_right bot_le]
  rw [hfl]
  unfold Node.staircase
  rw [if_pos hb, WithBot.coe_le_coe, hht1]
  unfold Line.at at hht ⊢
  have hdm : ((H.nodes[0]'h0).childWidth : ℚ)
        * ((c.2 / (H.nodes[0]'h0).childWidth : ℕ) : ℚ)
        + ((c.2 % (H.nodes[0]'h0).childWidth : ℕ) : ℚ) = (c.2 : ℚ) := by
    exact_mod_cast Nat.div_add_mod c.2 (H.nodes[0]'h0).childWidth
  have hkey : (H.nodes[0]'h0).line.intercept - (H.nodes[0]'h0).line.slope
        * (((c.2 / (H.nodes[0]'h0).childWidth * (H.nodes[0]'h0).childWidth : ℕ)) : ℚ)
      = ((H.nodes[0]'h0).line.intercept - (H.nodes[0]'h0).line.slope * (c.2 : ℚ))
        + (H.nodes[0]'h0).line.slope * ((c.2 % (H.nodes[0]'h0).childWidth : ℕ) : ℚ) := by
    push_cast
    rw [← hdm]
    ring
  rw [hkey]
  linarith [hht]

/-- U9a — root downset, ⊆ direction: after the root read, every interior pin sits
at-or-below the frame-1 floor. -/
theorem zc_root_downset_mp {n N : ℕ} {H : History p F} {keys : ℕ → Polynomial ℤ_[p]}
    (S : PresentSeed p F H n N keys) (vOf : VOf p (n * N))
    (hcoh : HistoryCoherent H) (hreal : Realizable H) (hbox : InBox n H) (hN : 1 ≤ N)
    (h0 : 0 < H.nodes.length) :
    ∀ j : Fin (n * N),
      (boxChart n N j).2 < (H.nodes[0]'h0).μ * (H.nodes[0]'h0).childWidth →
      (mkSigma H n N S vOf 1).pinned j = true →
      ((H.htH 1 (boxChart n N j) : ℚ) : WithBot ℚ) ≤ H.floorH 1 (boxChart n N j).2 := by
  classical
  intro j hj hpin
  have hsig : mkSigma H n N S vOf 1
      = pinTransportSystem (mkSigma H n N S vOf 0) (S.Theta 0) (mkFresh H n N S vOf 0 h0) := by
    show (if hi : 0 < H.nodes.length then
        pinTransportSystem (mkSigma H n N S vOf 0) (S.Theta 0) (mkFresh H n N S vOf 0 hi)
      else mkSigma H n N S vOf 0) = _
    rw [dif_pos h0]
  by_cases hEx : ∃ D' : Locus p (n * N),
      IsFreshAttach (mkSigma H n N S vOf 0) (S.Theta 0) (mkFresh H n N S vOf 0 h0) D'
  · -- witness branch: read the pin off the spec's clause (2)
    have spec := pinTransportSystem_spec (mkSigma H n N S vOf 0) (S.Theta 0)
      (mkFresh H n N S vOf 0 h0) hEx
    rw [hsig] at hpin
    rcases (spec.2.1 j).mp hpin with htop | ⟨cl, hclmem, hjsup⟩
    · -- no pins before the root read
      rw [show (mkSigma H n N S vOf 0).pinned j = false from rfl] at htop
      exact Bool.noConfusion htop
    · rcases List.mem_append.mp hclmem with hstrip | hval
      · -- STRIP pin: the band's upper edge feeds the bridge
        obtain ⟨c, hcmem, rfl⟩ := List.mem_map.mp hstrip
        have hjc : j = c :=
          Finset.mem_singleton.mp ((C1_stripClause (p := p) c).choose_spec.1 ▸ hjsup)
        subst hjc
        rw [Finset.mem_toList] at hcmem
        unfold stripSet at hcmem
        obtain ⟨-, hband, -⟩ := Finset.mem_filter.mp hcmem
        have hle := hband.2.2
        have hht0 : H.htH 0 (boxChart n N j) = ((boxChart n N j).1 : ℚ) := by
          unfold History.htH
          simp
        rw [hht0] at hle
        exact root_ht_le_floor hcoh h0 _ hj hle
      · -- VALUE pin: level-set membership gives height = slot valuation
        obtain ⟨jh, hjhmem, rfl⟩ := List.mem_map.mp hval
        rw [valueClause_support S vOf 0 h0 jh.1 (valueSlots_spanSlot jh.2)] at hjsup
        unfold levelSet at hjsup
        obtain ⟨-, hfs, hhtv⟩ := Finset.mem_filter.mp hjsup
        have hht0 : H.htH 0 (boxChart n N j) = ((boxChart n N j).1 : ℚ) := by
          unfold History.htH
          simp
        rw [hht0] at hhtv
        refine root_ht_le_floor hcoh h0 _ hj ?_
        rw [hfs]
        exact le_of_eq hhtv
  · -- no-witness branch: the transported system degenerates to the (pin-free) fallback
    rw [hsig] at hpin
    unfold pinTransportSystem at hpin
    rw [dif_neg hEx] at hpin
    rw [show (mkSigma H n N S vOf 0).pinned j = false from rfl] at hpin
    exact Bool.noConfusion hpin

/-! ### The ⊇ helpers (the backwards U9a route, unlocked by DC-3)

`clause_assign`/`valueClause_codim`/`mkFresh_codim` replicate the U7 per-coordinate
assignment machinery (private there; the `card_fin_fun` replication is the U9a precedent
above): every fresh clause of `mkFresh` pins its whole support (`codim = |support|` ⟹
`LevelClause.count` leaves one supported satisfier). They feed `freshAttach_exists`'s
`hasg` leg, so the DC-3 fresh-attach witness EXISTS at the root (`hunpinned` is free at
i = 0 — nothing is pinned before the root read). `floor_ht_gives_slot` is the CONVERSE of
`root_ht_le_floor`: the same root floor bridge run backwards (the reduction is by
equalities, so `htH 1 ≤ floorH 1` ⟺ the band's upper-edge bound `htH 0 = c.1 ≤ slotVal`). -/

private lemma clause_assign {m : ℕ} (cl : LevelClause p m)
    (hcodim : cl.codim = cl.support.card) :
    ∃ u : Fin m → ZMod p, ∀ x : Fin m → ZMod p,
      cl.sat x ↔ ∀ c ∈ cl.support, x c = u c := by
  classical
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hcount := cl.count
  rw [hcodim] at hcount
  have hone : Nat.card {y : Fin m → ZMod p // cl.sat y ∧ ∀ c ∉ cl.support, y c = 0} = 1 :=
    Nat.eq_of_mul_eq_mul_right (pow_pos hp _) (by rw [hcount, one_mul])
  obtain ⟨y₀, hy₀⟩ := Nat.card_eq_one_iff_exists.mp hone
  refine ⟨y₀.1, fun x => ⟨fun hx c hc => ?_, fun hx => ?_⟩⟩
  · have hres : cl.sat (fun c' => if c' ∈ cl.support then x c' else 0) := by
      refine (cl.dep x _ ?_).mp hx
      intro c' hc'
      rw [if_pos hc']
    have hz : (⟨fun c' => if c' ∈ cl.support then x c' else 0, hres,
        fun c' hc' => if_neg hc'⟩ :
        {y : Fin m → ZMod p // cl.sat y ∧ ∀ c ∉ cl.support, y c = 0}) = y₀ := hy₀ _
    have hzc : (if c ∈ cl.support then x c else 0) = y₀.1 c :=
      congrFun (congrArg Subtype.val hz) c
    rw [if_pos hc] at hzc
    exact hzc
  · exact (cl.dep x y₀.1 fun c hc => hx c hc).mpr y₀.2.1

private lemma card_fin_fun' (k : ℕ) : Nat.card (Fin k → ZMod p) = p ^ k := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  simp [Nat.card_eq_fintype_card, ZMod.card]

private lemma valueClause_codim {n N : ℕ} {H : History p F} {keys : ℕ → Polynomial ℤ_[p]}
    (S : PresentSeed p F H n N keys) (vOf : VOf p (n * N))
    (i : ℕ) (hi : i < H.nodes.length) (j : ℕ) (hsp : (H.nodes[i]'hi).spanSlot j) :
    (valueClause H n N S vOf i hi j hsp).codim
      = (valueClause H n N S vOf i hi j hsp).support.card := by
  classical
  have h := (C1_TYP_toClause
    (S.typObj i hi (levelSet H n N i (H.nodes[i]'hi) j)
      ⟨j, hsp, fun c => Iff.intro
        (fun hc => (Finset.mem_filter.mp hc).2)
        (fun hc => Finset.mem_filter.mpr ⟨Finset.mem_univ c, hc⟩)⟩)
    (vOf i j (levelSet H n N i (H.nodes[i]'hi) j))
    (levelSet H n N i (H.nodes[i]'hi) j).card
    (card_fin_fun' _)).choose_spec
  exact h.2.1.trans (congrArg Finset.card h.1).symm

private lemma mkFresh_codim {n N : ℕ} {H : History p F} {keys : ℕ → Polynomial ℤ_[p]}
    (S : PresentSeed p F H n N keys) (vOf : VOf p (n * N))
    (i : ℕ) (hi : i < H.nodes.length) :
    ∀ cl ∈ (mkFresh H n N S vOf i hi).clauses, cl.codim = cl.support.card := by
  intro cl hcl
  have hcl' : cl ∈ ((stripSet H n N i (H.nodes[i]'hi)).toList.map
        (fun c => (C1_stripClause (p := p) c).choose))
      ++ ((valueSlots H n N i (H.nodes[i]'hi)).attach.toList.map
        (fun jh => valueClause H n N S vOf i hi jh.1 (valueSlots_spanSlot jh.2))) := hcl
  rcases List.mem_append.mp hcl' with hstrip | hval
  · obtain ⟨c, -, rfl⟩ := List.mem_map.mp hstrip
    have h := (C1_stripClause (p := p) c).choose_spec
    rw [h.2.1, h.1, Finset.card_singleton]
  · obtain ⟨jh, -, rfl⟩ := List.mem_map.mp hval
    exact valueClause_codim S vOf i hi jh.1 (valueSlots_spanSlot jh.2)

/-- The root floor bridge run BACKWARDS (the converse of `root_ht_le_floor`): at an
interior coordinate, `htH 1 ≤ floorH 1` FORCES the band's upper-edge bound
`c.1 ≤ slotVal (fineSlot c.2)`. The reduction is by the same equalities (`κ₀ = slope`,
`Dwidth = 1`, the div/mod telescope), so the two bounds are equivalent. -/
private lemma floor_ht_gives_slot {H : History p F}
    (hcoh : HistoryCoherent H) (h0 : 0 < H.nodes.length) (c : Coord)
    (hb : c.2 < (H.nodes[0]'h0).μ * (H.nodes[0]'h0).childWidth)
    (hfloor : ((H.htH 1 c : ℚ) : WithBot ℚ) ≤ H.floorH 1 c.2) :
    ((c.1 : ℚ)) ≤ (H.nodes[0]'h0).slotVal ((H.nodes[0]'h0).fineSlot c.2) := by
  have hD : (H.nodes[0]'h0).Dwidth = 1 := by
    rw [(H.nodes[0]'h0).hDwidth]; exact hcoh.1 h0
  have hstrN : H.strFrame 0 = 1 := rfl
  have hnode : H.nodes[0]? = some (H.nodes[0]'h0) := by
    rw [List.getElem?_eq_getElem]
  have he0 : ((H.nodes[0]'h0).e : ℚ) ≠ 0 := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mp (H.nodes[0]'h0).he
  have hslope' : (H.nodes[0]'h0).line.slope * ((H.nodes[0]'h0).e : ℚ)
      = ((H.nodes[0]'h0).h : ℚ) := by
    have h' := hcoh.2.1 0 h0
    rw [hstrN, hD] at h'
    simpa using h'
  have hkap : H.kappaH 0 = (H.nodes[0]'h0).line.slope := by
    have hk : H.kappaH 0 = ((H.nodes[0]'h0).h : ℚ)
        / (((H.nodes[0]'h0).e : ℚ) * ((H.strFrame 0 : ℕ) : ℚ)) := by
      unfold History.kappaH
      rw [hnode]
      rfl
    rw [hk, hstrN, ← hslope']
    push_cast
    rw [mul_one]
    exact mul_div_cancel_right₀ _ he0
  have hinner : H.innerslotH 0 c.2 = c.2 % (H.nodes[0]'h0).childWidth := by
    unfold History.innerslotH
    rw [hnode]
    show (c.2 % (H.nodes[0]'h0).childWidth) / (H.nodes[0]'h0).Dwidth = _
    rw [hD, Nat.div_one]
  have hht1 : H.htH 1 c = (c.1 : ℚ)
      + ((c.2 % (H.nodes[0]'h0).childWidth : ℕ) : ℚ) * (H.nodes[0]'h0).line.slope := by
    unfold History.htH
    rw [Finset.sum_range_one, hinner, hkap]
  have hslot : (H.nodes[0]'h0).slotVal ((H.nodes[0]'h0).fineSlot c.2)
      = (H.nodes[0]'h0).line.at c.2 := by
    unfold Node.slotVal Node.fineSlot
    rw [hD, Nat.div_one, mul_one]
  have hflr : H.floorH 1 c.2 = (H.nodes[0]'h0).staircase c.2 := by
    have hf := C2_floorH_succ H 0 h0 c.2
    rw [C2_floorH_root] at hf
    rw [show (0 + 1 : ℕ) = 1 from rfl] at hf
    rw [hf, max_eq_right bot_le]
  rw [hflr] at hfloor
  unfold Node.staircase at hfloor
  rw [if_pos hb, WithBot.coe_le_coe, hht1] at hfloor
  rw [hslot]
  unfold Line.at at hfloor ⊢
  have hdm : ((H.nodes[0]'h0).childWidth : ℚ)
        * ((c.2 / (H.nodes[0]'h0).childWidth : ℕ) : ℚ)
        + ((c.2 % (H.nodes[0]'h0).childWidth : ℕ) : ℚ) = (c.2 : ℚ) := by
    exact_mod_cast Nat.div_add_mod c.2 (H.nodes[0]'h0).childWidth
  have hkey : (H.nodes[0]'h0).line.intercept - (H.nodes[0]'h0).line.slope
        * (((c.2 / (H.nodes[0]'h0).childWidth * (H.nodes[0]'h0).childWidth : ℕ)) : ℚ)
      = ((H.nodes[0]'h0).line.intercept - (H.nodes[0]'h0).line.slope * (c.2 : ℚ))
        + (H.nodes[0]'h0).line.slope * ((c.2 % (H.nodes[0]'h0).childWidth : ℕ) : ℚ) := by
    push_cast
    rw [← hdm]
    ring
  rw [hkey] at hfloor
  linarith [hfloor]

/-- U9b — root downset, ⊇ direction: every interior at-or-below-floor coordinate is
pinned (the root band exhausts the downset). PROVED (DC-3): the fresh-attach witness now
EXISTS at the root (`freshAttach_exists`, `hunpinned` free at i = 0), so the pin reads off
`pinTransportSystem_spec` clause (2); the ⊇ content is the U9a band cover run backwards —
`inFreshBand` at i = 0 is `c.2 < n` (auto, `boxChart`) ∧ `⊥ < htH 0` (auto,
`floorH 0 = ⊥`) ∧ `c.1 ≤ slotVal` (`floor_ht_gives_slot`), and the value-slot roster's
whole-level-set band condition is DISCHARGED at the root (every level-set member sits AT
its slot valuation, so its upper-edge bound is equality — the straddle needs i ≥ 1). -/
theorem zc_root_downset_mpr {n N : ℕ} {H : History p F} {keys : ℕ → Polynomial ℤ_[p]}
    (S : PresentSeed p F H n N keys) (vOf : VOf p (n * N))
    (hcoh : HistoryCoherent H) (hreal : Realizable H) (hbox : InBox n H) (hN : 1 ≤ N)
    (h0 : 0 < H.nodes.length) :
    ∀ j : Fin (n * N),
      (boxChart n N j).2 < (H.nodes[0]'h0).μ * (H.nodes[0]'h0).childWidth →
      ((H.htH 1 (boxChart n N j) : ℚ) : WithBot ℚ) ≤ H.floorH 1 (boxChart n N j).2 →
      (mkSigma H n N S vOf 1).pinned j = true := by
  classical
  intro j hj hfloor
  -- the state at step 1 IS the transported-and-attached system
  have hsig : mkSigma H n N S vOf 1
      = pinTransportSystem (mkSigma H n N S vOf 0) (S.Theta 0) (mkFresh H n N S vOf 0 h0) := by
    show (if hi : 0 < H.nodes.length then
        pinTransportSystem (mkSigma H n N S vOf 0) (S.Theta 0) (mkFresh H n N S vOf 0 hi)
      else mkSigma H n N S vOf 0) = _
    rw [dif_pos h0]
  -- DC-3: the fresh-attach witness EXISTS at the root (per-coordinate clauses; no prior pins)
  have hasg : ∀ cl ∈ (mkFresh H n N S vOf 0 h0).clauses, ∃ u : Fin (n * N) → ZMod p,
      ∀ x, cl.sat x ↔ ∀ c ∈ cl.support, x c = u c :=
    fun cl hcl => clause_assign cl (mkFresh_codim S vOf 0 h0 cl hcl)
  have hunpinned : ∀ c : Fin (n * N), (mkSigma H n N S vOf 0).pinned c = true →
      ¬ ∃ cl ∈ (mkFresh H n N S vOf 0 h0).clauses, c ∈ cl.support := by
    intro c hc
    rw [show (mkSigma H n N S vOf 0).pinned c = false from rfl] at hc
    exact Bool.noConfusion hc
  have hEx : ∃ D' : Locus p (n * N),
      IsFreshAttach (mkSigma H n N S vOf 0) (S.Theta 0) (mkFresh H n N S vOf 0 h0) D' :=
    freshAttach_exists (mkSigma H n N S vOf 0) (S.Theta_uni 0)
      (mkFresh H n N S vOf 0 h0) hasg hunpinned
  have spec := pinTransportSystem_spec (mkSigma H n N S vOf 0) (S.Theta 0)
    (mkFresh H n N S vOf 0 h0) hEx
  rw [hsig]
  refine (spec.2.1 j).mpr (Or.inr ?_)
  -- GOAL: `∃ cl ∈ (mkFresh …).clauses, j ∈ cl.support` — the root band cover, backwards
  -- htH at the root is the level coordinate; condition (1) of the band is automatic
  have hht0 : H.htH 0 (boxChart n N j) = ((boxChart n N j).1 : ℚ) := by
    unfold History.htH; simp
  have hbaseLt : ∀ c : Fin (n * N), (boxChart n N c).2 < n := by
    intro c
    have hnN : 0 < n * N := lt_of_le_of_lt (Nat.zero_le _) c.isLt
    have hn : 0 < n := Nat.pos_of_ne_zero (fun h => by subst h; simp at hnN)
    have hr : (c : ℕ) % n < n := Nat.mod_lt _ hn
    simp only [boxChart]
    omega
  -- band membership from the upper-edge bound (conditions (1)+(2) automatic at the root)
  have hbandVal : ∀ c : Fin (n * N),
      H.htH 0 (boxChart n N c) ≤ (H.nodes[0]'h0).slotVal ((H.nodes[0]'h0).fineSlot (boxChart n N c).2) →
      inFreshBand H n (boxChart n N) 0 (H.nodes[0]'h0) c := by
    intro c hle
    refine ⟨hbaseLt c, ?_, hle⟩
    rw [C2_floorH_root]
    exact WithBot.bot_lt_coe _
  by_cases hv : IsValueCoord H (boxChart n N) 0 (H.nodes[0]'h0) j
  · -- VALUE coordinate: `j` sits in its slot's level set = a value clause's support
    set j0 := (H.nodes[0]'h0).fineSlot ((boxChart n N j).2) with hj0
    have hspan : (H.nodes[0]'h0).spanSlot j0 := hv.1
    have hhtv : H.htH 0 (boxChart n N j) = (H.nodes[0]'h0).slotVal j0 := hv.2
    have hj_level : j ∈ levelSet H n N 0 (H.nodes[0]'h0) j0 := by
      unfold levelSet
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ j, rfl, hhtv⟩
    -- the root roster is CLEAN: every level-set member sits AT its slot valuation (equality)
    have hroster : ∀ c ∈ levelSet H n N 0 (H.nodes[0]'h0) j0,
        inFreshBand H n (boxChart n N) 0 (H.nodes[0]'h0) c := by
      intro c hc
      unfold levelSet at hc
      rw [Finset.mem_filter] at hc
      obtain ⟨-, hfs, hhtc⟩ := hc
      refine hbandVal c (le_of_eq ?_)
      rw [hhtc, hfs]
    have hj_val : j0 ∈ valueSlots H n N 0 (H.nodes[0]'h0) := by
      unfold valueSlots
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨by have := hspan.2; omega, hspan, ⟨j, hj_level⟩, hroster⟩
    refine ⟨valueClause H n N S vOf 0 h0 j0 (valueSlots_spanSlot hj_val), ?_, ?_⟩
    · show valueClause H n N S vOf 0 h0 j0 (valueSlots_spanSlot hj_val)
          ∈ mkFreshClauses H n N S vOf 0 h0
      unfold mkFreshClauses
      rw [List.mem_append]
      right
      rw [List.mem_map]
      exact ⟨⟨j0, hj_val⟩, by rw [Finset.mem_toList]; exact Finset.mem_attach _ _, rfl⟩
    · rw [valueClause_support S vOf 0 h0 j0 (valueSlots_spanSlot hj_val)]
      exact hj_level
  · -- STRIP coordinate: `j` is a non-value band coordinate, covered by its strip clause
    have hjband : inFreshBand H n (boxChart n N) 0 (H.nodes[0]'h0) j := by
      refine hbandVal j ?_
      rw [hht0]
      exact floor_ht_gives_slot hcoh h0 (boxChart n N j) hj hfloor
    have hj_strip : j ∈ stripSet H n N 0 (H.nodes[0]'h0) := by
      unfold stripSet
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ j, hjband, hv⟩
    have hspec := (C1_stripClause (p := p) j).choose_spec
    refine ⟨(C1_stripClause (p := p) j).choose, ?_, ?_⟩
    · show (C1_stripClause (p := p) j).choose ∈ mkFreshClauses H n N S vOf 0 h0
      unfold mkFreshClauses
      rw [List.mem_append]
      left
      rw [List.mem_map]
      exact ⟨j, by rw [Finset.mem_toList]; exact hj_strip, rfl⟩
    · rw [hspec.1]; exact Finset.mem_singleton_self j

/-- U9c — root interior zeros: interior pins solve to the literal constant 0. -/
theorem zc_root_interior_zero {n N : ℕ} {H : History p F} {keys : ℕ → Polynomial ℤ_[p]}
    (S : PresentSeed p F H n N keys) (vOf : VOf p (n * N))
    (hcoh : HistoryCoherent H) (hreal : Realizable H) (hbox : InBox n H) (hN : 1 ≤ N)
    (h0 : 0 < H.nodes.length) :
    ∀ j : Fin (n * N),
      (boxChart n N j).2 < (H.nodes[0]'h0).μ * (H.nodes[0]'h0).childWidth →
      (mkSigma H n N S vOf 1).pinned j = true →
      ∀ f : (j' : Fin (n * N)) → j' < j → ZMod p,
        (mkSigma H n N S vOf 1).solve j f = 0 := by
  -- STOP-THE-LINE (escalation, 2026-07-28) — UNPROVABLE AS STATED; two independent gaps.
  -- (i) It engages only under the U9b existence obstruction above (the no-witness branch
  --     is vacuously fine, but provability of the witness branch is what the unit needs).
  -- (ii) Even granted the witness: an interior coordinate pinned by a VALUE clause has
  --     `solve` UNCONSTRAINED by `IsFreshAttach` (clauses (3)/(4) pin only singleton
  --     zero-sat strips and transported zeros); on solution prefixes the exact-solution
  --     clause forces it to the unique `φ`-preimage digit of the emitted `vOf i j T` —
  --     the free R4.B.2 parameter, universally quantified here, generically ≠ 0. And
  --     interior value coordinates are NOT excluded: nothing places the root's span
  --     slots at/beyond the rim — `s0 ≥ μ·e·g` is underivable (hcoh/hreal/hbox allow
  --     `s0 = 0`, while `hOrd` gives `wSide ≥ μ·e·g`, so span slots cross the whole
  --     interior; an on-lattice interior line value then yields a nonempty level set,
  --     rostered in `valueSlots`, giving a genuinely value-pinned interior coordinate).
  --     The blueprint sketch's "value pins sit at the rim by the root band's shape" has
  --     NO Lean carrier — a RootD4-class Defs gap (§9 F-6's sibling). REPAIR (note-round
  --     gate): a root-shape law `μ·childWidth ≤ s0 · Dwidth` (equivalently: interior
  --     fine slots are never root span slots) as a Defs addendum or zcSeed law; with it
  --     plus the U9b Θ-normalization law, every interior pin is a strip pin and clause
  --     (3) closes this goal.
  sorry

/-- U9 assembled — the i = 0 instance of `JetSetup.zc` for the constructed chain. -/
theorem zc_root {n N : ℕ} {H : History p F} {keys : ℕ → Polynomial ℤ_[p]}
    (S : PresentSeed p F H n N keys) (vOf : VOf p (n * N))
    (hcoh : HistoryCoherent H) (hreal : Realizable H) (hbox : InBox n H) (hN : 1 ≤ N)
    (h0 : 0 < H.nodes.length) :
    ZCData (mkSigma H n N S vOf 1) (boxChart n N) (H.htH 1) (H.floorH 1)
      ((H.nodes[0]'h0).μ * (H.nodes[0]'h0).childWidth) := by
  -- STOP-THE-LINE (escalation, 2026-07-28): trivial packaging of U9a/b/c
  -- (`downset_exact := fun j hj => ⟨mp j hj, mpr j hj⟩`, `interior_zero := U9c`),
  -- blocked by the U9b and U9c records above.
  sorry

end LeanUrat.MovesJ
