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

/-- U9b — root downset, ⊇ direction: every interior at-or-below-floor coordinate is
pinned (the root band exhausts the downset; root_height puts the floor at ≥ 1). -/
theorem zc_root_downset_mpr {n N : ℕ} {H : History p F} {keys : ℕ → Polynomial ℤ_[p]}
    (S : PresentSeed p F H n N keys) (vOf : VOf p (n * N))
    (hcoh : HistoryCoherent H) (hreal : Realizable H) (hbox : InBox n H) (hN : 1 ≤ N)
    (h0 : 0 < H.nodes.length) :
    ∀ j : Fin (n * N),
      (boxChart n N j).2 < (H.nodes[0]'h0).μ * (H.nodes[0]'h0).childWidth →
      ((H.htH 1 (boxChart n N j) : ℚ) : WithBot ℚ) ≤ H.floorH 1 (boxChart n N j).2 →
      (mkSigma H n N S vOf 1).pinned j = true := by
  -- STOP-THE-LINE (escalation, 2026-07-28) — UNPROVABLE AS STATED.
  -- `mkSigma … 1 = pinTransportSystem (topLocus) (S.Theta 0) (mkFresh … 0 h0)` and
  -- `pinTransportSystem` falls back to its FIRST argument (pinned ≡ false) whenever
  -- `∃ D', IsFreshAttach …` fails — so this ⊇ direction needs that existence, and the
  -- existence is NOT seed-derivable: `IsFreshAttach` clause (3) forces `D'.solve ≡ 0`
  -- at every strip coordinate `c`, hence (via `IsSolution`) solution set ⊆ {x | x c = 0},
  -- while clause (1)'s exact solution set `{x | fd.sat (S.Theta 0 x)}` puts
  -- `x c = − corr_c (x|₍<c₎)` there (`Theta_uni`'s correction). Existence therefore
  -- REQUIRES the corrections of `S.Theta 0` to vanish at strip coordinates on the fresh
  -- locus — but `PresentSeed` constrains `Theta` ONLY through `pres`
  -- (`pres_theta`/`Theta_uni`/`pres_block`); a constant nonzero correction at a strip
  -- coordinate, with `pres 1 x f :⟺ Theta 0 x = pres-0 digit vector of f`, satisfies
  -- EVERY seed law (pres_zero/total/theta/block/attain/downsets_literal untouched at
  -- i = 0; block-local constants respect pres_block) and kills the witness — then no
  -- coordinate of `mkSigma … 1` is pinned while interior coordinates with
  -- `htH 1 ≤ floorH 1` exist (any root line with nonnegative interior values). So the
  -- statement is refutable modulo a concrete gate-style seed; it is certainly not
  -- provable. NOTE: the SAME obstruction re-blocks U7.mkSigma_recursion as stated (its
  -- fallback branch demands `IsSolution x ↔ IsSolution (Θ x) ∧ stratum (Θ x)` of the
  -- degenerate system — false); the §9 F-7 "QUEUED-PROVABLE-NOW / ∃-witness inlinable"
  -- ruling overlooked clause (3). REPAIR (stuck rule, D5's fence — designer sign-off):
  -- a Θ-normalization seed law (corrections vanish at read-i pinned coordinates —
  -- C.1.5(2)'s "(ZC-a) normalized presentation" carrier), or weaken `IsFreshAttach`
  -- clauses (3)/(4) to Θ-composed zeros. With that law, THIS direction closes by the
  -- proved U9a machinery run backwards (band membership from the bridge identity;
  -- `μ·childWidth ≤ wSide ≤ n` via `hOrd`+`hEdvd`+`InBox` gives the region bound).
  sorry

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
