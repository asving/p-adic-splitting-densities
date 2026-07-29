/-  MovesV unit V3-3d `spword_faithful` · HARD — the Codex-6 reconstruction
    bridge (the corpus's pre-declared E-phase RISK; escalation hatch at §2.D).
    ROSTER (3): readFits_unique, writeHeights_total (+ the TOTAL writeHeights),
    spWord_faithful.
    STATEMENT REPAIR 2026-07-29 (adjudicated; machine-verified refutation from
    the prover fleet): `readFits_unique` gains the hypothesis `s.sel.isSome` —
    `ReadFits` pins (g, μ) only through the clause "∀ gμ, s.sel = some gμ → …",
    which is VACUOUS at s.sel = none (terminal letters, MovesSp (G6)), leaving
    R.g/R.μ free (counterexample on file with the fleet). Blueprint row
    (MOVESV_LEAN_BLUEPRINT_2026-07-28.md V3-3d): "(a) `readFits_unique` — the
    `ReadFits`-satisfying ShapeRead is UNIQUE (e/g/μ/s0/wSide/Dwidth/w pinned by
    the letter's stage fields …)" — the g/μ pin needs the selection present.
    `s.sel.isSome` (not bare catalogue membership, which admits sel = ⊥ at
    W = 1 by (G6)) is what every downstream consumer supplies: the letters fed
    to `readOfLetter?` along an entrance word all carry sel = some — non-last
    letters have an outgoing SuccStep edge (sel = none ⇒ SuccStep is False,
    MovesSp SP.4) and the last letter carries sel = some (gsel, musel) by
    hEntry (§2.D); cf. V3-5b's inverse construction through this lemma.
    ADJ-2 STATEMENT REPAIRS (adjudicated; both unscoped forms machine-refuted
    in `V3_spword_negWitness2.lean`, the standing record): the family is
    SCOPED to the ORDER-0 / SELF-LOOP-FREE stratum, mirroring the capstone
    perimeter — `writeHeights_total` gains the single-letter stratum
    (`hword`/`hsl`) + the named `AnchorAdmissible` slot hypothesis (entDom
    owns the semilinear domain) and is PROVED; `spWord_faithful` gains the
    non-junk fitting-word hypotheses (`hfit`/`hfit'`) and is PROVED.
    SOUNDNESS REPAIR 2026-07-29 (ratification verdict M1, the stop-the-line
    warrant): the recorded ADJ-2 consumption shim `writeHeights_total_unscoped`
    (a SORRIED universal whose negation instance `WHNeg.writeHeights_total_false`
    is PROVED in-tree — the combined environment derived False) is DELETED.
    Every consumer re-keys to the scoped TRUE theorem through the named
    perimeter predicate `Order0Perimeter` (the order-0 perimeter family;
    "MIRRORS the capstone's order-0 perimeter", wave-A record) and the
    domain-scoping hypothesis `EntDomOrder0` threaded UP into consumer
    signatures — statements gaining hypotheses is the honest cost. -/
import LeanUrat.MovesV.V3_spwordA
import LeanUrat.MovesSp.SP0_memCoherent

set_option linter.style.longLine false
set_option linter.style.header false

namespace LeanUrat.MovesV

theorem readFits_unique (n : ℕ) (P : MovesD.ShapePrefix)
    (s : MovesSp.Species) (hsel : s.sel.isSome) (hslot uslot : ℕ)
    (R R' : MovesD.ShapeRead)
    (h : ReadFits n P s hslot uslot R) (h' : ReadFits n P s hslot uslot R') :
    R = R' := by
  obtain ⟨gμ, hgμ⟩ := Option.isSome_iff_exists.mp hsel
  obtain ⟨he, hs0, hw, hgm, hwid, hDw, hh, hgam, hust, ha, hsp, hmt⟩ := h
  obtain ⟨he', hs0', hw', hgm', hwid', hDw', hh', hgam', hust', ha', hsp', hmt'⟩ := h'
  -- the strS factor in the u* clause does not depend on the appended read
  have hstr : ∀ Q : MovesD.ShapeRead,
      (snocP P Q).strS P.reads.length = (P.reads.map MovesD.ShapeRead.e).prod := by
    intro Q
    simp [snocP, MovesD.ShapePrefix.strS]
  have hprodpos : 0 < (P.reads.map MovesD.ShapeRead.e).prod :=
    List.prod_pos (fun a ha => by
      obtain ⟨Rp, _, rfl⟩ := List.mem_map.mp ha
      exact Rp.he)
  -- shared data equalities
  have hE : R.e = R'.e := he.trans he'.symm
  have hS0 : R.s0 = R'.s0 := hs0.trans hs0'.symm
  have hWS : R.wSide = R'.wSide := hw.trans hw'.symm
  have hG : R.g = R'.g := ((hgm gμ hgμ).1).trans ((hgm' gμ hgμ).1).symm
  have hMu : R.μ = R'.μ := ((hgm gμ hgμ).2).trans ((hgm' gμ hgμ).2).symm
  have hW : R.w = R'.w := hwid.trans hwid'.symm
  have hDW : R.Dwidth = R'.Dwidth := hDw.trans hDw'.symm
  have hH : R.h = R'.h := hh.trans hh'.symm
  have hGam : R.gam = R'.gam := hgam.trans hgam'.symm
  -- u*: cancel the nonzero e · strS factor
  have hUst : R.ustar = R'.ustar := by
    rw [hstr R] at hust
    rw [hstr R'] at hust'
    have hkey : (R.e : ℚ) * (((P.reads.map MovesD.ShapeRead.e).prod : ℚ) * R.ustar)
        = (R.e : ℚ) * (((P.reads.map MovesD.ShapeRead.e).prod : ℚ) * R'.ustar) := by
      have hthis := hust'
      rw [← hE, ← hS0, ← hWS, ← hH, ← hGam] at hthis
      linarith [hust, hthis]
    have hne : (R.e : ℚ) * ((P.reads.map MovesD.ShapeRead.e).prod : ℚ) ≠ 0 := by
      have h1 : (0 : ℚ) < (R.e : ℚ) := by exact_mod_cast R.he
      have h2 : (0 : ℚ) < ((P.reads.map MovesD.ShapeRead.e).prod : ℚ) := by
        exact_mod_cast hprodpos
      positivity
    rw [← mul_assoc, ← mul_assoc] at hkey
    exact mul_left_cancel₀ hne hkey
  -- a: cancel the nonzero (e : ℤ)
  have hA : R.a = R'.a := by
    have heZ : ((R.e : ℤ)) ≠ 0 := by
      have := R.he; omega
    refine mul_left_cancel₀ heZ ?_
    rw [ha, hE, hS0, hH, hGam]
    exact ha'.symm
  have hSp : R.species = R'.species := hsp.trans hsp'.symm
  have hMt : R.monicTop = R'.monicTop := hmt.trans hmt'.symm
  cases R; cases R'
  simp_all only

/-- ORDER-0 SCOPE (ADJ-2) — the SEMILINEAR SLOT CONDITIONS at one letter:
height-positivity (`ShapeRead.hh`), the coprime residue (`ShapeRead.hcop`),
and the Bézout ANCHOR CONGRUENCE bezT·γ ≡ s₀ (mod e) (`ReadFits`' anchor
clause) — exactly what `WHNeg.writeHeights_total_false` exploits the absence
of (the h = 0 slot point + the noted congruence).  Typed as a hypothesis: the
finite-union-of-congruence-classes description of this domain is `entDom`'s
data — entDom OWNS it (Phase B discharges membership from the XHD-d entrance
face's `no_orphanE`/`no_strayE` laws). -/
def AnchorAdmissible (s : MovesSp.Species) (pr : ℕ × ℕ) : Prop :=
  1 ≤ pr.1 ∧ Nat.gcd s.e pr.1 = 1 ∧
    (s.e : ℤ) ∣ ((s.s0 : ℤ) - MovesD.bezT s.e pr.1 * (zig.symm pr.2 : ℤ))

/-- THE ORDER-0 PERIMETER at one slot point (M1 soundness repair,
2026-07-29): the template word is ONE non-self-loop letter and the slot
point satisfies the `AnchorAdmissible` semilinear conditions — exactly the
scope of the PROVED `writeHeights_total` below, packaged as the named
predicate every V3–V7 consumer threads up ("the order-0 perimeter family;
MIRRORS the capstone's order-0 perimeter", wave-A record).  The unscoped
∀-form is REFUTED (`WHNeg.writeHeights_total_false`,
`V3_spword_negWitness2.lean`). -/
def Order0Perimeter {n : ℕ} (εT : EntTemplate n) (h : Hpt εT.entDim) : Prop :=
  ∃ s : MovesSp.Species, εT.word = [s] ∧ SelfLoopLetter n s = false ∧
    ∀ pr ∈ εT.pairSlots h, AnchorAdmissible s pr

/-- ORDER-0 / SELF-LOOP-FREE SCOPE (ADJ-2; machine-verified refutation of the
unscoped ∀-form: `WHNeg.writeHeights_total_false`, `V3_spword_negWitness2.lean`
— the standing record): totality of `writeHeights?` on the order-0 stratum —
the template word is ONE non-self-loop letter (`hword`/`hsl`, mirroring the
capstone's order-0 decided perimeter) and the slot point satisfies the
`AnchorAdmissible` semilinear conditions (`hadm` — entDom owns the domain).
Phase B: deeper words need the letter-level species-coherence law +
per-prefix congruences; the consumers' token is the packaged
`writeHeights_total_of_perimeter` / `Order0Perimeter` below (M1 repair). -/
theorem writeHeights_total {n : ℕ} (εT : EntTemplate n) (h : Hpt εT.entDim)
    (s : MovesSp.Species) (hword : εT.word = [s])
    (hsl : SelfLoopLetter n s = false)
    (hadm : ∀ pr ∈ εT.pairSlots h, AnchorAdmissible s pr) :
    (writeHeights? εT h).isSome := by
  -- letter facts
  have hmem : MovesSp.InCatalogue n s := εT.hMem s (by rw [hword]; simp)
  obtain ⟨hcoh, hbud⟩ := MovesSp.InCatalogue.coherent_budget hmem
  have hsel : s.sel = some (εT.gsel, εT.musel) :=
    εT.hEntry s (by rw [hword]; simp)
  obtain ⟨⟨hD1, hw1, hW1, he1, hell1, hlam1⟩, ⟨hlf, hspan, hrf⟩, hG2, hG3,
    hG4, hG6⟩ := hcoh
  have hsw : s.s0 + s.wraw ≤ s.W := hbud.2.2.1.1
  have hWn : s.W ≤ n := hbud.2.2.2.2.2.2.2.2.1
  have hgmuell : εT.gsel * εT.musel ≤ s.ell := hbud.2.2.2.1 _ hsel
  -- the expansion is the single letter
  have hexp : expandRuns n εT.word (εT.depthSlots h) = [s] := by
    rw [hword, expandRuns, if_neg (by simp [hsl]), expandRuns]
  -- the pair-slot list is a singleton
  have hlen1 : εT.word.length = 1 := by rw [hword]; rfl
  have hpslen : (εT.pairSlots h).length = 1 := by
    simp [EntTemplate.pairSlots, hlen1]
  obtain ⟨pr, rest, hps⟩ : ∃ pr rest, εT.pairSlots h = pr :: rest := by
    cases hc : εT.pairSlots h with
    | nil => rw [hc] at hpslen; simp at hpslen
    | cons a t => exact ⟨a, t, rfl⟩
  have hrest : rest = [] := by
    have h1 := congrArg List.length hps
    rw [hpslen, List.length_cons] at h1
    have : rest.length = 0 := by omega
    exact List.length_eq_zero_iff.mp this
  obtain ⟨hpos, hcop, hdvd⟩ := hadm pr (by rw [hps]; exact List.mem_cons_self)
  -- the fitting read at the root position
  have hstr : ∀ Q : MovesD.ShapeRead,
      ((snocP emptyPrefix Q).strS emptyPrefix.reads.length : ℚ) = 1 := by
    intro Q
    norm_num [snocP, emptyPrefix, MovesD.ShapePrefix.strS]
  have hene : (s.e : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hex : ∃ R : MovesD.ShapeRead, ReadFits n emptyPrefix s pr.1 pr.2 R := by
    refine ⟨{ species := MovesC.ReadSpecies.root,
              e := s.e, h := pr.1, g := εT.gsel, μ := εT.musel,
              a := ((s.s0 : ℤ)
                - MovesD.bezT s.e pr.1 * (zig.symm pr.2 : ℤ)) / s.e,
              s0 := s.s0, wSide := s.wraw, Dwidth := 1,
              ustar := (((zig.symm pr.2 : ℤ) : ℚ)
                - ((s.s0 + s.wraw : ℕ) : ℚ) * (pr.1 : ℚ)) / (s.e : ℚ),
              gam := zig.symm pr.2, w := 1, monicTop := monicTopOf n s,
              he := he1, hg := εT.hsel_g, hμ := εT.hsel_μ,
              hw := le_refl 1, hDw := le_refl 1, hh := hpos, hcop := hcop,
              hspecInc := fun hc => (nomatch hc),
              hspecRec := fun hc => (nomatch hc),
              hmonicRoot := fun _ => rfl },
      rfl, rfl, rfl, ?_, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
    · -- the selection pin
      intro gμ hgμ
      rw [hsel, Option.some.injEq] at hgμ
      exact ⟨by rw [← hgμ], by rw [← hgμ]⟩
    · -- the γ-tie at the empty prefix (STR = 1)
      rw [hstr, one_mul]
      field_simp
      ring
    · -- the Bézout anchor (exact division by the congruence)
      exact Int.mul_ediv_cancel' hdvd
    · -- root species at the empty prefix
      rw [if_pos (show emptyPrefix.reads = [] from rfl)]
    · -- the monic tie bit
      show monicTopOf n s = (decide (emptyPrefix.reads = []) && monicTopOf n s)
      simp [emptyPrefix]
  have hread : readOfLetter? n emptyPrefix s pr.1 pr.2
      = some (snocP emptyPrefix hex.choose) := by
    rw [readOfLetter?, dif_pos hex]
  -- the chosen read's pinned fields
  obtain ⟨hre, hrs0, hrw, hrgm, hrw1, hrDw, hrh, hrgam, hrtie, hranch,
    hrspec, hrmt⟩ := hex.choose_spec
  set Rc := hex.choose with hRcdef
  have hg : Rc.g = εT.gsel ∧ Rc.μ = εT.musel := hrgm (εT.gsel, εT.musel) hsel
  have hw1' : Rc.w = 1 := hrw1
  have hDw' : Rc.Dwidth = 1 := hrDw
  have hspec' : Rc.species = MovesC.ReadSpecies.root := by
    rw [hrspec, if_pos (show emptyPrefix.reads = [] from rfl)]
  have hmt' : Rc.monicTop = monicTopOf n s := hrmt
  have helldiv : s.wraw / s.e = s.ell :=
    Nat.mul_div_cancel_left _ (by omega)
  have hlenRc : Rc.len = s.ell := by
    unfold MovesD.ShapeRead.len
    rw [hrw, hre]
    exact helldiv
  have hgmuRc : εT.gsel * εT.musel ≤ Rc.len := by rw [hlenRc]; exact hgmuell
  -- the fold lands on the one-read prefix
  have hfold : shapeOfSlots? n [s] (εT.pairSlots h)
      = some (snocP emptyPrefix Rc) := by
    rw [hps, hrest]
    unfold shapeOfSlots?
    simp only [List.zip_cons_cons, List.zip_nil_left, List.foldlM_cons,
      List.foldlM_nil]
    rw [hread]
    rfl
  -- the WF certificate
  have hL : (snocP emptyPrefix Rc).reads.length = 1 := rfl
  have hWF₁ : ShapeWFOf n (snocP emptyPrefix Rc) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- species_iff
      intro r hr
      have hr0 : r = 0 := by rw [hL] at hr; omega
      subst hr0
      exact iff_of_true hspec' rfl
    · -- root_box
      intro h0
      show Rc.s0 + Rc.wSide ≤ n
      rw [hrs0, hrw]
      omega
    · -- window (vacuous at one read)
      intro r hr
      rw [hL] at hr
      omega
    · -- gmu
      intro r hr
      have hr0 : r = 0 := by rw [hL] at hr; omega
      subst hr0
      show Rc.g * Rc.μ ≤ Rc.len
      rw [hg.1, hg.2]
      exact hgmuRc
    · -- edvd
      intro r hr
      have hr0 : r = 0 := by rw [hL] at hr; omega
      subst hr0
      show Rc.e ∣ Rc.wSide
      rw [hre, hrw]
      exact ⟨s.ell, rfl⟩
    · -- dchain0
      intro h0
      exact hDw'
    · -- dchain (vacuous)
      intro r hr
      rw [hL] at hr
      omega
    · -- monic
      intro r hr
      have hr0 : r = 0 := by rw [hL] at hr; omega
      subst hr0
      show Rc.monicTop = true ↔ (0 = 0 ∧ Rc.s0 + Rc.wSide = n)
      rw [hmt', hrs0, hrw]
      unfold monicTopOf
      constructor
      · intro hd
        exact ⟨rfl, of_decide_eq_true hd⟩
      · rintro ⟨-, hc⟩
        exact decide_eq_true hc
    · -- w0
      intro h0
      exact hw1'
    · -- wchain (vacuous)
      intro r hr
      rw [hL] at hr
      omega
    · -- gamTie
      intro r hr
      have hr0 : r = 0 := by rw [hL] at hr; omega
      subst hr0
      exact hrtie
    · -- anchorTie
      intro r hr
      have hr0 : r = 0 := by rw [hL] at hr; omega
      subst hr0
      exact hranch
  -- the entrance ties
  have hmbar : letterMbar s = Rc.mbar := by
    unfold letterMbar MovesD.ShapeRead.mbar
    rw [hsel, hlenRc, hg.1, hg.2]
    rfl
  have hbr : IsBranchingLetter n s = decide (IsBranchSlot Rc) := by
    unfold IsBranchingLetter IsBranchSlot
    rw [decide_eq_decide, hmbar]
  have hties : EntTiesAt ⟨snocP emptyPrefix Rc, hWF₁⟩ εT := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · -- reads nonempty
      show ([] ++ [Rc] : List MovesD.ShapeRead) ≠ []
      simp
    · -- the entry selection pin
      intro R hlast
      have hR : Rc = R := by simpa [snocP, emptyPrefix] using hlast
      rw [← hR]
      exact ⟨hg.1, hg.2⟩
    · -- eligibility of the designated pair
      intro R hlast
      have hR : Rc = R := by simpa [snocP, emptyPrefix] using hlast
      rw [← hR]
      exact ⟨εT.hsel_g, εT.hsel_μ, hgmuRc⟩
    · -- branch-slot count tie
      change εT.selRec.length
          = (([] ++ [Rc]).filter fun R => decide (IsBranchSlot R)).length
      rw [εT.hlen, hword, List.nil_append, List.filter_cons, List.filter_cons,
        List.filter_nil, hbr]
      cases decide (IsBranchSlot Rc) <;> simp
    · -- menu tie
      intro i hi
      have hcard : branchMenuCard n ⟨snocP emptyPrefix Rc, hWF₁⟩ i
          = letterMenuCard n εT.word i := by
        unfold branchMenuCard letterMenuCard
        rw [hword]
        show ((([] ++ [Rc]).filter fun R => decide (IsBranchSlot R))[i]?.map
            MovesD.ShapeRead.mbar).getD 0
          = (([s].filter (IsBranchingLetter n))[i]?.map letterMbar).getD 0
        rw [List.nil_append, List.filter_cons, List.filter_cons,
          List.filter_nil, hbr]
        cases hbs : decide (IsBranchSlot Rc) with
        | false => simp
        | true =>
          cases i with
          | zero => simp [hmbar]
          | succ j => simp
      rw [hcard]
      exact εT.hmenu i hi
  rw [writeHeights?, hexp, hfold, Option.bind_some, dif_pos ⟨hWF₁, hties⟩]
  rfl

/-- the packaged form of `writeHeights_total`, keyed to the named
`Order0Perimeter` predicate (M1 soundness repair: this REPLACES the deleted
false shim `writeHeights_total_unscoped` — totality holds ONLY on the
order-0 perimeter; the unscoped ∀-form is refuted in
`V3_spword_negWitness2.lean`). -/
theorem writeHeights_total_of_perimeter {n : ℕ} (εT : EntTemplate n)
    (h : Hpt εT.entDim) (hsc : Order0Perimeter εT h) :
    (writeHeights? εT h).isSome := by
  obtain ⟨s, hword, hsl, hadm⟩ := hsc
  exact writeHeights_total εT h s hword hsl hadm

/-- the SCOPED instantiation map — the token every V3–V7 statement uses.
M1 soundness repair 2026-07-29: the unscoped total wrapper is GONE; the map
now demands its point's `Order0Perimeter` certificate (proof-irrelevant, so
any two certificates give definitionally equal values). -/
noncomputable def writeHeights {n : ℕ} (εT : EntTemplate n)
    (h : Hpt εT.entDim) (hsc : Order0Perimeter εT h) : EntShapeV n :=
  (writeHeights? εT h).get (writeHeights_total_of_perimeter εT h hsc)

/-- THE DOMAIN-SCOPING HYPOTHESIS the V3–V7 aggregate consumers thread up
(M1 soundness repair): every entrance-domain point of every template lies
in the order-0 perimeter.  This is exactly the Phase-B entDom discharge
duty — entDom OWNS the semilinear domain, and the XHD-d entrance face laws
(`no_orphanE`/`no_strayE`) are the designated route. -/
def EntDomOrder0 {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    (V : CtsMeasured n C S) : Prop :=
  ∀ (εT : EntTemplate n) (h : Hpt εT.entDim),
    (V.entDom εT).Mem h → Order0Perimeter εT h

/-- component membership feeds the domain-scoping hypothesis (the listed
components partition the semilinear domain). -/
theorem EntDomOrder0.comp {n : ℕ} {C : CtsFamily n} {S : StepSys n}
    {V : CtsMeasured n C S} (hdom : EntDomOrder0 V) (εT : EntTemplate n)
    (j : Fin (V.entDom εT).comps.length) {h : Hpt εT.entDim}
    (hm : ((V.entDom εT).comps.get j).Mem h) : Order0Perimeter εT h :=
  hdom εT h ⟨_, List.get_mem _ _, hm⟩

/-- SP.1 genuinely forgets ONLY heights: equal species words + equal retained
height/u*-code slot data determine the WF prefix.  ORDER-0 SCOPE (ADJ-2;
machine-verified refutation of the unscoped form:
`SpFaithNeg.spWord_faithful_false` (+ `_with_width`),
`V3_spword_negWitness2.lean` — the standing record): both shapes carry the
NON-JUNK hypothesis the negWitness names — a FITTING species word
(`hfit`/`hfit'`), excluding the junk-[] collision (on fitting-word-free
prefixes `spWord` is the junk [] and `hw` is vacuously satisfiable between
DISTINCT shapes).  On this class SpFitsRead + `hs` pin all fields except
(a, Dwidth, ustar), which anchorTie/dchain/gamTie determine — proved below.
Phase B: the scoped `spWord_exists` (V3-3a) discharges `hfit` on the
species-coherent stratum.  [E-PHASE FORM: stated at the uncollapsed word +
the (h, zig γ) slot lists — MANIFEST deviations.] -/
theorem spWord_faithful {n : ℕ} (P P' : MovesD.Shape n)
    (hfit : ∃ ws, SpWordFits n (P : MovesD.ShapePrefix) ws)
    (hfit' : ∃ ws, SpWordFits n (P' : MovesD.ShapePrefix) ws)
    (hw : spWord n (P : MovesD.ShapePrefix) = spWord n (P' : MovesD.ShapePrefix))
    (hs : (P : MovesD.ShapePrefix).reads.map (fun R => (R.h, zig R.gam))
        = (P' : MovesD.ShapePrefix).reads.map (fun R => (R.h, zig R.gam))) :
    P = P' := by
  -- the fitted words behind the non-junk hypotheses
  have hf1 : SpWordFits n (P : MovesD.ShapePrefix)
      (spWord n (P : MovesD.ShapePrefix)) := by
    rw [spWord, dif_pos hfit]; exact hfit.choose_spec
  have hf2 : SpWordFits n (P' : MovesD.ShapePrefix)
      (spWord n (P' : MovesD.ShapePrefix)) := by
    rw [spWord, dif_pos hfit']; exact hfit'.choose_spec
  obtain ⟨hlen1, hfitP, -, -⟩ := hf1
  obtain ⟨hlen2, hfitP', -, -⟩ := hf2
  have hlenw := congrArg List.length hw
  have hlens : (P : MovesD.ShapePrefix).reads.length
      = (P' : MovesD.ShapePrefix).reads.length := by omega
  -- the pointwise letter-pinned fields
  have hpin : ∀ (r : ℕ) (hr : r < (P : MovesD.ShapePrefix).reads.length)
      (hr' : r < (P' : MovesD.ShapePrefix).reads.length),
      ((P : MovesD.ShapePrefix).reads[r]'hr).e
          = ((P' : MovesD.ShapePrefix).reads[r]'hr').e
      ∧ ((P : MovesD.ShapePrefix).reads[r]'hr).s0
          = ((P' : MovesD.ShapePrefix).reads[r]'hr').s0
      ∧ ((P : MovesD.ShapePrefix).reads[r]'hr).wSide
          = ((P' : MovesD.ShapePrefix).reads[r]'hr').wSide
      ∧ ((P : MovesD.ShapePrefix).reads[r]'hr).g
          = ((P' : MovesD.ShapePrefix).reads[r]'hr').g
      ∧ ((P : MovesD.ShapePrefix).reads[r]'hr).μ
          = ((P' : MovesD.ShapePrefix).reads[r]'hr').μ
      ∧ ((P : MovesD.ShapePrefix).reads[r]'hr).w
          = ((P' : MovesD.ShapePrefix).reads[r]'hr').w
      ∧ ((P : MovesD.ShapePrefix).reads[r]'hr).h
          = ((P' : MovesD.ShapePrefix).reads[r]'hr').h
      ∧ ((P : MovesD.ShapePrefix).reads[r]'hr).gam
          = ((P' : MovesD.ShapePrefix).reads[r]'hr').gam
      ∧ ((P : MovesD.ShapePrefix).reads[r]'hr).species
          = ((P' : MovesD.ShapePrefix).reads[r]'hr').species
      ∧ ((P : MovesD.ShapePrefix).reads[r]'hr).monicTop
          = ((P' : MovesD.ShapePrefix).reads[r]'hr').monicTop := by
    intro r hr hr'
    have hsw1 : r < (spWord n (P : MovesD.ShapePrefix)).length := by omega
    have hsw2 : r < (spWord n (P' : MovesD.ShapePrefix)).length := by omega
    have hfa := hfitP r hsw1 hr
    have hfb := hfitP' r hsw2 hr'
    have hgeq : (spWord n (P : MovesD.ShapePrefix)).get ⟨r, hsw1⟩
        = (spWord n (P' : MovesD.ShapePrefix)).get ⟨r, hsw2⟩ := by
      have h3 : (spWord n (P : MovesD.ShapePrefix))[r]?
          = (spWord n (P' : MovesD.ShapePrefix))[r]? := by rw [hw]
      rw [List.getElem?_eq_getElem hsw1, List.getElem?_eq_getElem hsw2] at h3
      simpa using h3
    rw [← hgeq] at hfb
    simp only [List.get_eq_getElem] at hfa hfb
    obtain ⟨hae, has0, hael, haw, hasel, -, -, -, -, hasp, hamt⟩ := hfa
    obtain ⟨hbe, hbs0, hbel, hbw, hbsel, -, -, -, -, hbsp, hbmt⟩ := hfb
    have hE := hae.symm.trans hbe
    have hLen : ((P : MovesD.ShapePrefix).reads[r]'hr).len
        = ((P' : MovesD.ShapePrefix).reads[r]'hr').len :=
      hael.symm.trans hbel
    have hwsa : ((P : MovesD.ShapePrefix).reads[r]'hr).e
        * ((P : MovesD.ShapePrefix).reads[r]'hr).len
        = ((P : MovesD.ShapePrefix).reads[r]'hr).wSide :=
      Nat.mul_div_cancel' (P.2.edvd r hr)
    have hwsb : ((P' : MovesD.ShapePrefix).reads[r]'hr').e
        * ((P' : MovesD.ShapePrefix).reads[r]'hr').len
        = ((P' : MovesD.ShapePrefix).reads[r]'hr').wSide :=
      Nat.mul_div_cancel' (P'.2.edvd r hr')
    have hgm := Option.some.inj (hasel.symm.trans hbsel)
    have hhg : ((P : MovesD.ShapePrefix).reads[r]'hr).h
          = ((P' : MovesD.ShapePrefix).reads[r]'hr').h
        ∧ zig ((P : MovesD.ShapePrefix).reads[r]'hr).gam
          = zig ((P' : MovesD.ShapePrefix).reads[r]'hr').gam := by
      have h4 : ((P : MovesD.ShapePrefix).reads.map
            (fun R => (R.h, zig R.gam)))[r]?
          = ((P' : MovesD.ShapePrefix).reads.map
            (fun R => (R.h, zig R.gam)))[r]? := by rw [hs]
      simpa [List.getElem?_map, List.getElem?_eq_getElem hr,
        List.getElem?_eq_getElem hr'] using h4
    refine ⟨hE, has0.symm.trans hbs0, ?_, congrArg Prod.fst hgm,
      congrArg Prod.snd hgm, haw.symm.trans hbw, hhg.1,
      zig.injective hhg.2, hasp.trans hbsp.symm, hamt.trans hbmt.symm⟩
    rw [← hwsa, ← hwsb, hE, hLen]
  -- Dwidth: the D.5 width chain determines it recursively
  have hDW : ∀ (r : ℕ) (hr : r < (P : MovesD.ShapePrefix).reads.length)
      (hr' : r < (P' : MovesD.ShapePrefix).reads.length),
      ((P : MovesD.ShapePrefix).reads[r]'hr).Dwidth
        = ((P' : MovesD.ShapePrefix).reads[r]'hr').Dwidth := by
    intro r
    induction r with
    | zero =>
      intro hr hr'
      rw [P.2.dchain0 hr, P'.2.dchain0 hr']
    | succ j ih =>
      intro hr hr'
      have hj : j < (P : MovesD.ShapePrefix).reads.length :=
        Nat.lt_of_succ_lt hr
      have hj' : j < (P' : MovesD.ShapePrefix).reads.length :=
        Nat.lt_of_succ_lt hr'
      rw [P.2.dchain j hr, P'.2.dchain j hr']
      unfold MovesD.ShapeRead.childWidthS
      obtain ⟨he, -, -, hg, -, -, -, -, -, -⟩ := hpin j hj hj'
      rw [he, hg, ih hj hj']
  -- the accumulated stretch agrees
  have hstr2 : ∀ r : ℕ,
      (P : MovesD.ShapePrefix).strS r = (P' : MovesD.ShapePrefix).strS r := by
    intro r
    unfold MovesD.ShapePrefix.strS
    congr 1
    apply List.ext_getElem (by simp [hlens])
    intro i h1 h2
    have hi1 : i < (P : MovesD.ShapePrefix).reads.length := by
      simp [List.length_take] at h1; omega
    have hi2 : i < (P' : MovesD.ShapePrefix).reads.length := by
      simp [List.length_take] at h2; omega
    simp only [List.getElem_map, List.getElem_take]
    exact (hpin i hi1 hi2).1
  -- u*: the γ-tie at the shared stretch determines it
  have hUst : ∀ (r : ℕ) (hr : r < (P : MovesD.ShapePrefix).reads.length)
      (hr' : r < (P' : MovesD.ShapePrefix).reads.length),
      ((P : MovesD.ShapePrefix).reads[r]'hr).ustar
        = ((P' : MovesD.ShapePrefix).reads[r]'hr').ustar := by
    intro r hr hr'
    have hta := P.2.gamTie r hr
    have htb := P'.2.gamTie r hr'
    obtain ⟨he, hs0, hws, -, -, -, hh, hgam, -, -⟩ := hpin r hr hr'
    rw [← hstr2 r, ← he, ← hs0, ← hws, ← hh, ← hgam] at htb
    have hstrpos : 0 < (P : MovesD.ShapePrefix).strS r := by
      apply List.prod_pos
      intro a ha
      obtain ⟨Rp, -, hRp⟩ := List.mem_map.mp ha
      rw [← hRp]
      exact Rp.he
    have hne : (((P : MovesD.ShapePrefix).reads[r]'hr).e : ℚ)
        * ((P : MovesD.ShapePrefix).strS r : ℚ) ≠ 0 := by
      have h1 : (0 : ℚ) < (((P : MovesD.ShapePrefix).reads[r]'hr).e : ℚ) := by
        exact_mod_cast ((P : MovesD.ShapePrefix).reads[r]'hr).he
      have h2 : (0 : ℚ) < ((P : MovesD.ShapePrefix).strS r : ℚ) := by
        exact_mod_cast hstrpos
      positivity
    have hkey : (((P : MovesD.ShapePrefix).reads[r]'hr).e : ℚ)
          * (((P : MovesD.ShapePrefix).strS r : ℚ)
            * ((P : MovesD.ShapePrefix).reads[r]'hr).ustar)
        = (((P : MovesD.ShapePrefix).reads[r]'hr).e : ℚ)
          * (((P : MovesD.ShapePrefix).strS r : ℚ)
            * ((P' : MovesD.ShapePrefix).reads[r]'hr').ustar) := by
      linarith [hta, htb]
    rw [← mul_assoc, ← mul_assoc] at hkey
    exact mul_left_cancel₀ hne hkey
  -- a: the Bézout anchor determines it
  have hA : ∀ (r : ℕ) (hr : r < (P : MovesD.ShapePrefix).reads.length)
      (hr' : r < (P' : MovesD.ShapePrefix).reads.length),
      ((P : MovesD.ShapePrefix).reads[r]'hr).a
        = ((P' : MovesD.ShapePrefix).reads[r]'hr').a := by
    intro r hr hr'
    have hta := P.2.anchorTie r hr
    have htb := P'.2.anchorTie r hr'
    obtain ⟨he, hs0, -, -, -, -, hh, hgam, -, -⟩ := hpin r hr hr'
    rw [← he, ← hs0, ← hh, ← hgam] at htb
    have heZ : ((((P : MovesD.ShapePrefix).reads[r]'hr).e : ℤ)) ≠ 0 := by
      have := ((P : MovesD.ShapePrefix).reads[r]'hr).he
      omega
    exact mul_left_cancel₀ heZ (hta.trans htb.symm)
  -- assemble: the read lists agree fieldwise
  have hreads : (P : MovesD.ShapePrefix).reads
      = (P' : MovesD.ShapePrefix).reads := by
    apply List.ext_getElem hlens
    intro r hr hr'
    obtain ⟨he, hs0, hws, hg, hμ, hwq, hh, hgam, hsp, hmt⟩ := hpin r hr hr'
    have hdw := hDW r hr hr'
    have hust := hUst r hr hr'
    have ha := hA r hr hr'
    set R := (P : MovesD.ShapePrefix).reads[r]'hr with hRdef
    set R' := (P' : MovesD.ShapePrefix).reads[r]'hr' with hRdef'
    clear_value R R'
    clear hRdef hRdef'
    cases R; cases R'
    simp_all only
  exact Subtype.ext (congrArg MovesD.ShapePrefix.mk hreads)

end LeanUrat.MovesV
