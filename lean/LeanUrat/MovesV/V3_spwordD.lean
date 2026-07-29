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
    hEntry (§2.D); cf. V3-5b's inverse construction through this lemma. -/
import LeanUrat.MovesV.V3_spwordA

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

theorem writeHeights_total {n : ℕ} (εT : EntTemplate n) (h : Hpt εT.entDim) :
    (writeHeights? εT h).isSome := by
  -- [PROVER PASS B3 2026-07-29: REFUTED AS STATED — machine-verified witness
  --  `WHNeg.writeHeights_total_false` in `V3_spword_negWitness2.lean`: at the
  --  zero slot point the first readOfLetter? dite demands R.h = 0, against
  --  ShapeRead.hh (1 ≤ h).  Pointwise-positive h is NOT a sufficient repair:
  --  ReadFits' anchor clause needs bezT·γ ≡ s0 (mod e) per e ≥ 2 letter — a
  --  semilinear congruence on the u*-slots (the entDom domain's job).
  --  SIGN-OFF ITEM: restrict the ∀ h to the template's admissible slot
  --  domain.]
  sorry

/-- the TOTAL instantiation map — the token every V3–V7 statement uses. -/
noncomputable def writeHeights {n : ℕ} (εT : EntTemplate n)
    (h : Hpt εT.entDim) : EntShapeV n :=
  (writeHeights? εT h).get (writeHeights_total εT h)

/-- SP.1 genuinely forgets ONLY heights: equal species words + equal retained
height/u*-code slot data determine the WF prefix.  [E-PHASE FORM: stated at
the uncollapsed word + the (h, zig γ) slot lists — MANIFEST deviations.] -/
theorem spWord_faithful {n : ℕ} (P P' : MovesD.Shape n)
    (hw : spWord n (P : MovesD.ShapePrefix) = spWord n (P' : MovesD.ShapePrefix))
    (hs : (P : MovesD.ShapePrefix).reads.map (fun R => (R.h, zig R.gam))
        = (P' : MovesD.ShapePrefix).reads.map (fun R => (R.h, zig R.gam))) :
    P = P' := by
  -- [PROVER PASS B3 2026-07-29: REFUTED AS STATED — machine-verified witness
  --  `SpFaithNeg.spWord_faithful_false` (+ `_with_width`) in
  --  `V3_spword_negWitness2.lean`: on any fitting-word-free prefix spWord is
  --  the junk [], so hw is vacuously satisfiable between DISTINCT shapes
  --  (witness pair P4/P4', s0 shifted, same (h, zig γ) lists, both width-
  --  compliant).  On the non-junk class the content stands: SpFitsRead + hs
  --  pin all fields except (a, Dwidth, ustar), which anchorTie/dchain/gamTie
  --  determine.  SIGN-OFF ITEM: needs V3-3a's species repair first (so
  --  spWord ≠ [] on the hypothesis class), or re-key hw to fitting words.]
  sorry

end LeanUrat.MovesV
