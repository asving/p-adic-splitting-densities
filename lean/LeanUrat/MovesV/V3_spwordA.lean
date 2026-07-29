/-  MovesV unit V3-3a `spword_exists` (RE-KEYED REV 9, N-3) — the dite PASSES
    on WF prefixes.
    STATEMENT REPAIR 2026-07-30 (adjudicated; machine-verified refutation
    `V3_spwordA_negWitness.lean`): `spWord_exists`/`spWord_fits` gained THE
    WIDTH-≥-2 CONTINUATION HYPOTHESES (`hn` + `hcont`) — (G6) forbids a
    selection at window 1; see the negWitness header for the full record.
    ADJ-2 STATEMENT REPAIR (adjudicated; machine-verified refutation
    `SpWordNeg2.spWord_exists_false'` in `V3_spword_negWitness2.lean`): even
    width-scoped the sentence was FALSE — THE SPECIES/TAG OFF-BY-ONE:
    `SpFitsRead`'s species clause ties read i's OWN move class to letter i's
    POSITION class (StageLaws' tag law), and `ShapeWF` carries no cross-read
    species law.  ADJUDICATED SCOPE: the ORDER-0 / SELF-LOOP-FREE stratum —
    `spWord_exists`/`spWord_fits` gain the NAMED typed hypothesis
    `SpeciesCoherent P` (the cross-read species-coherence law, below), the
    exact law the negWitness exploits the absence of.  This mirrors the
    capstone perimeter (the order-0 decided stratum).  PROVED on the scoped
    stratum (the explicit letter construction `bWord`): the fold of the stage
    laws along `P.reads` — each read's stage fields seed a catalogue member,
    `SuccStep` from the `ShapeWF` stage clauses (blueprint row V3-3a).  The
    negWitnesses stay on file untouched as the refutation record for the
    unscoped forms.  Phase B: discharging `SpeciesCoherent` from the engine's
    D.7/D.8 output laws (deeper `typeOf`-keyed strata) re-opens the unscoped
    family.  Consumption note: `template_total` (V3_spwordB) consumed the
    unconditional form; `EntShapeV` carries no width/species law, so its
    `hfits` leg stays an explicit open sorry — SIGN-OFF ITEM recorded there
    and in the MANIFEST. -/
import LeanUrat.MovesV.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesV

/-- ORDER-0 SCOPE (ADJ-2): the CROSS-READ SPECIES-COHERENCE law — read r+1's
recorded move class matches its POSITION class under `MovesSp.StageLaws`' tag
law, quoted: "`(s'.tag = .postInc ↔ 2 ≤ s.e * g) ∧ (s'.tag = .postRec ↔
(s.e = 1 ∧ g = 1))`" — i.e. the read AFTER read r is increment-species exactly
when read r's selected move is proper (2 ≤ e_r·g_r).  `ShapeWF` does not carry
this law (the `SpWordNeg2` off-by-one witness); on the order-0 stratum it is a
named hypothesis.  Phase B discharges it from the engine's D.7/D.8 output
laws. -/
def SpeciesCoherent (P : MovesD.ShapePrefix) : Prop :=
  ∀ (r : ℕ) (hr : r + 1 < P.reads.length),
    ((P.reads[r+1]'hr).species = MovesC.ReadSpecies.increment ↔
      2 ≤ (P.reads[r]'(Nat.lt_of_succ_lt hr)).e
          * (P.reads[r]'(Nat.lt_of_succ_lt hr)).g)

/-! ### the letter construction (proof apparatus, all `private`) -/

/-- the fitted residual partition: the selected pair + (1,1)-filler. -/
private def lamOf (R : MovesD.ShapeRead) : Multiset (ℕ × ℕ) :=
  (R.g, R.μ) ::ₘ Multiset.replicate (R.len - R.g * R.μ) (1, 1)

/-- singleton flank composition of a span. -/
private def flankOf (m : ℕ) : List ℕ := if m = 0 then [] else [m]

private theorem flankOf_comp (m : ℕ) : MovesSp.IsComposition (flankOf m) m := by
  by_cases h : m = 0
  · simp [flankOf, h, MovesSp.IsComposition]
  · constructor
    · intro x hx
      rw [flankOf, if_neg h] at hx
      have hxm : x = m := by simpa using hx
      omega
    · simp [flankOf, h]

/-- the species letter presented by read `R` at position `i`, with the
inherited stage degree `D` and window `W` fed externally (`n` rides along for
uniform signatures across the indexed lemmas). -/
private def letterOf (n i D W : ℕ) (R : MovesD.ShapeRead) : MovesSp.Species :=
  letI _ := n
  { tag := if i = 0 then MovesSp.Tag.root
      else if R.species = MovesC.ReadSpecies.increment then .postInc
      else .postRec,
    D := D, w := R.w, W := W, e := R.e, s0 := R.s0, ell := R.len,
    a := R.s0 / R.e, d := R.len + 1,
    slots := Finset.Icc (R.s0 / R.e) (R.s0 / R.e + R.len),
    lam := lamOf R, sel := some (R.g, R.μ),
    lflank := flankOf R.s0, rflank := flankOf (W - (R.s0 + R.wSide)) }

/-- the letter's Coherent + Budget certificate, from the read-level facts. -/
private theorem letterOf_ok (n i D W : ℕ) (R : MovesD.ShapeRead)
    (hD : 1 ≤ D) (hW2 : 2 ≤ W) (hn : 2 ≤ n)
    (hbox : R.s0 + R.wSide ≤ W) (hgmu : R.g * R.μ ≤ R.len)
    (hedvd : R.e ∣ R.wSide) (hWD : W * D ≤ n) (hwD : R.w ≤ D) :
    MovesSp.Coherent (letterOf n i D W R)
      ∧ MovesSp.Budget n (letterOf n i D W R) := by
  -- raw-term facts (every clause is assembled by defeq below)
  have hlw : R.e * (R.wSide / R.e) = R.wSide := Nat.mul_div_cancel' hedvd
  have hgm1 : 1 ≤ R.g * R.μ := Nat.mul_pos R.hg R.hμ
  have hgmu' : R.g * R.μ ≤ R.wSide / R.e := hgmu
  have hlen1 : 1 ≤ R.wSide / R.e := le_trans hgm1 hgmu'
  have hlel : R.wSide / R.e ≤ R.e * (R.wSide / R.e) :=
    Nat.le_mul_of_pos_left _ R.he
  have heel : R.e ≤ R.e * (R.wSide / R.e) := Nat.le_mul_of_pos_right _ hlen1
  have hWn : W ≤ n := le_trans (Nat.le_mul_of_pos_right _ hD) hWD
  have hgle : R.g ≤ R.g * R.μ := Nat.le_mul_of_pos_right _ R.hμ
  have hmle : R.μ ≤ R.g * R.μ := Nat.le_mul_of_pos_left _ R.hg
  have hlamsum : ((lamOf R).map fun gm => gm.1 * gm.2).sum = R.len := by
    unfold lamOf
    rw [Multiset.map_cons, Multiset.map_replicate, Multiset.sum_cons,
      Multiset.sum_replicate, smul_eq_mul]
    show R.g * R.μ + (R.len - R.g * R.μ) * (1 * 1) = R.len
    have : R.g * R.μ ≤ R.len := hgmu
    omega
  have hlammem : ∀ gm ∈ lamOf R, 1 ≤ gm.1 ∧ 1 ≤ gm.2 := by
    intro gm hgm
    rcases Multiset.mem_cons.mp hgm with h | h
    · subst h; exact ⟨R.hg, R.hμ⟩
    · rw [Multiset.eq_of_mem_replicate h]; exact ⟨le_refl 1, le_refl 1⟩
  have hG1mid : R.s0 + R.e * (R.wSide / R.e)
      + (flankOf (W - (R.s0 + R.wSide))).sum = W := by
    have h1 := (flankOf_comp (W - (R.s0 + R.wSide))).2
    omega
  have hselmem : ∀ gm : ℕ × ℕ, (some (R.g, R.μ) : Option (ℕ × ℕ)) = some gm →
      gm ∈ lamOf R := by
    intro gm hgm
    rw [← Option.some.inj hgm]
    exact Multiset.mem_cons_self _ _
  have hG6 : (some (R.g, R.μ) : Option (ℕ × ℕ)) = none ↔ W = 1 :=
    iff_of_false (by simp) (by omega)
  have hW1 : 1 ≤ W := by omega
  have hDn : D ≤ n := le_trans (Nat.le_mul_of_pos_left D hW1) hWD
  have hwn : R.w ≤ n := le_trans hwD hDn
  have hbox' : R.s0 + R.e * (R.wSide / R.e) ≤ W := by omega
  have haell : R.s0 / R.e + R.wSide / R.e ≤ W := by
    have h1 : R.s0 / R.e ≤ R.s0 := Nat.div_le_self _ _
    have h2 : R.wSide / R.e ≤ R.wSide := Nat.div_le_self _ _
    omega
  have hdw : R.wSide / R.e + 1 ≤ R.e * (R.wSide / R.e) + 1 := by omega
  have hWdiv : W ≤ n / D := (Nat.le_div_iff_mul_le hD).mpr hWD
  have hb4 : ∀ gm : ℕ × ℕ, (some (R.g, R.μ) : Option (ℕ × ℕ)) = some gm →
      gm.1 * gm.2 ≤ R.wSide / R.e := by
    intro gm hgm
    rw [← Option.some.inj hgm]
    exact hgmu'
  have hen : R.e ≤ n := by omega
  have helln : R.wSide / R.e ≤ n := by omega
  have hs0n : R.s0 ≤ n := by omega
  have hdn : R.wSide / R.e + 1 ≤ n + 1 := by omega
  have hlamcap : ∀ gm ∈ lamOf R, gm.1 ≤ n ∧ gm.2 ≤ n := by
    intro gm hgm
    rcases Multiset.mem_cons.mp hgm with h | h
    · subst h
      refine ⟨?_, ?_⟩ <;> · show _ ≤ n; omega
    · rw [Multiset.eq_of_mem_replicate h]
      exact ⟨by omega, by omega⟩
  have hanchor : R.s0 / R.e ≤ (W - R.e * (R.wSide / R.e)) / R.e :=
    Nat.div_le_div_right (by omega)
  exact ⟨⟨⟨hD, R.hw, hW1, R.he, hlen1, hlammem⟩,
      ⟨flankOf_comp _, hG1mid, (flankOf_comp _).1⟩, rfl, ⟨rfl, rfl⟩,
      ⟨hlamsum, hselmem⟩, hG6⟩,
    ⟨hDn, hwn, ⟨hbox', haell, hdw, hWdiv⟩, hb4,
      ⟨hen, helln, hs0n, hdn, hWn, hlamcap, heel, hanchor⟩⟩⟩

/-- the accumulated stage degree D_i = ∏_{m<i} e_m·g_m (D.5's output law). -/
private def bD (P : MovesD.ShapePrefix) (i : ℕ) : ℕ :=
  ((P.reads.take i).map (fun R => R.e * R.g)).prod

/-- the inherited window W_i (n at the root, μ_{i-1} after — D.8's output law). -/
private def bW (n : ℕ) (P : MovesD.ShapePrefix) : ℕ → ℕ
  | 0 => n
  | i + 1 => ((P.reads[i]?).map MovesD.ShapeRead.μ).getD 1

private theorem bD_zero (P : MovesD.ShapePrefix) : bD P 0 = 1 := rfl

private theorem bD_pos (P : MovesD.ShapePrefix) (i : ℕ) : 1 ≤ bD P i := by
  have h : 0 < ((P.reads.take i).map (fun R => R.e * R.g)).prod := by
    apply List.prod_pos
    intro a ha
    obtain ⟨R, -, hR⟩ := List.mem_map.mp ha
    rw [← hR]
    exact Nat.mul_pos R.he R.hg
  exact h

private theorem bD_succ (P : MovesD.ShapePrefix) (i : ℕ)
    (hi : i < P.reads.length) :
    bD P (i + 1) = bD P i * ((P.reads[i]'hi).e * (P.reads[i]'hi).g) := by
  unfold bD
  rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some,
    List.map_append, List.prod_append, List.map_singleton,
    List.prod_singleton]

private theorem bW_succ (n : ℕ) (P : MovesD.ShapePrefix) (i : ℕ)
    (hi : i < P.reads.length) : bW n P (i + 1) = (P.reads[i]'hi).μ := by
  have h0 : bW n P (i + 1) = ((P.reads[i]?).map MovesD.ShapeRead.μ).getD 1 := rfl
  rw [h0, List.getElem?_eq_getElem hi]
  rfl

private theorem bW_two {n : ℕ} {P : MovesD.ShapePrefix}
    (hn : 2 ≤ n)
    (hcont : ∀ (r : ℕ) (hr : r + 1 < P.reads.length),
      2 ≤ (P.reads[r]'(Nat.lt_of_succ_lt hr)).μ)
    (i : ℕ) (hi : i < P.reads.length) : 2 ≤ bW n P i := by
  cases i with
  | zero => exact hn
  | succ j =>
    rw [bW_succ n P j (Nat.lt_of_succ_lt hi)]
    exact hcont j hi

private theorem bW_box {n : ℕ} {P : MovesD.ShapePrefix}
    (hWF : MovesD.ShapeWF n P) (i : ℕ) (hi : i < P.reads.length) :
    (P.reads[i]'hi).s0 + (P.reads[i]'hi).wSide ≤ bW n P i := by
  cases i with
  | zero => exact hWF.root_box hi
  | succ j =>
    rw [bW_succ n P j (Nat.lt_of_succ_lt hi)]
    exact hWF.window j hi

private theorem bWD_le {n : ℕ} {P : MovesD.ShapePrefix}
    (hWF : MovesD.ShapeWF n P) :
    ∀ i, i < P.reads.length → bW n P i * bD P i ≤ n := by
  intro i
  induction i with
  | zero =>
    intro _
    rw [bD_zero]
    show n * 1 ≤ n
    omega
  | succ j ih =>
    intro hj1
    have hj : j < P.reads.length := Nat.lt_of_succ_lt hj1
    rw [bW_succ n P j hj, bD_succ P j hj]
    have hlw : (P.reads[j]'hj).e * ((P.reads[j]'hj).wSide / (P.reads[j]'hj).e)
        = (P.reads[j]'hj).wSide := Nat.mul_div_cancel' (hWF.edvd j hj)
    have hkey : (P.reads[j]'hj).e * (P.reads[j]'hj).g * (P.reads[j]'hj).μ
        ≤ bW n P j := by
      have h1 : (P.reads[j]'hj).e * ((P.reads[j]'hj).g * (P.reads[j]'hj).μ)
          ≤ (P.reads[j]'hj).e * ((P.reads[j]'hj).wSide / (P.reads[j]'hj).e) :=
        Nat.mul_le_mul_left _ (hWF.gmu j hj)
      have h2 := bW_box hWF j hj
      calc (P.reads[j]'hj).e * (P.reads[j]'hj).g * (P.reads[j]'hj).μ
          = (P.reads[j]'hj).e * ((P.reads[j]'hj).g * (P.reads[j]'hj).μ) := by ring
        _ ≤ (P.reads[j]'hj).wSide := by omega
        _ ≤ bW n P j := by omega
    calc (P.reads[j]'hj).μ * (bD P j * ((P.reads[j]'hj).e * (P.reads[j]'hj).g))
        = ((P.reads[j]'hj).e * (P.reads[j]'hj).g * (P.reads[j]'hj).μ) * bD P j := by
          ring
      _ ≤ bW n P j * bD P j := Nat.mul_le_mul_right _ hkey
      _ ≤ n := ih hj

private theorem bw_le_bD {n : ℕ} {P : MovesD.ShapePrefix}
    (hWF : MovesD.ShapeWF n P) :
    ∀ i, ∀ hi : i < P.reads.length, (P.reads[i]'hi).w ≤ bD P i := by
  intro i
  induction i with
  | zero => intro hi; rw [bD_zero, hWF.w0 hi]
  | succ j ih =>
    intro hj1
    have hj : j < P.reads.length := Nat.lt_of_succ_lt hj1
    rw [hWF.wchain j hj1, bD_succ P j hj]
    calc (P.reads[j]'hj).w * (P.reads[j]'hj).g
        ≤ bD P j * (P.reads[j]'hj).g := Nat.mul_le_mul_right _ (ih hj)
      _ ≤ bD P j * ((P.reads[j]'hj).e * (P.reads[j]'hj).g) :=
          Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (P.reads[j]'hj).he)

private theorem letterOf_fits {n : ℕ} {P : MovesD.ShapePrefix}
    (hWF : MovesD.ShapeWF n P) (i : ℕ) (hi : i < P.reads.length) :
    SpFitsRead n i (letterOf n i (bD P i) (bW n P i) (P.reads[i]'hi))
      (P.reads[i]'hi) := by
  have hmt : monicTopOf n (letterOf n i (bD P i) (bW n P i) (P.reads[i]'hi))
      = decide ((P.reads[i]'hi).s0 + (P.reads[i]'hi).wSide = n) := by
    have hlw : (P.reads[i]'hi).e * ((P.reads[i]'hi).wSide / (P.reads[i]'hi).e)
        = (P.reads[i]'hi).wSide := Nat.mul_div_cancel' (hWF.edvd i hi)
    unfold monicTopOf
    show decide ((P.reads[i]'hi).s0
        + (P.reads[i]'hi).e * ((P.reads[i]'hi).wSide / (P.reads[i]'hi).e) = n)
      = decide ((P.reads[i]'hi).s0 + (P.reads[i]'hi).wSide = n)
    rw [hlw]
  have hspecies : (P.reads[i]'hi).species
      = (if i = 0 then MovesC.ReadSpecies.root
         else speciesTagOf (letterOf n i (bD P i) (bW n P i) (P.reads[i]'hi))) := by
    by_cases h0 : i = 0
    · subst h0
      rw [if_pos rfl]
      exact (hWF.species_iff 0 hi).mpr rfl
    · rw [if_neg h0]
      unfold speciesTagOf letterOf
      by_cases hsp : (P.reads[i]'hi).species = MovesC.ReadSpecies.increment
      · simp only [if_neg h0, if_pos hsp]
        exact hsp
      · have hR : (P.reads[i]'hi).species = MovesC.ReadSpecies.recentering := by
          cases hR2 : (P.reads[i]'hi).species with
          | root => exact absurd ((hWF.species_iff i hi).mp hR2) h0
          | increment => exact absurd hR2 hsp
          | recentering => rfl
        rw [if_neg h0, if_neg hsp]
        exact hR
  have hmonic : (P.reads[i]'hi).monicTop
      = (decide (i = 0)
          && monicTopOf n (letterOf n i (bD P i) (bW n P i) (P.reads[i]'hi))) := by
    have htie := hWF.monic i hi
    by_cases h0 : i = 0
    · subst h0
      rw [hmt, decide_eq_true rfl, Bool.true_and]
      by_cases hc : (P.reads[0]'hi).s0 + (P.reads[0]'hi).wSide = n
      · rw [decide_eq_true hc]
        exact htie.mpr ⟨rfl, hc⟩
      · rw [decide_eq_false hc]
        cases hmt2 : (P.reads[0]'hi).monicTop with
        | false => rfl
        | true => exact absurd (htie.mp hmt2).2 hc
    · rw [decide_eq_false h0, Bool.false_and]
      cases hmt2 : (P.reads[i]'hi).monicTop with
      | false => rfl
      | true => exact absurd (htie.mp hmt2).1 h0
  have hlmem : ((P.reads[i]'hi).g, (P.reads[i]'hi).μ) ∈ lamOf (P.reads[i]'hi) :=
    Multiset.mem_cons_self _ _
  exact ⟨rfl, rfl, rfl, rfl, rfl, hlmem, rfl, rfl, rfl, hspecies, hmonic⟩

private theorem letterOf_stage {n : ℕ} {P : MovesD.ShapePrefix}
    (hWF : MovesD.ShapeWF n P) (hspec : SpeciesCoherent P)
    (i : ℕ) (hi1 : i + 1 < P.reads.length) :
    MovesSp.StageLaws
      (letterOf n i (bD P i) (bW n P i) (P.reads[i]'(Nat.lt_of_succ_lt hi1)))
      (letterOf n (i+1) (bD P (i+1)) (bW n P (i+1)) (P.reads[i+1]'hi1)) := by
  have hi : i < P.reads.length := Nat.lt_of_succ_lt hi1
  unfold MovesSp.StageLaws
  show _ ∧ _ ∧ _ ∧ _ ∧ _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- D′ = e·g·D
    show bD P (i+1) = (P.reads[i]'hi).e * (P.reads[i]'hi).g * bD P i
    rw [bD_succ P i hi]
    ring
  · -- w′ = g·w
    show (P.reads[i+1]'hi1).w = (P.reads[i]'hi).g * (P.reads[i]'hi).w
    rw [hWF.wchain i hi1]
    exact Nat.mul_comm _ _
  · -- W′ = μ
    exact bW_succ n P i hi
  · -- tag′ = POST-INC iff e·g ≥ 2 (the cross-read species-coherence law)
    show (if i + 1 = 0 then MovesSp.Tag.root
        else if (P.reads[i+1]'hi1).species = MovesC.ReadSpecies.increment
        then MovesSp.Tag.postInc else MovesSp.Tag.postRec) = MovesSp.Tag.postInc
      ↔ 2 ≤ (P.reads[i]'hi).e * (P.reads[i]'hi).g
    rw [if_neg (Nat.succ_ne_zero i)]
    by_cases hsp : (P.reads[i+1]'hi1).species = MovesC.ReadSpecies.increment
    · rw [if_pos hsp]
      exact iff_of_true rfl ((hspec i hi1).mp hsp)
    · rw [if_neg hsp]
      exact iff_of_false (by simp) (fun h2 => hsp ((hspec i hi1).mpr h2))
  · -- tag′ = POST-REC iff e = g = 1
    show (if i + 1 = 0 then MovesSp.Tag.root
        else if (P.reads[i+1]'hi1).species = MovesC.ReadSpecies.increment
        then MovesSp.Tag.postInc else MovesSp.Tag.postRec) = MovesSp.Tag.postRec
      ↔ ((P.reads[i]'hi).e = 1 ∧ (P.reads[i]'hi).g = 1)
    rw [if_neg (Nat.succ_ne_zero i)]
    have hegpos : 1 ≤ (P.reads[i]'hi).e * (P.reads[i]'hi).g :=
      Nat.mul_pos (P.reads[i]'hi).he (P.reads[i]'hi).hg
    by_cases hsp : (P.reads[i+1]'hi1).species = MovesC.ReadSpecies.increment
    · rw [if_pos hsp]
      refine iff_of_false (by simp) ?_
      rintro ⟨he1, hg1⟩
      have h2 := (hspec i hi1).mp hsp
      rw [he1, hg1] at h2
      omega
    · rw [if_neg hsp]
      refine iff_of_true rfl ?_
      have h1 : ¬ 2 ≤ (P.reads[i]'hi).e * (P.reads[i]'hi).g :=
        fun h2 => hsp ((hspec i hi1).mpr h2)
      have hle1 : (P.reads[i]'hi).e ≤ (P.reads[i]'hi).e * (P.reads[i]'hi).g :=
        Nat.le_mul_of_pos_right _ (P.reads[i]'hi).hg
      have hlg1 : (P.reads[i]'hi).g ≤ (P.reads[i]'hi).e * (P.reads[i]'hi).g :=
        Nat.le_mul_of_pos_left _ (P.reads[i]'hi).he
      have hee := (P.reads[i]'hi).he
      have hgg := (P.reads[i]'hi).hg
      exact ⟨by omega, by omega⟩

private theorem letterOf_cat {n : ℕ} {P : MovesD.ShapePrefix}
    (hWF : MovesD.ShapeWF n P) (hn : 2 ≤ n)
    (hcont : ∀ (r : ℕ) (hr : r + 1 < P.reads.length),
      2 ≤ (P.reads[r]'(Nat.lt_of_succ_lt hr)).μ)
    (hspec : SpeciesCoherent P) :
    ∀ i (hi : i < P.reads.length),
      MovesSp.InCatalogue n
        (letterOf n i (bD P i) (bW n P i) (P.reads[i]'hi)) := by
  intro i
  induction i with
  | zero =>
    intro hi
    obtain ⟨hcoh, hbud⟩ := letterOf_ok n 0 (bD P 0) (bW n P 0) (P.reads[0]'hi)
      (bD_pos P 0) (bW_two hn hcont 0 hi) hn (bW_box hWF 0 hi)
      (hWF.gmu 0 hi) (hWF.edvd 0 hi) (bWD_le hWF 0 hi) (bw_le_bD hWF 0 hi)
    have hroot : MovesSp.RootStage n
        (letterOf n 0 (bD P 0) (bW n P 0) (P.reads[0]'hi)) := by
      refine ⟨?_, bD_zero P, hWF.w0 hi, rfl⟩
      show (if 0 = 0 then MovesSp.Tag.root
          else if (P.reads[0]'hi).species = MovesC.ReadSpecies.increment
          then MovesSp.Tag.postInc else MovesSp.Tag.postRec) = MovesSp.Tag.root
      rw [if_pos rfl]
    exact MovesSp.InCatalogue.root ⟨hroot, hcoh, hbud⟩
  | succ j ih =>
    intro hj1
    have hj : j < P.reads.length := Nat.lt_of_succ_lt hj1
    obtain ⟨hcoh, hbud⟩ := letterOf_ok n (j+1) (bD P (j+1)) (bW n P (j+1))
      (P.reads[j+1]'hj1) (bD_pos P (j+1)) (bW_two hn hcont (j+1) hj1) hn
      (bW_box hWF (j+1) hj1) (hWF.gmu (j+1) hj1) (hWF.edvd (j+1) hj1)
      (bWD_le hWF (j+1) hj1) (bw_le_bD hWF (j+1) hj1)
    exact MovesSp.InCatalogue.step (ih hj)
      ⟨letterOf_stage hWF hspec j hj1, hcoh, hbud⟩

/-- the fitted species word — the ∃-witness of `spWord_exists`. -/
private def bWord (n : ℕ) (P : MovesD.ShapePrefix) : List MovesSp.Species :=
  List.ofFn (fun i : Fin P.reads.length =>
    letterOf n i (bD P i) (bW n P i) (P.reads[i]'i.isLt))

/-- ORDER-0 SCOPE (ADJ-2; supersedes the pass-B3 refutation note): the fitting
species word EXISTS on the scoped stratum — width hypotheses (`hn`/`hcont`,
2026-07-30 repair) + the cross-read species-coherence law (`hspec`, ADJ-2).
Unscoped forms: REFUTED, `V3_spwordA_negWitness.lean` (width) and
`V3_spword_negWitness2.lean` (species off-by-one) — the negWitnesses are the
standing record.  Phase B pointer: discharging `SpeciesCoherent` from the
engine's D.7/D.8 output laws re-opens the full family. -/
theorem spWord_exists (n : ℕ) (P : MovesD.ShapePrefix)
    (hWF : MovesD.ShapeWF n P) (hn : 2 ≤ n)
    (hcont : ∀ (r : ℕ) (hr : r + 1 < P.reads.length),
      2 ≤ (P.reads[r]'(Nat.lt_of_succ_lt hr)).μ)
    (hspec : SpeciesCoherent P) :
    ∃ ws, SpWordFits n P ws := by
  have hlen : (bWord n P).length = P.reads.length := by
    simp [bWord]
  refine ⟨bWord n P, hlen, ?_, ?_, ?_⟩
  · -- per-index fit clauses
    intro i hw hp
    have hg1 : (bWord n P).get ⟨i, hw⟩
        = letterOf n i (bD P i) (bW n P i) (P.reads[i]'hp) := by
      simp [bWord, List.get_eq_getElem]
    rw [hg1, List.get_eq_getElem]
    exact letterOf_fits hWF i hp
  · -- catalogue membership
    intro s hs
    simp only [bWord, List.mem_ofFn] at hs
    obtain ⟨i, rfl⟩ := hs
    exact letterOf_cat hWF hn hcont hspec i i.isLt
  · -- the SuccStep chain
    apply List.isChain_iff_getElem.mpr
    intro i hi
    have hi1 : i + 1 < P.reads.length := by
      rw [hlen] at hi
      exact hi
    have hi0 : i < P.reads.length := Nat.lt_of_succ_lt hi1
    have hg1 : (bWord n P)[i]'(by omega)
        = letterOf n i (bD P i) (bW n P i) (P.reads[i]'hi0) := by
      simp [bWord]
    have hg2 : (bWord n P)[i+1]'(by rw [hlen]; exact hi1)
        = letterOf n (i+1) (bD P (i+1)) (bW n P (i+1)) (P.reads[i+1]'hi1) := by
      simp [bWord]
    rw [hg1, hg2]
    obtain ⟨hcoh, hbud⟩ := letterOf_ok n (i+1) (bD P (i+1)) (bW n P (i+1))
      (P.reads[i+1]'hi1) (bD_pos P (i+1)) (bW_two hn hcont (i+1) hi1) hn
      (bW_box hWF (i+1) hi1) (hWF.gmu (i+1) hi1) (hWF.edvd (i+1) hi1)
      (bWD_le hWF (i+1) hi1) (bw_le_bD hWF (i+1) hi1)
    exact ⟨letterOf_stage hWF hspec i hi1, hcoh, hbud⟩

/-- ORDER-0 SCOPE (ADJ-2): `spWord` fits, on the same scoped stratum as
`spWord_exists` (whose hypotheses it threads). -/
theorem spWord_fits (n : ℕ) (P : MovesD.ShapePrefix)
    (hWF : MovesD.ShapeWF n P) (hn : 2 ≤ n)
    (hcont : ∀ (r : ℕ) (hr : r + 1 < P.reads.length),
      2 ≤ (P.reads[r]'(Nat.lt_of_succ_lt hr)).μ)
    (hspec : SpeciesCoherent P) :
    SpWordFits n P (spWord n P) := by
  rw [spWord, dif_pos (spWord_exists n P hWF hn hcont hspec)]
  exact (spWord_exists n P hWF hn hcont hspec).choose_spec

end LeanUrat.MovesV
