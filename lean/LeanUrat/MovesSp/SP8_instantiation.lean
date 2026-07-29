/-
Unit Sp.instantiation (SP8) — the wave-C INSTANTIATION charges of the ratification
verdict `lean/notes/MOVESSP_RATIFY_CODEX_2026-07-30.md` (REJECT 3M/2N; M1/M2/M3
"accepted as wave-C instantiation charges"). ADDITIVE ONLY: `SP_COMP` and its
interface `CanTreeModel` are untouched; this unit builds the BRIDGE.

M1 (this file, part 1) — the verdict: "SP-COMP is an interface closure lemma, not
the note's actual-tree completeness theorem … There is no definition of the actual
canonical tree and no theorem constructing `CanTreeModel` from it." The BUILT
canonical-tree carrier is `LeanUrat.MovesD.TreeModel` (T_can(f) with L2's
structural layer; branches = `Option (History p F)`, `none` the empty chain, root
presence a LAW). What the built vocabulary does NOT reach is the per-read RETAINED
SPECIES DATUM of a realized chain (λ needs the full residual factorization; the
window widths need the parent-μ thread) — that readout is exactly the W-7 seam
(CUT-3's image is the intended instance: `MovesS/Defs.lean:587` "[2a] finiteness;
CUT-3's image is the intended instance (W-7, seam)"). Per the charge, that residue
is typed as ONE named premise, `SpeciesReadout` (warrant: the W-7 seam row), and
the instantiation theorem `SP_COMP_ofTreeModel` is built as far as the built
vocabulary reaches: the branch carrier is the REAL one ({o // T.mem o x}), and
`hTotal` is discharged by the BUILT law `TreeModel.root_mem` — a law of the
E-phase core, not a hypothesis.

M2 (part 2) — the non-vacuity witness at n = 2, transported from the built G1 toy
(`MovesT/G1_toyGate.lean` `toyHead`/`toyLeafA` node literals). M3 (part 3) — the
strong verdict pin (alphabet V + τ + detection cap; D4R.0-K(c)) with the
strong-implies-weak bridge.
-/
import LeanUrat.MovesSp.SP3_compMember
import LeanUrat.MovesSp.SP0_reflCoherent
import LeanUrat.MovesSp.SP0_reflBudget
import LeanUrat.MovesSp.SP0_reflSucc
import LeanUrat.MovesT.G1_toyGate

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesSp

open LeanUrat.MovesC LeanUrat.MovesD

/-! ### M1 — the instantiation seam, typed as ONE named premise -/

-- [E-DEV, universe pin] `CanTreeModel.Branch : Type` is universe-0, so the real
-- carrier `{o : Option (History p F) // T.mem o x}` forces `F : Type` here (every
-- built instance — ZMod p, F4 — lives there; no content is lost).
variable {p : ℕ} [Fact p.Prime] {F : Type} [Field F] [Finite F]
variable {n N m : ℕ} {pol : CanonPolicy p F}

/-- **THE W-7 SEAM RESIDUE, AS ONE NAMED PREMISE** [ratification M1, warrant: the
W-7 seam row — `MovesS/Defs.lean:587` "CUT-3's image is the intended instance
(W-7, seam)"]: the per-read RETAINED-SPECIES READOUT of the BUILT canonical tree
`LeanUrat.MovesD.TreeModel`, with the SP-COMP engine laws stated AT the realized
carriers (`T.mem o x` guards every law — realized chains of T_can at the box
member x; the intended instance keys x = f's coefficient-box image). Every field
mirrors the corresponding `CanTreeModel` field one-for-one (same law, same ℕ∞
casts), so the constructor below is a literal re-keying, and each field's owner
line is inherited from `CanTreeModel`'s docstrings (hRoot/hStage/hCoh/hHalt:
§B2-DEF D.4–D.10 + §C DOM via §D4-R, owner HC-1/MovesD; hVerdictPin: the
D4R.0-K(c) residual, owner [3t] via VP — its STRONG form is `StrongVerdictPin`
below, M3). NOT expressible from the built vocabulary (hence residue): the datum
map itself — a `Node` records the selected (g, μ) but not the residual partition
λ, and the read's window width W is the parent-read's μ, threaded along the
chain. -/
structure SpeciesReadout (T : TreeModel p F n N m pol) (x : Box p m) where
  /-- the catalogue-word length of a realized chain (ℕ∞; ⊤ = prefixwise-infinite). -/
  lenOf : Option (History p F) → ℕ∞
  /-- the retained species datum of read r (junk above `lenOf`). -/
  datumOf : Option (History p F) → ℕ → Species
  /-- the leaf verdict of a finitely-ended chain. -/
  verdictOf : Option (History p F) → Option Verdict
  /-- the n = 1 clause (mirrors `CanTreeModel.hN1`). -/
  hN1 : n = 1 → ∀ o, T.mem o x → 0 < lenOf o
  /-- root stage + coherence + budget at read 0 (mirrors `CanTreeModel.hRoot`). -/
  hRoot : ∀ o, T.mem o x → 0 < lenOf o →
    RootStage n (datumOf o 0) ∧ Coherent (datumOf o 0) ∧ Budget n (datumOf o 0)
  /-- raw stage laws per consecutive read pair (mirrors `CanTreeModel.hStage`). -/
  hStage : ∀ o, T.mem o x → ∀ r : ℕ, (r + 1 : ℕ∞) < lenOf o →
    StageLaws (datumOf o r) (datumOf o (r + 1))
  /-- budgets + coherence at every read (mirrors `CanTreeModel.hCoh`). -/
  hCoh : ∀ o, T.mem o x → ∀ r : ℕ, (r : ℕ∞) < lenOf o →
    Coherent (datumOf o r) ∧ Budget n (datumOf o r)
  /-- the word closes at its first confirming W = 1 read (mirrors `CanTreeModel.hHalt`). -/
  hHalt : ∀ o, T.mem o x → ∀ r : ℕ, (r : ℕ∞) < lenOf o → (datumOf o r).W = 1 →
    lenOf o = (r + 1 : ℕ∞)
  /-- the weak verdict pin (mirrors `CanTreeModel.hVerdictPin`; D4R.0-K(c) carrier). -/
  hVerdictPin : ∀ o, T.mem o x → ∀ k : ℕ, lenOf o = (k : ℕ∞) → 0 < k →
    (verdictOf o).isSome

/-- **THE INSTANTIATION CONSTRUCTOR** [ratification M1]: a `CanTreeModel` whose
branch carrier is the REAL canonical-tree carrier — the realized states
`{o : Option (History p F) // T.mem o x}` of the BUILT `MovesD.TreeModel` at the
box member x (`none` = the empty chain ∅). What the built vocabulary discharges:
`hTotal` is the BUILT law `TreeModel.root_mem` (L2: "its root is the empty chain
∅" — the root's presence is a law of the E-phase core), NOT a hypothesis. All
remaining fields are the ONE named premise `R` re-keyed literally. The key `f` is
a phantom parameter of the abstract interface (no `CanTreeModel` field mentions
it — the ratification M1 finding); the intended instance pins x = f's
coefficient-box image, recorded here as the docstring tie, not a law. -/
def canTreeModel_ofTreeModel (f : Polynomial ℤ_[p])
    (T : TreeModel p F n N m pol) (x : Box p m)
    (R : SpeciesReadout T x) : CanTreeModel n p f where
  Branch := {o : Option (History p F) // T.mem o x}
  hTotal := ⟨⟨none, T.root_mem x⟩⟩
  len η := R.lenOf η.1
  hN1 := fun h1 η => R.hN1 h1 η.1 η.2
  datum η r := R.datumOf η.1 r
  hRoot := fun η h => R.hRoot η.1 η.2 h
  hStage := fun η r hr => R.hStage η.1 η.2 r hr
  hCoh := fun η r hr => R.hCoh η.1 η.2 r hr
  hHalt := fun η r hr hw => R.hHalt η.1 η.2 r hr hw
  verdict η := R.verdictOf η.1
  hVerdictPin := fun η k hk h0 => R.hVerdictPin η.1 η.2 k hk h0

/-- **THE INSTANTIATION THEOREM** [ratification M1, as far as the built vocabulary
reaches]: for every monic degree-n f, every BUILT tree model T (the actual
T_can(f) carrier once x = f's box image), every REALIZED chain o of T at x, and
every read r of its catalogue word, the retained datum is a member of 𝒮ₙ^raw —
SP-COMP fired THROUGH the real carrier. Conditionality: exactly the ONE named
premise `R : SpeciesReadout T x` (the W-7 seam row); nothing else is assumed
beyond the built `TreeModel` laws. -/
theorem SP_COMP_ofTreeModel (f : Polynomial ℤ_[p])
    (hf : f.Monic) (hdeg : f.natDegree = n)
    (T : TreeModel p F n N m pol) (x : Box p m) (R : SpeciesReadout T x)
    (o : Option (History p F)) (ho : T.mem o x)
    (r : ℕ) (hr : (r : ℕ∞) < R.lenOf o) :
    InCatalogue n (R.datumOf o r) :=
  SP_COMP n p f hf hdeg (canTreeModel_ofTreeModel f T x R) ⟨o, ho⟩ r hr

/-! ### M2 — the non-vacuity witness at n = 2, transported from the built G1 toy

The ratification M2 finding: "non-vacuity fails for every n ≠ 1 … `SP_COMP`,
`SP_COMP_edges`, and `SP_COMP_collapsed` can all hold with zero reads and no
engine content." The charge: exhibit a `CanTreeModel` with ≥ 1 ACTUAL catalogue
reads at n = 2 or 3, transported from a built witness. The built witness is the
G1 toy A branch (`MovesT/G1_toyGate.lean`): history [toyHead, toyLeafA] — the
REV-8 table's root read (e, g, μ) = (1, 1, 2) on window W = n = 2 followed by the
recentering read (1, 1, 1), which τ-irr halts (μ = 1). Its species readout is the
THREE-letter catalogue word below (the third letter is the confirming W = 1 read
the halt opens); the transport ties are `rfl`-checked against the node literals'
retained fields. -/

/-- the toy head read's species datum (from `MovesT.toyHead`: e = 1, s0 = 0,
ℓ = wSide/e = 2, selection (g, μ) = (1, 2); root window W = n = 2; λ = {(1, 2)}
by (G4) Σgμ = ℓ). -/
def wordHead : Species :=
  ⟨.root, 1, 1, 2, 1, 0, 2, 0, 3, Finset.Icc 0 2, {(1, 2)}, some (1, 2), [], []⟩

/-- the toy leaf-a read's species datum (from `MovesT.toyLeafA`: e = 1, s0 = 0,
ℓ = 1, selection (1, 1); window W = parent-μ = 2; tag POST-REC since the head's
e·g = 1). -/
def wordMid : Species :=
  ⟨.postRec, 1, 1, 2, 1, 0, 1, 0, 2, Finset.Icc 0 1, {(1, 1)}, some (1, 1), [], [1]⟩

/-- the confirming close (W = leaf-a's μ = 1, selection ⊥ by (G6)) — the first
W = 1 read, where the catalogue word ends (SP.4's halt convention). -/
def wordLast : Species :=
  ⟨.postRec, 1, 1, 1, 1, 0, 1, 0, 2, Finset.Icc 0 1, {(1, 1)}, none, [], []⟩

theorem wordHead_rootAdmissible : RootAdmissible 2 wordHead :=
  (rootAdmissibleB_iff 2 wordHead).mp (by decide)

theorem succStep_wordHead_wordMid : SuccStep 2 wordHead wordMid :=
  (succStepB_iff 2 wordHead wordMid).mp (by decide)

theorem succStep_wordMid_wordLast : SuccStep 2 wordMid wordLast :=
  (succStepB_iff 2 wordMid wordLast).mp (by decide)

/-- TRANSPORT TIE (head): the witness letter's retained fields ARE the built toy
head node's — stride, raw endpoint, side length, selection, species tag. -/
theorem wordHead_transports_toyHead :
    wordHead.e = MovesT.toyHead.e ∧ wordHead.s0 = MovesT.toyHead.s0 ∧
    wordHead.ell = MovesT.toyHead.wSide / MovesT.toyHead.e ∧
    wordHead.sel = some (MovesT.toyHead.g, MovesT.toyHead.μ) ∧
    (wordHead.tag = Tag.root ↔ MovesT.toyHead.species = MovesC.ReadSpecies.root) :=
  ⟨rfl, rfl, rfl, rfl, ⟨fun _ => rfl, fun _ => rfl⟩⟩

/-- TRANSPORT TIE (mid): fields from `MovesT.toyLeafA`; the WINDOW is the built
head node's μ (the parent-μ thread — exactly the datum the seam premise carries). -/
theorem wordMid_transports_toyLeafA :
    wordMid.W = MovesT.toyHead.μ ∧
    wordMid.e = MovesT.toyLeafA.e ∧ wordMid.s0 = MovesT.toyLeafA.s0 ∧
    wordMid.ell = MovesT.toyLeafA.wSide / MovesT.toyLeafA.e ∧
    wordMid.sel = some (MovesT.toyLeafA.g, MovesT.toyLeafA.μ) ∧
    (wordMid.tag = Tag.postRec ↔
      MovesT.toyLeafA.species = MovesC.ReadSpecies.recentering) :=
  ⟨rfl, rfl, rfl, rfl, rfl, ⟨fun _ => rfl, fun _ => rfl⟩⟩

/-- TRANSPORT TIE (close): the toy A branch τ-irr HALTS (leaf μ = 1), and the
transported word's final letter is exactly the confirming W = 1, selection-⊥
read that halt opens. -/
theorem wordLast_transports_halt :
    MovesT.toyLeafA.μ = 1 ∧ wordLast.W = MovesT.toyLeafA.μ ∧
    wordLast.W = 1 ∧ wordLast.sel = none :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- the witness key: f₂ := (X − 1)², monic of degree 2 over ℤ_[2] — the binder pin
matching the toy's residual data (toyHead's Ranch = 1 + X² = (X − 1)² over 𝔽₂,
zbar = 1). The key is PHANTOM in the abstract interface (the M1 finding: no
`CanTreeModel` field mentions f), so this pin is a quantifier-fidelity record. -/
noncomputable def f₂ : Polynomial ℤ_[2] := (Polynomial.X - Polynomial.C 1) ^ 2

theorem f₂_monic : f₂.Monic := (Polynomial.monic_X_sub_C 1).pow 2

theorem f₂_natDegree : f₂.natDegree = 2 := by
  rw [f₂, Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C]

/-- the transported catalogue word as a read map (junk `wordLast` above r = 2). -/
def toyWord : ℕ → Species
  | 0 => wordHead
  | 1 => wordMid
  | _ => wordLast

/-- **THE NON-VACUITY WITNESS** [ratification M2]: a `CanTreeModel` at n = 2 whose
single branch is the transported G1 toy A branch — len = 3, datum = the
three-letter word above. Every law field is DISCHARGED BY COMPUTATION on actual
letters (no vacuous premise: the read laws all fire). The verdict label `.ep`
records that the branch τ-irr halts (`wordLast_transports_halt`); WHICH bare
label the {(1,1)} verdict carries is VP-owned ([3t]) — see `toyStrongPin` (M3)
for the pinned alphabet route. -/
noncomputable def toyCanModel : CanTreeModel 2 2 f₂ where
  Branch := PUnit
  hTotal := ⟨PUnit.unit⟩
  len _ := 3
  hN1 := fun h => absurd h (by decide)
  datum _ r := toyWord r
  hRoot := fun _ _ => wordHead_rootAdmissible
  hStage := by
    intro η r hr
    have hr' : r + 1 < 3 := by exact_mod_cast hr
    have hr'' : r < 2 := by omega
    interval_cases r
    · exact succStep_wordHead_wordMid.1
    · exact succStep_wordMid_wordLast.1
  hCoh := by
    intro η r hr
    have hr' : r < 3 := by exact_mod_cast hr
    interval_cases r
    · exact ⟨wordHead_rootAdmissible.2.1, wordHead_rootAdmissible.2.2⟩
    · exact ⟨succStep_wordHead_wordMid.2.1, succStep_wordHead_wordMid.2.2⟩
    · exact ⟨succStep_wordMid_wordLast.2.1, succStep_wordMid_wordLast.2.2⟩
  hHalt := by
    intro η r hr hw
    have hr' : r < 3 := by exact_mod_cast hr
    interval_cases r
    · exact absurd hw (by decide)
    · exact absurd hw (by decide)
    · norm_num
  verdict _ := some Verdict.ep
  hVerdictPin := fun _ _ _ _ => rfl

/-- SP-COMP fires at every one of the witness's THREE actual reads. -/
theorem toyCanModel_reads_in_catalogue (r : ℕ) (hr : r < 3) :
    InCatalogue 2 (toyCanModel.datum PUnit.unit r) :=
  SP_COMP 2 2 f₂ f₂_monic f₂_natDegree toyCanModel PUnit.unit r
    (show (r : ℕ∞) < (3 : ℕ∞) by exact_mod_cast hr)

/-- **SP-COMP FIRES NON-VACUOUSLY AT n = 2** [ratification M2, discharged by
exhibition]: a `CanTreeModel` at n = 2 > 1 with a branch of catalogue-word length
3, whose read 0 is an ACTUAL root-stage letter, and all of whose reads land in
𝒮₂^raw through `SP_COMP`. (The M2 zero-read model still satisfies the interface —
that is the weak pin's honest perimeter — but the interface is now INHABITED with
engine content at n > 1, which is what the charge demanded.) -/
theorem SP_COMP_nonvacuous_at_n2 :
    ∃ (M : CanTreeModel 2 2 f₂) (η : M.Branch),
      M.len η = 3 ∧
      M.datum η 0 = wordHead ∧ RootStage 2 (M.datum η 0) ∧
      (∀ r : ℕ, (r : ℕ∞) < M.len η → InCatalogue 2 (M.datum η r)) :=
  ⟨toyCanModel, PUnit.unit, rfl, rfl, wordHead_rootAdmissible.1,
    fun r hr => SP_COMP 2 2 f₂ f₂_monic f₂_natDegree toyCanModel PUnit.unit r hr⟩

/-! ### M3 — the STRONG verdict pin (the note-faithful D4R.0-K(c) residual)

The ratification M3 finding: the weak field `hVerdictPin` "asserts merely that
some label exists after a finite nonempty word. It does not express: which
verdict is correct; where τ fires; the parent-read versus confirming-read pin;
mutual exclusivity; the detection cap." The residual's OWN statement
(`lean/notes/D4R0K_DERIVATION_2026-07-26.md` S2.6, quoted):
  (c1) "a pinned VERDICT ALPHABET V and a HALTING RULE τ … τ a function of CELL
       data alone (never of f)";
  (c2) "EXACTLY-ONE-VERDICT on a CLOSED domain … each receives exactly one
       verdict, none orphaned, none doubled";
  (c3-b) "FINITE-CAP DETECTABILITY … τ is a STOPPING RULE for the window digit
       filtration — every halt-and-verdict decision is determined by the capped
       cell datum at some finite height."
The vocabulary now exists in the built corpus: the alphabet is `MovesT.Vd`
(VP-1: finite multisets of pairs (E, F), MOVES 7061–7063), the rule is the
`MovesT.VerdictModelT.vdict` genre ((τ-irr)/(τ-ns)/(τ-hen), consumed by
`MovesT.VPPinned.model`), and the cap laws are `MovesT.TBCapPinned` /
`MovesT.CapIrrLaw` (TB-CAP). `StrongVerdictPin` below states that residual AT
THE CanTreeModel INTERFACE — the box-digit filtration transposed to the
catalogue-word filtration through the same W-7 readout seam as M1. -/

/-- **THE STRONG VERDICT PIN** [ratification M3]: the D4R.0-K(c) residual with
its full content, per clause: `tauV` is (c1)'s halting rule INTO the pinned
alphabet `MovesT.Vd` (VP-1), typed on `Species` — a function of CELL DATA ALONE
(the retained read datum), never of f; `dict` maps alphabet values onto the bare
labels (`Verdict` — "semantics owned by [3t]'s VP"); `htau` pins WHERE τ fires
(at the word's closing read — the confirming ⊥-read or the continuing letter
whose V_term edge ends the word) and WHICH verdict it emits — with `hinf`, this
is (c2) on the closed domain: every finitely-ended nonempty word gets EXACTLY
the τ-verdict (none orphaned — that is the weak field; none doubled — the value
is pinned), infinite branches get none; `cap`/`hcap` is (c3-b)'s UNIFORM
DETECTION CAP (the TB-CAP genre, `MovesT.TBCapPinned`): every halt-and-verdict
decision is determined by the cap-truncated word datum. NOT retyped into
`CanTreeModel` (statement fence — `SP_COMP` and its interface stand);
`StrongVerdictPin.weak` is the bridge. -/
structure StrongVerdictPin {f : Polynomial ℤ_[p]} (M : CanTreeModel n p f) where
  /-- (c1) the halting rule τ, into the VP-1 alphabet, from cell data alone. -/
  tauV : Species → MovesT.Vd
  /-- (c1) the bare-label dictionary out of the alphabet (label choice VP-owned). -/
  dict : MovesT.Vd → Verdict
  /-- (c2) attachment + exactly-one: a word of length r + 1 carries EXACTLY the
  τ-verdict of its closing read r. -/
  htau : ∀ η (r : ℕ), M.len η = ((r + 1 : ℕ) : ℕ∞) →
    M.verdict η = some (dict (tauV (M.datum η r)))
  /-- (c2) closed domain: infinite branches carry no leaf verdict. -/
  hinf : ∀ η, M.len η = ⊤ → M.verdict η = none
  /-- (c3-b) the uniform detection cap. -/
  cap : ℕ
  /-- (c3-b) the stopping rule: the verdict is determined by the capped word. -/
  hcap : ∀ η η', M.len η = M.len η' →
    (∀ r : ℕ, r < cap → M.datum η r = M.datum η' r) →
    M.verdict η = M.verdict η'

/-- **STRONG ⇒ WEAK** [ratification M3, the bridge direction]: a strong pin
discharges the interface's weak field verbatim, so every existing SP-COMP
consumer stands unchanged, and a model builder holding the strong residual owes
nothing further to the weak one. -/
theorem StrongVerdictPin.weak {f : Polynomial ℤ_[p]} {M : CanTreeModel n p f}
    (S : StrongVerdictPin M) :
    ∀ η (k : ℕ), M.len η = (k : ℕ∞) → 0 < k → (M.verdict η).isSome := by
  intro η k hk h0
  obtain ⟨r, rfl⟩ : ∃ r, k = r + 1 := ⟨k - 1, by omega⟩
  rw [S.htau η r hk]
  rfl

/-- **THE NOTE-FAITHFUL RESIDUAL, RECORDED** [ratification M3]: the ledger's
D4R.0-K(c) carrier for this interface is henceforth THIS Prop — the weak field
stays in `CanTreeModel` for interface stability only, `StrongVerdictPin.weak`
its bridge. Owner unchanged: [3t] via VP (VP-3's proof duties = (c2) + (c3) +
VP-SOUND); the built box-level carriers are `MovesT.VPPinned` (VP-1/VP-2) and
`MovesT.TBCapPinned` (TB-CAP). -/
def StrongVerdictResidual {f : Polynomial ℤ_[p]} (M : CanTreeModel n p f) : Prop :=
  Nonempty (StrongVerdictPin M)

/-- the witness carries a STRONG pin too (the strong residual is non-vacuously
satisfiable at n = 2): τ emits the built (τ-irr) alphabet value {(1, 1)} — the
toy A branch's accumulated (E, F) = (accE, accF) = (1, 1) — at every closing
read, `.ep` its bare label (choice VP-owned), cap 3 ≥ the word length. -/
noncomputable def toyStrongPin : StrongVerdictPin toyCanModel where
  tauV _ := MovesT.irrVerdict 1 1 le_rfl le_rfl
  dict _ := Verdict.ep
  htau := fun _ _ _ => rfl
  hinf := fun η h => absurd (show (3 : ℕ∞) = ⊤ from h) (by decide)
  cap := 3
  hcap := fun _ _ _ _ => rfl

/-- ALPHABET TIE: the pinned τ-value at the witness IS the built (τ-irr) verdict
of the built toy A branch history — `MovesT.irrVerdictOf MovesT.tA2a` = {(1, 1)}. -/
theorem toyStrongPin_alphabet_tie :
    toyStrongPin.tauV wordLast = MovesT.irrVerdictOf MovesT.tA2a := rfl

/-- the witness's weak pin, re-derived through the bridge (the M3 chain closes). -/
theorem toyCanModel_weak_of_strong :
    ∀ (η : toyCanModel.Branch) (k : ℕ), toyCanModel.len η = (k : ℕ∞) → 0 < k →
      (toyCanModel.verdict η).isSome :=
  toyStrongPin.weak

end LeanUrat.MovesSp
