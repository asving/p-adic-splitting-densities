# M11-cl19-rep — attempt (Fable, 2026-07-31)

Obligation: BK.cl19_rep, history face = `Slot_jcInvHist` (SlotsG10). Companion
brief: `M11-cl19-rep_brief.md` (statement + all definitions unfolded there;
this file assumes it).

## §0 Verdict summary

`Slot_jcInvHist n` — the normative Lean form of the history face — is **FALSE
at n = 2**, and the corpus itself already contains the kernel-checked
refutation (`slot_jcInvHist_falsifiable`, SlotsG11c_seamAudit.lean; axioms
re-verified this session: propext, Classical.choice, Quot.sound only). The
refutation is structural, not accidental: `Slot_jcInvHist` is the unique
member of the thirteen-slot family that closes over its carriers (∀ tree
model T, ∀ cell datum CA *inside* the Prop), so the campaign's own
non-vacuity falsifier — for the other twelve slots an ∃-degenerate-carrier
statement compatible with truth at the real carrier — here collapses to an
outright disproof of the closed consumable. Consequence: **no caller can
ever discharge `theoremU`'s `jcInvHist` hypothesis by proving
`Slot_jcInvHist 2`**; as normatively stated the obligation is dead, and I
record the verdict REFUTED-as-stated.

The intended mathematical content (CL-19's (JC-INV) display) is *not*
refuted. I give: (i) the exact structural diagnosis; (ii) a repaired
statement `Slot_jcInvHist'` matching the family's carrier-parameterized
pattern (a statement-change event — requires sign-off; the slot gates
nothing at HEAD, so the repair is cheap now); (iii) a rigorous reduction of
the repaired obligation at any instance to three named structural lemmas
(JC-a rectangularity, JC-b read locality, JC-c key-transport), via two fully
proved counting criteria; (iv) executed exact numeric tests supporting the
intended invariance at real-classifier-shaped instances, including a control
showing the tests have power.

## §1 The refutation (already known in-corpus; independently audited here)

Statement refuted: see the brief. In-corpus proof:
`LeanUrat.MovesU.slot_jcInvHist_falsifiable : ∃ n : ℕ, ¬ Slot_jcInvHist n`,
witness n = 2. I re-verified its axiom footprint through the LSP on
2026-07-31: `{propext, Classical.choice, Quot.sound}` — Lean-core only, no
sorryAx anywhere in its dependency cone (the one `sorry` in that file is the
unrelated `slot_m4bConst_falsifiable`).

The counterexample, in standard mathematics (p = 2, F = 𝔽₂, n = 2, N = 1,
m = 2; box = 𝔽₂², 4 points):

- Two one-node histories t1 = [ν₁], t2 = [ν₂], where ν₂ = ν₁ except in the
  recorded recentering-center field. That field is NOT in the retained
  roster (species, e, g, μ, a, s0, wSide, Dwidth, #K), so
  `NodeRetainedKeyEq t1.lastNode t2.lastNode` holds by nine `rfl`s, while
  t1 ≠ t2 as histories.
- The tree model (`MovesT.sibModel`): both t1 and t2 realized exactly on the
  slice Σ = Σ' = {x : x₀ = 0} (2 points); no deeper chains. All four
  TreeModel laws check; the realizability law is discharged because ν₁, ν₂
  genuinely satisfy HistoryCoherent/Realizable/IsCanonPres (proved in
  S2_sibFalse for the concrete node data — the center field is unconstrained
  there for a root-species node).
- The degenerate cell datum (`jcFalsCA`): alphabet Fin 4; the state-entrance
  joint read is **a function of the history identity alone**:
  Ψ_H(x) := if H = t1 then 2 else 3 (constant in x). Root/reduction entrance
  reads and branch sets are arranged so every CellData law holds (state
  cells 2, 3 carry empty branch sets; the toy has no children at state
  sites, so `child_cell` is two dead implications; `cell_local` is trivial
  for reads constant in x).
- At cell c = 2:  #(Ψ_{t1}⁻¹(2) ∩ Σ)·#Σ' = 2·2 = 4, while
  #(Ψ_{t2}⁻¹(2) ∩ Σ')·#Σ = 0·2 = 0.  4 ≠ 0. ∎

Elementary recount executed (test N1 below): 4 vs 0, confirmed.

**Generalization (conjecture, mechanical).** ∀ n ≥ 1, ¬ Slot_jcInvHist n.
Nothing in the witness uses n = 2 except types: `TreeModel`'s and
`CellData`'s fields and laws never mention n; the chart argument can be
taken constant (χ := fun _ => 0 : Fin n → Fin 2); the `.red g ψ` case of the
degenerate read only uses the box argument. So the same toy data literally
assembles a witness at every n. I have not compiled this; labeled
conjecture (compile-check estimated routine).

## §2 Why the interface cannot save the statement

The load-bearing fact: **`cellOf` at `.st H` entrances is free per-entrance
data.** The only law constraining `cellOf` in its entrance argument is —
none. `cell_local` constrains the BOX argument (locality in coordinates);
`child_cell`/`branch_cell_joint` relate `cellOf` to the child relation and
the per-site read *at the same entrance*; no law compares `cellOf (.st H)`
with `cellOf (.st H')` for H ≠ H'. A joint read that inspects the history
label itself is therefore a legal CellData, and any statement of
history-invariance quantified over ALL CellData is false for this trivial
reason. The same holds on the T side: `mem` at distinct histories is free up
to the snoc laws, so even a "history-blind" restriction on CA cannot rescue
the internal ∀ (see §4, alternative repair).

This is precisely the failure mode the campaign's own records anticipate:
the thirteen rows "were left bare precisely because faithful self-contained
typing FAILED once" (BP1 blueprint §3.8). The G10 formulation re-attempted a
self-contained typing; the falsifier certifies that it, too, is not
self-containable.

## §3 Structural diagnosis (the new finding of this attempt)

Signature census of the thirteen slots (all on disk except rel-family
details irrelevant here):

| slot | carrier position |
|---|---|
| Slot_rs0Lump n **(C : UCarriers n)** | parameter |
| Slot_trackRule n {C} **(KC) (K7)** | parameter |
| Slot_dnLattice n {C} **(KC) (K7)** | parameter |
| Slot_m1m5Echo n **(C)** | parameter |
| Slot_x1aDict n {C} **(KC)** | parameter |
| Slot_m4bConst n {Cv} {Sv} **(V : CtsMeasured …)** | parameter |
| Slot_rel1 … rel3 (G2/G3/G16–G18) | CInterface/SiteData parameters |
| **Slot_jcInvHist n** | **∀ p N m pol T CA internal** |

For every parameterized slot, the wave-2 falsifier doctrine ("must be FALSE
for a degenerate instance the note would reject") produces
`∃ carrier, ¬ Slot(carrier)` — fully compatible with `Slot(real carrier)`
being true and eventually proved. For `Slot_jcInvHist` alone, the same
doctrine produces `¬ Slot_jcInvHist n` outright. The D-SC per-slot design
table (BP1 blueprint §D-SC.3) records G10's falsifier uniformly with the
others as a discharged non-vacuity audit; I found no note recording that
for this one slot "falsifiable" = "refuted", i.e. that the planned
`theoremU_bridged` (IB-G13/G13′, not yet written) would, at
jcInvHist := Slot_jcInvHist n, carry a hypothesis PROVABLY FALSE at n = 2 —
permanently undischargeable, the exact condition the wave-4 boundary record
exists to prevent (in the opposite direction: it guards against trivial
dischargeability; this is the dual failure). This paragraph is the finding
that should reach the Q13 adjudication before G13′ is drafted.

## §4 The repair (statement-change proposal; requires sign-off)

**R1 (recommended): carrier parameterization, matching the family pattern.**

```lean
/-- CL-19 history face, carrier-parameterized (repair of Slot_jcInvHist;
    inner statement verbatim). -/
def Slot_jcInvHist' (n : ℕ) {p : ℕ} [Fact p.Prime] {N m : ℕ}
    {pol : MovesD.CanonPolicy p (ZMod p)}
    (T : MovesD.TreeModel p (ZMod p) n N m pol)
    (CA : MovesT.CellData p (ZMod p) n N m pol T) : Prop :=
  ∀ (χ : Fin n → Fin m) (H H' : MovesC.History p (ZMod p)),
    (MovesT.entEvent T χ (MovesT.EntSt.st H)).Nonempty →
    (MovesT.entEvent T χ (MovesT.EntSt.st H')).Nonempty →
    NodeRetainedKeyEq H.lastNode H'.lastNode →
    ∀ c : CA.Cell,
      Nat.card ↥(MovesT.cellEventE T CA χ (MovesT.EntSt.st H) c)
          * Nat.card ↥(MovesT.entEvent T χ (MovesT.EntSt.st H'))
        = Nat.card ↥(MovesT.cellEventE T CA χ (MovesT.EntSt.st H') c)
          * Nat.card ↥(MovesT.entEvent T χ (MovesT.EntSt.st H))
```

- Faithfulness: the inner statement is verbatim; only the quantifier over
  (p, N, m, pol, T, CA) moves from inside the Prop to the binder, where the
  consumer (G13′) instantiates it at the wave-D real tree/cell instances
  (per prime and level, exactly as the other twelve slots are instantiated
  at their real carriers). CL-19's display speaks of THE classifier's tree,
  not of all abstract tree models, so parameterization is *more* faithful,
  not less.
- The existing compiled falsifier survives verbatim as the repaired slot's
  non-vacuity audit: the same witness proves
  `∃ T CA, ¬ Slot_jcInvHist' 2 T CA` (the doctrine's intended shape).
- Cost: `Slot_jcInvHist` has zero consumers at HEAD (G12 manifest; grep) —
  the repair touches one def + the G11c falsifier statement + the G12
  manifest row. Statement-fence: sign-off required, warrant = this file +
  the kernel-checked refutation.

**Rejected alternative: lawfulness class, keeping the internal ∀.** One might
keep `Slot_jcInvHist n` closed and guard by "history-blind CA" (cellOf at
`.st H` factors through the retained key of H.lastNode). This still fails:
take the sib toy with child relation
`child none ν x := (ν = ν₁ ∧ x₀ = 0) ∨ (ν = ν₂ ∧ x₁ = 0)` (both nodes as in
§1), so Σ_{t1} = {x₀ = 0}, Σ_{t2} = {x₁ = 0}, and the SHARED history-blind
read Ψ(x) := (x₁ = 0). Then P(Ψ = true │ Σ_{t1}) = 1/2 but
P(Ψ = true │ Σ_{t2}) = 1 — key-equal entrances, history-blind read, law
fails, because the MODEL's membership data is still free. (Uncompiled
sketch; the point is architectural: the invariance is a property of the
real instance's (T, CA) *jointly*, not of any interface-definable subclass.
So carrier parameterization is the only sound repair shape.)

## §5 The repaired obligation, reduced (rigorous part)

All statements in this section are fully proved here except the three
labeled OPEN.

**Lemma A (balanced-factorization criterion).** Let B, B' be finite sets,
Σ ⊆ B, Σ' ⊆ B', and Ψ : B → C, Ψ' : B' → C maps to a set C. Suppose there
exist a finite set W, maps w : Σ → W, w' : Σ' → W, a map κ : W → C, and
constants k, k' ∈ ℕ such that

  (i) Ψ = κ ∘ w on Σ and Ψ' = κ ∘ w' on Σ';
  (ii) every fiber of w has exactly k elements and every fiber of w' has
       exactly k' elements (over ALL of W).

Then for every c ∈ C:  #(Ψ⁻¹(c) ∩ Σ)·#Σ' = #(Ψ'⁻¹(c) ∩ Σ')·#Σ.

*Proof.* By (i), Ψ⁻¹(c) ∩ Σ = w⁻¹(κ⁻¹(c)), a disjoint union of #κ⁻¹(c)
fibers of w, so #(Ψ⁻¹(c) ∩ Σ) = k·#κ⁻¹(c); likewise
#(Ψ'⁻¹(c) ∩ Σ') = k'·#κ⁻¹(c). Also #Σ = k·#W and #Σ' = k'·#W (disjoint
unions over W). Hence both sides equal k·k'·#κ⁻¹(c)·#W. ∎
(No nonemptiness or divisibility needed; entirely division-free.)

**Corollary B (bijective transport).** If there is a bijection β : Σ → Σ'
with Ψ' ∘ β = Ψ on Σ, the conclusion of Lemma A holds (take W = Σ, w = id,
w' = β⁻¹, κ = Ψ|_Σ, k = k' = 1). ∎

**Proposition C (rectangular-entrance schema).** Fix finite coordinate boxes
B = ∏_{i ∈ I} A_i and a subset R ⊆ I ("the read's fresh block"). Suppose

  (a) Σ ⊆ B is a *spectator* of R: membership in Σ depends only on the
      coordinates outside R (x ∈ Σ, x' agrees with x off R ⟹ x' ∈ Σ);
  (b) Ψ : B → C depends, on Σ, only on the coordinates in R, inducing
      ψ : ∏_{i ∈ R} A_i → C with Ψ = ψ ∘ proj_R on Σ;
  (a'),(b') the same for Σ', Ψ' with fresh block R' in a coordinate box B';
  (c) there is a bijection ρ : ∏_{i ∈ R} A_i → ∏_{i ∈ R'} A'_i with
      ψ = ψ' ∘ ρ.

Then for every c: #(Ψ⁻¹(c) ∩ Σ)·#Σ' = #(Ψ'⁻¹(c) ∩ Σ')·#Σ.

*Proof.* By (a), Σ = A_Σ × ∏_{i ∈ R} A_i under B ≅ (∏_{i ∉ R} A_i) ×
(∏_{i ∈ R} A_i), where A_Σ is the projection of Σ to the off-R part. Apply
Lemma A with W := ∏_{i ∈ R'} A'_i, w := ρ ∘ proj_R (fibers of size
k = #A_Σ, using (a) and bijectivity of ρ), w' := proj_{R'} (fibers of size
k' = #A_{Σ'}), κ := ψ'. Condition (i): κ ∘ w = ψ' ∘ ρ ∘ proj_R =
ψ ∘ proj_R = Ψ on Σ by (c),(b); and κ ∘ w' = ψ' ∘ proj_{R'} = Ψ' on Σ' by
(b'). ∎

**Reduction.** At any instance (T*, CA*), the repaired slot
`Slot_jcInvHist' n T* CA*` follows from, for every realized key-equal pair
(H, H'):

- **(JC-a) OPEN — entrance rectangularity.** Σ_H is a spectator of the
  read's fresh coordinate block R_H := {i : levelOf i < cellLevel (.st H),
  i not pinned at entrance}. This is the C.1.5 level-separation of the
  entrance state from the site's fresh digits. The corpus already carries
  its per-site interface form: `MovesT.SpectatorFor` and the SiteLedger
  field `spectator_sol` (MovesT/Defs.lean, the 2026-07-30 E6-adjudicated
  law), plus the `free`/`hfresh` clause-support laws — (JC-a) is its
  entrance-event-level statement at the real instance.
- **(JC-b) OPEN — read locality.** On Σ_H, Ψ_H depends only on R_H,
  inducing ψ_H on the fresh digit block. Interface form already present:
  `CellData.cell_local` (locality below `cellLevel`); what is open is that
  the entrance pins everything below the fresh block, i.e. R_H is exactly
  the residual dependence.
- **(JC-c) OPEN — key-only transport.** A bijection ρ of the fresh digit
  blocks with ψ_H = ψ_{H'} ∘ ρ, whenever NodeRetainedKeyEq holds. This is
  the genuine [2b] mathematics: the fresh-window digit-to-cell map is, up
  to a bijective re-coordinatization of the fresh digits, a function of
  (species, e, g, μ, a, s0, wSide, Dwidth, #K) alone. Supporting corpus
  assets: the HC1 carry-algebra kernel (the verifier-specified
  D = F[u]/(u^e − z̄) dictionary) and the anchor-monomial transport (the
  (z+c)^a factor, Case-J gate passed) — note the retained key KEEPS the
  anchor a and DROPS the height data (h, u*, γ): exactly the split these
  kernels predict, since heights translate valuations (absorbed into which
  coordinates are fresh — the ρ) while (a, e, g, μ, #K) govern the
  residue-level cell map. The h_ent-erasure is the height-shift conjugacy
  of the note's (β-1); (JC-c) is its JOINT upgrade — the step (u-R)-style
  single-branch marginal invariance provably does not supply (equal
  marginals tolerate different correlations and different branching-cell
  selection; the note says this explicitly).

By Proposition C, (JC-a) + (JC-b) + (JC-c) ⟹ the repaired slot at the
instance. The executed control test (below) shows (JC-a) is genuinely
load-bearing: over-pinning one fresh digit at the entrance breaks the law
at every cell.

Risk assessment for (JC-c) (honest): the danger spots are multi-side
windows (the joint cell includes the branching-cell selection law across
sides; the (SIB) row starts only after conditioning on the branching cell,
so nothing upstream supplies the selection law — a genuine correlation
claim) and recentering chains (species is retained, so recentering states
never key-match increment states — good); the note's own adjudication
channel for a surviving failure is R2's lumpability wall (one 𝒯-refinement
round, then wall). I did not find a counterexample to the intended
instance-level claim, and the numerics below support it.

## §6 Deliverable summary (for the orchestrator)

1. REFUTED as stated: `¬ Slot_jcInvHist 2` is a kernel-checked in-corpus
   theorem (Lean-core axioms; re-verified). No wave-D discharge of
   theoremU's `jcInvHist` via `Slot_jcInvHist n` is possible at n = 2;
   conjecturally at any n. **Do not draft G13′ against the current G10.**
2. Adjudication item (new): G10 is the unique carrier-internalized slot of
   the thirteen; its "discharged falsifier" is an outright refutation. The
   R1 repair (carrier parameterization, inner statement verbatim) restores
   the family pattern, keeps the falsifier as a genuine ∃-degenerate audit,
   and costs one def + two touch-ups; requires statement-change sign-off.
3. REDUCED after repair: Lemma A / Corollary B / Proposition C (proved
   here) reduce the repaired slot at any instance to (JC-a) entrance
   rectangularity + (JC-b) read locality + (JC-c) key-only fresh-digit
   transport — the third is the real [2b] mathematics, aligned with the
   HC1 carry-algebra + anchor-transport kernels and the note's (β-1)
   height-shift conjugacy.
4. Classification of results: §1 is (a) already known (in-corpus theorem,
   audited); §3's uniqueness finding and §4's repair analysis are (c)
   claimed new (to the corpus record); §5's Lemma A/Cor B/Prop C are (b)
   elementary/standard counting arguments given full proofs here; JC-a/b/c
   are explicitly OPEN lemmas.

VERDICT: REFUTED (as normatively stated; kernel-checked, in-corpus, axioms
re-audited) — with a proposed repair under which the obligation becomes
REDUCED to three named open structural lemmas via fully-proved counting
criteria; the intended instance-level invariance is numerically supported
and remains open.

## NUMERIC-TESTS

Executed this session (exact integer counting, python3; all counts exact,
no floats):

- **(N1) Falsifier recount** — Box = 𝔽₂², Σ = Σ' = {x₀ = 0}, Ψ ≡ 2,
  Ψ' ≡ 3, c = 2: LHS = 4, RHS = 0. CONFIRMS the compiled refutation's
  arithmetic.
- **(N2) h_ent-invariance at the n = 2 self-loop (real-classifier shape).**
  D uniform mod p^N; entrance at height k: Σ_k = {p^{2k} ∣ D} (the k-fold
  undecided doubling loop for x² − D); joint 2-digit read
  Ψ_k(D) = (D/p^{2k}) mod p². Cross-multiplied law checked at ALL cells and
  all height pairs k, l ∈ {0,1,2}: p = 2 (N = 8, #Σ = 256/64/16), p = 3
  (N = 6, 729/81/9), p = 5 (N = 6, 15625/625/25) — INVARIANT, exactly.
- **(N3) n = 3 dilation loop, p = 2, N = 8** — (a, b) mod 2^N,
  Σ_k = {v(a) ≥ 2k ∧ v(b) ≥ 3k} (the monomial-dilation self-loop for
  x³ + ax + b), joint read (a/2^{2k} mod 4, b/2^{3k} mod 4), heights
  k ∈ {0,1,2} (#Σ = 65536/2048/64): INVARIANT, exactly, at all 16 cells.
- **(Control, power check)** — same as N3 at k = 1 but with the entrance
  over-pinned by one fresh digit (v(a) ≥ 2k+1) while the read frame stays
  keyed to the state (divide by 2^{2k}): the cross-multiplied law FAILS at
  16/16 cells. So the tests are not vacuous, and (JC-a) — the entrance
  must be a spectator of the read's fresh block — is exactly the
  load-bearing hypothesis.

Proposed further tests (not run; specs concrete enough to hand to the
numerics fleet):

- **(P1) Genuine second-read joint law at an e = 2, μ = 2 window (n = 4,
  p = 2).** Entrance family at height parameter k: monic quartics
  x⁴ + a₃x³ + a₂x² + a₁x + a₀ with v(a₃) ≥ k+1, v(a₂) ≥ 2k+1 with
  a₂/2^{2k+1} ≡ 0 (mod 2), v(a₁) ≥ 3k+2, v(a₀) = 4k+2 with
  a₀/2^{4k+2} ≡ 1 (mod 2) — this realizes the first read: side of slope
  −(2k+1)/2 over slots [0,4] (e = 2, h = 2k+1, wSide = 4), residual
  z² + 1 = (z+1)² over 𝔽₂ (g = 1, μ = 2), retained key equal across k,
  h_ent = 2k+1 varying. Read: the SECOND-read joint digit cell — implement
  either directly (transported window digits of f(x) under the OM
  transform at the e = 2 frame) or, coarser but oracle-checkable, the
  final ℚ₂-splitting type via PARI `factorpadic` (any coarsening of an
  invariant law is invariant, so a coarsened FAILURE refutes; coarsened
  agreement is supporting evidence only — say so in the report).
  Enumerate coefficients mod 2^{4k+2+6}, k ∈ {0, 1, 2}; PASS = exact
  cross-multiplied equality of the coarsened law across k; FAIL at any
  cell = counterexample to (JC-INV) as roster'd — escalate to the R2
  lumpability channel per the note.
- **(P2) Representative-invariance at fixed h_ent (the cl19_rep face,
  same machinery).** Same family as P1 at fixed k, but vary the entrance
  REPRESENTATIVE: partition Σ_k by the erased data (e.g. the value of
  a₃/2^{k+1} mod 2, or recentering path taken to reach the state) into
  subclasses with identical retained key, and check the joint second-read
  law is identical across subclasses. PASS/FAIL as in P1. This probes the
  (r2) roster choice itself: a FAIL against a subclass keyed by an ERASED
  field means the roster is too coarse (a faithfulness failure of (r2),
  flagged in the G10 header as the falsifier-visible risk).
- **(P3) Roster-sharpness probe.** Deliberately merge entrances with
  DIFFERENT retained keys (e.g. different μ, or different a) and confirm
  the law FAILS — establishing that each roster component is necessary,
  i.e. the retained key is minimal as well as sufficient. Ranges: p ∈
  {2, 3}, n ∈ {2, 3, 4}, levels N ≤ 14 with #enumeration ≤ 2²⁴ per cell
  table.
