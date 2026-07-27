# MOVESD LEAN BLUEPRINT REV 4 — FRESH-INSTANCE CONFIRMATION AUDIT (FABLE #3)

Date: 2026-07-28 · Auditor: fresh Fable #3 (no rev-1/2/3 conversational context; ground
truth read directly) · Scope: rev-4 confirmation per
`CAMPAIGN_AUDIT_CHARGE_2026-07-28.md`, including an INDEPENDENT re-derivation of the
§0.6 gate numbers from the rebuilt canonRoot construction. Ground truth:
`MOVES_2026-07-24.md` §D4-R rev 9 (lines 4580–5435) + the dual-acceptance record
(6783–6831); `LeanUrat/MovesC/Defs.lean` (978 lines). Blueprint:
`MOVESD_LEAN_BLUEPRINT_2026-07-28.md` rev 4 (898 lines), read in full.

VERDICT LINE (details below): **ACCEPT** — 0 critical / 0 blocking gap; 2 non-blocking
observations (OBS-1, OBS-2).

---

## 1. Independent gate recomputation (charge item 1) — PASS, every number reproduced

All numbers recomputed from the blueprint's OWN definitions (not its prose), then
checked against §D4-R.6.

Shape data (from the note's pinned instance): read 0 (root): (e,h,g,μ,a) = (1,1,2,1,0),
s0 = 0, wSide = 3, Dwidth = 1, u*₀ = 0, w₀ = 1, monicTop = true; read 1 (recentering):
(1,3,1,1,0), s0 = 0, wSide = 1, Dwidth = 2 (= childWidthS of read 0 = 1·2·1), u*₁ = 1,
w₁ = 2, monicTop = false.

- ℓ₀ = wSide/e = 3, d₀ = ℓ₀ + 0 = 3; ℓ₁ = 1, d₁ = ℓ₁ + 1 = 2.
  **W = 1·3 + 2·2 = 7 ✓** (note: "W(P̂*) = Σ_r w_r·d_r = 1·3 + 2·2 = 7").
- mbar₀ = 3/(2·1) = 1, mbar₁ = 1/(1·1) = 1, **M = 1 ✓** (note: "⌊3/2⌋·⌊1/1⌋ = 1").
- lineS 0: slope = h/(e·strS·Dwidth) = 1/(1·1·1) = 1, intercept = u*₀ + 1·((0+3)·1) = 3.
  lineS 1: strS 1 = e₀ = 1, slope = 3/(1·1·2) = 3/2, intercept = 1 + (3/2)·((0+1)·2) = 4.
  **Nshape = 1 + max(⌈3⌉, ⌈4⌉) = 5 ✓** (note: "N(P̂*) = 1 + (largest pinned base
  level = 4, at c₀) = 5").
- A via the blueprint's OWN bandS (an independent check the blueprint did not display):
  read 0 — prevRimS 0 = 3, floorS = ⊥, htS = ℓ, slotVal(b) = 3 − b; band =
  {(ℓ,b) : b < 3, ℓ ≤ 3−b} = 4+3+2 = 9 coordinates — exactly the note's "3 cluster +
  3 below-line + 3 on-line = 9" (b=0: ℓ∈0..3; b=1: ℓ∈0..2; b=2: ℓ∈0..1). Read 1 —
  prevRimS 1 = μ₀·childWidthS₀ = 2, floorS = line₀.at 0 = 3, htS = ℓ + (b mod 2)·κ₀
  (κ₀ = 1), fineSlot = b/2 = 0, slotVal(0) = 4; band = {3 < ℓ+(b%2) ≤ 4, b < 2} =
  {(4,0), (3,1)} = 2 — exactly the note's "two ν₁ pins binding c₀'s level-4 and c₁'s
  level-3 digits". **A = 9 + 2 = 11 ✓**, and all 11 sit in the 5×3 grid, so A′ = 11 ✓.
- **C_P̂*(2) = 3 ✓**: over F₂ the unique monic irreducible quadratic is ψ = z²+z+1,
  r = 1, R₀ = (z²+z+1)(z+1) = z³+1 → the single tuple (d₂,d₁,d₀) = (0,0,1); ψ-image
  determined by the tuple (UFD); zbar₀ NOW PINNED to canonRoot (rev 3's ×2 conjugate
  split is gone — the ×2 was exactly Fable#2's C = 6 defect); read 1: d'₁ = vtx(ν₀)
  — recomputed literally: R₀/ψ = z+1, mod ψ = z+1, a₀ = 0, m̂₀ = 0 ⟹ vtx = z̄+1 =
  z̄−r (char 2), one canonical value ω₀+1 (×1); ψ₁ = z−s with s = −d'₀/d'₁ determined
  (×1); d'₀ ∈ F₄ˣ (×3, endpoint d'₀ ≠ 0 = hpat0). Total 1·1·3 = 3 = the sealed
  "C_P̂*(2) = 1·1·3 = 3".
- **C_P̂*(3) = 48 ✓**: quadratics {z²+1, z²+z+2, z²+2z+2} verified rootless over F₃
  (values (1,2,2), (2,1,2), (2,2,1) at z = 0,1,2), N₂(3) = 3 ✓; r ∈ {1,2} → 6 pairs →
  6 DISTINCT digit tuples (UFD); spot check (z²+1)(z+2) = z³+2z²+z+2 → (2,1,2) = the
  note's displayed example ✓; zbar₀ pinned ×1; d'₁ forced ×1 (e.g. ψ = z²+1, r = 1:
  vtx = z̄+2 = z̄−1 ✓); d'₀ ∈ F₉ˣ ×8. Total 6·8 = 48 = the sealed "3·2·8 = 48".
- **mult ≡ 1 ✓**: within P̂*, equal etaData across both reads forces equal (ψ₀, r) and
  equal ψ₁ (unique quadratic: deg R₀ = 3 < 4 = 2g₀μ₀; R₁ linear — the note's FACTOR
  SELECTION line), so distinct classes occupy distinct digit cells and each f realizes
  exactly its cell's one class — the note's rev-6 gate re-derivation verbatim
  ("m_r = 1 PER CELL at both reads … mult_P̂* ≡ 1 … D4R.1-EV/D4R.4-EV hold with
  EQUALITY").

§0.6's re-derivation is CONFIRMED number-for-number, including the parts it did not
itself display (the bandS coordinate lists).

## 2. canonRoot + IsCanonPres — the conjugate quotient (charge item 2) — PASS

Two-conjugate example, checked: at the p = 2 gate, ψ₀Image = z²+z+1 has the two roots
{ω, ω²} ⊂ F₄ ⊆ F; rev 3's PrefSet contained both presentations (conjugated stages
satisfy the Stage/Node laws), and the (HV)-forced depth-1 lead ω+1 vs ω²+1 gave
distinct ambient etaData — 2 classes per note-η, C = 6. Rev 4's `IsCanonPres` clause
`(zbar : F) = canonRoot ν` keeps exactly the fieldEnum-least root: 1 class per
note-η, count 3 ✓. Consistency checks: (i) at recenterings `hspecRecCenter` forces
zbar = center while canonRoot(X − center) = center — compatible, no over-constraint;
(ii) `hzbarRoot` (every legal Node's zbar is a root of ψ in F) guarantees ψImage has
roots in F, so canonRoot's junk-0 branch never fires on real nodes and the clause is
satisfiable; (iii) the by-induction canonical tower embedding (prime field unique;
depth r+1: z ↦ pinned least root) makes abstract-η digit data ⟺ F-valued class data,
both directions (no split, no merge — Codex 2's merge direction closed too).

PRESENT-NORM: declared ✓ SINGLE ✓ (one ledger row, §2, HC-2 owner, both proof
ingredients named: conjugation equivariance + finite-field embedding rigidity;
gate-checked). Typed: NO — see OBS-1 below (non-blocking; the exactly parallel
junk-lift normalization pin is likewise prose and passed two prior audits).

## 3. The four §11 pushbacks (charge item 3) — ALL FOUR UPHELD

- **C-1 (monicTop) — UPHELD, partial concession sound.** L11's own reconstruction
  mechanism ("digits give each R_anch; s_r picks ψ_r; canonical lifts are functions of
  node data") needs every side slot's digit except box-forced ones; the only box-forced
  digit the note displays is the ROOT monic lead ("slot 3 = the monic lead, digit 1",
  §D4-R.6), while the depth-1 lead is IN the tuple ("the (HV)-forced lead makes the
  pool bound strict — slack displayed"). d_r = ℓ_r + (monicTop ? 0 : 1) reproduces
  d₀ = 3, d₁ = 2, W = 7 (checked, §1). `hmonicRoot` (monicTop → root species) is a
  correct guard: deeper windows sit inside the box (window containment s0'+w' ≤ μ),
  and note the monic lead x^n is not even a box coordinate (the box is c₀..c_{n−1}).
  Junk monicTop=false full-span shapes constrain only their own PrefSet — consistent.
- **C-4 (CanonPolicy) — UPHELD.** L1's display is verbatim "the digits t_k are
  FUNCTIONS of the node data … the policy is deterministic" — `liftOf` + `blind` is
  exactly that law; `fun _ => False` is inexpressible; ∀-pol theorems are a sound
  strengthening (instantiating at the (S6b) policy later recovers the note); WHICH
  policy is §B2-DEF/HC-1's by the campaign DAG, now named POL-PIN in the ledger.
- **C-6 first half (empty ontology) — UPHELD.** `History.nonempty` (Defs.lean:
  `nodes ≠ []`) means the Lean History type genuinely has no empty chain; CD's
  if-branch IS the note's own definition-level dispatch ("Pref(∅) = {∅} … dispatched
  FIRST, separately from Theorem C(b)"), `Pref_empty_shape` displays the History-level
  emptiness honestly, and D14a's law is L5's normalized full-box display connected in
  corpus vocabulary (emptyFiber = univ, card p^{nN}, A′ = 0, CD = 1). Second half
  (hne) verified applied: D10/D12/D13/D3b/D4R4_all all carry `hne`.
- **C-8 (TreeModel) — UPHELD; the displayed falsifying computation CHECKS.**
  mem := False satisfies the generation laws, but D15 consumes `D4R_CYL S T`, and D0c
  (fiber_pos, from Theorem C(b)'s positive mass — "Theorem C(b) gives mass
  p^{−A(P̂)} > 0") makes every enumerated fiber nonempty; so for any family with a
  realized class, some x ∈ S.fiber i has x ∈ fiber ↔ T.mem (reprOf i) x = False —
  contradiction: the empty tree enters no consumer. And a root-inhabitation law WOULD
  be unfaithful: L5's "(ns) NO-SIDE cases — the window polygon admits no eligible
  side: a terminal verdict" makes ∅ a leaf for some inputs. Exhaustive-children
  semantics correctly parked behind the kernel-(b)/HC-2 pins.

## 4. EligibleImage vs L11 (charge item 4) — PASS

The transported predicate: `q.Monic ∧ q.natDegree = g ∧ OrdPsiPoly q Rq μ ∧
∃ q₀ over poolSubfield, Irreducible q₀ ∧ q₀.map subtype = q`. Predecessor's
counterexample re-run: R with 4 distinct linear factors over the pool, g = 2, μ = 1 —
the six monic ord-1 quadratic divisors are products of two pool-rational linears, so
their (unique, coefficient-determined) lifts q₀ are REDUCIBLE over the pool subfield:
all six FAIL the ∃-clause; only the (here zero) genuinely irreducible-over-the-pool
quadratics survive, ≤ m̄ = 2 via E6's coprimality/degree count. Conversely
Irreducible-over-F would have wrongly excluded ψImage itself (z̄ ∈ F splits it —
hzbarRoot); the predicate correctly demands irreducibility over the POOL subfield,
where ψ's lift is irreducible by hψirr through E3's identification
(range of σ.K's coercion = pool, equal finite subfields). Divisibility/ord transport
across the coefficient embedding both ways ✓. E7 (membership + card ≤ m̄, rank <
m̄) and E8 (strict-total lex through the shared fieldEnum, equal initial-segment
counts ⟹ equal element) go through on this predicate. Matches the note's eligible set
"{ψ monic irreducible : deg ψ = g_r, ord_ψ R_anch = μ_r}" read on F-images.

## 5. PRESENT-EXIST + D4R4_all vs D4R.4's quantifier (charge item 5) — PASS (documented boundary)

The note: "N(P̂) is finite, and for EVERY N ≥ N(P̂): (D4R.4-SUM) … (D4R.4-EV)".
Blueprint: D10/D12/D13 are ∀-statements over (N)(hN : Nshape ≤ N)(S) — every
presentation at every sufficient level — with N-free constants C = Nat.card PrefIdx
and A′ (L9s); D4R4_all adds the ∃-witness at every level under the DECLARED
`hex = PRESENT-EXIST : ∀ N ≥ Nshape, Nonempty (Presented …)` — typed, single-row
ledger entry, owner HC-2, sole consumer D4R4_all ✓. Quantifier order faithful
(∀ N ≥ threshold, witness + SUM ∧ EV). Two boundary facts, both HONESTLY documented,
adjudicated acceptable: (i) the threshold is Nshape ≥ N(P̂) (band levels ≤ intercepts;
constrained levels ≤ heights), i.e. the Lean range is [Nshape, ∞) ⊆ [N(P̂), ∞) — the
note itself licenses this ("an a priori shape bound on N(P̂) is available but not
needed"), and no falsity can arise below Nshape since C(b)-at-a-jet needs only the
jet (MovesC round-4 finding 18: the ≥ N(H,Z) half is existence-side); (ii) jets'
existence IS the note's §C C.2 presentability, the corpus's HC-2 boundary — stated as
hex, never smuggled. Empty-Pref case at every N ≥ 1 carried by D14b with explicit
hN/hm, matching L12's "for EVERY N ≥ 1" ✓.

## 6. MovesC signature spot-checks (charge item 6) — PASS

Checked against Defs.lean: Node fields/types match every Matches tie (species, e h g μ
: ℕ, a gam : ℤ, s0 wSide Dwidth : ℕ, ustar : ℚ, zbar : Fˣ, ψ pat over ↥σ.K);
heights PAIRED (h + ustar retained, gam tied — the rev-9 pass-10 F1 point honored: A
consumes u* via lineS's intercept, W does not); hbezCanon makes (s,t) shape-derived so
Matches need not tie them; hspecRecCenter/hzbarRoot as consumed by §0.6; hRanch/
hpatTop/hpat0/hψmonic/hψdeg/hψirr/hOrd exactly power E4–E8; History.nonempty +
root_iff (snoc's non-root guard ✓); HistoryCoherent's window containment (s0'+w' ≤ μ)
powers W1; slope law matches lineS; hLineU matches lineS's intercept formula;
JetSetup.SHZ : Locus → Set (Fin m → ZMod p) matches Presented.fiber; totalPins
signature matches D9; inFreshBand's ROUND-6 fine-slot boundary (slotVal ∘ fineSlot) is
mirrored EXACTLY by bandS's third clause, floor stays coarse (staircase) — both
granularities correct; prevRim/kappaH/innerslotH/htH mirrored field-for-field by
prevRimS/kappaS/innerslotS/htS. TransitionAdmissible = (NA)+(HV)+(SAE) — the L3 rev-6
realizability binding ✓.

## 7. Fresh sweep of all 45 units (charge checklist 1–5 per unit)

D0a/D0b/D0c ✓ (⊤ laws; C(b) summands; positivity). E1 ✓ (pow_card). E2 ✓ (root count,
hp/hw guard the nonzero polynomial). E3 ✓ (card squeeze). E4 ✓ (hRanch+hpatTop). E5 ✓
(hOrd+hψdeg degrees, Ranch ≠ 0). E6 ✓ (coprime product; note's m̄ display). E7 ✓
(transported predicate — §4 above; rank < card ≤ m̄ needs ψImage-membership, present).
E8 ✓ (equal sets + strict total order). E9 ✓ (counted digits + scoped hmonic recover
the full tuple → RanchImage → E8 recovers ψImage → etaData equal → subtype ext; the
rev-4 comment right that the chain is granularity-independent). D2a ✓ (EtaData finite
Pi; CD_eq if_neg). F1 ✓ (choose_spec; PRESENT-NORM correctly cited as the dictionary
pin, not consumed by the Lean statements). W1 ✓ (InBox → ℓ₀ ≤ n; window chain + E5
descent — matches "deg R_anch,r ≤ n always"). W2 ✓ (m̄ ≤ ℓ ≤ n; endpoint of the
note's coarse chain). W3 ✓ (unconditional via case split — the Codex-5 repair; the
junk-shape pushback correct: the note's "always" ranges over degree-n classifier
shapes). D1c ✓ (Pi cards regroup to Mfac·p^W). D3a ✓ (E9+D1c, hypothesis-free — see
OBS-2 for the ∅ edge). D3b ✓ (division-free Corollary D4R.2 with Anet recorded).
D4a/D4b ✓ (chart bijection/counting, split units). D5a/D5b ✓, D6a–e ✓, D7a–c ✓, D8 ✓
(the shape-transport mirrors — formulas byte-match MovesC's, incl. the ROUND-6 fine
boundary). D9 ✓ (totalPins = A n N; numPinned ⊤ = 0). L9s ✓ (levels ≥ Nshape band-free
— ht ≥ level, line ≤ intercept; verified at the gate). D10 ✓ (SUM, index-set sum, NO
disjointness, hne, ∀ N ≥ Nshape, N-free constants — D4R.1-SUM ≡ D4R.4-SUM). D11a/b ✓
(double counting). D12 ✓ (union bound = EV). D13 ✓ (equality ⟺ mult ≡ 1 POINTWISE on
the event — the finite-level form carries no a.e. slack, matching the note's pointwise
upgrade). D4R4_all ✓ (§5). D14a ✓ (§3, C-6). D14b ✓ (L12 empty case, explicit hN/hm).
T1a ✓ (prefix-closure from the generation laws; root_iff makes every length-≥2 last
node non-root, so the snoc peel closes). D15 ✓ (bridges consume D4R_CYL as a named
deferred hypothesis; ClassFiberWelldef cited alongside — the Codex-9 scope repair).
VerdictModel ✓ (typed (c)/VP surface: halt dichotomy = L2's sentence both directions;
per-class cap law; rev-4 vdict_local + levelOf_lt; consumed by nothing in MovesD —
matches the kernel-(c) residual "alphabet V + halting rule τ + the uniform per-class
detection cap"). Non-vacuity: every theorem-bearing structure has an inhabitation
story (CanonPolicy constant-inhabited; degenerate TreeModel displayed non-consumable;
degenerate VerdictModel possible but it is OPEN typed data owned by MovesT, consumed
by nothing here). Checklist §7 items 1–7 all verified.

## 8. Findings

No critical. No blocking gap. Two NON-BLOCKING observations, recorded for the repairer:

**OBS-1 (PRESENT-NORM is prose-only).** Spec: "**PRESENT-NORM** (declared pin) [REV 4]
| every note-η has EXACTLY ONE root-normalized presentation class …" (§2 ledger). Its
sibling pins D4R_CYL and ClassFiberWelldef carry Lean-typed Prop forms; PRESENT-NORM
does not. Adjudication: it is consumed by NO Lean statement (only by the semantic
classes↔η dictionary, whose η-side is not a Lean object), and its exact parallel — the
junk-lift normalization — is likewise prose and passed two audits; so prose is an
honest register here. RECOMMENDED (not required): when the wave-4 tree corpus lands
the conjugation action, add the typable shadow (existence half: every IsCanon member
has a conjugate in the IsCanonPres PrefSet; uniqueness half: conjugate normalized
members have equal etaData).

**OBS-2 (D3a/W3 at the ∅ shape state a surplus truth, not the note's display).** Spec:
"`theorem D4R2' : Nat.card (PrefIdx n pol P) ≤ P.Mfac * p ^ P.W`" (no hne). At
P.reads = [] the LHS is 0 while the corpus C is CD = 1; both inequalities (0 ≤ 1 and
1 ≤ 1) are true, and rev 4's documented two-mechanism split assigns the ∅ display to
D14a only — so nothing is false or weakened on the C-carrying domain. Cosmetic option:
add `hne` (or a CD-form corollary) to make the LHS the corpus C on the whole domain,
matching the D10/D12/D13/D3b treatment.

## 9. Verdict

Counts: **0 critical / 0 gap** (2 non-blocking observations above).

**ACCEPT**

The rev-4 headline repairs are all verified against the note and the gate: the
canonRoot rebuild restores the note's η-granularity (independent recomputation:
C_P̂*(2) = 3, C_P̂*(3) = 48, mult ≡ 1, W = 7, M = 1, Nshape = 5, A = 11 — the last via
the blueprint's own bandS, coordinate lists matching the note's pin ledger); the
transported EligibleImage excludes the predecessor's counterexample in exactly the
right way; all four pushbacks are upheld on note evidence; PRESENT-EXIST/D4R4_all
thread D4R.4's quantifier honestly through the declared HC-2 boundary; MovesC
signatures check. Acceptance remains subject to the campaign's dual bar (the parallel
Codex verdict on the identical text).
