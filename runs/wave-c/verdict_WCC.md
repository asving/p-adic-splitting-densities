# UNIT WCC verdict — the weighted convolution carrier LANDS at a general tower level (2026-08-30)

**Status: COMPLETE.**  `leanfinal/Uniformity/ChapI/I10WeightedCarrier.lean` (NEW, 756
lines, namespace `Uniformity.Density.Tower.I10wcc`) — 0 errors, 0 warnings, 0 `sorry`;
all **6** printed footprints exactly `[propext, Classical.choice, Quot.sound]` (per-file
`timeout 580 ~/.elan/bin/lake env lean Uniformity/ChapI/I10WeightedCarrier.lean` exit 0;
per-target `lake build Uniformity.ChapI.I10WeightedCarrier` — Build completed
successfully, 8846 jobs; aggregator `Uniformity/ChapI.lean` re-verified exit 0 after the
one standing import-line edit).  Cite ledger: **empty** — the general convolution law
and the keystone pin are Lean-core.

## STATUS FIRST

| charge | status | exact result |
|---|---|---|
| 1. dissect refutation vs `s2Mu4Coeff_mul` | **DONE — design finding §1 below (recorded before building)** | the weight is the absolute fixed-grade read's letter power `η^offset`; S2 hides it because `eval` at the letter `1` erases `1^offset`; the seam kill `eval 1 (X+1) = 0` is a ROOT relation, not a char-2 accident |
| 2. the weighted carrier at a GENERAL tower level | **GREEN — LANDED, Lean-core, uniform in `q` and the frame** | ★★ `wcoeff_mul` : on any `WeightedCarrier` (abstract support grading + absolute graded read, 9 laws) with any `CarrierKey` (monic key, pinned grade `s`, root relation `read s key = 0`, `+1` strictness `ℓ·s < u`, two D3AD-interface support laws), the next-level coefficient family `wcoeff` is multiplicative under pointwise LINE FLOORS alone — no exactness hypothesis, no `residueCard`, no `LevelDatum`, no keystone numeral |
| 2'. keystone coherence pin | **GREEN — the landed D3-10 statement RE-DERIVED through the abstract law** | `s2Mu4Coeff_mul_via_carrier` (conclusion byte-identical to `C136l2e4.s2Mu4Coeff_mul`; anti-drift `example` machine-checks interchangeability); `s2Carrier`/`s2Key` instantiate EVERY abstract field by a landed S2 lemma — machine evidence the abstraction is exactly the landed interface |
| 3. `LevelSiteBank` remainder | **STATED EXACTLY — §4 below** | the convolution is REMOVED from the per-level research list; the depth-adapter / key-lifting / B-1 legs are now precisely "supply a `WeightedCarrier` + `CarrierKey` per rung" — a field-by-field obligation map, several fields already landed at level 2 by the f14 series |

## 1. Charge 1 — THE DESIGN FINDING (recorded in the stub BEFORE building)

### 1.1 What the refutation exploits, exactly

`C136l2e4.fixedGrade_unweighted_add_forces_letter_one` is the terminal cancellation of
the following mechanism (verdict_L2E4 §1, re-verified against the source):

* The level engine has TWO reads of a dev-coefficient: the **own-height normalized**
  read (`dv2Res` genre) and the **absolute fixed-grade** read (`dv2FullRead` genre).
* The shift identity (`dv2FullReadPoly_eq_shift`, C136f14b) says a summand whose own
  residual window starts `δ` lattice steps above the common grade base reads absolutely
  as `η^δ · (own-height read)`, `η := AdjoinRoot.root L.r` the level letter.
* Fixed-grade additivity therefore produces the **weighted** diagonal `Σ η^{δ_p}·R_p`;
  L2E-09's `hconv` asserted the unweighted `Σ R_p`; at offsets `0,1` this cancels to
  `a + η·b = a + b`, forcing `η = 1`.  A general `LevelDatum` has no such hypothesis.

### 1.2 What the S2/μ₃-mirror structure provides that the bare carrier lacks

`s2Mu4Coeff_mul` reads through `eval (1 : fld 2) (s2Mu3GradedRes m ·)` — the GRADED
(absolute) residue evaluated at the letter.  Two S2 collapses hide the general shape:

1. **weights collapse**: `GradedRes m f = NormRes f · X^offset` at exact grade, and
   `eval 1` erases `1^offset` — exactly the symmetry the refutation forbids generally;
2. **the seam kill is a root relation**: reduction mod `g8` is invisible because
   `eval 1 (NormRes g8) = eval 1 (X+1) = 0` in char 2 — the point `1` is a ROOT of the
   key's residual polynomial; generically that is the DEFINITION of the next letter.

**Design constraint extracted**: read at a fixed absolute grade (weights inside the
read, never dropped) and record `read(key at its exact grade) = 0` as a FIELD.

### 1.3 Corpus state this unit built on (the charge's grep, completed)

The A24B → F14C → A24C → HCONV chain (2026-08-28/29) had already settled the weight
design AT THE GENERIC LEVEL-2 ENGINE: `C136f14f.dv2FullRead_dev_mul_conv_split` is the
weighted digit-split convolution, frame-generic Lean-core, firing the signed C.38/C.39.
What did NOT exist was the same law ABOVE level 2 — `s2Mu4Coeff_mul`'s level-3→4 shape
exists only at the S2 numerals `(21,2)`, key grade `42`, `(85,2)`, char-2 kill.  The
`LevelSiteBank` needs it at EVERY level, so the missing object was a **level-uniform
carrier**: the inner-engine laws as a structure + a one-step propagation theorem.
(The dv-grading is indeed the weight bookkeeping — charge 2's hint confirmed: `supp`
IS the dv-grading of the level below, and the weights ride inside the absolute read.)

## 2. What landed (namespace `Uniformity.Density.Tower.I10wcc`)

* **§1 `WeightedCarrier O K`** (NEW STATEMENT, review): `supp : Polynomial O → ℕ∞`,
  `read : ℕ → Polynomial O → K` with `supp_zero/supp_mul/min_supp_le_add` and
  `read_zero/read_add/read_above/read_mul` — the last is the cocycle-coherent carry
  law (absolute read multiplicative at exact grades).  **`CarrierKey C u ℓ`** (NEW):
  `key/kgrade/monic/deg_pos/supp_key/read_key/ell_pos/strict/supp_mod/supp_quot` —
  `read_key : read kgrade key = 0` is the root relation; `strict : ℓ·kgrade < u` is the
  corpus's `+1` mechanism (S2: `85 = 2·42+1`); `supp_mod/supp_quot` are the two
  D3AD-interface support laws on small-degree products.
* **`wcoeff C P β f J`** (NEW): the next-level coefficient family, ABSCISSA-indexed:
  `if u·J ≤ β ∧ ℓ ∣ β−u·J then read ((β−u·J)/ℓ) (dev key f J) else 0`.  `LineFloor`
  (NEW): the pointwise line floor `∀ j, β ≤ ℓ·supp(dev key f j) + u·j` in `ℕ∞`.
* **§3 derived laws** (all Lean-core, abstract): `le_supp_finsetSum`, `read_finsetSum`,
  `read_mul_of_le` (floors version of the carry law), ★ `read_key_mul` (the seam kill:
  every key multiple reads `0` at any cleared grade — derived from the root relation +
  `read_mul`, the generic content of `eval_one_mu3GradedRes_g8_mul`), ★
  `read_mul_modByKey` (reduction mod the key invisible to the read).
* **§4 ★★ `wcoeff_mul`** — the general weighted convolution law:
  `LineFloor β g → LineFloor β' z → wcoeff (β+β') (g·z) J = Σ_{j≤J} wcoeff β g j ·
  wcoeff β' z (J−j)`.  Proof: `dev_mul_conv_split_monic` + read additivity over the
  split; the whole carry diagonal killed by `carry_strict` (the `ℓ·s < u` pricing
  through `supp_quot` and `dev_key_mul_one`); off-lattice main terms killed by
  `offlattice_strict` (the mod-ℓ ceiling argument, variable modulus); on-lattice terms
  evaluated by `read_mul_modByKey` + `lattice_split` + `read_mul_of_le`.  **The
  abscissa-indexed form eliminates the S2 proof's parity filter + image reindex from
  the general law entirely** (termwise matching); the reindex reappears only at the pin
  where the numerals make it an `omega` exercise.  FLOORS ONLY: the landed S2 proof's
  exactness hypotheses were discovered to be consumed only through `le_of_eq` — the
  abstract law needs none.
* **§5 the keystone pin**: `s2Carrier` (`supp := dv2Supp … 21 2`, `read := eval 1 ∘
  s2Mu3GradedRes`) and `s2Key` (`g8`, `42`, slopes `(85,2)`) — every field a landed S2
  lemma (`dv2Supp_zero_eq_top`, `C132nv4.s2_dv2Supp_mul_at_21` (+nonemptiness),
  `min_dv2Supp_le_dv2Supp_add`, `C132rp3.s2Mu3GradedRes_add_of_le`,
  `s2Mu3GradedRes_zero_of_above`, `eval_one_mu3GradedRes_mul_of_exact`,
  `s2_dv2Supp_g8`, `eval_one_mu3GradedRes_g8_mul` at `Q = 1` (the root relation!),
  `C136d3ad.dv2Supp_mul_modByKey_eq`/`dv2Supp_add_le_key_quot_add` with
  `s2_isMu3Key_g8`).  `s2_lineFloor` converts `S2Mu4ExactGrade` through
  `C136d0.dv3Supp_le_term`; `s2Mu4Coeff_eq_wcoeff` is the dictionary through the two
  landed conversion lemmas (`eq_zero_of_grade_lt` / `eq_eval_of_le` — the
  `S2Mu4SlotOnGrade` gate and `s2Mu4Eps` never unfolded); ★
  `s2Mu4Coeff_mul_via_carrier` re-derives the landed D3-10 conclusion byte-identically,
  and the anti-drift `example` closes the same statement by the landed name.

## 3. Honesty

* **Uniform in `q` and the frame**: §§1–4 mention no `residueCard`, no numeral, no
  `LevelDatum`; `Nat.lt_or_ge`-style keystone facts appear only in §5.
* **Keystone content only as coherence pin**: the S2 material proves the INSTANCE, is
  consumed from landed lemmas only, and no landed file was edited.
* Nothing weakened: `s2Mu4Coeff_mul`'s statement is consumed verbatim (anti-drift
  example); the abstract law's hypotheses (line floors) are WEAKER than the landed
  lemma's (exact grades), i.e. the general theorem is stronger at the instance.
* The carrier packs are HYPOTHESIS PACKAGES: `wcoeff_mul` is unconditional given a
  carrier+key, and carriers/keys are constructed (not assumed) at the S2 pin.  No new
  Prop is asserted about bare towers.

## 4. Charge 3 — what remains of `LevelSiteBank`, exactly

`wcoeff_mul` removes "the weighted absolute-read convolution carrier" from SCS's bank
remainder as a PER-LEVEL research item: the convolution now exists once-and-for-all,
and the bank's calculus-supply legs become the INSTANTIATION obligations of the two
packs at each rung.  The map (SCS remainder leg → pack obligation):

| SCS leg | pack obligation | present supplier state |
|---|---|---|
| D3-03 depth adapter | a `WeightedCarrier` at rung `k` (the level-`k` support + absolute read with the 7 laws) | level 2 generic: read laws landed in f14b/c/f (`dv2FullRead_add_of_le` = `read_add`, `dv2FullRead_eq_zero_of_lt` = `read_above`, `dv2FullReadCarryLaw` ⊇ `read_mul`); the S2 level-3 instance is this unit's `s2Carrier`; level ≥ 3 generic = open (needs the generic level-3 read, the μ₃-mirror made frame-generic) |
| key lifting (`Rres_exists` genre) | a `CarrierKey` at rung `k`: the next key monic + `read_key = 0` — the root relation IS the key-lift content (the next letter is a root of the key's residual polynomial) | S2: `eval_one_mu3GradedRes_g8_mul`; generic: open (exactly the `Rres_exists` leg, now with a pinned Lean shape) |
| B-1 grades | the numeric fields: `supp_key` (the key's exact grade — the towerNorm computations), `strict` (`ℓ·kgrade < u` — the slope arithmetic), `supp_mod`/`supp_quot` (the D3AD interface at the rung) | S2: `s2_dv2Supp_g8`, `2·42 < 85`, D3AD's two lemmas (which are already generic GIVEN inner `supp_mul` + `IsMu3Key` — so this leg reduces to the μ-key property + the grade numeral per rung) |
| the convolution itself | — | **CLOSED (this unit)** |

**Do the downstream pieces consume the weighted carrier directly?**  Yes in shape: the
five S2 source laws that funnel through `s2Mu4Coeff_mul` (per SCS's provenance audit,
all via `C136d2`) consume exactly the statement re-derived here, so a general-rung
calculus supplier can consume `wcoeff_mul` + a rung instance in place of the S2 name.
Two derivable-next pieces were deliberately NOT built (scope): (a) `lineFloor_mul`
(new-level support super-multiplicativity — same pricing, ceiling arithmetic at
non-lattice abscissae); (b) the ITERATED carrier (the next-level `supp`/`read` packaged
back into a `WeightedCarrier`, needing the next residue ring/letter — blocked on the
key-lifting leg by content, not by form).

## 5. New statements flagged for the standing review

`WeightedCarrier`, `CarrierKey`, `wcoeff`, `LineFloor` (interface shapes below the
signed surface; no leanspec name touched; the landed `s2Mu4Coeff_mul` statement
consumed verbatim on the pin's both sides).

## 6. Verification, repair log, footprint

* Required command after every increment; final: exit 0, zero `sorry`, zero warnings.
  AxCheck 6/6 Lean-core (`wcoeff_mul`, `read_key_mul`, `read_mul_modByKey`,
  `s2Carrier`, `s2Key`, `s2Mu4Coeff_mul_via_carrier`).  `lake build
  Uniformity.ChapI.I10WeightedCarrier` — success (8846 jobs); `Uniformity/ChapI.lean`
  aggregator re-verified exit 0.
* Repair log (3 rounds, all mechanical): (1) two `Nat.dvd_add_iff_right` orientation
  swaps + the `w = 1` case needed `w = 0` substituted before `omega` (opaque `ℓ*w`
  atom); (2) `Polynomial.modByMonic_add_div` takes the divisor polynomial, not the
  monic proof, in this mathlib; (3) one trailing `rfl` for a structure-projection
  defeq after `rw`.  The star theorem §4, both §5 instances, and the final corollary
  compiled first-attempt.  Tactic note for the corpus: `omega` ATOMIZES variable
  products (`ℓ*m`, `u*j`) and closes linear cores over them — the whole S2-numeral
  arithmetic abstracted to variable slopes with only `Nat.le_of_mul_le_mul_left` /
  `Nat.eq_of_mul_eq_mul_left` cancellation bridges (scratch-verified before use).
* Footprint: `leanfinal/Uniformity/ChapI/I10WeightedCarrier.lean` CREATED;
  `leanfinal/Uniformity/ChapI.lean` one import line; this verdict.  No landed file
  edited, no git operation, IFCG23 untouched.
