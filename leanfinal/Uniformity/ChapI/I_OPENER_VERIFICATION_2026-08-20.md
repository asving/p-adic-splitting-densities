# CHAPTER-I OPENER — byte-freeze diff + green re-check + the PLACEHOLDER CENSUS

**Unit:** CHAPTER-I OPENER, 2026-08-20.  Nodes landed: I.01, I.02, I.03, I.05, I.06, I.07, I.21.
Note dispositions: `I04_I12_I19_I22_NOTES_2026-08-20.md`.  **I.10 / I.10a / I.10b UNTOUCHED**
(tower-instantiation freeze).  `Uniformity/ChapI.lean` NOT created (the owner serialises roll-ups).

---

## 1. DOES CHAPTER I HAVE A SIGNED LEANSPEC?  **YES.**

`leanspec/Leanspec/ChapI.lean` — **100 808 bytes, dated 2026-08-16**, wrapper
`namespace LeanspecI`, with a signature block for every one of the 25 blueprint nodes plus
A-I.1's two new sockets (I.10a/I.10b).  **Chapter I's statements are signed**, so every
statement below was transcribed BYTE-FROZEN rather than drafted.

## 2. THE BYTE-FREEZE DIFF — 8/8 statement blocks IDENTICAL

Extracted each `def` block (declaration line through the end of its indented body) from both
sides and compared byte-for-byte.  Result: **all eight identical, zero diff.**

| declaration | leanspec `ChapI.lean` | landed | identical |
|---|---|---|---|
| `NS7Termination` | L422–425 | `ChapI/I01.lean` L114–117 | ✅ |
| `DecidedSliceAt` | L438–445 | `ChapI/I02.lean` L98–105 | ✅ |
| `MenuLawAt` | L470–477 | `ChapI/I03.lean` L123–130 | ✅ |
| `MenuLawAtVoided` | L484–489 | `ChapI/I03.lean` L137–142 | ✅ |
| `WindowPinningAt` | L521–522 | `ChapI/I05.lean` L93–94 | ✅ |
| `GenhnHEAt` | L545–546 | `ChapI/I06.lean` L98–99 | ✅ |
| `GenhnTow1At` | L564–565 | `ChapI/I07.lean` L92–93 | ✅ |
| `TypeOfFaithful` | L1096–1097 | `ChapI/I21.lean` L109–110 | ✅ |

The **only** permitted change was the namespace: leanspec's flat `LeanspecI` wrapper →
`Uniformity.Density`, which is GC-6.2's landed-side assignment (chapter I gets no
sub-namespace).  Signatures, binder order, binder names and `Prop` kinds are unchanged.

## 3. GREEN RE-CHECK AND AXIOM FOOTPRINTS — all seven files, exit 0

`lake env lean Uniformity/ChapI/<f>.lean` for `f ∈ {I01, I02, I03, I05, I06, I07, I21}`:
**every one exit 0.**  `grep -rn "sorry\|^axiom \|native_decide" Uniformity/ChapI/` → **NONE**.

| declaration | `#print axioms` footprint |
|---|---|
| `NS7Termination` | `[propext, Classical.choice, Quot.sound]` |
| `DecidedSliceAt` | `[propext, Classical.choice, Quot.sound]` |
| `MenuLawAt` | `[propext, Classical.choice, Quot.sound]` |
| `MenuLawAtVoided` | `[propext, Classical.choice, Quot.sound]` |
| `WindowPinningAt` | **does not depend on any axioms** |
| `GenhnHEAt` | **does not depend on any axioms** |
| `GenhnTow1At` | **does not depend on any axioms** |
| `TypeOfFaithful` | **does not depend on any axioms** |
| `Tower.tower_first_live` (I.07's `#check`ed supplier) | `[propext, Classical.choice, Quot.sound]` |

**Lean core or cleaner throughout.  ZERO of the six signed cites is inherited** —
`exists_slope_factorization`, `fgmn_residual_mul`, `agnprw_termination`, `bBox1_cite`,
`exists_dvDissection`, `fgmn_dvDissection_factor_eq` appear in no footprint above.  The
allowlist stays at exactly six; this unit declared no axiom and imported no cite.

⚠ **Read the four "does not depend on any axioms" rows correctly.**  They are cleaner than the
Lean-core allowance for the worst possible reason: those bodies are `True`.  See §4.

---

## 4. THE PLACEHOLDER CENSUS — WHICH LANDED STATEMENTS ARE MATHEMATICALLY EMPTY

**This is the section that must not be skipped when reading chapter I's progress.**  A landed,
green, sorry-free, Lean-core `def … : Prop` proves **nothing mathematical** if its body is `True`.
Four of the seven nodes this unit landed are in exactly that state, **by signature** — it is the
blueprint's own recorded defect **I-D12** (*"six SIGNED bodies are the literal placeholder
`True`"*), not a shortcut taken here.

### 4a. REAL CONTENT — 3 declarations across 2 nodes

| node | declaration | what the body actually says | machine-witnessed non-vacuity |
|---|---|---|---|
| **I.02** | `DecidedSliceAt n` | the **literal** degree-`n` slice of the landed capstone target `UniformityStatementDecided` (`Density/Statement.lean:84`) — a real rational-function density law | **YES.** `DecidedSliceAt 2` PROVED outright (`I02.lean` gate 2) from landed `uniformityStatement_two` via `genuineDensity_eq_decidedDensity_two`.  Plus the `Iff.rfl` literal-slice pin. |
| **I.03** | `MenuLawAt n` | a `q`-independent `(A1)`-admissible family whose σ-labels **enumerate** a covering menu at degree `n` (A-I.1's re-signed 4-conjunct form) | **YES.** `MenuLawAt 2` PROVED (`I03.lean` gate 6) at a **real three-cell family** from landed `coveringMenu_two`. |
| **I.03** | `MenuLawAtVoided n` | the pre-A-I.1 one-directional form — **CITE-FORBIDDEN, exists to be refuted** | **REFUTED, deliberately**: gate 3 proves it EQUALS its bare menu clause, i.e. its `A1Family` existential carries nothing. |

### 4b. PLACEHOLDER `True` BODIES — 4 nodes, ZERO mathematical content

| node | declaration | signed body | provable by | what a hypothesis of it buys a consumer |
|---|---|---|---|---|
| **I.01** | `NS7Termination` | `∀ (O) [bundle], True` | `fun _ => trivial` | **NOTHING** |
| **I.05** | `WindowPinningAt n` | `True` | `trivial` | **NOTHING** |
| **I.06** | `GenhnHEAt n` | `True` | `trivial` | **NOTHING** |
| **I.07** | `GenhnTow1At n` | `True` | `trivial` | **NOTHING** |
| **I.21** | `TypeOfFaithful` | `True` | `trivial` | **NOTHING** |

(Five rows: I.01's bundle quantifier makes it structurally distinct from the other four — its
binders are real and inhabited at `ℤ_[p]` — but its **conclusion** is `True`, so it belongs here.)

**WHAT THESE FIVE ARE FOR, stated so no reader over-reads them.**  Each is a *label for a future
obligation*, reserved at frozen signature so that the capstone hypothesis structure's field list
is fixed before the bodies land.  What is genuinely frozen and therefore genuinely gained: **the
name, the index (where there is one), the `Prop` kind**, and — for I.21 — the docstring's locus
and both API names.  Nothing else.

**THIS IS THE OPPOSITE FAILURE MODE TO A-C.7 VACUITY, and both are dishonest if hidden.**
A-C.7 vacuity is a guard *no* instance satisfies (which makes a stated conditionality a fiction by
unsatisfiability).  These are clauses *every* instance satisfies.  A-C.7's registry checks cannot
catch them, which is why they are called out separately in every one of the five headers.

### 4c. THREE SPECIFIC DISCLOSURES, consolidated

1. **The triviality is DISCLOSED, not dressed up (I.05, I.06, I.07, I.21).**  I deliberately wrote
   **no** `example : <carrier> := trivial` in any of these files.  Such a gate would compile,
   would look like a certificate, and would certify only that `True` is true.  The triviality is
   stated in each header's audit instead.
2. **THE DEGREE RESTRICTIONS ARE NOT IN THE `Prop`s (I.06, I.07).**  Display A carries these
   conjuncts as *`if n ≥ 6`* and *`if n ≥ 8`*, but both signed `Prop`s are indexed by a bare
   `n : ℕ` with **no guard**.  The restriction lives at the use site (the structure field, the
   stage display), not the carrier.  So `GenhnHEAt 2` and `GenhnTow1At 2` are well-typed
   off-Display instances, and they are `True`.  **No consumer may read `∀ n, GenhnHEAt n` or
   `∀ n, GenhnTow1At n` as an assertion about low degrees.**  Same genre as defect I-D10;
   not repairable from these nodes (adding a guard is a Display-A field change, owner-gated
   under Part V gate (a)).
3. **C.93 clause (i) is SUPPLIER REACHABILITY ONLY (I.07).**  `I07.lean` `#check`s landed
   `Tower.tower_first_live` (`ChapC/C93.lean:49`) — a genuine, sharp theorem.  It **discharges no
   part of `GenhnTow1At`**, whose body is `True` and has no clause for the threshold to fill.
   Recorded because a landed-theorem `#check` sitting inside a carrier file could otherwise be
   mistaken for partial discharge.

### 4d. THE ONE-LINE HONEST HEADLINE FOR THIS UNIT

*Chapter I's frontier `[def]` nodes are landed at their signed statements, byte-frozen and
Lean-core.  Of the eight declarations, **three carry real mathematical content** (two of them
non-vacuity-witnessed at `n = 2`, one deliberately refuted), and **five are signed `True`
placeholders that assert nothing** (blueprint defect I-D12).  No mathematics was proved and no
open obligation was discharged by this unit.*

---

## 5. OWNER-GATED CONTENT — reached, recorded, NOT crossed

| node | why owner-gated | disposition |
|---|---|---|
| **I.01** | its discharge is chapter C's **gate-(b) literature cite C.94** ([AGNPRW] Thm 5.6), **NOT signed** | landed as a `Prop` CARRIER; header records it awaits the owner's gate-(b) signature, and that on signature it becomes cite-conditional and visible to `#print axioms` (gate I.25) |
| **I.06 / I.07** | the missing `n ≥ 6` / `n ≥ 8` guards are **Display-A field shape**, a Part V **gate-(a)** matter | asymmetry DISCLOSED in each header; no repair attempted |
| **I.02** | defect **I-D10** (the `n = 0` over-demand) is repairable only by a field change at I.10 | RECORDED in the header + made machine-visible by the `Iff.rfl` pin; NOT repaired |
| **I.10 / I.10a / I.10b** | the capstone hypothesis structure itself — **gate (a)** — and under the standing tower-instantiation freeze | **NOT TOUCHED.**  No field written, typed or `#check`ed.  I.04's clause about the `a2` field stops at this boundary. |

**Not owner-gated, and landed without a signature:** I.02, I.03, I.05, I.21 — their terminal fates
are discharge nodes (or, for I.21, a discharge node *or* a future cite), not existing cites.
