/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapB

/-!
# Uniformity.ChapB.B86 — the chapter-B census gate

**Chapter B, NODE B.86** [gate] (`blueprint/CHAP-B_leaf_layer.md` §10). **No public
declaration**: this is a census block, following chapter G's G.78 and chapter H's H.99.

It executes three things:

* **(i)** the `#print axioms` footprint of every capstone-facing chapter-B declaration and of
  all ten §10 gate theorems;
* **(ii)** the chapter's arithmetic audit at `q = 2` **and** `q = 3`, by `decide`/`#eval` — the
  gate values' degree conservation, D-3's bracket arithmetic, and the two residue cardinalities;
* **(iii)** non-vacuity, by `#check`ing the ten gate theorems at their stated types.

## ⚠ Part (i)'s expected values, honestly — the 2026-08-16 B.42 cite

The blueprint's §10 text was written before the B.42 literature cite was signed as an `axiom`,
and says every line "must print exactly `[propext, Classical.choice, Quot.sound]`". That is now
**superseded** by the chapter's own A-§9 record and by the amendment table's row

> "B.80–B.82, §10 gates B.83–B.86 … inherit the cite-conditionality; **visible mechanically** at
> B.86 part (i)'s `#print axioms` census — the cite axiom appears by name in every downstream
> footprint"

so the honest expected values, and the ones this file asserts in its comments, are:

| declarations | expected footprint |
|---|---|
| B.48, B.58, B.60, B.61, B.65, B.68 | `[propext, Classical.choice, Quot.sound]` |
| B.42 (the cite itself), B.63, B.71, B.79a, B.79b, B.80, B.81, B.82, and **all ten gates** | the same three **plus** `Uniformity.Density.Leaf.exists_slope_factorization`, and nothing else |

**Nothing else may appear.** In particular no `sorryAx` and no `Lean.ofReduceBool`: a
`native_decide` anywhere in chapter B is a stop-the-line event (H.99 precedent, repo policy), and
every `decide` below is the kernel one.

## ⚠ THE `#eval` COLUMN IS DELIBERATELY THIN, AND WHY THAT IS HONEST

Chapter H's H.99 executes count formulas because chapter H *has* computable count functions.
Chapter B's objects (`gaussVal`, `suppVal`, `order1Type`) are `noncomputable` (`ℕ∞`-infima,
`Classical` field instances), so the chapter's real numeric teeth are the **gate theorems
themselves** — B.83–B.85 prove `DecidedAt` at explicit values, which is strictly stronger than
evaluating a formula. The `decide` lines below are the residual *arithmetic* audit (multiset
degree bookkeeping, the gcd bracket, the residue cards) — the layer where a silent edit could
drift without breaking a proof. A future chapter-C count layer gets the H.99-style executable
column; nothing in this chapter states a count (B.82's FULL-GENERALITY note).

**DEPENDS.** every node named below (the census imports the chapter roll-up `Uniformity.ChapB`).

**PROOF.** none (a census block). **TEST:** the file compiles; every `#print axioms` line prints
its tabulated value; every `#eval` prints the commented expected value; both `example`s
elaborate.

**SOURCE.** repo policy (`CLAUDE.md`: "`lake env lean LeanUrat/AxChk_baseline.lean` prints every
capstone's `#print axioms` footprint … a footprint regression is a stop-the-line event"); chapter
G's G.78 and chapter H's H.99; GC-6.6's gate order.

**TEETH.** this gate IS the chapter's teeth roll-up; §13's disposition table is its index.
-/

set_option linter.style.longLine false

/-! ## (i) axiom footprints

Lines 1–6 of the first block must print exactly `[propext, Classical.choice, Quot.sound]`;
every other line must print those three **plus**
`Uniformity.Density.Leaf.exists_slope_factorization` (the 2026-08-16 owner-signed B.42
literature cite) and nothing else. -/

section AxiomCensus

-- ### core-only: the §7 dissection and the §8 leaf laws that do not route through B.42
#print axioms Uniformity.Density.Leaf.exists_residual_dissection      -- B.48   core only
#print axioms Uniformity.Density.Leaf.typeOf_leaf_resDeg_one          -- B.58   core only
#print axioms Uniformity.Density.Leaf.typeOf_leaf_integral_slope      -- B.60   core only
#print axioms Uniformity.Density.Leaf.typeOf_leaf_of_resDeg_lower_bound -- B.61 core only
#print axioms Uniformity.Density.Leaf.ns6_biconditional               -- B.65   core only
#print axioms Uniformity.Density.Leaf.typeOf_of_separable_reduction   -- B.68   core only

-- ### the cite itself
#print axioms Uniformity.Density.Leaf.exists_slope_factorization      -- B.42   core + itself

-- ### the cite-conditional upper layer
#print axioms Uniformity.Density.Leaf.typeOf_of_separable_residuals   -- B.63   core + cite
#print axioms Uniformity.Density.Leaf.typeOf_order1                   -- B.71   core + cite
#print axioms Uniformity.Density.Leaf.typeOf_eq_order1Type            -- B.79a  core + cite
#print axioms Uniformity.Density.Leaf.typeOf_congr_of_certificate     -- B.79b  core + cite
#print axioms Uniformity.Density.Leaf.decidedAt_of_order1_certificate -- B.80   core + cite
#print axioms Uniformity.Density.Leaf.exists_decidedAt_of_terminating -- B.81   core + cite
#print axioms Uniformity.Density.Leaf.decidedAt_of_leaf_certificate   -- B.82   core + cite

-- ### the ten §10 gates
#print axioms Uniformity.Density.Leaf.gate_inert_two                  -- B.83 (i)    core + cite
#print axioms Uniformity.Density.Leaf.gate_ram_two                    -- B.83 (ii)   core + cite
#print axioms Uniformity.Density.Leaf.gate_linram_two                 -- B.83 (iii)  core + cite
#print axioms Uniformity.Density.Leaf.gate_split_two                  -- B.83 (iv)   core + cite
#print axioms Uniformity.Density.Leaf.gate_inert_three                -- B.84 (i)    core + cite
#print axioms Uniformity.Density.Leaf.gate_ram_three                  -- B.84 (ii)   core + cite
#print axioms Uniformity.Density.Leaf.gate_linram_three               -- B.84 (iii)  core + cite
#print axioms Uniformity.Density.Leaf.gate_split_three                -- B.84 (iv)   core + cite
#print axioms Uniformity.Density.Leaf.gate_ef_two                     -- B.85 (i,ii) core + cite
#print axioms Uniformity.Density.Leaf.gate_ef_three                   -- B.85 (iii,iv) core + cite

end AxiomCensus

/-! ## (ii) the two-prime arithmetic audit, executed (all `decide`, no `native_decide`) -/

section GC11Arithmetic

-- degree conservation of every gate value (GC-4's mandatory invariant, B.72's law instantiated):
-- `Σ e·f` over the multiset = the instance's degree `n`.
-- [repaired: A-F.3/B-D14] `FactorizationType` is declared in `Uniformity` (`LocalData.lean:43`),
-- BEFORE `namespace Density` opens; the qualified name `Uniformity.Density.FactorizationType`
-- does not exist.
#eval decide ((⟨{(1,2)}⟩ : Uniformity.FactorizationType).degree = 2)       -- expect true
#eval decide ((⟨{(2,1)}⟩ : Uniformity.FactorizationType).degree = 2)       -- expect true
#eval decide ((⟨{(1,1),(2,1)}⟩ : Uniformity.FactorizationType).degree = 3) -- expect true
#eval decide ((⟨{(1,1),(1,2)}⟩ : Uniformity.FactorizationType).degree = 3) -- expect true
#eval decide ((⟨{(2,2)}⟩ : Uniformity.FactorizationType).degree = 4)       -- expect true
#eval decide ((⟨{(3,2)}⟩ : Uniformity.FactorizationType).degree = 6)       -- expect true

-- D-3's bracket arithmetic at the B.85 witnesses (the `m ∣ inertiaDeg ∣ m·d` collapse site):
#eval (Nat.gcd (2*1*1) (2*2*1), Nat.gcd (2*1*1) (3*2*1), Nat.gcd (1*1*1) (2*1*1))
                                                          -- expect (2, 2, 1) = (m·d, m·d, m·d)

-- the two residue cardinalities the gates rely on (via landed `residueCard_padicInt`):
example : Uniformity.Density.residueCard ℤ_[2] = 2 := Uniformity.Density.residueCard_padicInt 2
example : Uniformity.Density.residueCard ℤ_[3] = 3 := Uniformity.Density.residueCard_padicInt 3

-- the split-gate multiset sum (B.80's `Σ`-shape at instances B.83 (iv) / B.84 (iv)):
#eval decide (({(1,1)} + {(1,2)} : Multiset (ℕ × ℕ)) = {(1,1),(1,2)})      -- expect true

end GC11Arithmetic

/-! ## (iii) non-vacuity: the ten gate theorems elaborate at their stated types -/

section NonVacuity

#check @Uniformity.Density.Leaf.gate_inert_two
#check @Uniformity.Density.Leaf.gate_ram_two
#check @Uniformity.Density.Leaf.gate_linram_two
#check @Uniformity.Density.Leaf.gate_split_two
#check @Uniformity.Density.Leaf.gate_inert_three
#check @Uniformity.Density.Leaf.gate_ram_three
#check @Uniformity.Density.Leaf.gate_linram_three
#check @Uniformity.Density.Leaf.gate_split_three
#check @Uniformity.Density.Leaf.gate_ef_two
#check @Uniformity.Density.Leaf.gate_ef_three

end NonVacuity
