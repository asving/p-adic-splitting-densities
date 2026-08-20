# DEFECT record — NODE C.35, `blockFactor_spec` clause 3, and the blueprint's D13 disposition

**Unit:** chapter-C fleet, NODES C.35 + C.53 (2026-08-20).
**Node file:** `leanfinal/Uniformity/ChapC/C35.lean` (defs LANDED; the signed companion
`blockFactor_spec` BLOCKED — `C35_BLOCKED_2026-08-20.md`).
**Signed statement:** `leanspec/Leanspec/ChapC.lean` lines 1543–1572 — **byte-frozen,
untouched by this unit** (the three DEFS were diff-verified byte-identical before any proving).

This record exists because the MANDATORY A-C.7 vacuity audit, run before proof work as
charged, produced a finding that is NOT a vacuity instance but IS a real defect of the same
family (a signed clause that the signed BODY cannot supply). Per the charge it is recorded,
not repaired: **any re-sign is owner-gated and is not attempted here.**

## 1. The exact clause and the exact object at fault

Signed (leanspec `blockFactor_spec`, clause 3 of four):

```lean
    (blockFactor L f).natDegree = L.keyDeg₂ * mult₂ L f
```

with, from the same signed block,

```lean
noncomputable def blockFactor {F : KeyFrame O π} {H₀ hpin} (L : LevelDatum F H₀ hpin)
    (f : Polynomial O) : Polynomial O :=
  open Classical in
  if h : ∃ fS : Polynomial O, HasLabel L fS ∧ fS ∣ f ∧
      ∀ fS' : Polynomial O, HasLabel L fS' → fS' ∣ f → fS' ∣ fS
  then h.choose else 1

noncomputable def mult₂ … (f : Polynomial O) : ℕ := (blockFactor L f).natDegree / L.keyDeg₂
```

Since `mult₂` is `natDegree / L.keyDeg₂` by `ℕ`-division, clause 3 is **exactly the assertion
`L.keyDeg₂ ∣ (blockFactor L f).natDegree`** — i.e. `(F.e₁ * F.f₁) * L.ℓ * L.r.natDegree`
divides the block's degree.

**The object at fault is the BODY, not a hypothesis.** `blockFactor`'s body selects the
*maximal `HasLabel`-divisor of `f`*, an object defined purely by `HasLabel` + divisibility. The
audit asks what such an object determines, and the answer is: **not clause 3.**

## 2. The blueprint's D13 disposition is the specific claim that fails

`blueprint/CHAP-C_tower_grammar.md` NODE C.35 carries:

> (**A-C.1 note for D13:** `blockFactor_spec`'s `HasLabel` clause plus C.29's existential `m`
> and the exactness clause tie the two multiplicities the stub gate's D13 flagged: under
> `hctx`, `HasLabel`'s `m` and `mult₂` agree through C.26's degree law — the fleet proves the
> tie inside this spec, which is the D13 disposition.)

**That disposition is not available as written.** C.26's degree law
(`natDegree_dvResPoly`: the residual's degree is `dvSideDeg`) plus C.08's `dvSideLen_eq` plus
C.29's `IsDvPure` give precisely, and only, the **divided** identity — which this unit has
machine-checked and LANDED as `hasLabel_natDegree_div` (`C35.lean`, Lean-core):

```lean
theorem hasLabel_natDegree_div … (hg : HasLabel L g) :
    ∃ m : ℕ, 0 < m ∧ g.natDegree / (F.e₁ * F.f₁) = L.ℓ * (m * L.r.natDegree)
```

Note the `/ (F.e₁ * F.f₁)`. The undivided identity `g.natDegree = L.keyDeg₂ * m` follows from it
**if and only if** `(F.e₁ * F.f₁) ∣ g.natDegree`, and that divisibility is nowhere in
`HasLabel`. The reason is structural, and it is the sharp point of this record:

> `IsDvPure F g u ℓ` is `0 ∈ dvSideSet F g u ℓ ∧ g.natDegree / (F.e₁ * F.f₁) ∈ dvSideSet F g u ℓ`
> — the top abscissa is named by **`ℕ`-division (floor)**. So purity constrains
> `⌊deg g / D′⌋` and says nothing whatever about `deg g mod D′`.

## 3. Classification: NOT vacuous, and NOT over-strong. It is a BODY-CARRY defect

The charge asks specifically which of the two it is; it is neither, and blurring them would be
wrong in both directions:

* **NOT VACUOUS.** No hypothesis is unsatisfiable and nothing is vacuously true.
  `BlockContext L f` is a conjunction of POSITIVE requirements; its `∃ hne` binder is always
  inhabitable (C.34's landed `dvSideSet_nonempty` applies to any monic `f`), so the content
  sits in the two positive clauses `0 < dvSideDeg` and `L.r ∣ dvResPoly`, and C.34's landed
  `one_le_dvSideDeg_of_dvd_dvResPoly` shows the second independently forces the first. There
  is no C.113-shaped empty-domain escape and no C.118-shaped `≠ ⊤`-guarded implication.
* **NOT OVER-STRONG.** The signed statement is **expected TRUE**. Under C.34 the maximal
  labelled divisor IS the dissection block `f_S`, and the dissection's own degree law
  (`DvDissection.hdeg`: `deg (factor p) = D′ · (p.2 · dvSideDeg …)`) makes `D′ ∣ deg f_S`
  outright. Clause 3 is therefore the right statement about the right object; nothing needs
  weakening, and **the statement fence is not in question.**
* **WHAT IT IS: a BODY-CARRY defect** (proposed registry name `D-CARRY`). A signed conclusion
  clause is not determined by the signed total BODY; it can only be discharged by importing an
  upstream node's bookkeeping. Here: clause 3 is not a consequence of clauses 1+2, so C.35 is
  not a self-contained `[def]` node — it silently inherits C.34's degree law.

**Consequence, concretely.** Clause 3 cannot be discharged at C.35 in isolation, so the D13
disposition ("the fleet proves the tie inside this spec") mis-states where the work lives. The
divisibility must travel with the block's PROVENANCE. That is why this unit's landed frontier
carries it as an explicit rider:

```lean
def BlockFrontier … (f : Polynomial O) : Prop :=
  ∃ fS : Polynomial O, HasLabel L fS ∧ fS ∣ f ∧ (F.e₁ * F.f₁) ∣ fS.natDegree ∧
    ∀ fS' : Polynomial O, HasLabel L fS' → fS' ∣ f → fS' ∣ fS
```

and `blockFactor_spec_of_frontier` (LANDED, Lean-core) derives all four signed clauses from it.
Dropping the rider makes that packaging theorem UNPROVABLE — the rider is load-bearing, not
defensive.

## 4. The concrete instance, and exactly how far it is established

Take `D′ = F.e₁ * F.f₁ = 2`, `L.ℓ = 1`, `L.r.natDegree = 1`, hence `L.keyDeg₂ = 2·1·1 = 2`,
and a `g` with `g.natDegree = 3`:

| quantity | value | source |
|---|---|---|
| top `Φ′`-digit index | `3 / 2 = 1` | `ℕ`-division in `IsDvPure`'s second conjunct |
| `dvSideMin` | `0` | `IsDvPure`'s first conjunct (`dvSideMin_eq_zero_of_isDvPure`, landed) |
| `dvSideMax` | `1` | `dvSideMax_eq_of_isDvPure` (landed) |
| `dvSideDeg` | `(1 − 0)/1 = 1` | C.07 def, C.08 `dvSideLen_eq` |
| residual degree | `1 = m · d_r` ⟹ `m = 1` | C.26 `natDegree_dvResPoly` |
| `deg (dev F.key g 1)` | `1 < 2 = D′` | permitted: development digits have degree `< D′` |
| `mult₂` | `3 / 2 = 1` | C.35 def |
| **clause 3** | `L.keyDeg₂ * mult₂ = 2 ≠ 3 = g.natDegree` | **fails** |

**Honesty fence on this instance — read this before citing it.** What is *fully established*
(machine-checked, `C35.lean`) is the ENTAILMENT FAILURE: the landed `hasLabel_natDegree_div`
delivers only the divided identity, and the table shows the undivided one is inconsistent with
`deg g ≡ 1 (mod D′)`, so no derivation of clause 3 from clauses 1+2 can exist. What is **NOT**
established is a REALIZABLE witness: no concrete `(O, π, F, H₀, L, g)` with `HasLabel L g` and
`D′ ∤ g.natDegree` has been constructed here. So this is a refutation of the *derivation*, not
(yet) of any signed or intermediate mathematical claim.

**The machine-settleable question that closes the gap either way** — one fleet unit, decidable:

```lean
theorem hasLabel_natDegree_dvd … (hg : HasLabel L g) : (F.e₁ * F.f₁) ∣ g.natDegree
```

* **PROVED** ⟹ the D13 disposition is rescued, clause 3 becomes a genuine C.35-local discharge,
  and the rider drops out of `BlockFrontier` (which shortens the C.34 obligation).
* **REFUTED by a constructed frame** ⟹ the D13 disposition is dead as written, and the signed
  `blockFactor_spec` survives **only** through maximality: one must show such a `g` can never be
  the MAXIMAL labelled divisor of a `BlockContext` `f`. That is a within-slope refinement claim,
  i.e. C.34's frontier again — so the obligation would be confirmed as inseparable from C.34.

Either outcome is a genuine result; neither requires touching a signed statement.

## 5. Honest repair options, for the OWNER (recorded, not enacted)

1. **NO CHANGE (recommended default).** Keep the signed statement byte-frozen. Amend the
   blueprint's D13 *note* only — replacing "agree through C.26's degree law" with "agree through
   C.34's dissection degree law" — and let clause 3 be discharged as part of C.34's landing. This
   is a blueprint-prose correction, not a statement change, and it costs nothing.
2. **Settle it first.** Charge the one-unit `hasLabel_natDegree_dvd` question above before any
   amendment; the answer determines whether option 1's note should say "C.34" or can keep a
   C.35-local claim.
3. **Re-sign (owner gate, only if 2 refutes).** If a realizable counterexample appears AND
   maximality turns out not to exclude it, the honest re-sign is to add the provenance to
   `BlockContext`/`blockFactor` (e.g. define the block from the dissection rather than by
   maximality-choice) — a DEFINITION change, hence the strongest gate. **Not proposed here.**

## 6. Registry rider — this is a NEW pattern, not a fifth A-C.7 instance

The A-C.7 registry's four entries (C.111 `hnode` unpinned carrier · C.94 self-loop · C.113
unconditional `hne` · C.118's one-sided `Visible₂` guard, both clauses) are all **hypothesis**
degeneracies: a guard that fails to bind. This one is a **conclusion/body** mismatch: every
guard binds, and the defect is that the total body does not determine a signed conclusion
clause. Recommended standing check, to sit beside the A-C.7 one-liner:

> For every unlanded A-C.1 signature whose BODY is `Classical.choice` from a maximality or
> extremality property (`blockFactor` is the archetype), audit each conclusion clause against
> the question: *does the defining property alone determine this clause, or does the clause
> silently import an upstream node's bookkeeping?* Any clause of the second kind must be named
> in the node's frontier, not assumed discharged at the node.

Candidates to sweep under this check (choice-from-extremality bodies elsewhere in §5/§8):
C.36 (`complementConst`, a `toNat` of a support that C.36's own clause 3 must first prove
finite), C.38a/C.39 (`γg`/`pinHeight`), and C.40 (whose signed conclusion
`fS'.natDegree = L.keyDeg₂ * (mult₂ L f − 1)` re-uses exactly the arithmetic audited here and
therefore inherits the same rider).

---

## SETTLED 2026-08-20 — `hasLabel_natDegree_dvd` is **REFUTED**, so consequence 2 holds

The decidable question this record named in §4 has been answered, machine-checked, in
`C35b.lean` (`C35B_D13_REFUTED_2026-08-20.md`): **`hasLabel_natDegree_dvd` is FALSE.**

Frame (all at the corpus's own landed `s2Frame`, C.97, realized over ℤ_[2] — not a
degenerate artifact): `Φ′ = x² − 2`, `(e₁, f₁, h) = (2, 1, 1)`, `D′ = 2`, pin `H₀ = 1`;
`g₀ = x³ − 2x + 4 = x·Φ′ + 2²`, monic of degree **3**; `L₀` with `u = 3`, `ℓ = 1`, and
`r := ρ` the residual of `g₀` itself. `HasLabel L₀ g₀` holds with `m = 1`
(`dvResPoly = ρ = r¹` by `rfl`), while `e₁f₁ = 2 ∤ 3`.

Three theorems carry it: `hasLabel_g₀` (the label holds), `d13_refuted : ¬ D13Statement`
(the ∀-closure), and `hasLabel_natDegree_dvd_false` — the negation at the target's EXACT
printed binder shape, so the closure's faithfulness is machine-checked rather than judged.
Zero `sorry`, footprints Lean core.

**CONSEQUENCE — this record's option 2, as written: D13 IS DEAD AS WRITTEN.** Clause 3 of
`blockFactor_spec` is NOT a C.35-local discharge. It survives only through MAXIMALITY: one
must show a `g₀`-like polynomial can never be the maximal labelled divisor of a
`BlockContext` `f`. That is a within-slope refinement claim, i.e. C.34's frontier — so **the
obligation is confirmed INSEPARABLE FROM C.34**, and the `BlockFrontier` divisibility rider
**cannot** be dropped. C.40's `level2_peel` clause (iii) stays blocked for the same reason
(`deg g₀ = 3 ≠ 2m` for any `m`, while `hasLabel_natDegree_div`'s divided identity holds at
`m = 1`).

**Why the label cannot see it.** The purity is genuine, not an endpoint artifact — `g₀`'s
level polygon really is one-sided of slope −3. What `HasLabel` loses is PROVENANCE:
`g₀ = (valuation-1 linear)·(θ-like quadratic)` hides a mixed factor in the odd degree, and
the floor-divided top abscissa cannot see it. This makes C.29's FAITHFULNESS warning (the
root-side reading is not stated) **executable** rather than cautionary.

One addition to the orchestrator's sketched candidate, worth recording: `HasLabel` forces the
residual to be monic (`r^m` is monic), so the refutation also needed the top digit's ϖ-read
to be `1`. At `s2Frame`, `ϖ = x` and the top digit IS `x`, so the read is `res(θ/ϖ) = 1` on
the nose.
