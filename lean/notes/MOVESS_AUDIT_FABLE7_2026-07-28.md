# MovesS blueprint REV 9 — fresh-instance confirmation audit (Fable #7)

Date: 2026-07-28 · Auditor: fresh Fable instance #7 (workflow-spawned, no prior
MovesS context) · Scope: closing confirmation of REV 9 (the typing-rule rev) ·
Charge: `CAMPAIGN_AUDIT_CHARGE_2026-07-28.md` below the `---`, <CORPUS> = MovesS,
<NOTE> = §S-RESUM · Ground truth: `MOVES_2026-07-24.md` 11557–12577 read in full
(+ the S-RESUM rev-4/5/6 pass records 12578–12878 for the in-place final text; the
acceptance record at ~12854 cited per the header rule, never the stale in-body
STATUS trailer) · Blueprint: `MOVESS_LEAN_BLUEPRINT_2026-07-28.md`, all 1761 lines.

**VERDICT: REJECT (0 crit / 2 gap).** Every REV-9 repair verified genuine; every
settled item recomputed exact; the fresh sweep of all 82 units found no critical.
Two GAP-class residues below — both one-line-repairable, neither touches wave-2
soundness.

---

## 1. Charge item (1) — the typed packages and the W2/W3 shape: PASS

**XRBPackage vs the note's S.1 status line, field-by-field.** Note (S.1 STATUS,
11998–12003): "XHD (w/u/d/s — owner [2b]…) + (JC-INV) … + (SIB)/(JC-multi) (CL-10,
open) + TB-CAP/VP ([3t] §T.2…) + REL.2(a)/(b)/(d) (CL-8, open) + (ns-null)
(CLOSED)." Blueprint fields (965–972): xhd_w/xhd_u/xhd_d/xhd_s [4] · jc_inv [1] ·
sib, jc_multi [2] · tb_cap, vp [2] · rel2_a/b/d [3] · ns_null [1] = **13 fields,
13 note items, bijective, owner tags matching. None missing, none invented.**

**RS1GivenPackage vs the S.2 GIVEN list.** Note (12016–12019): "GIVEN the [3t]
package (TREE-EXP fin/ns + TREE-N + ONE-F; (SIB), CL-10; TB-CAP/VP), the S.0
nine-input ledger (CL-5), XRB (S.1, proved above), and [2r]'s REL.2 obligations…
(CL-8, open)". Blueprint (983–991): tree_exp_fin/ns, tree_n, one_f [4] · sib [1] ·
tb_cap, vp [2] · pci [1] · rel2_a…e [5]; the ledger enters as the REAL
`LedgerIV T M` argument L; the XRB leg as the premise `W2_xrb Π B₀`. The pci field
is display-supported beyond the headline GIVEN (RS.1-SH's display "with PCI
substituting β_{e_i,τ_i} for each subtree mass", 12040–41; S.0's b_e^split "CITES
the named interface PCI", 11718–19). rel2_c/e: the note's five (a)–(e) per S.6
("every β(q^δ) leg cites (e1)–(e5)", 12291). **Faithful.**

**W2_xrb/W3_recursion as implications FROM the packages.** W2 (974–980): all 13
Π-fields as premises → the pool-quantified h_ent-invariance of B₀.βmeas — exactly
XRB's display (11899–11902) in theorem-under-hypotheses shape, R40's pool
quantifier present. W3 (993–1006): all 13 Π′-fields + `W2_xrb Π B₀` ("XRB (S.1,
proved above)") → the activity-guarded fixpoint, quantifier-identical to
`recursion_meas` (R16(i) verified by comparison). Binder types check against
βmeas's signature. Grep for comment/quoted-register rationales: live-spec hits are
only the rule text itself, W2's "No premise in comments" claim, and historical
ruling tables — with the ONE exception recorded as GAP-1 below.

## 2. Charge item (2) — U-22b's derivation: statement DERIVES; sketch miscites

Walked in full. First conjunct: a pool prime p failing all-activity has, by
act_iff (677–678, an iff at q₀ ∈ M.Pools), some (e ∈ Icc 1 n, τ, o) with
(tgP e τ o).countS.eval p = 0; cellsize_nonzero (675) makes each countS a nonzero
polynomial (finitely many ℚ-roots); T.fin/finO + Icc 1 n make the (e,τ,o) index
finite; p ↦ (p:ℚ) injective. Finite. ✓ Second conjunct: Pools \ (finite root
union) ⊆ allActivePools by act_iff's ⟸ direction, and **M.pools_infinite** (481)
makes it infinite. ✓ The note's display (S.4(ii), 12198–12200) is exactly this
content — DERIVED, as R39 rules. But the unit's route line is wrong — GAP-2 below.

## 3. Charge item (3) — TreeIface/W7_cutWD/U-29d6: PASS

Order laws (919–924): refl/trans/antisymm + ancestor comparability = the partial
order CUT-1's "linearly ordered" presupposes; finN + path_total + path_antisymm
make the ∃!-least-first-entrance clause (1011–1013) well-posed — the note's "the
FIRST one (if any) is unique" (12070), strengthened per Codex#5-3 from mere
antisymmetry to the least-element form. ✓ Typed fence (1017): `isDeepSplit t ν →
¬ TI.isEntrance t ν` — a clause, not a comment (Fable#6-G3); with the induced
dichotomy this renders "Deep-recursion splits are never re-classified as shallow …
their children are convolution legs, not new entrances" (12087–90): a deep split
below a first entrance can never contribute a first entrance to CUT-3's enum, and
the site-level disjointness is the typed clause. ✓ σ₀ clause (1019–1022): shallow
filter = "no entrance node at-or-before ν" (onPath includes ν itself — matches
CUT-2's at-or-before, 12078) filterMapped through leafHalt = "its leaf feeds
σ₀(Ŝ)". ✓ (CUT-3) equivalence (1026–1032): `Fin Ŝ.k ≃ {first entrances}` with
blockOf = ⟨eOf i, τOf i⟩ and entδ = δOf i — "entrance and halt boundary data
retained" (12093), typed per Fable#6-G2; choice-freeness = shapeOf a function;
`shapeOf t ∈ F.Sh`. ✓ Non-vacuity: tree_ne/node_ne. ✓

**U-29d6 computes.** One tree per n = 2 shape (root + shallow leaves + ≤ 1
entrance node, δ ≡ 1, isDeepSplit ≡ False): clause (1) — the only entrance is its
own unique least entrance ancestor; clause (2) vacuous; clause (3) — the entrance
node has an entrance at-or-before itself, so it exits the shallow filter, and the
shallow leaves' Option-verdicts assemble σ₀ by construction; clause (4) — Fin 1 ≃
{ν₁} (k = 1 shape) or Fin 0 ≃ ∅ (all-halted shapes), blockOf ν₁ = ⟨2, τ★⟩, entδ =
1 = δOf; clause (5) by construction. Fintype/decide-scale. ✓

## 4. Charge item (4) — pool quantification: PASS (one WATCH)

Grep of every `∀ q₀` / `q₀ : ℚ` site: xrb (789), rexact (804), W2 (978), W3
(999), W10 (1041), β_bdd (779), all nine ledger mass claims, act_iff, ι_count,
wsh_*/shweight_card/wshval_card, W1m (955), W17ii (1058) — all `q₀ ∈ M.Pools`- or
locus-guarded (R40 uniform). Bare-ℚ sites are infrastructure (OKat/evalAt/
powSubst, PoolHyp's parameter with `pool_mem` inside) or carrier DATA types
(cellEvt/entEvtH/entInst/shEvtH/visH/shEvt/finB/boxpos/decA) — correct register.
WATCH (not counted, pre-REV-9, instantiable): `xhd_no_orphan` (537–538) and
`shevt_grouping` (850–851) quantify unguarded `∀ q₀` on carrier-controlled events
— off-pool the instantiator owns the events outright (∅ suffices; no other field
constrains them off-pool), so no demand beyond the note is created; d4r0's
unguarded form is self-justified in-text ("empty events are disjoint").

## 5. Charge items (5)–(7) — splits, settled items, census, sweep: PASS

**(5)** Nine U-29a units present and one-obligation-group each (n2_shape/
scs_data/boxes/pools/heights_ent/polygeom/interp/degpins_act/shapefam); the 2/3/2
splits: n2_kstep_one + n2_hmc · n2_init_agg + n2_init_count + n2_entcount ·
n2_xrb + n2_rexact — one field each. ✓

**(6)** Recomputed exactly (script, q₀ = 2,3,5,7,11): part1 q⁻³ + (1−q⁻¹) +
(q⁻¹−q⁻³) = 1; all rows > 0; det(1−K) = (q−1)(q²+q+1)/q³; β_{(1,2)} =
(q+1)/(q²+q+1), β_{(1,1)²} = q²/(q²+q+1), sum 1; kernel 1/8 and β = 3/7, 4/7 at
q₀ = 2 (the msW_eighth_le shadow). Window (R35): ℓ = g = μ = 1, W = 2, D = 1 —
window_comp 2 = 2·1+0, res_sum g·μ = 1 = ℓ, W′D′ = 1·(2·1·1) = 2 = WD = member
size — every SCSData law exact. PolyGeom.qpow: reduced denominators X³, X, X³, X³
all divide X^qpow·∏(1−X^a) with qpow = 3,1,3,3, geomDenoms ∅ — the corrected R30
law contains all four gate objects; the REV-3 no-qpow law would exclude all four.
✓ Convention-fix reading confirmed against S.3's q⁻¹-variable display.

**(7)** Spot-checks beyond the charge minimum (U-1 routing iff-triple vs the
(m,c) classification; U-2 ktri arithmetic; U-4's now-complete chain; U-8's
regroup vs (K-SUB)'s three summands with J per cell once; U-16a1's halted-member
indicator vs §T.4's factor-1 leaf convention; U-21b/c and U-23a–d matrix
analysis; U-27/U-28's RS.4 route vs S.5's three-step display incl. the full
inherited tag list; U-7a/b/c + W8 vs (BDY)'s edge/node shadow; W10's positive
series; ledger nine-vs-nine 1:1) — all faithful. Census re-counted: S0:9 S1:4
S2:16 S3:11 S4:6 S5:36 = 82; easy 18 + 25 = 43, medium 39, 0 hard — exact. §3b
DAG walked: acyclic; consumption discipline (nothing proves toward xrb; no PCI
site consumed by S.1-shaped content) matches the note's binding CONSUMPTION-DAG
order. No `True`/`∨ True` anywhere live.

---

## FINDINGS

**GAP-1 (rule uniformity; missing hypothesis-fields at the W1-family pins).**
Quote (§2.E, 944–951): `def W1_RS1SH (C : RS4Chain …) (hdet) : Prop := ∀ σ ∈
C.Sigmas, ∀ p ∈ C.PrimePools, ∃ hok…, (evalAt p ⟨Rsh …⟩ : ℝ) = C.Rval σ p` with
"`-- (Owners MovesT: TREE-EXP, (CUT-WD), (SIB)/CL-10, PCI/CL-8, XRB/CL-9,
CL-17(ii).)`". The note displays ONE GIVEN list premising ALL THREE RS.1 clauses
(S.2, 12016–19: "GIVEN the [3t] package …: (RS.1-DEEP)… (RS.1-SH)…
(RS.1-MARKED)…"); REV 9 typed that package at the DEEP pin only (W3 ←
RS1GivenPackage, Codex#5-2), while the SH pin (W1), the equating pin (W1e,
952–953), and the MARKED pin (W1m, 954–961, which types only the (ii-c) OKat
gate) remain premise-free with the hypothesis items in a Lean comment. Under R37
as written ("every note-displayed hypothesis package appears as TYPED FIELDS…
for a PIN … the obligation becomes an IMPLICATION from the package") and the
STATUS claim "THE TYPING RULE (R37) is now uniform", this is a residue of the
rev-8 disease one clause over: the pins are stronger than the note's conditional
display, and §5 lists W-1/W-1e/W-1m as wave-4 DISCHARGE duties — undischargeable
while (SIB)/CL-8/CL-17(ii) are open, with no premise slots to received them.
Why GAP, not CRIT: no wave-2 statement is wrong or vacuous (the contents enter
wave 2 only as RS4Chain hypothesis FIELDS — rsh_interp/rs1_equates — so U-28's
conditionality is preserved); the note does NOT list RS.1 among its DERIVED items
(S.6/STATUS), so a consumed-item reading (the W-4/X.3 precedent) is defensible —
but X.3's package is displayed in [5]'s note, whereas the S.2 GIVEN list is THIS
note's display, so the precedent does not cleanly cover W1/W1e/W1m. Repair:
premise the three pins on RS1GivenPackage (+ Wsh17Package at W1's CL-17(ii) leg)
per the R38 pattern, or record the consumed-vs-proved adjudication as a ruling.

**GAP-2 (U-22b's sketch cites out-of-scope hypotheses; correct route exists).**
Quote (U-22b, 1266–1270): "hyp: RB.cellsize_nonzero + RB.act_iff (+ prime_base ⊆
Pools via the chain's prime_sub) · sketch: … a prime outside the finite root
union is all-active by act_iff; infinitude from `Nat.exists_infinite_primes`."
The displayed statement binds only `(RB : RatBurdens T M)` — `prime_base`/
`prime_sub` live on RS4Chain, not in scope, and `Nat.exists_infinite_primes`
alone cannot place a single prime in M.Pools. The statement is nevertheless TRUE
and provable in scope: allActivePools ⊇ M.Pools \ (finite root union), and
**M.pools_infinite** (already a MeasuredSide field, 481) gives the infinitude —
no chain hypotheses needed. Classify GAP: statement faithful to the note's
display and derivable; the sketch/hyp lines would send the phase-E prover after
an unavailable hypothesis. Repair: rebase the route line on pools_infinite (one
line); optionally note the base-prime specialization as the chain-level corollary
consumers like U-24b's locus actually use.

---

## Counts and verdict

CRITICAL: 0. GAP: 2 (GAP-1 W1/W1e/W1m register; GAP-2 U-22b route line).

**REJECT (0 crit / 2 gap).** The REV-9 typing rule holds at W2/W3/W17ii and the
package contents are exact; the gate is jointly inhabitable with every number
recomputed; the sweep is otherwise clean. On the campaign convention (CLEAN = 0/0)
this is not an acceptance pass; both gaps are one-line-repairable and neither
invalidates any unit statement, so a REV 10 confined to the two repairs should be
confirm-ready.
