# MovesX blueprint REV 4 — fresh-instance CONFIRMATION audit (Fable #2)

- **Date:** 2026-07-28
- **Auditor:** fresh Fable instance #2 (no prior MovesX context; charge = CAMPAIGN_AUDIT_CHARGE_2026-07-28.md, `<CORPUS>` = MovesX, `<NOTE>` = §X-EXHAUST; parallel to Codex's final confirmation on the identical rev-4 text)
- **Scope:** rev-4 confirmation of `lean/notes/MOVESX_LEAN_BLUEPRINT_2026-07-28.md` (635 lines, read in full) against ground truth `lean/notes/MOVES_2026-07-24.md` lines 10947–11556 (read in full). Charged specifically with: (1) the X2BridgeP witness feed, traced independently; (2) surgical-scope verification (only the four flagged objects changed); (3) pinned-mathlib grep of the two repaired names; (4) the Fin.cast/omega repair; then a fresh whole-blueprint sweep.

## 1. The four rev-4 repairs, each independently confirmed

**F1 (was CRITICAL) — X2BridgeP witness, REPAIR CONFIRMED and the feed CLOSES.**
Rev-4 spec (Defs §D), both clauses:
> `{ f | ∃ b : (X.ctx p).Branch f, IsLeafB b ∧ NsFreeB b ∧ N < (X.ctx p).threshold b + capHB b }` … clause 2: `frac { f | f ∈ Undec N ∧ ¬ ∃ b, IsLeafB b ∧ NsFreeB b ∧ N < threshold b + capHB b } = 0`

Note display (X2-BRIDGE): "Undec(N) ⊆ {disc f = 0} ∪ (𝒯^ns fibers) ∪ {…infinite branch} ∪ {f : ∃ (τ-ns)-FREE **finite branch** H, threshold(H) + cap(H) > N}" + the a.e. bridge statement — whose quantifier the same block pins to the finite-branch family ("every quantifier over 'finite branch H' in this bridge block ranges over (τ-ns)-FREE branches only"). `IsLeafB b ∧ NsFreeB b` is exactly the leaf-terminated reading already fixed at the rev-3 FourthPieceB repair (under the any-node reading FourthPieceB's second disjunct would be redundant) — faithful, in BOTH clauses.

Feed traced independently: witness b gives `IsLeafB b` ⟹ first disjunct of `FourthPieceB b := (IsLeafB b ∨ ∃ b', complete b' ∧ isPrefixB b b') ∧ NsFreeB b`, and `NsFreeB b` the second conjunct ⟹ `FourthPieceB b`. The third conjunct `N < threshold b + capHB b` is verbatim X2ProgressP's (and XD.4's) second hypothesis. So in XE.2, `PR` applies to the witness and yields `K.cd*N − K.cd' ≤ dTotal (hist b) ∨ K.ch*N − K.ch' ≤ maxH (hist b)`, i.e. membership in `DeepEvent ⌈d*⌉` / `TallEvent` at the note's thresholds; deep leg then closes via XG.1/XC.3 + `gmnLink` (vdisc ≥ 2(d*−log)/(2s+1) = the note's (d*−⌊log₂n⌋)/(s+1/2)) + `vdisc_le_tail` + XF.7, tall leg via TL — the note's two mass legs exactly. In XE.3 the identical feed discharges XD.4's `hb`/`hN`. The rev-3 hole (NsFreeB alone cannot supply FourthPieceB) is genuinely closed; XE.2's sketch now states this trace ("WITNESS FEED (rev 4, traced)") correctly.

**F2 (was CRITICAL) — vdisc signature, REPAIR CONFIRMED against the pinned mathlib.**
Rev-4 spec: `noncomputable def vdisc … : ℕ := (f.1.discr).valuation`.
Pinned mathlib grep (`lean/.lake/packages/mathlib/Mathlib/NumberTheory/Padics/PadicIntegers.lean`), exact line:
> `321:def valuation (x : ℤ_[p]) : ℕ := (x : ℚ_[p]).valuation.toNat`

ℕ-valued as the blueprint now pins (line number 321 exact); `.toNat` correctly dropped; `@[simp] lemma valuation_zero : valuation (0 : ℤ_[p]) = 0` exists in the same file, so the documented junk-0-on-discZero convention survives; every use remains guarded by `f ∉ discZero`. No `valuation.toNat` remains anywhere in the blueprint (grep clean).

**F3 (was GAP) — hom name, REPAIR CONFIRMED.**
Pinned mathlib, exact line:
> `130:def Coe.ringHom : ℤ_[p] →+* ℚ_[p] := (subring p).subtype`

Spelling `PadicInt.Coe.ringHom` (capital H) — the fully-qualified form appears verbatim inside mathlib's own `coe_sum` proof (`map_sum PadicInt.Coe.ringHom f s`), so namespace + spelling are exact. Blueprint occurrences: fTail's `.map PadicInt.Coe.ringHom` and XF.4's three uses — all renamed; grep for `PadicInt.coe` in rev 4 hits only the §6 repair-record row. It is a `RingHom`, which is what `Polynomial.map` requires — typing sound.

**F4 (was GAP) — fTail/Event Fin arity, REPAIR CONFIRMED.**
Rev-4 spec: `((Fin.cons 0 aTail) ∘ Fin.cast (by omega : n = n - 1 + 1))` (fTail; Event identical with `a0`), with new argument `hn : 1 ≤ n`.
Pinned toolchain (4.31.0, `Init/Data/Fin/Basic.lean:312`): `protected def cast (eq : n = m) (i : Fin n) : Fin m`. So `Fin.cast (h : n = n − 1 + 1) : Fin n → Fin (n − 1 + 1)` — correct direction; `Fin.cons (x : α 0) (p : ∀ i, α i.succ) : ∀ i, α i` (Tuple/Basic.lean:113) gives `Fin.cons 0 aTail : Fin (n − 1 + 1) → ℤ_[p]`; the composite is `Fin n → ℤ_[p]`, exactly `polyOfCoeffs`'s argument type. The omega identity `n = n − 1 + 1` holds in ℕ from `hn : 1 ≤ n` (truncated subtraction; omega reads hn from the local context inside the def). Semantics: slot 0 ↦ 0/a₀, slot j+1 ↦ aTail j — the a₀-free monic family, and the derivative in fTail kills the slot-0 choice as documented. Threading verified at both consumers: XF.6's statement passes `(by omega)` for fTail's and Event's `hn` with `h2 : 2 ≤ n` in scope; XF.7's sketch likewise. No consumer lacks the needed `1 ≤ n`; no `Fin (n−1+1)` restatement ripple exists (grep: the only Fin.cast occurrences are the two Defs + records).

## 2. Surgical-scope check (charge item 2): CONFIRMED mechanically

`git diff 24e02fc..83bdb0e` on the blueprint (rev 3 → rev 4, 49+/22−) touches EXACTLY: the header block; D5's prose + the `vdisc` def; the fTail/Event docstring + defs; X2BridgeP + its comment; XE.2's sketch (one inserted WITNESS FEED sentence, all else byte-identical); XF.4/XF.6/XF.7 (name rename + `(by omega)` threading only); two §4 audit-table rows (rev-4 annotations appended); the §6 rev-4 table. Byte-stable in content, verified against the predecessor's clean findings: all arithmetic units (XA.1–XA.9, XB.1–XB.4, XD.2/XD.3), FourthPieceB's two disjuncts (comment block untouched), König XG.2, the XG chain XG.1–XG.4, the seven other kernel Props, XConsts/D9, XCtx's fields, SeriesData/VPSoundP/CountableFiberAdditive. The "ONLY the four flagged objects changed" claim is true.

## 3. Fresh sweep (whole blueprint, checklist items 1–5)

- FAITHFULNESS spot-set re-derived independently this pass: rowOf/XA.1's five iffs against the T1–T5 table (T3's h=1 via hpos, T4's e=1 via epos); `p1Region`'s `≤` = the (P1) on-or-below pin, T1 witness (s+e, u+(ℓ−1)h) ON S with height (ℓ−1)h ≥ h ≥ 1; ind2's ℕ-subtraction guarded by XA.4's `e + h ≤ ehℓ + 1` (no truncation on T1); (3b) spot values recomputed — 4 and 1/4 at (2,2,0)/(2,2,4); 2/3, 2/9, 2/27 at (3,3,5/7/9) — and XF.7's cleared form `tailCount·p^tailExp ≤ (n−1)·p^{nD}` = (3b) exactly, trivial face at tailExp ≤ 0 checks (p^tailExp ≤ 1 ≤ n−1); the XD.4 chain (N < 1 + c₀Σh + c_cap(1+Σh), XD.2's (d_total+1)·max h with the +1 carrying the lone-terminal history, XD.3's ab ≤ max(a²,b²) dichotomy — closes including the c₀+c_cap = 0 corner); XG.1's both-route arithmetic (a1: 2(I+R₁) ≤ v, T₄ ≤ sv; a2: 2I ≤ v, R₁+T₄ ≤ sv; both ⟹ 2d_total ≤ (2s+1)v + 2⌊log₂n⌋); XB.4's 2^{#T3} ≤ Πe ≤ n; XF.5's max-element pigeonhole (sign-free, correctly flagged); XG.3's chain and its hyp line matching the CONDITIONALITY SUMMARY (VP-SOUND inherited by the SERIES identity XG.4 only — correct per note finding 13).
- NON-VACUITY: Ruling-1 architecture intact — every kernel a Prop over the shared `X : XFamily n`; single ledger-tracked inhabitation obligation; XF.3 constructs ValExt; no structure without an inhabitation story.
- HYPOTHESIS FIDELITY: XE.2/XE.3 carry the full tag sets (both mass legs; XE.3 = XE.2 minus PR plus XD.4, matching the rev-4 leg-tag line of the note); no kernel silently dropped/strengthened/axiomatized; no new axioms.
- DEFS SOUNDNESS: no def decides an open question (densityOf/TallEvent/DeepEvent/InfTree are honest set definitions; tailExp's ⌈·⌉ in ℚ before any ℕ-cast); mathlib names spot-set re-confirmed against the predecessor's §4 table.
- DECOMPOSITION: 48 units re-counted (10+4+4+4+10+9+7); EASY 19 / MEDIUM 17 / HARD 12 checks against the census including the band assignments.

## 4. Non-findings carried forward (repairer bookkeeping, no action required for acceptance)

- XE.2's dep list still omits XF.10 while naming it implicitly ("discZero via XF.7/vdisc_le_tail" — quantitatively self-sufficient since the tail set contains discZero); predecessor remark, unchanged, bookkeeping only.
- The ℚ-valued thresholds d*, h* vs X2TailsP's ℕ `hstar` need a floor/ceiling step inside XE.2/XE.3's proofs — inside the declared HARD assembly, not a statement defect.
- AF's mathematical redundancy in XE.2 given PR (note-internal tension, superset reading safe) — predecessor remark, stands.

## 5. Counts and verdict

CRITICAL: 0. GAP: 0.

All four rev-4 repairs are genuine and complete; the witness feed closes end-to-end (traced §1); the diff is surgical (verified mechanically §2); both repaired mathlib names exist at exactly the pinned lines and spellings; the Fin.cast repair typechecks conceptually with `hn` threaded at every consumer; the fresh sweep found no new defect. The blueprint is faithful to §X-EXHAUST rev 8.

**VERDICT: ACCEPT**
