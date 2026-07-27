# MovesX blueprint REV 3 — fresh-instance semantic audit (Fable)

- **Date:** 2026-07-28
- **Auditor:** fresh Fable instance (no prior MovesX context; charge = CAMPAIGN_AUDIT_CHARGE_2026-07-28.md, `<CORPUS>` = MovesX, `<NOTE>` = §X-EXHAUST)
- **Scope:** rev-3 audit of `lean/notes/MOVESX_LEAN_BLUEPRINT_2026-07-28.md` (608 lines, read in full) against ground truth `lean/notes/MOVES_2026-07-24.md` lines 10947–11555 (read in full), INCLUDING the Mathlib name spot-check against the pinned mathlib under `lean/.lake/packages/mathlib`.
- **Addendum applied:** third revision; rev-2 repairs verified genuine (not paper); fresh sweep on the whole unit census; the five named pressure points each re-derived independently.

## 1. Rev-3 repairs: genuineness check (all 13)

| # | repair claimed | verdict |
|---|---|---|
| 1 | FourthPieceB 'finite branch' disjunct restored | GENUINE — `(IsLeafB b ∨ ∃ b', complete b' ∧ isPrefixB b b') ∧ NsFreeB b` matches "H is a finite branch or prefix of a complete τ-halted tree AND H is (τ-ns)-FREE" verbatim under the leaf-terminated reading the note's family forces (otherwise the second disjunct is redundant) |
| 2 | X2CapP inside ns-free family | GENUINE — `FourthPieceB b → capDetectable b → detCap b ≤ ccap·(1 + sumH)` = the note's "for every CAP-DETECTABLE branch H … (τ-ns) branches never enter it" |
| 3 | p-freeness by binder order (D9) | GENUINE — `XConsts n` bound before any `p`; kernels quantify `∀ p [Fact p.Prime]` inside |
| 4 | TallEvent a defined set | GENUINE — `{f | ∃ b, ∃ ν ∈ hist b, hstar ≤ ν.h}` = "some read of some branch has h_r ≥ h*"; `tallFrac` field gone |
| 5 | `frac_univ = 1` | GENUINE — field present |
| 6 | kernels as Props over the shared `XFamily n` | GENUINE — no kernel carries own F/branch/frac data; each is falsifiable for the real family (asserting a junk `ind ≡ 0` family with one certified node falsifies `X1aAlignP`, etc.); single ledger-tracked inhabitation |
| 7 | XE.2 ∃-envelope + XE.3 √N fallback | GENUINE in shape (∃ c3 c4 before ∀ p — n-only constants; both note displays covered) — but the assembly has the Finding-1 hole below |
| 8 | XF.9 deleted | GENUINE |
| 9 | ValExt riders removed | GENUINE — XF.7/XF.8/XF.10/XG.3 signatures carry no `ValExt`; V explicit only in the internals XF.4/XF.6 per Ruling 2; NO other unit acquired a rider (checked all 48) |
| 10 | König premise | GENUINE — `¬ ∃ g : ℕ → Branch f, g 0 = root ∧ ∀ k, parent (g (k+1)) = some (g k)` = the note's "every branch finite", no uniform depth bound; finite branching = `children : Finset` field |
| 11 | detectInter → XG.2b/2c/2d | GENUINE — chains close (§3 below) |
| 12 | hσ → densityOf + XG.4 | GENUINE — `densityOf := frac {f | splitType f = σ}`; identity derived, not a field |
| 13 | fTail/Event/CountableFiberAdditive specified | GENUINE in content — but the execution carries Findings 2–4 below (name/typing errors in exactly these Defs) |

## 2. Pressure points, re-derived independently

**(1) Arithmetic units — CONFIRMED.**
- (3b) spot values: (n,p,D) = (2,2,0): exponent ⌈(0 − 2·1)/1⌉ = −2, bound (n−1)·p² = **4** ✓; (2,2,4): ⌈(4−2)/1⌉ = 2, bound 2⁻² = **1/4** ✓; (3,3,5/7/9): 2·3^{−⌈(D−3)/2⌉} = **2/3, 2/9, 2/27** ✓ (= the note's X.5(ii) v₃ legs). `tailExp : ℤ` with the subtraction in ℤ/ℚ before ⌈·⌉ — no ℕ-truncation; XF.7's form `tailCount·p^{tailExp} ≤ (n−1)·p^{nD}` is exactly (3b) cleared of division; trivial face at tailExp ≤ 0 checks (tailCount ≤ p^{nD} ≤ (n−1)p^{nD−tailExp} for n ≥ 2). Ball-count bookkeeping in XF.6→XF.7 checks including the tailExp ≥ D corner (tailExp ≤ ⌈D/(n−1)⌉ ≤ D).
- Branch-length bound: fourPop dTotal = I + R₁ + T₃ + T₄; route (a2): 2I ≤ vdisc (XB.2 + X1aAlignP⟨true,false⟩ + p2), T₃ ≤ ⌊log₂n⌋ (XB.4 via degProd, 2^{#T3} ≤ Πe ≤ n), R₁+T₄ ≤ s·vdisc (WC-full) ⟹ **2·dTotal ≤ (2s+1)·vdisc + 2⌊log₂n⌋** ✓; route (a1): 2(I+R₁) ≤ vdisc, T₄ ≤ s·vdisc — same bound ✓. Matches the note's two-step reduction display cleared of the /（s+1/2) division.
- Lattice layer re-derived: XA.4's bracket ((e−1)(hℓ−1) ≥ 0 chain) ✓; XA.6 (coprime ℓ=1 triangle: interior (e−1)(h−1)/2, no on-segment points, endpoints excluded) ✓; XA.7a column-block decomposition (slice constraint reduces to hx″+ez ≤ eh exactly, rectangle e·(ℓ−1−k)h) ✓; XA.7b telescopes to ℓ(ehℓ+1−e−h) ✓; T2 witness (s+1,u+1): e+h ≤ eh, coprimality kills (2,2), parity of (e−1)(h−1) ✓; T3/T4 empty regions ✓; T1 witness ON S at height ≥ h ≥ 1 — the (P1) on-or-below pin carried by `p1Region`'s `≤` ✓.

**(2) XG.2b/2c/2d + XG.4 — chains CLOSE from stated inputs.**
- XG.2b: N := max over the finitely many leaf branches of (threshold + capHB) (exists by `Finite`; vacuous-leaf case any N); `detectBranch` (Thm 2.1 + TB-CAP per-clause caps, the ONE note-cited input) detects each ns-free leaf; `undec_spec` (X.0's Undec definition) closes `∃ N, f ∉ Undec N` ✓.
- XG.2c: f ∉ InfTree ⟹ Finite; all leaves ns-free ⟹ XG.2b contradicts f ∈ ⋂; so an ns leaf exists; `nsCover` ((NS-c) input) lands f in a fiber ✓.
- XG.2d: infinite path ⟹ hist(g k) has length k (parent_hist + hist_root induction), each in f's stratum (`gmnLink`) with HistWF (`wf`), dTotal ≥ k−1 (termLast) ⟹ contradicts XG.1's fixed bound ✓ (with XG.2's contrapositive supplying the path).
- XG.4: I := σ-typemult fibers, E := their union; VP-SOUND gives E ⊆ {splitType = σ}; `decided_covered` + XG.3's frac(⋂Undec) = 0 + XF.10 give the reverse inclusion mod null; ADD (Tonelli, an honestly OWED interface — countable additivity does NOT follow from the listed frac laws, correctly not smuggled) gives HasSum to frac E = densityOf ✓. VP-SOUND consumed exactly at the typemult identification (note finding 13) ✓.

**(3) FourthPieceB verbatim** ✓ (§1 row 1). **(4) König** ✓ (§1 row 10).

**(5) Kernel Props one-by-one:** X1aAlignP (= the assembled "ind(f) ≥ d_cert(H)" at discharge state st, exactly what every consumer cites; trivially true at ⟨false,false⟩ matching "at zero discharge (X.1a) is trivially true", honest unconditional instance XC.2) ✓ · WeightChargeT4P/FullP (T4-restricted vs FULL recentering burden = recT1 + t4, matching the rev-2-corrected burden statement) ✓ · X2AffP (sum over ALL reads via sumH; fourth-piece domain matches the X.2 block's quantifier) ✓ · X2CapP ✓ · X2ProgressP (level-relative hypothesis `N < threshold + capHB`, positive slopes in XConsts) ✓ · X2TailsP ✓ · NsNullP ✓ · X3aRouteP (⟨true,true⟩∧T4) ∨ (⟨true,false⟩∧full) = the note's corrected tag verbatim ✓ · **X2BridgeP ✗ — Finding 1.**

## 3. FINDINGS

**FINDING 1 — CRITICAL. `X2BridgeP` drops the note's "finite branch" qualifier; the witness it supplies cannot feed the envelope assembly.**
Offending spec (Defs §D):
> `{ f | ∃ b : (X.ctx p).Branch f, NsFreeB b ∧ N < (X.ctx p).threshold b + capHB b })` … and clause 2's `¬ ∃ b : (X.ctx p).Branch f, NsFreeB b ∧ …`

Note display (X2-BRIDGE), decomposition owed:
> "Undec(N) ⊆ {disc f = 0} ∪ (𝒯^ns fibers) ∪ {…infinite branch} ∪ {f : ∃ (τ-ns)-FREE **finite branch** H, threshold(H) + cap(H) > N}"

The blueprint itself fixes the reading "finite branch" = leaf-terminated (`IsLeafB` comment, rev-3 finding-1 repair; under the any-chain reading the family's second disjunct would be redundant). The Prop as written existentially quantifies over ALL branch nodes — a strictly larger fourth piece, i.e. a WEAKER kernel than the display. And the weakening is load-bearing: XE.2/XE.3's sketches apply `X2ProgressP` (and XD.4) "on the witness", but both require `FourthPieceB b`, which `NsFreeB b` alone does not supply — with the note's leaf-qualified witness it would (first disjunct). The note's own duty (i) ("level-N certification failure of a finite complete tree ⟹ some branch's threshold or its OWN cells' cap exceeds N") produces exactly a leaf witness — as does the blueprint's own XG.2b contrapositive. Repair direction (not prescribed): put `IsLeafB b ∧ NsFreeB b` (or `FourthPieceB b`) in both clauses' witness.

**FINDING 2 — CRITICAL (per the charge's wrong-signature rule). `vdisc` uses `PadicInt.valuation` at the wrong signature.**
Offending spec (Defs §B, D5):
> `noncomputable def vdisc … : ℕ := (f.1.discr).valuation.toNat        -- junk value 0 on discZero`

Pinned mathlib (`Mathlib/NumberTheory/Padics/PadicIntegers.lean:321`): `def valuation (x : ℤ_[p]) : ℕ := (x : ℚ_[p]).valuation.toNat` — **already ℕ-valued**; there is no `Nat.toNat`, so `.valuation.toNat` does not elaborate. The blueprint models the ℤ-valued `Padic.valuation` signature. Mitigation, for the repairer: this fails LOUDLY at compile, and dropping `.toNat` restores exactly the intended semantics — `valuation_zero : valuation 0 = 0` preserves the documented junk-0-on-discZero convention, and every use is guarded. No downstream statement's meaning shifts. Classified CRITICAL only because the charge pins wrong-signature uses as such.

**FINDING 3 — GAP. `PadicInt.coe` does not exist in the pinned mathlib.**
Offending spec (Defs §B `fTail`; XF.4's statement; XF.6's sketch):
> `((polyOfCoeffs ℤ_[p] n …).map PadicInt.coe).derivative` · `(f.map PadicInt.coe)` (×4 in XF.4)

Grep of the pinned mathlib finds no declaration `PadicInt.coe`; the ℤ_[p] → ℚ_[p] ring hom is `PadicInt.Coe.ringHom` (`PadicIntegers.lean:130`), which is also what `Polynomial.map` requires. Nonexistent name ⟹ GAP (trivial rename).

**FINDING 4 — GAP. `fTail`/`Event` arity: `Fin.cons` produces `Fin (m+1) → ℤ_[p]`, which does not unify with `Fin n → ℤ_[p]`.**
Offending spec (Defs §B):
> `polyOfCoeffs ℤ_[p] n (Fin.cons 0 (aTail ∘ Fin.cast (by omega)))` (in both `fTail` and `Event`)

For variable `n`, `n − 1 + 1` is not definitionally `n`, so the elaborator cannot unify `Fin (?m + 1)` with `Fin n`; an outer cast (or an `if i = 0` definition) is needed. Typing not plausible as written; compile-loud, standard repair. (Same finding-13-repair Defs block as Finding 3.)

## 4. Mathlib name spot-check (pinned mathlib under `lean/.lake/packages/mathlib`)

| cited name | status |
|---|---|
| `Polynomial.discr` | EXISTS (`RingTheory/Polynomial/Resultant/Basic.lean:930`; import path `Mathlib.RingTheory.Polynomial.Resultant.Basic` exists) |
| `Polynomial.resultant` | EXISTS (`…/Resultant/Basic.lean:134`, default degree args — `f.resultant f.derivative` well-typed) |
| `resultant_deriv` | EXISTS (`:973`, `Res(f,f') = ±lc·discr` given `0 < f.degree`) — supports XF.2's ‖·‖ equality for monic |
| `resultant_eq_prod_roots_sub`, `resultant_map_map` | EXIST (`:406`, `:140`) — XF.4's route |
| `PadicInt.toZModPow`, `PadicInt.ker_toZModPow` | EXIST (`RingHoms.lean:445/457`) |
| `spectralNorm` | EXISTS (`Analysis/Normed/Unbundled/SpectralNorm.lean:379`) — XF.3's route |
| `nonempty_sections_of_finite_inverse_system` | EXISTS (`CategoryTheory/CofilteredSystem.lean`) — XG.2's Mathlib route |
| `PadicInt.valuation` | EXISTS but **ℕ-valued** — Finding 2 |
| `PadicInt.coe` | **DOES NOT EXIST** — Finding 3 (`PadicInt.Coe.ringHom` is the ring hom) |
| `discr_map` (monic case) | correctly flagged by the blueprint itself as a Mathlib gap / in-corpus helper — not a finding |

## 5. Remarks (non-findings, recorded for the repairer)

- XE.2 carries `AF`/`CP` although PR makes them mathematically unnecessary; this follows the note's envelope paragraph ("Given (X2-BRIDGE) + (X2-CAP) + (X2-AFF)…") though the CONDITIONALITY SUMMARY's exponential tag set omits (X2-AFF) — a tension internal to the note; the blueprint's superset is not silent and is the safe reading. Likewise `R` is redundant given `AL ∧ WC` (route (a2)) but is needed by name for the null pieces via XG.2d — fine.
- Clause 1 of X2BridgeP uses `InfTree` (infinite node set) where the note says "has an infinite branch"; the two are provably equal in-corpus (König one way, the hist-length argument the other) — representation choice, acceptable.
- The frac laws do not include `frac ∅ = 0`; XG.3's ns-union step must case-split on empty `nsIdx` (provable without the law) — no repair required.
- XE.2's dep list omits XF.10 (its sketch says "discZero via XF.7/vdisc_le_tail"); bookkeeping only.
- Arithmetic re-confirmation: the two rev-2-audited inequalities (tail values; the (2s+1) reduction) are correct as claimed; the whole lattice layer (XA.4/6/7a/7b, T2 witness incl. the (2,2) coprimality exclusion and the parity of (e−1)(h−1)) re-derived clean.

## 6. Counts and verdict

CRITICAL: 2 (Finding 1 — X2BridgeP witness qualifier, breaks fidelity AND the XE.2/XE.3 assembly; Finding 2 — `PadicInt.valuation` wrong-signature use in `vdisc`, compile-loud, one-token repair).
GAP: 2 (Finding 3 — nonexistent `PadicInt.coe`; Finding 4 — `Fin.cons` arity in `fTail`/`Event`).

All 13 rev-3 repairs verified genuine; the four findings are fresh (Finding 1 in the rev-3 rebuilt bridge Prop; Findings 2–4 in the D5/finding-13 Defs execution). Everything else — the index-table layer, (CD)/populations/degree charge, the X.1a chain and both reduction routes, the (X2-HYP) derivation, the tail layer's unconditional public statements, the X.3 derivation chain XG.1–XG.4, the kernel Props other than the bridge, D9, the census (48 units, counts check) — is faithful to §X-EXHAUST rev 8.

**VERDICT: REJECT (2 crit / 2 gap)**
