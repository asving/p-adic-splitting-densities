# MovesT round-6 Codex verdict (2026-07-29)

I’ll audit this as a statement-level adversarial pass, then independently recompute the finite counts and check the post-ratification seam names/types. I’ll treat any §7 “fixed” row whose repair does not actually enforce the quoted note clause as critical.

## Audit findings

### CRITICAL

1. **§7 row 1 — `root_total` does not restore per-track covering.**

   Blueprint:

   > “a repeated reduction factor OPENS the window”

   Actual field:

   ```lean
   (...) → ∃ ν, (Tat N' h).child none ν x
   ```

   The witness is not tied to the repeated factor `ψ` or to `trackOf ν = ψ`. One unrelated child can witness every repeated factor. The note says “one track per root cluster” and, for each `m_i ≥ 2`, that track opens its window. The claimed repair is therefore incomplete.

2. **§7 row 2 — the W4-1 BDY hold is invalid under the stated non-vacuity doctrine.**

   Blueprint concedes:

   > “the (b)-demand AT the W4-1 layer stays UNMET IN-CORPUS”

   The constant-false-child/unit-cell model still satisfies `eligibleT_iff_child`. Moving rejection to `KBTotTower` does not make the W4-1 interface itself false on the contract-rejected instance. The note also supplies a covering law, so this is not merely an unavoidable untyped boundary. The fourth-round hold fails.

3. **§7 row 4 — `OmSat` remains vacuous for lawful but unrelated `trackOf`.**

   The added monic/irreducible/divisibility fields kill `trackOf := 0`, but do not require `trackOf` to be the actual head-track factor. Choose a monic irreducible polynomial of degree greater than `n`; then its degree cannot divide the positive degree of a factor of a degree-`n` polynomial, so `ClusterFactorOf` has no witnesses and `OmSat` is again vacuous. `VPPinned` carries no `RedCellPartition` tie for its `trackOf`.

4. **§7 row 7 — `hScale`/`hRes` are still not genuinely displayed typed values.**

   Their bodies depend on new, undefined accessors:

   > “`windowBlockHts H` … E-phase binds the NAME only”

   > “`slot0Block H` … E-phase binds the NAME”

   These accessors determine the principal non-vacuity mechanism. Replacing one future placeholder with several future load-bearing accessors does not complete the claimed repair.

5. **§7 row 8 — `ns_bridge : Prop` is not a typed hypothesis package.**

   Blueprint:

   ```lean
   (ns_bridge : Prop)
   ...
   ns_null := NsAmendedPair pol ∧ ns_bridge
   ```

   A comment quoting the intended measure statement does not constrain the field. `ns_bridge := True` remains a valid instantiation, silently weakening the note’s conclusion

   > “μ((τ-ns) class │ Σ) = 0 by continuity from above.”

   This directly violates the charge’s typed-field requirement.

6. **§7 row 11 — the toy node tables remain non-closed.**

   The blueprint still says:

   > “remaining Node fields are E-phase-bound junk consistent with `HistLawful`”

   Those are data, not merely proof fields, and can affect `NodeExtends`, history construction, shapes, track identity and ledger obligations. Pinning `Dwidth` and carrier-B slopes does not verify the quoted finding in full. The claimed F* boundary misclassifies remaining load-bearing data as harmless proof plumbing.

7. **§7 row 12 — `shapeExp` remains an unresolved name-for-value.**

   ```lean
   def shapeExp ... := (bandFresh R n).card
   ```

   But `bandFresh` is itself only promised for E-phase binding. Consequently `hdict` still cannot be checked against a typed definition. The claimed display repair is not real.

8. **Seam content — old `Presented.event`/`mult` is now materially wrong at the empty shape.**

   REV-6 consumes and uses the old interface, notably:

   ```lean
   S.mult x
   ```

   in T-F4. The current MovesD corpus requires `Presented.eventO`/`multO`, with `reads = [] ↦ univ/1`. This changes statement content for the empty shape, not merely naming. Uniform dictionary/event consumers must be re-keyed.

### GAPS

1. **F1 joint satisfiability is only numerically demonstrated.**

   The cardinal equation is consistent, but no actual F1 `CellAssign`/ledger/scaffold witness is supplied. Thus the former contradiction is numerically removed, but “the joint row is SATISFIABLE” is stronger than what was established.

2. **W4-4 references are stale.**

   The blueprint still targets the old `D4R4all`/derived-NP-ID story. Current MovesD exposes `NPIDPin`, `NthrSup`, `noteNP`, and `D4R4_all_noteRange`. The “DISCHARGED” seam row and dependency roster must be checked against those real types.

3. **W4-5 is absent.**

   Current MovesD has `OffsetPPin` and `CD_canonical`. The claim

   > “MovesD blueprint §2.5 (4 entries)”

   and the 19-entry seam census are stale; there are now five MovesD seam entries.

4. **S-8/W17ii accounting is stale.**

   REV-6 describes an old `Wsh17Package`/pin arrangement. `RS4Chain.wsh17_pin` is now a definition equal to `W17ii`, not a supplied `Prop` field. Any relevant instance must prove or explicitly carry the actual `W17ii` type.

5. **S-10/RS4Chain accounting omits the new read-off field.**

   Current `RS4Chain` instances require `legs_read : LegAgree` for consumed non-all-active pools. The S-10 provenance row does not mention this requirement.

6. **The RS4 pool description is stale.**

   `deltaFactors` now includes only continuing split members. Any S-10/RS4 provenance statement inherited from the old all-split-member collection needs re-audit, even though no direct incorrect factor formula is displayed here.

## §7 disposition verification

| Row | Result |
|---|---|
| Codex-5 #1 `KBTotTower` | **Not fixed — CRITICAL** |
| Codex-5 #2 W4-1 | **Hold rejected — CRITICAL** |
| Codex-5 #3 finite subtrees | Fixed: `Tsub.Finite` is threaded through the kernel and named consumers |
| Codex-5 #4 `trackOf`/OM-SAT | **Not fixed — CRITICAL** |
| Codex-5 #5 `hdict` | Substantive hold is justified by note 7537–7540; implementation remains blocked by row-12’s unresolved `shapeExp` |
| Codex-5 #6 henflip | Fixed |
| Codex-5 #7 `hScale`/`hRes` | **Not fixed — CRITICAL** |
| Codex-5 #8 `ns_bridge` | **Hold rejected — CRITICAL** |
| Codex-5 #9 `belowEnt` | Fixed and correctly threaded through `trackOf` |
| Codex-5 #10 `ReprInj` | Fixed as a named typed premise |
| Codex-5 #11 toy tables | **Not fixed — CRITICAL** |
| Codex-5 #12 E10/`shapeExp` | **Not fixed — CRITICAL** |
| Fable-5 C-1 `child_cell@none` | Fixed at the stated toy/table level |
| Fable-5 G-1 slopes | Fixed: `1 < 2,3` and `2 < 3` are compatible with the stated ties |
| Fable-5 G-2 ShapeWF roster | Fixed: `root_box` is now explicitly the twelfth clause |

Thus only 8 of the 11 claimed `F` repairs are verified; both relevant `BDY` holds fail or remain untyped, while the `hdict` F* hold is textually sound.

## Recomputed checks

### Full \(2^9\) toy enumeration

The closed predicates reduce to simple nested cylinder counts:

- Carrier A old root-child event: `x₀=x₁=0`, size \(2^7=128\).
- Carrier A singleton-state event: `x₀…x₅=0`, size \(2^3=8\).
- Old violations: \(128-8=120\).
- New root-child event is exactly `x₀…x₅=0`: **0 violations**.

- Carrier B old root-child event: `x₀=x₁=0`, size \(128\).
- Carrier B singleton-state event: `x₀=x₁=x₂=0`, size \(2^6=64\).
- Old violations: \(128-64=64\).
- New root-child event is exactly `x₀=x₁=x₂=0`: **0 violations**.

For \(x^*=(0,0,1,0,\ldots,0)\):

- Carrier A: new child side false; singleton-state side false.
- Carrier B: new child side false; singleton-state side false.

So the post-fix enumeration claims are correct.

### Census integers

- \(8=2^{9-6}=2^3\): correct.
- `toyA = 2 + (4+0+0) = 6`: correct.
- Carrier-B JC-multi: \(2^4\cdot2^2=2^6=64\): correct.
- T-E5 toy identity: \(2^3(2^7)2^2=2^{12}=2^9 2^3\): correct.

### F1 ten-pin window

- Fourteen-pin state in the \(5^{22}\) box: \(5^{22-14}=5^8\).
- Ten-pin conditional charge: \(5^{10}\).
- Product: \(5^8\cdot5^{10}=5^{18}\), matching the four-pin reduction cell.
- Old clash: \(0<5^8<5^{18}\): correct.

This proves cardinal compatibility, not by itself existence of the complete joint interface witness.

## Held-item judgments

- **`hdict`: HELD on the note quote.** The note expressly asserts per-site shape determination and identifies its per-clause warrants. A pointwise owner field is legitimate; summed constancy is still derived. The unresolved `shapeExp` definition is a separate implementation failure.
- **W4-1 fourth-round BDY: NOT HELD.** The forbidden constant-childless instance still satisfies the actual W4-1 interface. Rejection in another package/layer does not establish W4-1 non-vacuity.
- **Henflip reversal:** correct. Since carrier A has `henV=∅`, replacing it by `{(1,1)}` is a real mutation; `fiberAt` clause (iii) then conflicts with the genuine empty `henPayload`, making the flipped tree unrealizable.

## Verdict

**REJECT — 8 critical / 6 gaps.**