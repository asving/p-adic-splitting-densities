# MovesT E-phase Lean blueprint — Codex semantic audit (rev 4, 2026-07-28)

CORPUS: `lean/LeanUrat/MovesT/` per `lean/notes/MOVEST_LEAN_BLUEPRINT_2026-07-28.md`
**REV 4** (full 3449-line blueprint). NOTE: `lean/notes/MOVES_2026-07-24.md`
§T-ASSEMBLY, rev 7, body lines 6970–7761 (dual-accepted 2026-07-27, unchanged
since rounds 1–3's audits). This is the FOURTH round on this blueprint. Round 1
found 35 crit / 10 gap (`MOVEST_AUDIT_CODEX_2026-07-28.md`) + Fable 5/8
(`MOVEST_AUDIT_FABLE_2026-07-28.md`) and DUAL-REJECTED. Round 2 found 21 crit /
4 gap (`MOVEST_AUDIT_CODEX2_2026-07-28.md`) + Fable 3/4
(`MOVEST_AUDIT_FABLE2_2026-07-28.md`) and DUAL-REJECTED AGAIN. Round 3 found 18
crit / 5 gap (`MOVEST_AUDIT_CODEX3_2026-07-28.md`) + Fable 2/4
(`MOVEST_AUDIT_FABLE3_2026-07-28.md`) and DUAL-REJECTED AGAIN — Fable-3 verified
the henV-flip dies on `hreal`, the seam map is contract-faithful, the S-3
reversal is sound and typed over the real imported `RS1Meas.βmeas`, and the F1
14-pin cell reaches the sealed integers exactly; its own two fresh criticals
were the `HistLawful`/`wchain` sourcing gap and the unbounded slot-0 ladder at a
fixed level. Rev 4, submitted this round, claims to repair the UNION of both
round-3 verdicts (Codex-3's 18/5 + Fable-3's 2/4) via a §7 "REV-4 DISPOSITION
TABLE" dispositioning all 29 union rows one by one (21 F / 5 F* / 2 PB / 1 BDY
claimed), plus a §5 SEAM ACCOUNTING whose 1 DISCHARGED / 4 REDUCED / 12
SUPPLIED-PARTIAL / 2 NOT-OURS tally over 19 seam entries is unchanged from rev 3
(re-certified, not re-argued).

SEAM CONTRACTS cross-checked against, pasted verbatim into the prompt (all three
line ranges verified unchanged since round 3's audit): MovesD blueprint §2.5
(the §W4-SYNC contract, `MOVESD_LEAN_BLUEPRINT_2026-07-28.md` lines 318–379),
MovesS blueprint's ratification addenda + §W4-SYNC seam contract (S-1..S-11 + 2
addenda, `MOVESS_LEAN_BLUEPRINT_2026-07-28.md` lines 1104–1349), HC-2's Wall
A/B/C architecture notes (`HC2_LEAN_BLUEPRINT_2026-07-28.md` lines 66–139).

Charge: `lean/notes/CAMPAIGN_AUDIT_CHARGE_2026-07-28.md`, instantiated for
CORPUS = MovesT / NOTE = §T-ASSEMBLY, with an APPENDING paragraph (this round's
addition) directing the auditor to: (a) verify each of Codex's own 18 round-3
criticals row-by-row against §7 (real Lean field / real quoted note-or-contract
sentence / real built signature, and not itself a fresh "name for a future
value"); (b) do the same for the 5 round-3 gap dispositions; (c) re-adjudicate
the two PB rows (#8 SideSplit partition, #13 ns-null finite-face) and the one
BDY row (#14 W4-1 layer) directly against the quoted text; (d) sweep the entire
rewrite fresh, with particular attention to the two brand-new rev-4 repair
mechanisms (`HistLawful`'s W-MULTIPLICATIVITY clause, the `Mlev`-capped slot-0
ladder) which have no round-3 antecedent; (e) recount §5's and §7's tallies from
their own rows. The charge also recorded that an independent auditor (Fable, a
fresh context on the same rev-4 text) reports the seam rows and the S-3
reversal SOUND with COMPUTED evidence (type-checks against the real imported
`MovesS.LedgerIV`/`RS1Meas.βmeas`, a field-by-field roster match, and the
build-artifact check), and instructed that where a finding would conflict with
an already-computed row the burden is a COUNTER-computation, not re-assertion.

Run: `codex exec --skip-git-repo-check --sandbox workspace-write -` (stdin; the
assembled prompt was 334,502 bytes, over the 128KB argv-safe threshold, so
stdin was mandatory). The entire corpus (charge + appending paragraph + the
frozen 6970–7761 note excerpt + all three seam-contract sources + the full
rev-4 blueprint) was pasted inline into the prompt, not read from the repo, per
the paste-context rule; the codex working directory (`/tmp/leanaudit_t4`) does
not contain the repo, so no shell-based cross-check of the actual `.lean`/
`.olean` tree was possible or attempted this round (consistent with the charge
telling the auditor to trust the build-check record rather than re-verify it).
First attempt succeeded, no retry needed. Model `gpt-5.6-sol`, session
`019faaa9-97fa-7731-90bb-3eebea81b53f`, 121,927 tokens, wall time ≈3.5 minutes.
Full transcript: `/tmp/leanaudit_t4/codex.log`; prompt assembly:
`/tmp/leanaudit_t4/prompt.txt` (four parts — the instantiated charge + appending
paragraph, the frozen 6970–7761 note excerpt, the three seam-contract sources,
the full rev-4 blueprint).

## Verdict

**REJECT (9 crit / 4 gap)**. A substantial numeric improvement over round 3's
18 crit / 5 gap, and Codex explicitly certifies both tallies as arithmetically
row-faithful (§5: 1+4+12+2 = 19 ✓; §7: 21+5+2+1 = 29 ✓). But nine of the
disposition rows fail on direct inspection of the pasted rev-4 text: two are
the brand-new rev-4 repair mechanisms themselves (`KBTot`'s fixed-level
degenerate inhabitation, `T-C7`'s `ns_null`/`hMgrow` non-implication — findings
1–2), and seven are re-adjudications of round-3-flagged rows that Codex found
still defective under the new text, each with an explicit counter-model or a
quoted textual mismatch (findings 3–9). Four gap findings round out the pass
(10–13), concerning `RedCellPartition`, the SideSplit PB, non-Lean prose
placeholders inside `hjcm` hypotheses, and `T-G1`'s gate specification.

## CRITICAL findings (9)

1. **`KBTot` remains degenerately inhabitable at a fixed level.** Against
   `ns_lumps : … ∃ J : JetSetup H n N m, M₀ J ≤ Mlev J N ∧ Nonempty (NsLumpFamily T J)`
   together with `slot0 : ∀ M, M₀ J ≤ M → M ≤ Mlev J N → …`: take `T.mem`
   everywhere, `T.child` nowhere, `Mlev J N = M₀ J`, `interiorFreshIdx = ∅`, and
   `Lf.L M = Set.univ`. `BranchDichotomy` is vacuous, `tie` holds, and the
   capped `slot0` inequality is vacuous (empty range). The exact
   childless/constant model the non-vacuity requirement targets still inhabits
   `KBTot`, hence can inhabit `VPPinned.covering`. The claimed tower-scoped
   rejection is external to `KBTot` itself and does not repair its fixed-level
   satisfiability — i.e. the `Mlev` cap (rev 4's central repair mechanism, =
   Codex-3 #3 / Fable-3 CRIT-2's claimed fix) does not actually close the
   degeneracy at a single level.
2. **T-C7's `ns_null` is false under its own displayed hypotheses.** Against
   `(hMgrow : Tendsto (fun N' => Mlev (Jat N'.1 N'.2) N'.1) atTop atTop)` and
   the sketch's assertion "lower := `Mlev − M₀` diverging by `hMgrow`": growth
   of `Mlev` does not imply growth of `Mlev − M₀`. Counter-assignment:
   `M₀ (Jat N) = Mlev (Jat N) = N`; then `hMgrow` holds while the lower bound is
   constantly zero, so the capped ladder supplies no growing fresh equations
   and the asserted limit-zero conclusion is contradicted. Propagates to
   `TreeExpNs`, `NsAmendedPair`, and T-E12 — i.e. rev 4's tower-form restatement
   of the falsifier (the other half of the same repair mechanism as finding 1)
   is itself unsound as typed.
3. **The retained `hdecomp` is not the note's recursive subtree decomposition.**
   Against `hdecomp : {x | Tr.fiberAt T χ x} ∩ entEvent T χ es = cellEventE T CA χ es c ∩ ⋂ ν ∈ CA.branchSetOf c, S ν`:
   at a split nested inside one root branch, the LHS is the fiber of the
   *entire* tree (including conditions on the other root siblings), while the
   RHS contains only the nested site's child events — those outside-sibling
   conditions live in neither `entEvent` nor any permitted `ContFiber` child
   event. A canonical nested tree generally cannot supply this field, making
   `TreeScaffold` vacuous on genuinely nested sibling trees. Disposition #11's
   F* "ownership" framing does not cure the wrong equation.
4. **T-E10 weakens the per-shape corollary by assuming its conclusion-side
   content.** Against `(hfin : (shapeClass Tr₀ T χ).Finite)` and
   `(hA : ∀ Tr h, AofTr Tr (Lat Tr h) = AofTr Tr₀ L₀)`: the note's
   "(JC-multi): shape-determined GIVEN its side-product form" licenses
   dependence on the already-present `hjcm`, not an arbitrary new `hA`
   hypothesis, and the displayed finite value-tree count is not conditional on
   a separately assumed `hfin`. Also: T-E10's proof claims to apply T-E8, but
   T-E8 now requires `RedCellPartition` and T-E10 supplies no `hred`.
   Disposition #12 is therefore still incomplete.
5. **The W4-1 BDY disposition contradicts the contract's explicit non-vacuity
   requirement.** Against `theorem eligibleT_iff_child … : T.child o ν x ↔ eligibleT T CA o ν x`
   with `eligibleT … := ν ∈ CA.branchSetOf (CA.cellOf … x)`: a model with no
   children and a constant empty branch set satisfies this theorem identically.
   The contract's own text ("NO `eligible := child` vacuity … the root-only
   childless tree must not satisfy the law for realizable inputs") is not
   satisfied by moving the actual falsification to the unconsumed, fenced
   `WallAReconciled` Prop — tree-level `fiberAt` rejection and tower-level
   ledger rejection are different layers from the W4-1 layer itself.
   Disposition #14's boundary citation does not license the boundary.
6. **The S-2/S-9 `(ns-null)` PB substitutes a strictly weaker statement.**
   Against `ns_null := NsAmendedPair pol`, whose second leg concludes only
   `Tendsto (Nat.card nsTrunc / Nat.card stateTrunc) … 0`: the note's
   `(ns-null)` display concludes the conditional measure identity
   `μ((τ-ns) class │ Σ) = 0` via the intersection identity and continuity from
   above — the finite-level limit is an ingredient, not the displayed
   conclusion. A self-imposed "measure-free corpus" doctrine cannot alter what
   the frozen note or the contract field means; the missing bridge should
   remain an explicit hypothesis or gap. Disposition #13's PB is unlicensed,
   and (per finding 2) T-C7 does not even establish the finite precursor as
   stated.
7. **`OmSat` is vacuously satisfiable through the undisplayed factor relation.**
   Against `ClusterFactorOf H fη → IrrHalts H → Irreducible fη ∧ ramIdx fη = accE H ∧ resDeg fη = accF H`:
   the blueprint leaves `ClusterFactorOf` an undefined/unconstrained pointer;
   reading it as `False` makes `OmSat` automatic, so `VPPinned.om_sat` no
   longer pins the declared OM-SAT citation. Disposition #22's "consumed by
   nothing" claim is also inaccurate — `VPPinned` and the re-keyed `vp` package
   consume the Prop — so the residual is a critical vacuity, not an acceptable
   F*.
8. **T-D11's `fibOf_fiber_disjoint` is refutable by association-list
   permutation.** Against `(ct ct' : ClassTree n pol) (h : ct ≠ ct') : ¬ VTree.ext (fibOf hrep ct) (fibOf hrep ct') ∧ …`:
   `ClassTree.leafV` is a `List`; two association lists differing only by
   permuting two distinct key/value entries both satisfy `Nodup` and yield
   identical lookup function, address set, root payload, and ns marks, hence
   extensionally equal `fibOf` trees despite being unequal `ClassTree`
   structures. Key uniqueness does not make list order canonical, so the first
   conjunct is false as stated.
9. **T-D11's `fibOf_partition` lacks the hypotheses needed to encode an
   arbitrary decided tree by `PrefIdx` addresses.** Against
   `theorem fibOf_partition … (hx : Decided T χ x) : ∃ ct : ClassTree n pol, (fibOf hrep ct).fiberAt T χ x`:
   `Decided` supplies only an arbitrary `VTree` fiber, not membership in some
   `PrefSet`, a `Shape` match, a `PrefIdx` class, or `reprOf`-compatibility
   (precisely the `HistLawful`/InBox/class-locality bridges used elsewhere).
   `PrefixCoherentRepr` only preserves prefixes of already-existing class
   addresses; it cannot manufacture addresses for arbitrary chains, so the
   claimed ONE-F keying does not follow.

## GAP findings (4)

10. `RedCellPartition` partitions children by arbitrary factors, not by their
    actual root tracks: `∃! ψ, ψ ∈ normalizedFactors (redPoly χ x).toFinset ∧ ν ∈ branchSetOf (cellOf (.red g ψ) x)`
    has nothing relating `ψ` to the reduction factor encoded by `ν`, so a child
    can be assigned uniquely to the wrong factor and satisfy the definition — a
    Wall-A/root-node factor-identification field is missing.
11. The SideSplit PB (disposition #8) still does not identify the partitions
    with the polygon's actual sides: `sideOf`/`clausesOf`/`sideSpan` plus
    `hpartition`/`hspan_disj`/`hsupport` permit arbitrary regrouping of clauses
    and coordinates; no field connects them to a hull-side datum, and
    `splitAt` does not require `ss.k = L.sides H`. The note's phrase "the k
    per-side systems" presupposes those are the actual polygon-side systems,
    which the added disjoint supports do not supply.
12. Several unit statements still contain non-Lean prose placeholders, e.g.
    `(hjcm : ∀ Tr h, (T-E8's per-site hjcm row at (Tr, Lat Tr h)))` and
    `(hjcm : (T-E8's per-site hjcm row))` in T-E10/T-E11 — not terms Lean can
    elaborate, and it is unclear whether the exact multi-site domain, split
    proof, and exponent tie are preserved.
13. T-G1 is still not a complete gate specification: `toyModel`/`toyCA`/
    `toy_e5_instance` remain ellipses. A prose promise that ellipses become a
    build failure later does not supply the current unit statement or the
    enumerated tables needed to audit it — disposition #23 remains an
    underspecified future implementation, not F* closure.

## Recounts (Codex's own, matching the blueprint's claimed tallies)

* §5 seam rows: 1 DISCHARGED / 4 REDUCED / 12 SUPPLIED-PARTIAL / 2 NOT-OURS = 19
  — arithmetic matches the rows.
* §7 disposition rows: 21 F / 5 F* / 2 PB / 1 BDY = 29 — arithmetic matches the
  listed rows, though (per findings above) the PB/BDY rows and several F*
  adjudications fail semantically.

## Disposition

Rev 4 is a genuine numeric improvement over round 3 (9+4 vs. Codex-3's 18+5),
and this round's charge's "counter-computation, not re-assertion" standard was
largely met: seven of the nine criticals (1–9 above) carry an explicit
counter-model, a concrete numeric counter-assignment, or a specific structural
mismatch quoted against the pasted rev-4 text, rather than a repeat of prior
prose. Two findings (1, 2) land squarely on the two brand-new rev-4 repair
mechanisms the charge specifically flagged as unprecedented (`KBTot`'s `Mlev`
cap and its tower-form falsifier) — both found unsound at the fixed-level and
tower-growth statements respectively. Two more (5, 6) are direct
re-adjudications of round-3's two PB/BDY rows (#14, #13); Codex was directed to
re-check these against the quoted text and reports the citations do not
license the pushback/boundary as claimed, rather than treating the rev-3
ruling as settled. The remaining findings (3, 4, 7, 8, 9) are fresh structural
defects in specific rev-3/rev-4 units (`hdecomp`, T-E10's `hfin`/`hA`, `OmSat`
via `ClusterFactorOf`, and `ClassTree`/`fibOf`'s two theorems) not previously
raised in exactly this form. No shell-based cross-check of the real `.lean`
tree occurred this round (the codex sandbox's working directory held only the
pasted materials), so the S-3/`LedgerIV`/build-artifact claims that Fable
reportedly verified by computation were not independently re-litigated here —
consistent with the charge's standing instruction to treat those as settled
absent a counter-computation, and Codex raised no finding against them. A rev 5
addressing the 9 criticals (with priority on the two `KBTot`/`ns_null`
mechanism defects, since further units build on `KBTot`/`Mlev`) and the 4 gaps
should be re-audited against this file plus the parallel Fable-4 pass.
