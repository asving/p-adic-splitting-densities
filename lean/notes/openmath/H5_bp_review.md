# H5_bp_review — Codex adversarial review of HDISCHARGE_H5.md (r1), 2026-08-05

**Unit:** H5 discharge lead, hypothesis-discharge swarm (Asvin directive
2026-08-05). **Reviewed text:** `lean/blueprints/HDISCHARGE_H5.md` at its r1
form (pre-fold). **Reviewer:** Codex (fresh context, quote-and-classify charge:
CRITICAL vs GAP, fix nothing; 8-point checklist — door-table faithfulness, no
fiat discharge, independent re-derivation of the R1/R2 skeleton, (RE) carrier
fidelity, PACK-ii conditionality, PACK-iii coverage, new-declaration dedup,
wave/dependency correctness). **Prompt:** the charge + the full r1 blueprint +
pasted sources (ROOT §3.1 (PACK) row REVISION-12 text; D-11 r4 Theorem M2 (RE)
display + consumed-instance note; leaf §2A.1–2A.3 (ROW-Σ); design V5 §3.5 +
route display; landed corpus declarations). Raw event stream:
`/tmp/openmath/H5_bp_review.jsonl` (10.6 KB; final agent message below,
VERBATIM).

**VERDICT on r1: REJECT — 5 CRITICAL + 8 GAP.** All findings statement/display
level; finding 7 CONFIRMS the mathematical core ("Conditional on symbolic EXM,
BASE, handoff_lt, trow_canonical, hsolve, hblockU, and hu.1, the R1 induction
is sound. The three R2 totals also agree with the leaf's Φ values.").

**Disposition:** ALL 13 findings adjudicated VALID and folded as the
blueprint's REVISION 2 — the full finding-by-finding disposition table lives at
`lean/blueprints/HDISCHARGE_H5.md` §7 (with the changed Lean statements
re-probed at HEAD b314edc: 4 sorries, 0 errors). Post-fold status: READY.

---

## The findings (verbatim)

1. **CRITICAL — `REWitness` does not encode the “no allocation datum” conjunct (checklists 2, 4).** The blueprint claims: “`REWitness T` types the (RE) conjunction exactly” and “‘No allocation datum’ is carried STRUCTURALLY: `REWitness` mentions no `AllocDatum`.” But the authoritative carrier has the mandatory field `BnCoordinates.allocation : ℕ → AllocDatum n`. Omitting any proposition about that field does not assert its absence or triviality; it merely ignores it. This directly contradicts (RE): “the member carries NO allocation datum at any block.” Consequently, `mkREMember` cannot establish this conjunct “by construction” from the displayed inputs, and its claimed `REWitness` is not a witness of source-level (RE).

2. **CRITICAL — `REWitness.trow_canonical` omits the actual displayed-row part of (RE) (checklists 2, 4).** The only row field is quoted as `trow_canonical : ... (T.blocks e he).trow = tRow T.β (exits e)`. The blueprint then says: “The displayedRow tie … enters R2 through `displayedRow` itself” and that O2′/O3 conformance is “route-a/route-b territory.” Source (RE), however, requires the member’s actual family-(iv) rows to have the O2′ re-feed or O3 scaling “and nothing else.” Defining an auxiliary `displayedRow` does not prove that any row carried by `T`, its coordinates, entries, or realized pack equals that auxiliary function. Thus D2 is not “(RE)-exact,” and C2’s proposed `rfl` construction cannot discharge PACK-iv even for the constructed member without another conformance field or theorem.

3. **CRITICAL — B1’s stated theorem is unprovable from `MassFacts` because it lacks the range condition and base nonnegativity (checklists 2, 3, 5, 8).** B1 concludes `∀ e σ ...` with no `e ≤ n`, while `mass_complete` is available only under `e ≤ n`. Therefore the advertised induction has no mass-total input for blocks `e > n`. The blueprint itself also concedes: “e ≤ 1 nonneg is NOT derivable from `MassFacts` as displayed; add `base_nonneg` to `MassFacts`.” That is an acknowledged missing hypothesis, not an implementation detail. Until the statement is changed, B1 and hence B2/PACK-ii are not among the declarations “provable at HEAD.”

4. **CRITICAL — B1 also lacks regularity/membership facts for exit masses (checklist 3).** The sole mass sign field is `∀ h : mass F ∈ OKat q₀, 0 ≤ evalAt ...`; it supplies a result only after an `OKat` proof is given. Yet `ExitData.mass` has no link to `T.entries`, `MemRcyc`, `Gram`, or `OKat`. The claim that B1 can evaluate “masses (MNN) × legs” therefore has no way to form the required evaluated mass terms, use the evaluation ring hom on each product, or invoke `mass_nonneg`. The missing hypothesis is at least regularity of every exit mass at every relevant evaluation point, or a proved identification with regular member entries.

5. **CRITICAL — `H5PackTyped` cannot express the H5 package it claims to express (checklists 2, 7).** Its quoted fields are `corr`, `re_profile`, `wsh`, and `bdd`, followed by a claimed theorem “unpacking to the four member conclusions.” There is no PACK-i/rsh-interpolation field at all. Moreover, `corr` relates `P` to `R`, while `re_profile` and the row-law fields concern a separate `T`; no field identifies `T` with the member represented by `R` or `P`. The deferred “`InstancePin` plug-slot as an opaque-parameter comment” cannot enforce that relation. Finally, B2 requires a particular `W : REWitness T` and `M : MassFacts T W`, while the displayed bundle provides only `Nonempty (REWitness T)` and no `MassFacts`. This is a Lean-level carrier that cannot mean “actual-pack correspondence plus PACK-i–iv.”

6. **GAP — PACK-ii conditionality is source-compatible, but “honest maximal scope” and the retirement wording are unsupported (checklists 1, 5).** The restriction motivated by “arbitrary-allocation members whose rows leave [0,1]” is consistent with C2/C3: arbitrary-α members are excluded. But the door table says “YES at (RE)+MassFacts members” and calls this “the honest maximal scope,” while the intended member has not been shown to carry `MassFacts`, and the proposed B1 does not follow from that structure as written. C6 shows that unrestricted arbitrary-α members fail; it does not establish that this particular strengthened symbolic hypothesis package is maximal.

7. **GAP — the symbolic R1 theorem uses a stronger, unretired mass hypothesis than the leaf (checklist 3).** The blueprint says it proves “the SAME algebra one level up, at ℚ(q)” using `(EXM) Σ_F m(F) = 1 − κ₀ − κ₁`, but C3 supplies this identity semantically, separately at each prime-power evaluation, through M1(a)/M1(d). A symbolic rational-function identity may be derivable from infinitely many regular evaluations, but that derivation is not provided; the blueprint instead assumes it and lists its derivation as a follow-on. Conditional on symbolic EXM, BASE, `handoff_lt`, `trow_canonical`, `hsolve`, `hblockU`, and `hu.1`, the R1 induction is sound. The three R2 totals also agree with the leaf’s Φ values. The statement that child-pool bookkeeping “disappears” is correct for symbolic R1, but not for evaluated nonnegativity B1, where uniformity in `q₀` must still be arranged explicitly.

8. **GAP — PACK-iii’s “full discharge” lacks a coverage theorem (checklists 1, 6).** The blueprint concludes: “every row entry AND every solved leg lies in the evaluation-regular subring,” from `entries_memRcyc` and `beta_memRcyc`. This plausibly proves regularity for those two corpus collections, and `2 ≤ q₀` correctly covers prime powers. But the source obligation concerns every row’s “weight/shape series,” and no displayed theorem identifies all such series with `T.entries ∪ range(T.β)`, nor connects them to the chain’s `wsh_ok` field. D-6 may indeed be only the already-landed ring-hom partner, but the entries/legs-to-weight/shape coverage and chain-instance seam remain unproved. Thus “fully discharge … at the 𝔅_n side” is stronger than the displayed warrant.

9. **GAP — C1 is only a tautological self-correspondence, with a fidelity risk for “entry-for-entry” (checklists 1, 2, 7).** The blueprint accurately admits that `packOfMember_corr` proves only that “the constructed pack conforms to the member it was constructed from.” However, its row type is built from values in the finset `T.entries e`, not from semantic row identities. Distinct rows with equal rational-function entries would collapse, and no row-to-verdict or member-to-reference pin is present. This may be useful scaffolding, but it is not yet demonstrated to implement the source’s entry-for-entry correspondence. The section 6 residue is honest about the realized-pack identification remaining open; C1 should therefore not be counted as clause-4 law-transfer without a row-identity/`InstancePin` seam theorem.

10. **GAP — the door table adds an unsupported n=2 “route-a” and uses ambiguous retirement language (checklist 1).** It describes clause 4 as “route-b constructor (+ route-a n ≤ 3 data instances).” The authoritative retirement display defines route-a specifically for `n = 3`; n=2 numerics are falsifier/executed-instance evidence, not a named retirement route. The table otherwise correctly assigns CONF to clause 4/PACK-iv and acknowledges they do not retire at the consumed instance, and it correctly leaves the chain-vocabulary PACK-i seam open. The PACK-ii/iii cells labeled “YES” should likewise not be read as ROOT-row retirement because the required intended-member and chain-instance bindings remain open.

11. **GAP — the O2 junk branch is locally guardable but creates an avoidable soundness interface risk (checklist 4).** The definition contains `| Booking.O2 => tRow β E σ -- guarded placeholder`, while the only guard lives separately in `REWitness.booking_reentrant`. The case-specific R2 theorems are safe if they always require an O1/O2r/O3 equality, but `displayedRow` itself is public and its type does not require the guard. A later generic consumer can evaluate the fabricated O2 meaning without contradiction. This does not falsify R1/R2, but it weakens carrier fidelity and demands an explicit guarded API discipline not present in the declarations.

12. **GAP — new-declaration deduplication is incomplete around `H5PackTyped` and the coordinate refinement (checklist 7).** `tRow` and `displayedRow` are reasonable derived operations reusing `rowOf`; `packOfMember` is a constructor for the existing `AssembledPack`; and the blueprint does acknowledge that `ExitData` overlaps `BnCoordinates.handoffs/composition`. But it leaves that overlap as a future seam with no compatibility proposition, while using `ExitData` as the authoritative row roster. More seriously, `H5PackTyped` overlaps both `PackCorrespondence` and BP_VI’s existing `h5_pack` home while declaring no equivalence, migration theorem, or ownership-respecting refinement path. An “opaque-parameter comment” is not deduplication.

13. **GAP — the wave schedule has a backward dependency and understates probe status (checklist 8).** B1’s proof route explicitly closes the quotient “by positive pivot (P0),” yet W3 schedules `B1 → B2` before W4 schedules `P0 ∥ P1`. Either B1 consumes a later-wave result or independently reproves P0’s content; the plan specifies neither. R2’s use of R1 and R1’s BASE case are otherwise ordered correctly, but BASE does not provide the nonnegativity B1 needs. P1’s membership binders are plausible call-site obligations, not hidden conclusions, but P1 is expressly “NOT probed verbatim,” contradicting the broader §4.0 claim that every §4 statement was probed verbatim.

**VERDICT: REJECT**
