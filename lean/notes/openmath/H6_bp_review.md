# H6 blueprint adversarial review — Codex pass 1 (2026-08-05)

Unit: H6 discharge lead (terminal-seam group (T-DEC)/(T-READ)/(T-VERD) + D-11
item (vii)). Reviewed artifact: `lean/blueprints/HDISCHARGE_H6.md` at the
PRE-fold draft (post the D-9 self-catch patch launch race — the review read the
PRE-patch D1; see the §5 timeline note in the blueprint). Charge: fresh-context
quote-and-classify (CRITICAL vs GAP), fiat-discharge hunt, quantifier audit,
defect-census soundness, new-declaration discipline, the two displayed design
questions. Runner: `codex exec --skip-git-repo-check` detached, /tmp/openmath,
prompt = charge + context pack + full blueprint (45,443 bytes).

**VERDICT: REJECT — 9 CRITICAL, 6 GAP, 1 ADVISORY.** All 16 findings folded at
fold round 1 (disposition table: blueprint §5; every repaired Lean statement
re-probed GREEN). Pass 2 on the repaired text is OWED before prover fan-out.

Full review text follows verbatim.

---

1. **(severity: CRITICAL)** “`tDECdec ... (DecIrrSeam H ∨ (DecHenSeam f H D ∧ 2 ≤ H.a0)) → ∃ ν EF, E.emits ...`” and “the a₀ = 1 booking is carried by the machine record, priced at the CU-4/Dfloor face, not by this row.”  
   This silently removes the \(a_0=1\) branch from (T-DEC-dec), although the quoted authority explicitly includes both DEC(\(\tau_{\rm hen}\)) branches in the terminal booking obligation. The carrier note explains why an `ENodeData` cannot represent that branch; it does not authorize moving the obligation to another hypothesis group. The interface therefore needs a carrier capable of representing the non-node machine record. Guarding the branch away under-asserts H6 and constitutes fiat-discharge.

2. **(severity: CRITICAL)** “`DecHenSeam ... := H.nodes = [] ∧ (H.a0 = 1 ∨ ∃ S ∈ D.principalSides 0, S.isNegInfty = true)`” together with “`tDECcor : ∀ ... (D : GMNData ...), E.emits ... → DecSeam ... D ∨ DeepCorner ... D`.”  
   `GMNData` has no laws, and neither `DecHenSeam` nor `tDECcor` requires a reader or semantic-data certificate. Thus a caller can insert or remove a negative-infinity side at will. Worse, because `tDECcor` quantifies over every `D`, a genuine \(j_0=1\) Hensel emission with \(a_0\ne1\) fails the row for the lawless `D` whose side lists are empty. Replacing the old existential `D` by a universally quantified but unpinned `D` does not repair D-7; it makes the canonical theorem generally unprovable.

3. **(severity: CRITICAL)** “`tREAD ... ConsF ... → ∃ S ∈ D.principalSides H.nodes.length, (ν.e,...,ν.u) = (...)`” and “`rc_of_rows ... → RCConsistentD`.”  
   This is weaker than the quoted (T-READ). It only matches the record to some member of a side list; it does not identify the side selected by `R.side`, establish the requested slope, or carry the uniqueness/forcing result. `R` is otherwise unused. The promised forcing lemma is not a field of `TerminalSeamRows` and hence is unavailable to `rc_of_rows`. Consequently the newly defined `RCConsistentD` weakens “the polygon side the engine reads” into “some listed side,” allowing junk or the wrong side to satisfy the terminal read.

4. **(severity: CRITICAL)** “`terminalDatumD ... slope := (D.principalSides ...).head?...`” and “`head?` is junk-tolerant; on DEC seams the side is forced unique.”  
   The definition arbitrarily chooses the list head, while `tREAD` may witness a different side. No hypothesis in A4/A7 establishes uniqueness. Moreover, `RCConsistentD` never relates its witnessed side to `terminalDatumD.slope`, so the purported “forced terminal datum” has two disconnected read notions. This does not faithfully cure D-5 and can certify inconsistent shape and slope data.

5. **(severity: CRITICAL)** “`EngineTied ... emits_irr_verdict ...`” followed by “`TerminalSeamRows ... seam : ∀ ... E, EngineTied ... E → TerminalSeamHypsE ... E`.”  
   `EngineTied` is far too weak for that universal conclusion. It has no emission soundness, Hensel-emission, shape, or completeness field. For example, an interface can have engine-realizable `reaches` and no emissions at all: `emits_irr_verdict` is then vacuous, but `tDECdec` fails at a reachable decided seam. An interface can also add junk non-irr emissions without violating `EngineTied`, causing `tDECcor` or `tREAD` to fail. Therefore `TerminalSeamRows` is not discharged by proving conformance for the canonical engine; it asserts a generally false theorem about every weakly engine-tied interface.

6. **(severity: CRITICAL)** “`TDecRow n := ... ∀-quantified over ... engine-tied E`,” similarly for `TReadRow` and `TVerdRow`.  
   These RootRows inherit the preceding arbitrary-interface error. B2/B3/C1/C2 only target `engineEmissionSV` or its upgraded canonical emission, so they cannot prove RootRows quantified over all `EngineTied` emissions. The wave graph contains no strengthening theorem from `EngineTied` to canonical equality. Thus the construction-conformance results do not discharge the propositions intended for `RootHyps`.

7. **(severity: CRITICAL)** “the `(X, FF)` keys are ... phantom at HEAD” and “the label tie ... is ... NOT statable here.”  
   This does not honestly render the K4/D-a consumption. `TerminalSeamRows n p X FF` contains no occurrence of `X` or `FF` in its data, so the same proof applies to any classifier and table, including one whose leaf labels disagree with every engine verdict. That loses precisely the tie by which terminal-seam labels enter O5triple/Step 18. Exact application shape alone is not semantic signature fidelity.

8. **(severity: CRITICAL)** “`structure FenceVII ... xhdDEx : Prop ... inFence : xhdDEx ∧ ...`” and “True-instantiable device.”  
   This does not state item (vii). The six propositions are data chosen by the constructor and are unrelated to `P`; choosing all six as `True` yields a witness for every pack. No field says that the built pack lies inside any fixed fence. The RootHyps precedent is only honest when a fixed external proposition remains an explicit assumption; existentially packaging caller-selected propositions erases the general-\(n\) claim. The docstring, flags, escalation warning, and future upgrade path do not repair the Lean semantics.

9. **(severity: CRITICAL)** “`Honest sorry permitted at the catalogue lemma if absent from the corpus`.”  
   A `sorry` in B3b would silently discharge (T-DEC-cor), contrary to §0’s rule that all four members remain hypotheses until proved. Routing the missing lemma to another owner is legitimate, but the theorem depending on it must remain conditional or unproved. Calling the resulting artifact construction-conformance is an open-row discharge by fiat.

10. **(severity: GAP)** “`engineEmissionSV ... ν existentially free in shape fields`” and “until C0 lands, `tREAD` at this emission is intentionally NOT provable.”  
    The honesty note is correct about the intermediate emission, but the exact relational definition is not supplied. Depending on what “existentially free” means, it may emit every terminal node, merely ignore shape fields, or existentially hide a node unrelated to the arguments. These choices have materially different interface laws and countermodels. B1 cannot be treated as a compile-probed unit specification without its actual statement.

11. **(severity: GAP)** “C0 ... `terminalReadRecord` def + its `SideReads`-style spec” and “the final signature is the unit prover’s E-phase probe duty.”  
    Signature freedom is unsafe here. A new definition can trivially manufacture a record from a selected `D` and then prove a tautological spec about itself, without showing it is the engine’s actual emitted record or the polygon read of \(f\). The blueprint must pin the inputs, output, semantic read certificate, index convention, and theorem connecting it to the existing machine leaf before C0 can serve as the mathematical home of (T-READ).

12. **(severity: GAP)** “`eAccF := f₀ · ∏ ...` must match ...; this reconciliation IS unit B2’s content — if it fails ... report.”  
    The \(f_0\)-included form is adequately motivated and honestly flagged, so it is a reasonable proposed declaration. It is not yet established, however. Until the root-node/dressed-history decomposition is checked, B2, the irr part of `tVERD`, and any downstream row using it must remain conditional. Calling B2 merely MED and placing the rows on a quick unblock path understates this possible definitional obstruction.

13. **(severity: GAP)** “`DeepCorner` never reached” and “the leaf trichotomy ... is UNVERIFIED.”  
    The quoted sources only corroborate saturation behavior; they do not establish the asserted as-built leaf catalogue or corner-unreachability. This is a legitimate proof route, but it cannot yet support the claimed vacuous discharge of the corner fence. If the catalogue is absent, the missing inventory is itself part of H6, not an implementation detail.

14. **(severity: GAP)** “D-8 ... `1 ≤ k` at 0-indexed lookup excludes single-read (\(k′=1\)) saturated seams.”  
    D-8(b), existential-any-position versus last-position, is unquestionably real from the quoted definition. D-8(a) additionally assumes a specific correspondence between paper level \(k′\) and the EHist list position. The pasted sources establish zero-based lookup but do not fully establish whether the base/root entry occupies position zero in that representation. That half of the accusation needs the missing representation lemma. D-1 through D-7 are supported by the quoted sources.

15. **(severity: GAP)** “G1 ... compiled countermodel” and “G2 ... toy seam + emission satisfying the trio.”  
    Neither gate is specified sufficiently to show that the required `EHist`, semantic `D/R`, and decided seam exist under the generic field assumptions. G2 also fails its stated purpose if the toy uses empty `reaches` or `emits`, since the trio would then be vacuous. These gates need explicit non-vacuity witnesses and antecedents.

16. **(severity: ADVISORY)** “**Unit count: 18** (A1–A7, B0/B1/B2/B3a/B3b, C0–C2, D1–D4, R1).”  
    The listed units total 20: seven A units, five B units, three C units, four D units, and R1. The “+ 3 gates” count is separate. This is bookkeeping rather than a logical defect, but it undermines the scheduling claim.

**Verdict: REJECT.** The blueprint is candid about several open points, but its typed replacements do not preserve H6: the \(a_0=1\) obligation disappears, semantic reads are weakened to membership in lawless data, arbitrary weak `EngineTied` interfaces are universally quantified, the K4 keys are phantom, and item (vii) is True-instantiable with no relation to the built pack. Those are logical-chain failures, not merely unfinished proofs.

**D1 keying recommendation:** add a genuine label/run tie before treating `TerminalSeamRows` as the K4 row. If `ClassifierSpec` does not yet expose enough structure, keep a clearly provisional syntactic unblocker separate from the discharge statement, or postpone the final K4 carrier. Do not land phantom `X, FF` parameters as the semantic row: later adding the tie changes both what K4 means and what existing proofs establish.

**C0 signature recommendation:** do not grant the prover unconstrained signature freedom. Pin a design-level signature now that identifies the actual machine leaf/prefix, polynomial and chain, canonical semantic read or certified reader, level index, emitted record, and a theorem tying that record both to the engine emission and to the existing `SideReads`/polygon semantics. Implementation details may remain flexible, but those observable inputs and guarantees are the substance of (T-READ).