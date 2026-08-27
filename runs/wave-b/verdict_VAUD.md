# Verdict VAUD — LADDER-SUPPLY stop-line validity

**Date:** 2026-08-27  
**Unit:** VAUD (MATH/validity, certificate-and-tooth-first)  
**Verdict:** **VARTHETA GUARD-DERIVABILITY REFUTED; MP1 CITE ROUTE FAILS; LB1 NOT
VALIDATED; NO LANDED CLOSED DEGREE-TWO OCCURRENCE**

## Audit results

| Stop line | Result | Consequence |
|---|---|---|
| LB1 inhabited-socket validity | **NOT VALIDATED** | The landed S2 degree-four socket is a genuine antecedent at its honest threshold/completeness context. After that antecedent, `LB1Carrier` still ranges over an independently supplied arbitrary `RungInterface`; no guard field links it to the realization. The abstract malicious-interface certificate has not been rebased to the S2 carrier, so VAUD does not claim an arising-pair refutation. LS-G0 remains stopped. |
| MP1 cite hypotheses at an inhabited socket | **CITE ROUTE REFUTED** | The exact Lean trigger has only `Λ ≠ 0`, `Λ.natDegree < C.D`, `B'.Φ = B.Φ-Λ`, and `B'.Φ ∣ B.F`, besides `B' : BlockData C`. It then demands irreducibility of `B'.Φ`. The cited results do not prove that conclusion at those premises. |
| Vartheta all-`i ≥ 3` demand | **DERIVABILITY FROM THE GUARD REFUTED** | `GaugeFamilyViewEq` is invariant under arbitrary dependent `(v,ρ)` and `q` replacement at an off-range index, while `HVarthetaRes` has a concrete false instance. At the landed depth-two S2 socket, the first demanded index `3` is already not gauge-live. Owner repair must restrict the target to live indices; it may not add an HVR-shaped guard premise. |
| Closed degree-two occurrence | **NOT CONSTRUCTIBLE FROM LANDED MATERIAL** | The depth-one tower, key chain, and FGMN calculus are landed, but no depth-one `SplitNodePointSource`, hence no depth-one `ChainRealization`, exists. Consequently no `ArisingCore … 2` + `RealizedInput` package reaches the guard constructor. The only landed source/realization is depth/stage two and its accepted input has degree `4`. |

## Certificates

`leanfinal/scratch/VAUD_probe.lean` contains zero `sorry` and declares no axiom. Its named
teeth are:

- `s2_degree_four_socket` and `landed_s2_degree_ne_two`;
- `lb1_inhabited_socket_tooth`;
- `mp1_inhabited_socket_forces_irreducible`;
- `s2_three_not_gaugeLive`;
- `vartheta_sitewise_negative`;
- `gauge_view_offRange_kernel_replacement`;
- `CanonicalLadderLiveAt`, `LadderVarthetaSupplierLive`, and `LadderSupplyLive`;
- `ladderFieldLive_iff_suppliers` and `ladderFieldLive_of_suppliers`.

The off-range theorem mutates the dependent sigma package
`KernelRead = Σ v, MonoidHom.ker v →* Lˣ`; it therefore audits `v` and `ρ` together rather
than proving only the easier `q`-update lint.

Verification command (run from `leanfinal/`, never by bare `lake build`):

```bash
lake env lean scratch/VAUD_probe.lean
```

Result: exit 0. Every printed audited declaration reports only
`[propext, Classical.choice, Quot.sound]`.

## MP1 source check

The queued attribution cannot discharge `MidPeelEmission.hirr`:

- [GN15] Theorem 2.3 assumes an inductive valuation with a MacLane chain, a key polynomial
  `φ ∈ KP(μ)` outside the specified equivalence class, and a monic polynomial `g`. Its
  irreducible-leaf conclusion is attached to a prime residual factor of multiplicity one.
  None of those key-polynomial/tangent/residual-multiplicity hypotheses appears in
  `MP1Carrier`.
- GMN Theorem 2.11 / Definition 2.12 is an existence theorem for a representative/key
  polynomial of a type with prescribed degree, value, and residual polynomial. The current
  trigger does not provide such a type or prove that its arbitrary `B'.Φ` is the constructed
  representative.

Thus the current carrier needs owner repair or a different theorem with additional,
non-circular key-polynomial/minimality hypotheses placed on the MP1 trigger—not on the global
ladder guard.

## Proposed vartheta amendment

The blueprint now records the exact IFC0 signature replacement, and the probe elaborates the
complete code. The repaired conclusion is:

```text
∀ i ≥ 3,
  CanonicalLadderLiveAt C B G Kt L N v ρ q n i →
  VarthetaRes G Kt L N v ρ q i.
```

`CanonicalLadderLiveAt` repeats the full realization witness and appends
`GaugeLive core.r i`, so liveness and the external family views belong to the same witness.
The first three supplier fields are unchanged. The four-way equivalence and reverse assembly
remain projection/constructor proofs and are machine checked.

This is proposed, not enacted. The current capstone field still returns E.24's unbounded
`LadderSupply`; owner acceptance must rebind that field or move the repaired record into E.24.
No conclusion-shaped premise was added to `CanonicalLadderConfig`.

## Degree-two obstruction

The precise first missing object is a depth-one source of the form

```text
SplitNodePointSource (s2DepthOne h2 hq) E receiver
  (s2DepthOneKeyChain h2 hq).
```

It must supply legal points, stage tables, threshold/window data, letters, and the separate
canonical/arena reads. That source is required to build a depth-one `ChainRealization`.
Afterward the campaign still needs the degree-two input occurrence (`ArisingCore … 2`) and its
accepted point (`RealizedInput`). The landed `s2Frontier` is not reusable by definitional
transport because its tower, live stage, cumulative stage degree, and input degree are all the
depth/stage-two values.

## Files delivered

- `leanfinal/scratch/VAUD_probe.lean`
- `docs/in-progress/LADDER_SUPPLY_2026-08-27.md` with `[VAUD]` amendments
- `runs/wave-b/verdict_VAUD.md`

No commit was made and no other file was changed by VAUD.
