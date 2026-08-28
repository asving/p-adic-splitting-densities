# Verdict MP1R — redesign of the MP1 supplier route

**Date:** 2026-08-28  
**Unit:** MP1R  
**Verdict:** **PROVED: unrestricted `MP1Carrier` is false. BLOCKED-BECAUSE: neither the
existing realization funnel nor the two queued citations supplies the missing recenter-step
provenance. CHOSEN ROUTE: a superseding `MP1CarrierLive` restricted by a same-realization
recenter-step export, with `hirr` discharged by the landed direct key-irreducibility bank.**

## Route results, in required order

- **[BLOCKED-BECAUSE — option 1, live citation route]** Restricting the quantifier to a
  genuinely exported `B'` is the correct scope repair, but the current `RealizedInput` and S2
  sockets export only the parent block. They do not export a recentered successor, refined
  type, residual multiplicity, quotient, or exact representative/factor identification.

- **[PROVED — option 1, source check]** [GN15] Theorem 2.3 cannot infer irreducibility from
  recentering plus divisibility. Its irreducible-leaf clause applies to the selected
  `g_{λ,ψ}` only when the residual factor has multiplicity one, after MacLane-chain,
  key-polynomial/properness, slope, and residual-factor hypotheses.

- **[PROVED — option 1, source check]** GMN Theorem 2.11 constructs a particular monic
  representative of a specified type and proves that constructed polynomial irreducible. No
  current Lean premise identifies `B'.Φ` with that construction.

- **[CITED-FAITHFUL — option 1, corrected source]** FGMN, *Residual ideals of MacLane
  valuations*, J. Algebra 427 (2015), Lemma 1.8 states that a key polynomial is irreducible
  over the completed field. This targets the exact live repair once the exporter proves
  key-polynomialhood of its exact `B'.Φ`.

- **[PROVED — option 2, direct mechanism]** With `S.keyPolynomial B'.Φ` and an
  `FGMNSourceLaws` package tied to the same realization, landed
  `FGMNSourceLaws.key_irreducible` gives irreducibility in `Polynomial O`, and
  `Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map` gives the exact `hirr`
  field. `B'.hΦdeg.trans C.hef` gives `hef`.

- **[GAP — option 2, producer]** The final assembly is small, but no landed declaration
  produces `S.keyPolynomial B'.Φ` or the item-2--4 peel core for a recentered successor at a
  ladder socket. At S2, `C132kp5.s2Mu3_key_irreducible` and
  `C132kp6b.s2Mu3_calculus_nonempty` are landed; the missing statement is that the actual
  recentered `B'.Φ` is an `S2Mu3KeyPoly`, plus its quotient/interface export.

- **[PROVED — option 3, countermodel]** `leanfinal/scratch/MP1R_probe.lean` proves
  `unrestricted_mp1_false : ¬ MP1Carrier C₂ B₂` using `Λ=4`,
  `B'.Φ=X²-4`, and `B.F=(X²-4)(X²-1)`.

## Citation mapping table

| Status | Source clause | Proposed live Lean supplier | Conclusion mapping |
|---|---|---|---|
| **GAP** | [GN15] Thm 2.3: inductive valuation with MacLane chain | `core.T`, `A.keys`, and same-chain `FGMNSourceData`/`FGMNSourceLaws` | No landed analytic dictionary theorem at this socket |
| **GAP** | [GN15]: `φ ∈ KP(μ)` and `φ ≁μ φ_r`; published FGMN Thm 6.4 uses `φ` proper | `S.keyPolynomial B'.Φ`; properness/non-equivalence absent | Cannot select the theorem's branch |
| **PROVED** | [GN15]: monic `g` | `(Ladder.BlockData.natDegree_F B).2` | Supplies monicity of `B.F` once the guard's domain instance is unpacked |
| **GAP** | [GN15]: slope `λ` and prime residual factor `ψ` | No current export | No selected factor |
| **GAP** | [GN15]: `ord_ψ(R_λ(g)) = 1` | No current export; `B'.Φ ∣ B.F` is not this | Irreducible-leaf clause unavailable |
| **GAP** | [GN15]: theorem factor `g_{λ,ψ}` | No equality `B'.Φ = g_{λ,ψ}` | Even a leaf theorem would concern an unidentified polynomial |
| **GAP** | [GN15] eq. (2.1): chain `(e,f)` | No leaf-to-`B'.Φ` identification | Not needed for current `hef`, which is already derived from block/carrier degrees |
| **GAP** | GMN Thm 2.11: a specified type and residual polynomial | No refined-type/residual export | Construction cannot be instantiated |
| **GAP** | GMN Thm 2.11: the constructed `φ_r` | No equality to `B'.Φ` | Its irreducibility conclusion cannot fill `hirr` |
| **CITED-FAITHFUL** | FGMN 2015 Lemma 1.8: key polynomials are irreducible | `S.keyPolynomial B'.Φ` plus the source/field dictionary | Supplies the exact polynomial's irreducibility; landed direct banks implement the algebraic step |

## Exact supersession target

- **[PROVED — shape]** The exact proposed code is recorded in
  `docs/in-progress/LADDER_SUPPLY_2026-08-27.md`, section `[MP1R 2026-08-28]`. Its
  `MP1CarrierLive` preserves every old trigger and the old conclusion, adding only
  `CanonicalMP1StepExport ... Λ B'` immediately before the conclusion.

- **[PROVED — non-circularity]** The associated `MP1StepCore` contains only
  `MidPeelEmission` items 2--4: quotient, key alignment, peel identity, mass, threshold, and
  quotient interface. It does not contain `hirr` or `hef`.

- **[PROVED — supersession direction]** Any old `MP1Carrier` proof implies the live form by
  ignoring the new export premise. The converse is intentionally absent because the
  countermodel refutes it.

- **[BLOCKED-BECAUSE — funnel]** E.24's `LadderSupply.mp1` and IFC5's current live record
  still use unrestricted `MP1Carrier`. A production amendment needs a new
  `LadderMP1SupplierLive`, a combined live supply record preserving IFC5's vartheta repair,
  and owner-authorized rebinding of the signed capstone `ladder` field.

## Source-numbering fence

- **[PROVED]** [GN15] is Guàrdia--Nart, *Genetics of polynomials over local fields*,
  Contemp. Math. 637 (2015), Theorem 2.3 and equation (2.1).

- **[PROVED]** The representative-construction result is GMN, *Higher Newton polygons in
  the computation of discriminants and prime ideal decomposition in number fields*, Trans.
  AMS 364 (2012), Theorem 2.11, followed by Definition 2.12; the repo source is
  `docs/references/HigherNewton.tex`, label `phir`.

- **[PROVED]** Theorem 2.11 of `docs/references/s10208-024-09646-x.pdf` is instead a
  tangent-direction/initial-form-factor theorem in the 2025 paper *Polynomial Factorization
  Over Henselian Fields*. It is not the GMN representative theorem and supplies no shortcut.

## Verification and files

- **[PROVED]** Required command executed:

  ```bash
  cd leanfinal
  timeout 580 ~/.elan/bin/lake env lean scratch/MP1R_probe.lean
  ```

  Exit 0; zero `sorry`; all ten `#print axioms` results are exactly
  `[propext, Classical.choice, Quot.sound]`.

- **[PROVED]** Files delivered:

  - `leanfinal/scratch/MP1R_probe.lean` (new optional probe)
  - `docs/in-progress/LADDER_SUPPLY_2026-08-27.md` (dated section appended)
  - `runs/wave-c/verdict_MP1R.md` (this verdict)

- **[PROVED]** No landed `.lean`, leanspec file, or existing scratch file was edited. No git
  commit was made.

## Open work

- **[GAP]** Define and land the producer-side, same-realization recenter-step export.
- **[GAP]** Prove key-polynomialhood of the exact exported `B'.Φ` and export its quotient/core
  data at every arising transition.
- **[GAP]** Enact the supplier/supply/capstone supersession under owner review.
- **[BLOCKED-BECAUSE]** The old unrestricted MP1 target must not receive further proof or
  citation effort: it has a Lean-core countermodel.
