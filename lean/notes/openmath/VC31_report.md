NOT-CONFIRMED. I found no critical scope promotion, but two display/provenance gaps prevent confirmation.

### Fold audit

- Anchor fold: PASS. The operative §0, §3.2, §6, and §35 sites identify the current anchor as “REVISION 28/VC30+VC30b” and display the full lineage: “VC30 … 1 critical / 0 gaps” → “r29-ERRATUM … 573bd1b” → “VC30b … 0 critical / 0 gaps.” They consistently say “VC31 is OWED” and “NEVER self-confirms.” Older REVISION 27/VC29 citations are historical or supersession-bracketed.

- TR3-S3 proved scope: PASS. The operative ROOT displays state:
  > “TR-3′-GEN is PROVED on {all order-2} ∪ {order-3 all-e_j = 1}, CONDITIONAL ON (H-v3)”

  They also distinguish attribution from algebra:
  > “ATTRIBUTION ONLY … the finite identity … is UNCONDITIONAL as algebra”

  No silent promotion of the (H1) row occurs; it explicitly “STAYS [M].”

- PIN-GEN-i: PASS in ROOT and the TR3-S3 provenance. The owed leg is consistently:
  > “a fresh `pdftotext -layout` re-extraction … at Defs 3.15/3.16/3.18”

  No site claims this leg discharged.

- Synthesis pass 7: PASS. REVISION 29 calls it “RUNNING,” “in flight,” and says “NOTHING is folded or claimed from it here.” The later ledger material is not imported as an r30 result.

- Roster: PASS. The nine live §3.1 rows are:

  1. (H1)
  2. (FRESH)/(H2)
  3. (ADM), an (H3) member
  4. (UB-X)/(H4b)
  5. (PACK)/(H5)
  6. (H6)
  7. (I-τ)/K-LOC/(H7)
  8. (H8′)
  9. (E-N), an (H3) member

  TR3-S3 changes content inside (H1), not the roster.

### Findings

GAP 1 — incomplete GRB provenance slice.

The appendix labels its GRB extract a “verbatim slice,” but it terminates mid-sentence:

> “CONDITIONALITY, displayed: the order-3 leg is CONDITIONAL ON”

The supplied slice therefore does not itself resolve `(H-v3)`, the PIN-GEN-i/Defs 3.15–3.16–3.18 language, or the deeper-strata fence. ROOT and the commit summaries assert those facts, but the specifically charged GRB second-bracket provenance cannot be independently verified from the embedded record.

GAP 2 — the deeper-strata fence does not explicitly enumerate the entire complement.

The operative fence says:

> “e_j ≥ 2 strata at orders ≥ 3 stay FENCED and OPEN”

This covers order 3 with some ramification and analogous higher-order strata, but does not explicitly name the second required family: all strata at orders ≥4, including all-e_j=1. The exact proved union prevents an actual promotion or unconditional-scope leak, so this is a display gap rather than a critical mathematical overclaim.

### Enumeration audit

The §35 r30 census reproduces as follows. There are 43 exact patterns represented by 42 rows because the `TransDeep`/`TRANS-DEEP` row combines two patterns.

| Pattern | r30 |
|---|---:|
| `(R1)–(R4)` | 119 |
| `(H4a)` | 199 |
| `K3-δ` | 131 |
| `SITE-EXH` | 33 |
| `GRADED-READ` | 27 |
| `TransDeep` + `TRANS-DEEP` | 45 |
| `TEN rows` | 35 |
| `NINE rows` | 51 |
| `VC25` | 57 |
| `VC23` | 26 |
| `VC26` | 104 |
| `ROUTE (a)` | 43 |
| `TR3-S2` | 36 |
| `REC-SL` | 41 |
| `RECSL` | 43 |
| `HUNI-V2` | 13 |
| `VC27` | 127 |
| `VC27b` | 55 |
| `VC28` | 74 |
| `VC29` | 81 |
| `POOL-DICT` | 48 |
| `TR-4` | 35 |
| `BasePolygonLengthLaw` | 41 |
| `ITER-LAW` | 37 |
| `leakFree` | 64 |
| `LeakFreeCarrierV4` | 10 |
| `junc_bundle` | 79 |
| `G-ADM-2` | 25 |
| `BPLL` | 18 |
| `K1ConsumerFace` | 15 |
| `N-H7-1` | 26 |
| `VACUOUS-BY-TYPE` | 10 |
| `ADM-REAL` | 39 |
| `CLASS-LAT` | 17 |
| `JUNCFORGE` | 16 |
| `TR3-S3` | 29 |
| `VC30` | 91 |
| `VC30b` | 37 |
| `VC31` | 16 |
| `H-v3` | 17 |
| `PIN-GEN-i` | 11 |
| `TWIST-3` | 11 |

Containment is correctly disclosed: `VC30b ⊂ VC30`; all 37 `VC30b` occurrences also contribute to the `VC30 = 91` count.

Clause recount at the declared hypothesis-group unit:

- (0): 0 §3.1 groups.
- (SQ): 0 §3.1 groups.
- (R): 8 groups — H1, H2, H3, H4b restricted to K3-δ, H5, H6, H7, H8′.
- (UB): 8 groups — H1, H2, H3, full H4b, H5, H6, H7, H8′.

Line-anchored falsifier: the §3.1 table has exactly the nine row starts listed above; there is no live row beginning with `(H4a)/(R1)–(R4)`, no TR3-S3 row, and no additional row created by PIN-GEN-i or TWIST-3. Thus the silent-promotion falsifier returns zero hits in the pasted REVISION 29 text.

All supplied commit resolutions and the complete TR3-S3/N-T4 embedded records reconcile under the embedded-record convention. The sole unresolved provenance item is the truncated GRB slice identified above.

VC31 FINDINGS: 0 critical, 2 gaps
VERDICT: NOT-CONFIRMED