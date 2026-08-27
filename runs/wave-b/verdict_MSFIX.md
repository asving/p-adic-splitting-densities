# Verdict MSFIX — H.116b4 restricted Smith repair

[MSFIX 2026-08-27]

Source verdict disposed: `runs/wave-b/verdict_VSMITH.md` (all five numbered
items read at current HEAD).  Amended proof:
`docs/in-progress/H116B4_SMITH_PROOF_2026-08-26.md`.

## Per-finding disposition

| # | disposition | amendment and resulting proof status |
|---|---|---|
| 1 | **REPAIRED** | In Theorem E, Step 2 now sets `w'_i := Σ λ^(i) g_(p,j) + c_i Φ̃`, with the same plus sign as the Step-1 residue identity.  The text re-derives integrality: for `j < d`, insertion through the cofactor generator has multiplier `π^(ε-δ_j)c_(i,j)` and `ε-δ_j = β-kj ≥ k`; subsequent monic top-down clearing is integral by the displayed junk bounds and preserves `w'_i ≡ Y^i (mod π)` because all high coefficients remain in `πO`.  The change of generators is therefore block triangular with diagonal `Λ,I` and belongs to `GL_m(O)`.  Step 3 and the determinantal-ideal calculation now follow.  **Theorem E remains paper-proved**, but is not landed Lean. |
| 2 | **CORRECTED / SCOPE DEMOTED** | Removed “at EVERY base of every genre.”  A fresh certificate run checked exactly 91,945 exhaustive target-genre bases in CELL-1/2/4 and 970 sampled Block-B matrices, with 16 reported genre instances total.  Exit was 0 in 8.2s.  The document now says finite instances only, prime residue fields only, not a universal proof. |
| 3 | **DEMOTED TO A NAMED OPEN LEMMA** | U2 is retained only through the proved integral split `A ~ diag(πI_r,S)` and the `r` exact exponent-1 factors.  U3, including its V-bound, is retained as proved only for `r=0`.  The cofactor-inclusive passage is now **OPEN GR-7b-0 (cofactor Schur/V-inheritance)**: the Schur complement must retain the entrywise V-bound and, at every slope frame, the residue span/block normalization required by U3.  Theorem U now explicitly requires GR-7b-0 in addition to GR-7b-I/II. |
| 4 | **DEMOTED; OPEN INPUTS NAMED PRECISELY** | U4 is no longer in the proved ledger.  Its determinant formula is conditional on **OPEN GR-4a** (equal-slope planted resultant valuation), **OPEN GR-4b** (unequal-slope planted resultant valuation), **OPEN GR-4c** (`v(Res(P_p,Q)) = μ_p β_(k_p)`), and **OPEN GR-5** (multi-Sylvester determinant equals a unit sign times the pairwise-resultant product).  The scale/coprimality discussion is identified as motivation, not a proof.  U4 is optional if GR-7b-II is proved for all `t`. |
| 5 | **AUDIT ACCEPTED; CITATION SCOPES MADE EXPLICIT** | No staleness claim is made.  The new landed-input audit records the actual scopes of `alphaParent_coeff`, `comp_recentre_injective`, `plantedPoly_frame_profile`, `resFactor_surjective`, `card_res`, `monicPoly_map_residue`, `proj_classSect`, and the signed `planted_presentation_card`.  In particular, B50 `exists_smith_of_norm` is stated only as a multiplication-map determinant-length/Smith-API template; it is not the restricted multi-Sylvester map and does not prove GR-7 or GR-8.  The absence of landed GR-4a/b and GR-5 declarations is recorded. |

## Certificate verification

The proof repair changes no statement computed by
`verification/openmath/h116b4_smith_cert.py`.  It was nevertheless rerun from
the repository root on 2026-08-27:

```text
total time 8.2s
==== ALL CHECKS PASSED ====
```

Observed scope from that run:

- exhaustive: 128 + 59,049 + 32,768 = **91,945** target-genre base matrices;
- sampled Block B: **970** base matrices;
- reported genre instances: **16** (three anchors plus thirteen Block-B
  instances, counting B4's two genres separately).

## Final honest status

- **Theorem E:** PROVED ON PAPER for one equal-slope block with admissible
  cofactor, with exponents
  `{1 + D - k i : 0 ≤ i < s_μ} ∪ {1}^r`, then capped at `N`.  The repaired proof
  is not yet a landed Lean theorem.  It supplies paper-level input for GR-6/GR-8
  but does not itself land those wrappers.
- **Chain S0--S3:** survives as rigorous informal/paper lemmas.  S3 is standard
  Smith/determinantal-ideal packaging; B50 is only an implementation template
  at the narrower scope described above.
- **Theorem U:** OPEN.  U1 is paper-proved in all regimes; U2 is paper-proved
  only through `diag(πI_r,S)`; U3 is paper-proved for `r=0` and conditional on
  GR-7b-0 for `r>0`.  Completion requires **GR-7b-0, GR-7b-I, and GR-7b-II**.
- **U4 / wider GR-4--8 chain:** U4 is OPEN/conditional on GR-4a/b/c and GR-5.
  It does not upgrade Theorem U.  The GR-8 Lean kernel-cardinality wrapper is
  also not claimed landed.
- **SM-5 transcription:** **MAY FIRE.**  The corrected equal-slope paper proof
  is transcription-ready and independent of the unequal-slope and U4 open
  nodes.  “May fire” authorizes implementation work only; it does not mean the
  theorem is already formalized or landed.

MSFIX disposition: every verifier finding is either repaired or demoted to an
explicitly named OPEN statement; no universal claim rests on the finite
certificate.
