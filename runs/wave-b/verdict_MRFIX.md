# Repair verdict MRFIX — ramified level-1 norm exactness (2026-08-27)

Scope: repair of `docs/in-progress/RAMIFIED_EXACTNESS_2026-08-26.md` against the full VRAMX
verdict. All amendments in the target document carry `[MRFIX 2026-08-27]` markers.

## Per-finding disposition

1. **FINDING 1 (normalized residue): REPAIRED.** The document no longer applies `res : O→k`
   to an expression containing `π^{-i}`. It defines `[c]_i := digAt π i c` on `(π^i)` and
   cites the landed ChapB construction and laws: B21--B22 for factorization read,
   witness-independence, additivity, and exact vanishing; B35a `resMk_mul` specialized to
   constants and transported through B59a `resFieldXEquiv` for multiplication. Both `in(P)`
   and the scalar polynomial `ψ` now use these digits.

2. **FINDING 2 (critical truncated subtraction): REPAIRED.** The definition is now guarded by
   the literal conjunction

       h*a ≤ γ AND e₁ ∣ (γ-h*a).

   The additivity, `W>γ` vanishing, `W=γ` agreement, product convolution, SPREAD 2, NC,
   multiplicative filtration, graded dimension, band count, and T1 telescoping arguments were
   rechecked and rewritten with the guard. The band count is piecewise (`γ<s` versus `s≤γ`),
   rather than using truncated `d(γ-s)`. For the adversarial nondegenerate example
   `P=X, γ=0`, the coefficient at `a=1` fails `h*1≤0`, so the repaired definition proves
   `in_0(X)=0`.

3. **FINDING 3 (I1): GAP ACCEPTED AND HONESTLY EXPOSED; STILL OPEN.** I1 is now a real OPEN
   node, estimated at 90--160 Lean lines. Its obligations are stated precisely: prove the side
   endpoints/degree; derive the non-`rfl` `hpin` from P2 and `npHgt_X`; identify B29/B35c
   `resCoeff` coefficientwise with scalar `digAt` after the explicit B59a
   `resFieldXEquiv`; then transport irreducibility and degree along the polynomial map
   equivalence. The document no longer calls this bookkeeping or invokes
   `F.hresirr H₀ rfl`.

4. **FINDING 4 (degenerate case): REPAIRED.** The false claim that degenerate T1 is exactly
   B53c `addVal_norm_key_eval` was removed. The route is now B53b
   `span_mk_eq_span_algebraMap_pow` for the arbitrary degree-bounded `A₀`, followed by the
   scalar-power quotient length and B53c's generic `length_quot_eq_addVal_norm` dictionary.

## Final status

- **T1: PARTIAL.** The guarded chain is valid conditional on I1, but I1 remains open and is
  load-bearing for residual irreducibility, NC, and the value theorem.
- **T2: PROVED.** It is independent of the extraction/I1 chain; the domain,
  norm-nonvanishing, and Cayley--Hamilton membership argument remain intact.
- **X-node transcription:** the full T1/X0 value-node transcription **MAY NOT FIRE** until I1
  is proved and reviewed. Guarded X1--X3 may be transcribed independently; X9/T2 may proceed.

## Verification

`python3 verification/ramx_cert.py` was rerun on 2026-08-27 and exited `0`: 4,443/4,443
positive instances were exact, and the reducible-residual negative control again produced 10
violations. The checked norm formula was unchanged, so `verification/ramx_cert.py` itself was
not modified.

**MRFIX disposition: document repaired honestly; T1 remains gated on OPEN I1.**
