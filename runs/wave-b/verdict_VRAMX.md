# Adversarial verdict VRAMX — ramified level-1 norm exactness

1. **JUSTIFICATION GAP.** The initial form is not defined in the stated coefficient ring. The offending passage is:

   > `in(P) := Σ_{a ∈ Att(P)} res( P.coeff a · π^{−v(P.coeff a)} ) · t^{v(P.coeff a)} x^a ∈ k[t,x],`

   In the stated setting `π^{-v(P.coeff a)}` is not an element of `O`, while `res : O → k` is only defined on `O`. The intended object exists: from the exact valuation one can uniquely write `P.coeff a = π^i u` and reduce `u`, or equivalently construct a division/extraction map on the ideal `(π^i)`. But that construction, its independence, and its additive and multiplicative laws are not supplied or cited. Assuming this normalized-residue construction has the asserted laws, the audit continues.

2. **CRITICAL ERROR.** The additive extraction map is false with the natural-number subtraction used throughout the document and corpus. The offending passage is:

   > 1. (additive extraction) for each γ the map `in_γ` — defined coefficientwise by
   >    `in_γ(P) := Σ_{a : e₁ ∣ (γ−h·a), i(a) := (γ−h·a)/e₁ ≥ 0} res(P.coeff a · π^{−i(a)}) t^{i(a)} x^a`
   >    — is additive on `{P : W(P) ≥ γ}`, equals `in(P)` when `W(P) = γ`, and equals `0` when
   >    `W(P) > γ`;

   Here `γ,h,a,e₁ : ℕ`. Thus `γ-h·a` truncates to `0` when `h·a>γ`, and the condition `i(a) ≥ 0` is vacuous. For the allowed nondegenerate case `h≥1`, take `γ=0` and `P=X`. Then `W(X)=h>0`, but the displayed definition admits `a=1` because `0-h=0`, `e₁ ∣ 0`, and `i(1)=0`; it contributes `res(1)x=x`. Hence the formula gives `in_0(X)≠0`, contradicting the asserted `W(P)>γ ⇒ in_γ(P)=0`. The proof at §3.2 repeats the same truncated-subtraction condition and therefore does not repair it. SPREAD 2, NC, the multiplicative filtration, the band count, and T1 all depend on this false extraction lemma, so in accordance with the verifier charge I stopped checking that dependent chain. In particular the document's “None at math level: §3 is a complete proof” and the unit verdict's “PROVED at math level, no open gaps” are not sustained.

3. **JUSTIFICATION GAP.** Independently checking the load-bearing residual-polynomial interface reveals that the cited landed definition does not by itself provide the claimed identification. The offending passage is:

   > **INTERFACE I1 (resPoly identification; bookkeeping, no mathematics).** At the frame key,
   > `sideMin X Φ′ h e₁ hne = 0` and `sideMax = D′` (both endpoints on-side by `hpure`; the
   > range caps at `D′`), so `sideDeg = f₁`, the pin is `H₀ = h·f₁` (P2), and B29's
   > `resPoly π X Φ′ h e₁ hne (h·f₁)` has `k`-th coefficient the residue of
   > `Φ′.coeff (e₁·k)` read at height `h·f₁ − h·k` — coefficientwise equal to `ψ` above under
   > the canonical identification `resField X ≅ k`. `hresirr H₀ rfl` then supplies
   > `Irreducible ψ` and `ψ.natDegree = f₁`.

   `B29.lean:91-94` only defines the coefficients as `resCoeff` values in `resField X`; it does not identify them with the scalar normalized residues used in `ψ`. The current corpus has a relevant pure-case coefficient theorem at `B35c.lean:84-105`, but applying it still requires the `sideMin/sideDeg` proofs, specializing `dev X`, unfolding `resMk`/the digit construction, and transporting along an explicit `resField X ≃ k`. Moreover the pin supplied to `KeyFrame.hresirr` is not `rfl`: `C01.lean:98-100` requires an equality involving `npHgt` at `sideMin`, whereas `H₀=h·f₁` follows propositionally from P2 plus the `X`-development/height identities. Since irreducibility of `ψ` is the UFD endgame's essential input, this is a genuine gap, not mere bookkeeping. Assuming the identification, its conclusion is mathematically plausible.

4. **JUSTIFICATION GAP.** The claimed degenerate-case citation is not an instance of the cited theorem. The offending passages are:

   > At the degenerate frame `h = 0` (forcing `e₁ = 1`, `D′ = f₁`) this is exactly the landed
   > B53c `addVal_norm_key_eval` instance read through `stageHeight = gaussVal` (C05)

   and

   > (Consistency: T1 at `h = 0` is B53c's `addVal_norm_key_eval` read through
   > C05's `stageHeight = gaussVal` — and battery 7 of the cert checks it numerically.)

   `B53c.lean:158-161` computes the norm of an order-1 key `φ` evaluated in `AdjoinRoot g`, with `g` monic and `dev φ g 0 ≠ 0`. T1 instead computes the norm of an arbitrary nonzero polynomial `A₀` of degree below `F.key` evaluated in `AdjoinRoot F.key`; an arbitrary `A₀` is neither the key `φ` nor subject to B53c's key hypothesis. The degenerate T1 can be derived using the separate ideal statement `B53b.span_mk_eq_span_algebraMap_pow` plus the determinant-length dictionary, but it is not “exactly” an `addVal_norm_key_eval` instance. This overclaim is only a consistency aside and does not create an additional break beyond finding 2.

5. **Citation spot-check and current-corpus audit (no additional mathematical finding).** I checked the current HEAD (`18509ad1`, which contains amendment commit `b59e2dd5`) rather than the pre-amendment tree.

   - `C01.lean:80-100` does supply precisely the displayed `KeyFrame` fields, including positive `e₁,f₁`, coprimality, monicity, degree, irreducibility, purity, nonempty side, and the pinned residual irreducibility/degree pair.
   - `C131p.lean:112-117` does supply the stated coefficient-infimum formula for `stageHeight`.
   - `C27.lean:164-171` does supply the cleared constant-coefficient purity equation used for P2.
   - `B33.lean:84-88` supplies only the superadditive inequality for `suppVal`; its extra hypotheses (`hπ`, monic positive-degree `X`, and `0<e₁`) are available here. It does not supply SPREAD's equality, and the document correctly attempts to prove that separately.
   - `B53c.lean:121-140` supplies the generic determinant-length dictionary with free, finite, positive-rank and nonzero-norm hypotheses and, as claimed, no completeness hypothesis. This spot-check does not validate the later stopped band-count argument.
   - `Leanspec/ChapC.lean:883-889` confirms that signed C.27 has no `IsAdicComplete` assumption.
   - `C27x.lean:241-242` supplies `dv2Hgt_key` exactly as quoted.
   - The membership-assisted transfers cited from `scratch/DEC4_check.lean:42-131` have since landed in the current corpus as `ChapB/B53d.lean:43-124` with the same essential hypotheses. Referring only to the scratch namespace is therefore **staleness, not a mathematical error**.

   T2 is independent of the stopped extraction/NC chain. Its domain and Cayley–Hamilton membership components are genuinely proved in `scratch/MRAMX_probe.lean:48-111`, and its norm-nonvanishing argument by scalar extension of an injective multiplication map is mathematically sound. This does not rescue T1, which is the unit's exactness claim.

   Amendments A-C.17--A-C.19 concern the previous-grade fence, below-current chain normalizer, and `shadow_persistence` degree fence; they do not alter the KeyFrame/level-1 norm inputs audited here. A-C.20 now degree-pins every load-bearing C.34/C.35 block candidate (`C35.lean:163-172,273-282`). Thus the document's generic references to the “C.35 frontier” are pre-amendment/underspecified commentary, but its explicit fence that the general-`C` consumer needs more than this KeyFrame-only theorem remains directionally correct. None of A-C.17--A-C.20 cures finding 2.

**FINAL VERDICT: REJECT**
