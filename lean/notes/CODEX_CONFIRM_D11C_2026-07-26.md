The attainable-block construction itself is mathematically genuine: the per-height alphabets are correctly typed as additive \(\mathbf F_p\)-subspaces, absent heights are no longer treated as zero coordinates, and D.9 supplies the required characterization of attainable weights. D.8 is two-sided, and D.11’s product follows for nonempty landing cylinders. The displayed text still has one endpoint-critical empty-locus omission and one false ancillary assertion.

1. **CRITICAL — D.11 and the §C retype drop the off-alphabet/empty-locus branch.**

D.3(e) correctly states:

> “Pinning \(d_\gamma(B) = X\) is solvable iff \(X \in \mathbb A(\gamma)\) — an off-alphabet pin EMPTIES the locus”

and later:

> “an off-alphabet pin empties the locus (mass 0; zero pins never do — \(0 \in \mathbb A\) always).”

D.8’s narrower assertion is valid:

> “the off-alphabet guard never fires on a nonempty stratum.”

Indeed, once the source stratum is nonempty, every transported value comes from actual data, hence lies in the relevant image alphabet. This also makes D.8’s two-sidedness genuine: \(\Theta\) is a global digit-unitriangular bijection, and the landing equations are its translated source equations.

But D.11 removes the nonemptiness qualification and asserts:

> “every value the cylinder pins is attained (transported from an actual locus through D.8’s bijection — the off-alphabet guard never fires)”

followed unconditionally by the positive product of \(|\mathbb A(\gamma)|^{-1}\). For an off-alphabet source pin, there is no “actual locus” from which to transport anything; both corresponding loci are empty and their mass is \(0\), not the positive alphabet product.

This is not hypothetical. Take a valid shallow step with \(e_1=h_1=1\), \(g_1=2\), and \(\gamma=0\). Then \(I(0)=\{0\}\), so the top alphabet is a proper subspace
\[
\mathbb A(0)=u(0)F_1\subsetneq F_2.
\]
Pinning any \(X\in F_2\setminus u(0)F_1\) gives an empty cylinder, while the displayed D.11 product assigns the positive factor \(|F_1|^{-1}\).

The §C sentence inherits the same problem:

> “each \(F\)-digit contributes the factor \(|\mathbb A|^{-1}\) of its ATTAINABLE alphabet \(\mathbb A\) at its height”

It states no membership guard. Moreover, the displayed definition says a history is realizable iff its node data satisfy only (NA) and (HV); neither condition tests membership of every shallow pin in its attainable alphabet. Computing image cardinalities in (ZC)/TYP/C.3 is insufficient unless those clauses also explicitly test that the right-hand side lies in the computed image and assign zero otherwise. That connection is not present in the supplied retype.

For nonempty/image-admissible histories, the product is correct: each block bijects with exactly \(\log_p|\mathbb A(\gamma)|\) fresh leaf coordinates, and the unitriangular change of frame preserves that count.

2. **GAP — the claim that the base-stage index set is “always full” is false.**

The text says:

> “base: \(\mathcal W_1=e_1\cdot\mathbb Z_{\ge0}\) exactly, always full.”

With the same valid example \(e_1=h_1=1\), \(g_1=2\), \(\gamma=0\), one has \(j_0=0\) and
\[
\gamma_0=0,\qquad \gamma_1=-1.
\]
Thus
\[
I(0)=\{i<2:\gamma_i\in\mathcal W_1\}=\{0\},
\]
not the full set \(\{0,1\}\). This does not damage the revised formulas—the definition using \(I(\gamma)\) handles the case correctly, and the subsequent text correctly predicts a smaller shallow alphabet—but the quoted sentence contradicts those formulas.

The rest of the requested sweep passes. The map in (ii.2) is an \(\mathbf F_p\)-linear injection because the \(\bar z^i\) are \(F_k\)-independent; independence of development slots gives surjectivity onto the displayed image and the cardinality product. “Absent” is correctly distinguished from a zero digit, (ii.3) gives disjoint leaf blocks, and (ii.4) preserves one fresh base coordinate per equation. D.9(a), together with the stage-scale stretch, characterizes the actual weight sets; D.9(b) supplies eventual fullness. The D-11/D-11b repairs spot-checked—height-scale conversion, VERTEX’s factor \(\bar z^{-\mu\hat m}\), Laurent-valued downward transport, parent-scale standard-lift bounds, and coefficient-unit exponent-vector transport—are consistent.

**Count: 1 CRITICAL, 1 GAP.** D-11c genuinely repairs the shallow-height “absent as zero” defect and proves D.8/D.11 on every nonempty, alphabet-admissible cylinder. It does not yet justify the unconditional mass statement or the §C block convention for off-alphabet patterns, because those loci have mass zero rather than the displayed positive attainable-alphabet product.
