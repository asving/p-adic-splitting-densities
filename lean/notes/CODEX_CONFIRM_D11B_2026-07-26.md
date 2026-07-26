The D-11b scale correction is genuine. However, the flagged “\(\gamma_i\notin\mathcal W_k\) read as \(0\)” convention exposes one remaining critical defect: the asserted full \(F_{k+1}\)-block size and resulting nominal mass factor are false at shallow weights.

### (a) D-11b scale repair

The repaired scale chain is consistent:

> “\(\gamma^* := \gamma/e_{k+1}\) … \(\gamma^* := \gamma\) at the top space”

For \(B\in C_{k+1}\), non-top weights are indeed stretched by
\[
w_{k+1}(B)=e_{k+1}w_k(B),
\]
so division by \(e_{k+1}\), not \(e_k\), correctly returns to the stage-\(k\) scale in which the \(\Phi_k\)-development is read.

Likewise, the repaired slot height

> “\(\gamma_i := \gamma^*-(j_0+i\cdot e_k)\cdot h_k\) … (NO division…)”

is correct: this is \(w_k(B_j)\), whereas division by \(e_k\) would incorrectly convert it to \(w_{k-1}(B_j)\).

The lattice argument is also valid:

> “\(h_k\cdot t_k\equiv1\pmod {e_k}\), so  
> \(\gamma_i\equiv\gamma^*\cdot(1-h_k\cdot t_k)\equiv0\pmod {e_k}\).”

Since \(j_0\equiv t_k\gamma^*\pmod {e_k}\), this proves \(\gamma_i\in e_k\mathbb Z\). It does not prove \(\gamma_i\in\mathcal W_k\), which is the separate defect below.

The repaired scales are consumed correctly in (ii.3): after the stretch division, \(\gamma^*\neq\gamma'^*\), and for a fixed slot \(j\), translation by \(-jh_k\) remains injective. Thus the stated disjointness of blocks at distinct attainable heights is sound. The scale repair also reaches (ii.4) correctly: no erroneous \(e_k\)-division remains in the leaf-address order or carry substitution.

### (b) CRITICAL — missing heights do not form full blocks

The problematic sentence is:

> “terms with \(\gamma_i\notin\mathcal W_k\) read as \(0\)”

This is not benign when combined with:

> “Since \((1,\bar z,\ldots,\bar z^{g_k-1})\) is an \(F_k\)-basis of \(F_{k+1}\) and \(u(\gamma)\) is a unit, (ii.2) is an \(F_k\)-linear BIJECTION between \(d_\gamma(B)\) and the slot-digit tuple”

and:

> “by induction \(|\beta(B,\gamma)|=g_k\cdot[F_k:F_p]=[F_{k+1}:F_p]\)”

If \(\gamma_i\notin\mathcal W_k\), that component is identically zero, not a free \(F_k\)-coordinate. Its block \(\beta(B_j,\gamma_i)\) is not even defined by the preceding definition, which only defines blocks for heights in the space’s scale set. Declaring the component zero cannot supply the missing \([F_k:F_p]\) leaf coordinates.

A direct instance demonstrates the failure. Take
\[
e_1=2,\qquad h_1=1,\qquad g_1=2,\qquad
\mathcal W_1=2\mathbb Z_{\ge0},
\]
and stage-\(1\) total weight \(\gamma^*=0\). Then \(j_0=0\), and the two advertised predecessor heights are
\[
\gamma_0=0,\qquad \gamma_1=-2.
\]
Here \(\gamma_1\notin\mathcal W_1\). Consequently
\[
d_\gamma(B)=u(\gamma)d_0(B_0)
\]
ranges only over an \(F_1\)-line in \(F_2\), not all of \(F_2\). Its actual leaf block has \([F_1:F_p]\) coordinates, not
\[
2[F_1:F_p]=[F_2:F_p].
\]

This is also consistent with the section’s own split \(S6\) invariant: shallow digits generally have only the constant base-field orbit, while full current-field scalar freedom is asserted only above the clean threshold.

### (c) Consumers

D.8’s set-theoretic two-sidedness largely survives this defect. Its strongest formulation deliberately works between actual loci:

> “NO claim that every abstract digit sequence is realized — the correspondence is between actual loci”

and the backward containment routes through \(\Theta^{-1}\), rather than demanding surjectivity onto arbitrary residual windows. Thus the scale repair does not reintroduce the old D.8 window-surjectivity problem.

The counting claim does not survive unchanged. D.3(e)(ii) states:

> “ONE stage-\((k+1)\) digit = ONE block of \([F_{k+1}:F_p]\) leaf digits, of alphabet size \(|F_{k+1}|\)”

and concludes:

> “a locus cut by \(k\) block equations with alphabets \(F^{(1)},\ldots,F^{(k)}\) has mass \(\prod_i|F^{(i)}|^{-1}\)”

At the shallow instance above, pinning the actual component fixes only \([F_k:F_p]\) leaf digits and contributes \(|F_k|^{-1}\), not \(|F_{k+1}|^{-1}\). Some nominal \(F_{k+1}\)-values are also infeasible because the actual alphabet is a proper subspace.

D.11 explicitly consumes this false block assertion:

> “vol(cylinder) := the product … of (the pinned digit’s alphabet size)\(^{-1}\)”

and:

> “the translation between residual conditions and digit conditions is the unitriangular digit-equation translation of D.3(e)(ii)”

Therefore the global bijection and equality of the two finite cardinalities remain plausible, but the asserted identification with the nominal field-alphabet product is not proved and is false under the displayed shallow-weight convention. This reaches the endpoint mass statement, so the defect is critical rather than a local gap.

### (d) Three other D-11 repairs

Three unrelated D-11 repairs remain intact:

- Root augmentation: the corrected statement

  > “every side has POSITIVE slope”

  is sufficient for \(w(x)=0\); it no longer asserts the false integral lower bound.

- Laurent transport in D.8: the revision correctly observes

  > “the individual anchored terms \(d_j\) … need NOT be \(z\)-polynomials”

  and performs the exact carry recursion in \(F[z^{\pm1}]\), where \(\psi\) remains prime because \(\psi\ne z\). The displayed divisibility induction is sound.

- D.10 well-typedness: at \(e_{\rm read}=1\), \(t=0\), so minimizing positions are \(p_j(\gamma)=j\ge0\). Hence \(R(f)\in F[z]\) and

  > “\(a:=\operatorname{ord}_zR(f)\ge0\)”

  correctly types the factor \((z'+\tilde c)^a\) in \(F[z']\).

**Count: 1 CRITICAL, 0 GAP.**

The D-11b scale mismatch itself has been repaired correctly: the stretch conversion, absence of an \(e_k\)-division, and anchor-congruence lattice calculation all check out, including their use in (ii.3) and (ii.4). The remaining failure is the pre-existing shallow-height convention: lattice membership is weaker than membership in the attainable weight set, and an unavailable predecessor digit cannot be counted as a free zero-filled field coordinate. That makes the claimed uniform \(F_{k+1}\)-block size—and therefore D.11’s nominal mass product—false in general.
