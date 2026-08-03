1. **GAP — recursive closure is mathematically plausible but not operationally well-defined.**

   Quote: “every identifier t … `grep -rn '<t>'` … every declaration … joins the set BY NAME.”

   On a finite corpus, a monotone declaration-reference closure reaches a fixpoint. But the stated procedure leaves reproducibility ambiguities:

   - Plain `grep` matches substrings, comments, and unrelated namespace/name collisions—not identifiers.
   - Declaration boundaries and qualified names are unspecified.
   - The declaration kinds listed omit possible Lean forms such as `lemma`, `class`, `inductive`, and `opaque`.
   - “fixpoint UNION the pinned semantic ring” does not say whether ring-only entries are themselves recursively expanded. Several ring entries (`SideClause`, `sideReads_`) appear to be prefixes rather than identifiers.

   Thus two faithful implementers can obtain different perimeters. This is an application-perimeter gap, not a defect in the two-scale diagnosis.

   The claimed round-2 evidence does contain exactly 15 distinct filenames, and—if its grep predicates are true—it convincingly demonstrates that a one-round `SideReads` grep is insufficient. I could not independently establish that each file references an intermediary while containing no direct `SideReads`.

2. **GAP — the census and computational artifacts remain unverified in this pass.**

   Quote: “`grep -rn 'SideReads' lean/LeanUrat/` = 260 reference lines — 246 in `.lean` files across 36 distinct files + 14 in the two `MANIFEST.json`.”

   Both normal and non-login command attempts failed before execution because the sandbox launcher could not find `bubblewrap`. Consequently, this pass cannot independently certify:

   - the 260/246/36/14 census;
   - the 15 intermediary-only files;
   - named line locations and the three-token count;
   - provenance hashes;
   - the 1,093-check rerun, meters, or byte-identical JSON.

   The honesty rider is accurate: “this is PROVER-SIDE re-execution, not verifier-independent execution,” and it correctly preserves F2c as the acceptance obligation. That disclosure prevents a critical overclaim, but it cannot make this verifier pass CLEAN.

3. **CONFIRMED TEXTUALLY — standing substantive perimeter.**

   No new substantive contradiction was found:

   - The parent-scale `wPrev` versus graded-scale `R` diagnosis remains internally coherent.
   - Row A still gives corrected values `[6,6]` and compiled values `[12,6]`.
   - The repaired any-`gam′` criterion and support meter are stated consistently.
   - R1 and R4 remain properly rescoped as falsifiers, not full satisfiability or independent derivations.
   - REVISION 2 correctly supersedes “four-token” with a three-token change.
   - The recommended new-definition route preserves old `SideReads` and JuncForge meanings; the in-place alternative honestly does not.
   - D0, S8, and the owed Lean construction remain appropriately fenced.

Acceptance counter remains **0/2**: this pass is not CLEAN.

FGMN-P8 FINDINGS: 0 critical, 2 gaps  
VERDICT: GAPS-ONLY