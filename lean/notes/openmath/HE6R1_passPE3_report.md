# HE6R1 passPE3 — hostile pass 3 on the RECONCILIATION note + its post-PE2 dated micro-annex (fresh context; THE ACCEPTANCE ATTEMPT)

**VERDICT: PENDING (pass in progress; sections land as verified).**

Target: `lean/notes/openmath/HE6R1_RECON_2026-08-08.md` at HEAD (annex
a57c486 on the PE2-era text; arc seal 4f5ebaa → verdict 850e77e → [r2]
rows → PE1 (0C/2G/5m) → [r1′] 71c7457/8cbfaa2/57700f3 → PE2 CLEAN 2118e59
(count 1/2) → dated micro-annex a57c486). Protocol: quote-and-classify,
nothing fixed. Surfaces owned by this pass (disjoint from PE1/PE2's
routes): (1) §S2's four-case analysis + the n ≤ 7 chain end-to-end;
(2) the [r2]-era row updates as a set — timeline consistency of the three
tag eras at HEAD; (3) LEMMA HE6R1-1's bounds vs THEOREM HE7.C [r1] at the
CURRENT frozen HE7, character level; (4) the battery's exception taxonomy
re-derived from the sealed code (12 READ2 + 5 SIG2 + 4 SEP2); (5) the
dated micro-annex (all four riders) as part of the charge; (6) free hunt;
plus machine-leg integrity (pins, isolated re-run, tautology audit) and a
fresh route disjoint from the seal battery (p ∈ {3,5,7} prime-q ℓ=1
d_r=2), PE1's legs (p = 11/13; peel∘refine μ₂=3), and PE2's non-prime-q
f₁ = 2 leg.

---

## FINDINGS

(sections land below as verified)

---

## CLEAN CHARGES (attacked, survived)

(sections land below as verified)

---

## MACHINE LEG (this pass's own isolated re-verification)

* **Pins.** At HEAD, all six committed artifacts byte-identical (md5) to
  their 850e77e blobs: runner 7112f7c738ed13fb352f96849da1d309, supp
  79da51dcd40535da82effb2e347b7f18, output f842065a…, results json
  cbd8fd25…, supp output 691f5bce…, supp json 6cd743ce…. The four import
  pins recorded inside the committed json (he6_checks 321fa4d4…,
  he7_checks 688adbe8…, w12 7dc040d9…, w10 a9c34244…) equal the md5s of
  the 850e77e blobs and of the HEAD files.
* **Isolated re-run.** Full `verification/openmath` tree extracted from
  850e77e via `git archive` into a clean directory (transitive import
  chain pinned by construction); `he6r1_checks.py --full` re-run there:
  stdout IDENTICAL to the sealed `he6r1_checks_output.txt` modulo per-row
  timing strings; results json identical modulo `secs` fields
  (field-by-field compare after dropping `secs`: True); legs
  {LIFT2 59, READ2 932, SLOT2 1512, GEN2 252, SEP2 46, SEP2-inf 4,
  SIG2 682}; teeth 5/5 FIRED; 21 violation records; 87.2 s. Supp re-run
  in the same directory: 12/12 peels decided, 5/5 PARI agree, 4/4
  post-refine STRICT. Exit 0 on both. (One re-run wrinkle, disclosed:
  invoking the runner with no flags runs the SMOKE path only — exactly as
  the sealed docstring's smoke record states; `--full` is the battery.)
* **Tautology audit.** `level2_read` (runner L347–524) contains zero
  gp/pari/factorpadic references (grep over the exact line range); PARI
  enters only at `run_row`'s scoring and the teeth.
* **Exception taxonomy re-derived from the sealed code (owned surface 4).**
  The 21 records classify as 12 READ2 + 5 SIG2 + 4 SEP2, and each class's
  mechanism was read off the code, not the note: (a) READ2 — `run_row`
  files a violation whenever `level2_read` returns status ≠ OK; all 12
  records carry status BADTOTAL, produced at runner L413 when the reader's
  block sizes fail to sum to deg f (the Ψ | f stratum: A₀^{(2)} = 0 kills
  the j = 0 pin). (b) SIG2 — the PARI leg runs only on char-0 rows
  (`oracle and R.char0`); a BADTOTAL member there has σ = None ≠ PARI's
  {(2,2),(2,2)}. Verified: the 5 SIG2 f-strings are an exact subset of the
  12 READ2 f-strings; the 12 distribute 4 (ℤ₃) + 1 (ℤ₅, r = Z²+Z+1) +
  4 (F₃[[t]]) + 3 (F₅[[t]]) — char-0 subset = 5, matching the note's
  "5 of the 12 sit in the PARI count" and the per-row σ census (each row's
  decided counts sum to members − its BADTOTALs). (c) SEP2 —
  `grid2_labels` harvests (λ₂, r₂) labels from the reader's FINAL trace
  (post-α-refine states) while `build_psi2` always builds the test key
  over `fr.Psi`, the frame's PRE-refine key; the 4 violations are all
  `got == flat` (56=56, 56=56 at κ₂ = 8; 88=88, 88=88 at κ₂ = 12) — flat
  equality where strict excess was predicted, exactly the misalignment
  mechanism (the mis-keyed Ψ₂ behaves generically). The supp's recovery
  over the refined key gives 4/4 STRICT (68>64 ×2, 100>96 ×2), the note's
  numbers.

## FRESH ROUTE

(lands below after the run)

---

## GRADE LINE

(lands with the verdict)
