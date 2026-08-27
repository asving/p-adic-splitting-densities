#!/bin/bash
# 09:20 wave (after the 09:16 codex reset): the two pending verification reads
# (VSMITH, VLIFT) + the re-read of the repaired ramified doc (VRAMX2).
cd /data/users/asvin/math-and-lean/p-adic-splitting-densities || exit 1
launch () {
  local U=$1 PROMPT=$2
  if [ -s "runs/wave-b/out_${U}.log" ] || [ -f "runs/wave-b/verdict_${U}.md" ]; then
    echo "SKIP $U"; return
  fi
  nohup codex exec -c model_reasoning_effort=high --sandbox workspace-write \
    "$PROMPT" < /dev/null > "runs/wave-b/out_${U}.log" 2> "runs/wave-b/err_${U}.log" &
  disown
  echo "LAUNCHED $U (pid $!)"
}
VCHARGE='You are an adversarial verifier in a fresh context for the p-adic-splitting-densities campaign (repo: /data/users/asvin/math-and-lean/p-adic-splitting-densities). Verify the mathematical document %DOC% (unit verdict: %VERDICT%). Charge, binding: quote each offending passage VERBATIM and classify CRITICAL ERROR (breaks the chain — stop checking dependents) or JUSTIFICATION GAP (assume the conclusion, keep verifying downstream). Fix NOTHING. Check especially: quantifier slips, empty/degenerate cases, circularity, claims exceeding the cited landed inputs (spot-check at least five file:line citations against the actual files, at CURRENT HEAD — amendments A-C.17..A-C.20 and A-I.4 are landed; distinguish staleness from error). Write findings to runs/wave-b/%OUT% as a numbered list ending with ACCEPT / ACCEPT-WITH-GAPS / REJECT. No other edits; no commits.'
launch VSMITH "$(echo "$VCHARGE" | sed 's|%DOC%|docs/in-progress/H116B4_SMITH_PROOF_2026-08-26.md|; s|%VERDICT%|runs/wave-b/verdict_MSMITH.md|; s|%OUT%|verdict_VSMITH.md|')"
launch VLIFT "$(echo "$VCHARGE" | sed 's|%DOC%|docs/in-progress/H116B4_LIFT_PROOF_2026-08-26.md|; s|%VERDICT%|runs/wave-b/verdict_MLIFT.md|; s|%OUT%|verdict_VLIFT.md|')"
launch VRAMX2 "$(echo "$VCHARGE" | sed 's|%DOC%|docs/in-progress/RAMIFIED_EXACTNESS_2026-08-26.md (RE-VERIFICATION: the doc was repaired per your predecessor VRAMX'"'"'s REJECT — see runs/wave-b/verdict_MRFIX.md for the repairs, and note the I1 interface is now PROVED IN LEAN at leanfinal/Uniformity/ChapB/B59c.lean; check the repairs dispose the original findings and hunt NEW breaks in the rewritten guarded chain)|; s|%VERDICT%|runs/wave-b/verdict_MRFIX.md|; s|%OUT%|verdict_VRAMX2.md|')"
sleep 15
for U in VSMITH VLIFT VRAMX2; do echo "== $U =="; grep -m1 model "runs/wave-b/err_${U}.log" 2>/dev/null; done
