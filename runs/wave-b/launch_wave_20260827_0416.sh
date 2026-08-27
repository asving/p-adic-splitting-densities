#!/bin/bash
# 04:16 wave (after the 04:09 codex reset): NS7R (the reconciliation amendment) +
# VHENS/VRAMX (adversarial verification reads of the two biggest new-math docs —
# quote-and-classify, fix nothing; the repo's top-priority codex use).
# VSMITH/VLIFT verification reads go in the NEXT window (budget: 3 HIGH ≈ one window).
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
launch NS7R "$(cat runs/wave-b/brief_NS7R_codex.md)"
VCHARGE='You are an adversarial verifier in a fresh context for the p-adic-splitting-densities campaign (repo: /data/users/asvin/math-and-lean/p-adic-splitting-densities). Verify the mathematical document %DOC% (its unit verdict: %VERDICT%). The verifier charge, binding: quote each offending passage VERBATIM and classify it as CRITICAL ERROR (breaks the logical chain — stop checking steps that depend on it) or JUSTIFICATION GAP (assume the conclusion, keep verifying downstream). Fix NOTHING. Check especially: quantifier slips, empty/degenerate cases, circular use of an equivalent statement, claims that exceed what the cited landed inputs (file:line) actually say — spot-check at least five of those citations against the actual files. Write your findings to runs/wave-b/%OUT% as a numbered list with a final verdict line (ACCEPT / ACCEPT-WITH-GAPS / REJECT). Do not edit any other file; no commits.'
launch VHENS "$(echo "$VCHARGE" | sed 's|%DOC%|docs/in-progress/HENSEL_ENGINE_2026-08-26.md|; s|%VERDICT%|runs/wave-b/verdict_MHENS.md|; s|%OUT%|verdict_VHENS.md|')"
# VRAMX pushed to the NEXT window — its slot goes to MADJ (the Dv2ResSurv numeral
# adjudication, which GATES the mu3 chain at node NV4; found by MNV3b 2026-08-27 ~02:00).
launch MADJ "$(cat runs/wave-b/brief_MADJ_codex.md)"
sleep 15
for U in NS7R VHENS VRAMX; do echo "== $U =="; head -6 "runs/wave-b/err_${U}.log" 2>/dev/null | grep -E 'model|provider'; done
