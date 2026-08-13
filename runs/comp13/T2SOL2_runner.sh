#!/bin/bash
cd /data/users/asvin/math-and-lean/p-adic-splitting-densities
echo "[$(date -u +%H:%M:%S)] T2SOL2 start" >> runs/comp13/progress.txt
codex exec --skip-git-repo-check -c model_reasoning_effort=high - \
  < runs/comp13/T2SOL2_brief.txt > runs/comp13/T2SOL2_output.log 2> runs/comp13/T2SOL2_stderr.log
echo "[$(date -u +%H:%M:%S)] T2SOL2 exit $? ($(wc -c < runs/comp13/T2SOL2_output.log) B; $(grep -E '^VERDICT' runs/comp13/T2SOL2_output.log | tail -1 | cut -c1-80))" >> runs/comp13/progress.txt
