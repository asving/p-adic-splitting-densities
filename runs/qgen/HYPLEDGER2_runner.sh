#!/bin/bash
cd /data/users/asvin/math-and-lean/p-adic-splitting-densities
echo "[$(date -u +%H:%M:%S)] HYPLEDGER2 start" >> runs/qgen/progress.txt
codex exec --skip-git-repo-check -c model_reasoning_effort=high - \
  < runs/qgen/HYPLEDGER2_brief.txt > runs/qgen/HYPLEDGER2_output.log 2> runs/qgen/HYPLEDGER2_stderr.log
echo "[$(date -u +%H:%M:%S)] HYPLEDGER2 exit $? ($(wc -c < runs/qgen/HYPLEDGER2_output.log) B; $(grep -E '^HYPLEDGER v2' runs/qgen/HYPLEDGER2_output.log | tail -1 | cut -c1-70))" >> runs/qgen/progress.txt
