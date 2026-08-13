#!/bin/bash
cd /data/users/asvin/math-and-lean/p-adic-splitting-densities
echo "[$(date -u +%H:%M:%S)] HYPLEDGER start" >> runs/qgen/progress.txt
codex exec --skip-git-repo-check -c model_reasoning_effort=high - \
  < runs/qgen/HYPLEDGER_brief.txt > runs/qgen/HYPLEDGER_output.log 2> runs/qgen/HYPLEDGER_stderr.log
echo "[$(date -u +%H:%M:%S)] HYPLEDGER exit $? ($(wc -c < runs/qgen/HYPLEDGER_output.log) B; $(grep -E '^HYPLEDGER' runs/qgen/HYPLEDGER_output.log | tail -1 | cut -c1-70))" >> runs/qgen/progress.txt
