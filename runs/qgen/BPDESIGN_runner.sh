#!/bin/bash
cd /data/users/asvin/math-and-lean/p-adic-splitting-densities
echo "[$(date -u +%H:%M:%S)] BPDESIGN start" >> runs/qgen/progress.txt
codex exec --skip-git-repo-check -c model_reasoning_effort=high - \
  < runs/qgen/BPDESIGN_brief.txt > runs/qgen/BPDESIGN_output.log 2> runs/qgen/BPDESIGN_stderr.log
echo "[$(date -u +%H:%M:%S)] BPDESIGN exit $? ($(wc -c < runs/qgen/BPDESIGN_output.log) B; $(grep -E '^BPDESIGN VERDICT' runs/qgen/BPDESIGN_output.log | tail -1 | cut -c1-70))" >> runs/qgen/progress.txt
