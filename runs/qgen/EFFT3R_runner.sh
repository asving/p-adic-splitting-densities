#!/bin/bash
cd /data/users/asvin/math-and-lean/p-adic-splitting-densities
echo "[$(date -u +%H:%M:%S)] EFFT3R start" >> runs/qgen/progress.txt
codex exec --skip-git-repo-check -c model_reasoning_effort=high - \
  < runs/qgen/EFFT3R_brief.txt > runs/qgen/EFFT3R_output.log 2> runs/qgen/EFFT3R_stderr.log
echo "[$(date -u +%H:%M:%S)] EFFT3R exit $? ($(wc -c < runs/qgen/EFFT3R_output.log) B; $(grep -E '^EFF-T3 v2 COMPILED' runs/qgen/EFFT3R_output.log | tail -1 | cut -c1-70))" >> runs/qgen/progress.txt
