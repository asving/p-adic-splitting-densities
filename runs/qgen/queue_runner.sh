#!/bin/bash
cd /data/users/asvin/math-and-lean/p-adic-splitting-densities
for S in Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8; do
  echo "[$(date -u +%H:%M:%S)] $S start" >> runs/qgen/progress.txt
  codex exec --skip-git-repo-check -c model_reasoning_effort=high - \
    < runs/qgen/${S}_brief.txt > runs/qgen/${S}_output.log 2> runs/qgen/${S}_stderr.log
  echo "[$(date -u +%H:%M:%S)] $S exit $? ($(wc -c < runs/qgen/${S}_output.log) B; $(grep -E "^QGEN-${S} VERDICT" runs/qgen/${S}_output.log | tail -1 | cut -c1-90))" >> runs/qgen/progress.txt
done
echo "[$(date -u +%H:%M:%S)] qgen queue done" >> runs/qgen/progress.txt
