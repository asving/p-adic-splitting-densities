#!/bin/bash
# SOL comp3 + compression kickoff runner (goal: Asvin 2026-08-12).
cd /data/users/asvin/math-and-lean/p-adic-splitting-densities
NAMES="S6R T1P3 T3P2"
echo "[$(date -u +%H:%M:%S)] comp3 queue start" > runs/comp3/progress.txt
for name in $NAMES; do
  echo "[$(date -u +%H:%M:%S)] $name start" >> runs/comp3/progress.txt
  codex exec --skip-git-repo-check -c model_reasoning_effort=high - \
    < runs/comp3/${name}_brief.txt > runs/comp3/${name}_output.log 2> runs/comp3/${name}_stderr.log
  echo "[$(date -u +%H:%M:%S)] $name exit $? ($(wc -c < runs/comp3/${name}_output.log) B; $(grep -E '^(SUMMARY|OUTCOME|OUTCOMES|VERDICT|GRADE|FINAL VERDICT)' runs/comp3/${name}_output.log | tail -1 | cut -c1-90))" >> runs/comp3/progress.txt
  git add -f runs/comp3/${name}_output.log runs/comp3/${name}_brief.txt runs/comp3/progress.txt 2>/dev/null
  git commit -q -m "SOL comp3: ${name} run of record" 2>/dev/null
done
echo "[$(date -u +%H:%M:%S)] comp3 queue done" >> runs/comp3/progress.txt
