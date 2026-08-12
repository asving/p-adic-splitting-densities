#!/bin/bash
# SOL cert4 + compression kickoff runner (goal: Asvin 2026-08-12).
cd /data/users/asvin/math-and-lean/p-adic-splitting-densities
NAMES="RC1_grtja RC2_gentow5 RP1_genind X1_e13 P1_w12_history P2_genhn_count P3_opacity T1A_arc1"
echo "[$(date -u +%H:%M:%S)] cert4 queue start" > runs/cert4/progress.txt
for name in $NAMES; do
  echo "[$(date -u +%H:%M:%S)] $name start" >> runs/cert4/progress.txt
  codex exec --skip-git-repo-check -c model_reasoning_effort=high - \
    < runs/cert4/${name}_brief.txt > runs/cert4/${name}_output.log 2> runs/cert4/${name}_stderr.log
  echo "[$(date -u +%H:%M:%S)] $name exit $? ($(wc -c < runs/cert4/${name}_output.log) B; $(grep -E '^(SUMMARY|OUTCOME|OUTCOMES|VERDICT|GRADE|FINAL VERDICT)' runs/cert4/${name}_output.log | tail -1 | cut -c1-90))" >> runs/cert4/progress.txt
  git add -f runs/cert4/${name}_output.log runs/cert4/${name}_brief.txt runs/cert4/progress.txt 2>/dev/null
  git commit -q -m "SOL cert4: ${name} run of record" 2>/dev/null
done
echo "[$(date -u +%H:%M:%S)] cert4 queue done" >> runs/cert4/progress.txt
