#!/bin/bash
# SOL cert3 + compression kickoff runner (goal: Asvin 2026-08-12).
cd /data/users/asvin/math-and-lean/p-adic-splitting-densities
NAMES="D3a_grtja D3b_grtjb D3c_grtjc D3d_grtw2 D3e_weldmaster D3f_hmenu3 D3g_jd0 D3h_liftcorner D3i_gentow5 D3j_genhn_corr R11_genind N1_w12_history N2_opacity N3_genhn_f2 S1_t1_rev"
echo "[$(date -u +%H:%M:%S)] cert3 queue start" > runs/cert3/progress.txt
for name in $NAMES; do
  echo "[$(date -u +%H:%M:%S)] $name start" >> runs/cert3/progress.txt
  codex exec --skip-git-repo-check -c model_reasoning_effort=high - \
    < runs/cert3/${name}_brief.txt > runs/cert3/${name}_output.log 2> runs/cert3/${name}_stderr.log
  echo "[$(date -u +%H:%M:%S)] $name exit $? ($(wc -c < runs/cert3/${name}_output.log) B; $(grep -E '^(SUMMARY|OUTCOME|OUTCOMES|VERDICT|GRADE|FINAL VERDICT)' runs/cert3/${name}_output.log | tail -1 | cut -c1-90))" >> runs/cert3/progress.txt
  git add -f runs/cert3/${name}_output.log runs/cert3/${name}_brief.txt runs/cert3/progress.txt 2>/dev/null
  git commit -q -m "SOL cert3: ${name} run of record" 2>/dev/null
done
echo "[$(date -u +%H:%M:%S)] cert3 queue done" >> runs/cert3/progress.txt
