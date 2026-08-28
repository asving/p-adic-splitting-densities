#!/bin/bash
# wave-c launcher — waits for the 03:03 codex window reset, then launches the six
# sol-HIGH units. Idempotent via launched_<U> marker files (NOT via out-log emptiness —
# codex writes stdout at the end, so empty-log guards misfire; lesson of 2026-08-27).
# Run inside tmux: tmux new-session -d -s padic-wavec 'bash runs/wave-c/launch_0303.sh'
set -u
cd /data/users/asvin/math-and-lean/p-adic-splitting-densities || exit 1

TARGET=$(date -d "2026-08-28 03:04:00" +%s)
NOW=$(date +%s)
if [ "$NOW" -lt "$TARGET" ]; then
  echo "$(date): sleeping $((TARGET - NOW))s until 03:04"
  sleep $((TARGET - NOW))
fi

for U in AI6 MP1R LB1G WLE SMGR MSF3; do
  B="runs/wave-c/brief_${U}.md"
  M="runs/wave-c/launched_${U}"
  if [ -e "$M" ]; then
    echo "$(date): $U already launched (marker present), skipping"
    continue
  fi
  touch "$M"
  nohup codex exec --sandbox workspace-write -c model_reasoning_effort=high \
    "Read the brief file at $PWD/$B and execute it exactly as written. Working directory: $PWD. The brief's Deliverables and Rules sections are binding." \
    < /dev/null > "runs/wave-c/out_${U}.log" 2> "runs/wave-c/err_${U}.log" &
  disown
  echo "$(date): launched $U (pid $!)"
  sleep 20
done
echo "$(date): all launches attempted; launcher exiting (codex jobs continue detached)"
