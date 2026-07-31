export const meta = {
  name: 'lean-division',
  description: 'One blueprint division: plan -> wave-by-wave prover fan-out -> checkpoint',
  phases: [
    { title: 'Plan', detail: 'extract wave/unit list from the blueprint' },
    { title: 'Prove', detail: 'prover per unit, waves in order' },
    { title: 'Checkpoint', detail: 'build gate + commit per wave' },
  ],
}

const REPO = '/data/users/asvin/math-and-lean/p-adic-splitting-densities'
const BP = args.bp // e.g. "BP_I"

const PLAN_SCHEMA = {
  type: 'object', required: ['waves'],
  properties: {
    waves: {
      type: 'array',
      items: {
        type: 'object', required: ['name', 'units'],
        properties: {
          name: { type: 'string' },
          units: {
            type: 'array',
            items: {
              type: 'object', required: ['id', 'file', 'task'],
              properties: {
                id: { type: 'string' },
                file: { type: 'string', description: 'repo-relative .lean path under lean/LeanUrat/Scaffold/' },
                task: { type: 'string', description: '<=600 chars: what to prove, deps, pointers into the BP' },
              },
            },
          },
        },
      },
    },
  },
}

const VERDICT_SCHEMA = {
  type: 'object', required: ['status', 'note'],
  properties: {
    status: { type: 'string', enum: ['PROVED', 'PARTIAL', 'BLOCKED'] },
    decls: { type: 'string' },
    note: { type: 'string' },
  },
}

phase('Plan')
const plan = await agent(
  `Read ${REPO}/lean/blueprints/${BP}.md (REVISION 2) in full. Extract its complete wave plan as structured output: every wave IN DEPENDENCY ORDER, every unit in each wave. For each unit: id (the blueprint's unit id, e.g. I-H7), file (the repo-relative target path the blueprint assigns, always under lean/LeanUrat/Scaffold/), task (<=600 chars: one-line goal, the blueprint section/anchor where its VERBATIM Lean statement lives, dependency unit ids, difficulty tag if the BP gives one). Do NOT paraphrase Lean statements into the task — provers read the blueprint themselves. Every unit in the blueprint must appear exactly once; do not invent or merge units. If the blueprint groups several tiny units into one file+wave cluster explicitly, you may emit one unit entry per cluster with all ids in the task.`,
  { label: `${BP}:plan`, schema: PLAN_SCHEMA },
)
if (!plan || !plan.waves?.length) { log(`${BP}: plan extraction FAILED`); return { bp: BP, error: 'no plan' } }
log(`${BP}: ${plan.waves.length} waves, ${plan.waves.reduce((s, w) => s + w.units.length, 0)} units`)

const results = []
for (const wave of plan.waves) {
  const wr = await parallel(wave.units.map(u => () =>
    agent(
      `You are prover ${u.id}, ${BP} division, Lean swarm. Repo: ${REPO} (Lean 4.31 + Mathlib; work from ${REPO}/lean). UNIT: ${u.task}\n` +
      `RULES: (1) Open lean/blueprints/${BP}.md, find unit ${u.id} — its Lean statement is there VERBATIM; transcribe EXACTLY (statement changes forbidden; if the statement cannot compile as written, report BLOCKED with the exact error — do not weaken it). (2) Target file ${u.file}; namespace LeanUrat.Scaffold.*; you may create it or extend it; imports from the existing corpus welcome; editing files outside lean/LeanUrat/Scaffold/ is FORBIDDEN (blueprints read-only). (3) Prove: skeleton first, then the cascade rfl/simp/omega/ring/linarith/nlinarith/positivity/exact?/grind/aesop per goal; search before hand-writing (lean_local_search, loogle); bounded repair ~3 attempts per error then step back. (4) [M]-hypotheses stay NAMED structure rows — never axioms, never discharged by fiat. (5) GATE: 'lake env lean ${u.file.replace('lean/', '')}' from ${REPO}/lean must pass; zero sorry in YOUR declarations (a genuinely stuck subgoal: leave sorry + '-- BLOCKED(${u.id}): <reason>' and report BLOCKED/PARTIAL honestly — an honest sorry beats a weakened statement). (6) Do NOT run git. (7) Keep total output <2000 chars.`,
      { label: `${BP}:${u.id}`, phase: 'Prove', schema: VERDICT_SCHEMA },
    ).then(v => ({ id: u.id, file: u.file, ...(v || { status: 'BLOCKED', note: 'agent died' }) }))
  ))
  const flat = wr.filter(Boolean)
  results.push({ wave: wave.name, units: flat })
  const proved = flat.filter(r => r.status === 'PROVED').length
  log(`${BP} ${wave.name}: ${proved}/${flat.length} proved`)

  const ck = await agent(
    `Wave checkpoint for ${BP} ${wave.name} (repo ${REPO}). Prover reports: ${JSON.stringify(flat.map(r => ({ id: r.id, file: r.file, status: r.status })))}. Do: (1) cd ${REPO}/lean && for each touched file run 'lake env lean <file>' (relative to lean/); if a file fails, apply MINIMAL repairs (imports, namespaces, syntax — never statement weakening); if unrepairable in ~3 attempts, comment the broken declaration out with '-- WAVE-QUARANTINE(${BP} ${wave.name}): <1-line reason>' so the file compiles (full decl preserved in the comment). (2) grep -rn 'sorry' lean/LeanUrat/Scaffold/ | wc -l — report the count. (3) Commit: cd ${REPO} && git add lean/LeanUrat/Scaffold lean/blueprints && git commit -m '${BP} ${wave.name}: <proved>/<total> units' (retry up to 5x on index.lock, sleep 2 between). Return <1500 chars: files green y/n, sorry count, quarantines, commit hash.`,
    { label: `${BP}:${wave.name}:ckpt`, phase: 'Checkpoint' },
  )
  results[results.length - 1].checkpoint = ck
}

const totals = results.flatMap(r => r.units)
return {
  bp: BP,
  waves: results.map(r => ({ wave: r.wave, proved: r.units.filter(u => u.status === 'PROVED').length, total: r.units.length, blocked: r.units.filter(u => u.status === 'BLOCKED').map(u => u.id) })),
  proved: totals.filter(u => u.status === 'PROVED').length,
  total: totals.length,
}
