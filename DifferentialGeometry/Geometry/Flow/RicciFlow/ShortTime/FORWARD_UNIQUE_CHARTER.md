# FORWARD-UNIQUENESS session charter (written 2026-07-24 by the (N)-lane planner)

For the NEW Fable planner session taking `ricci_flow_forward_unique`.  This
charter is the coordination contract between the two planner sessions
sharing branch `codex/analytic-producers-e87b` and this machine.  Read this
FIRST, then `CLAUDE.md`/`important_lesson.md`/`lessons.md`, then build your
own plan file (see §5).

## 1. Target

`DifferentialGeometry/Geometry/Flow/RicciFlow/Evolution/ExtendViaUniqueness.lean`
holds exactly TWO `sorry`s:
- `:92` — `ricci_flow_unif_existence` (black box (N), uniform existence).
  OWNED BY THE (N) SESSION.  Do not touch.
- `:201` — the forward-uniqueness theorem (two flows `g₁ g₂` on `Ico a b`,
  chart-Gram interior-C∞ + C⁰-to-the-left regularity packages, both
  satisfying the RF PDE `HasDerivWithinAt (fun s => (g s).inner x v w)
  (−2·ricciTensor …) (Ici a) t`, with `g₁ a = g₂ a` ⟹ `g₁ t = g₂ t` on
  `Ico a b`).  YOUR TARGET.

Honest accounting rule (house standard): the theorem is 0% until its exact
`sorry` is gone; machinery is reported separately.

## 2. Known assets (verify before trusting — see §4 false-green rule)

- VERIFIED (lake-green + axiom-audited, committed):
  - `Analysis/Parabolic/QuasiLinear/TensorMaximalRegularity/TameNemytskii.lean`
    — abstract two-orientation tame `timeL2` contraction (ruling item 4).
  - `Analysis/Parabolic/QuasiLinear/TensorMaximalRegularity/LowScaleCutoff.lean`
    — `H^{a+1}`-controlled cutoff (ruling item 3).
  - `Analysis/Parabolic/TimeSobolev/TimeH1Modulus.lean` — √t modulus.
  - `Analysis/Spectral/Intrinsic/HeatSemigroup/MaxRegSolutionJointlySmooth.lean`
    — incl. the NEW fixed-horizon representative
    `maxreg_solution_jointly_smooth_representative_of_tame_nemytskii`.
  - `Analysis/Spectral/Intrinsic/DeTurck/StrongSolutionUniqueness.lean` —
    EXISTS; audit its exact statement early: if it is the per-datum
    Ricci–DeTurck strong-solution uniqueness, it is your PDE-side core.
- UNVERIFIED 07-19 Codex drafts (same dir as TameNemytskii; their own
  `.md`s admit "no focused elaboration was run"; the false-green family):
  `TimeLocalNemytskii.lean`, `TimeTameFixedPoint.lean` (742 lines; the
  time-dependent tame fixed point, `(r,s)`-generic — built with the
  vector-field HMF coordinate equation `(r,s)=(1,0)` in mind),
  `MovingMass.lean`, `RadialMixedBound.lean`.  Real `lake build` them
  before consuming anything.
- MISSING (per `TimeTameFixedPoint.md`): the geometric tension-field
  producer needed to instantiate the HMF nonlinearity.  Expect this to be
  a genuine build.
- Context notes mentioning `ricci_flow_forward_unique`: the Koch–Lamm
  Euclidean lane (`Analysis/Parabolic/Euclidean/KochLamm*.md`), the DeTurck
  `Edge*` notes, `Pullback/ConnAdd*.md` — Codex-lane material, read as
  reference only.

## 3. Route guidance (plan, do not assume)

The classical closed-M route: gauge both flows by DeTurck (solve the
harmonic-map heat flow to a fixed background to build the gauges, or use
the DeTurck vector-field trick directly), apply strictly-parabolic
uniqueness (energy/Gronwall or the maximal-regularity contraction) to the
gauged flows, then transfer back through the gauge ODE.  Per house
protocol: recon the codebase's actual interfaces FIRST, and if the route
choice is genuinely open (e.g. HMF-gauge vs direct DeTurck-uniqueness +
ODE-gauge-back), run the GPT Pro consult protocol (see `CLAUDE.md` §Pro
consultation; precedent: `UNIF_N_PRO_PROMPT.md`/`UNIF_N_PRO_RULING.md`)
BEFORE heavy building.

## 4. Coordination rules (BINDING for your session and its executors)

- Branch: `codex/analytic-producers-e87b`, worktree
  `C:\Users\liao9\.codex\worktrees\e87b\testdifferential-geometry`.
  BuildDir is branch-local `C:/dgb2/e87b` (lakefile.toml; Windows MAX_PATH
  fix — do NOT revert or bypass it).
- Machine sharing: before EVERY lean/lake invocation run
  `tasklist //FI "IMAGENAME eq lean.exe"`; if a foreign lean.exe is alive,
  wait-poll 60–90 s with printed markers; NEVER kill foreign processes;
  one Lean process per executor; `LEAN_NUM_THREADS=4`.  The (N) session
  runs up to ~3 executor lanes concurrently; expect contention.
- Full builds: use `lake build DifferentialGeometry` (the library target;
  the bare default also regenerates DeclIndex).  Never `lake clean` /
  `lake update`.
- Verification standard: `lake env lean` exit-0 is NOT trustworthy (both
  false-green AND false-fail observed); authoritative = `lake build
  +Module`; every new public theorem gets `#print axioms` = exactly
  `[propext, Classical.choice, Quot.sound]` via direct lean with
  LEAN_PATH = `C:/dgb2/e87b/lib/lean` + each
  `.lake/packages/<p>/.lake/build/lib/lean` (p in mathlib batteries aesop
  Qq importGraph proofwidgets plausible LeanSearchClient Cli); strip audit
  lines after green.  Documented frontier `sorry`s keep their `sorryAx`
  marker deliberately.
- Instance-layer lessons (will save you days): `set_option
  backward.isDefEq.respectTransparency false` for `Tensor0SModel`
  NormedSpace synthesis (`Agreement/Nabla0SFunAgreement.md`);
  `synthInstance.maxHeartbeats` bumps for RiemannianBundle→Norm;
  a bundle-layer TotalSpace-topology dedup (GPT Pro ruling
  `UNIF_DIAMOND_PRO_RULING.md`) is IN FLIGHT — if your lanes hit
  `ContMDiffSection.ext` FiberBundle-synthesis failures in minimal-import
  files, coordinate with the (N) session instead of patching.
- File ownership: the (N) session owns `ShortTime/UNIF_*`, the
  `TensorHilbert` constituent files, `SobolevScale/UnifBochnerGap.*`,
  `HCGCompactness/Unif*`/`MetricCovDeriv*`, `LieCorr0*`, and sorry `:92`.
  YOU own sorry `:201`, your new plan/notes, and the files your plan
  claims (list them in your plan file §ownership as you go).  The shared
  `ExtendViaUniqueness.lean` is edited ONLY to discharge your own sorry,
  at endgame, with a `git status` check for the other session's in-flight
  state first.  The four 07-19 drafts (§2) are YOURS to verify/repair.
- Commits: your planner commits only your scope; executors never commit;
  never sweep unrelated dirty files (the user sometimes makes manual
  sweep commits — tolerated, but do not rely on them).  Commit messages
  end with the Claude co-author trailer.
- Plans: create `ShortTime/FORWARD_UNIQUE_PLAN.md` as your running source
  of truth (acceptances, status log, executor constraints — mirror the
  structure of `UNIF_EXISTENCE_PLAN.md`).  Do not edit
  `UNIF_EXISTENCE_PLAN.md`.
- Executor pattern (house standard, works): Opus executors in background,
  recon-first sessions, batch edits before ~15-min whole-file checks,
  foreground waits only (detached waiters do NOT survive session stops),
  stop-and-propose on scope/home questions, verified-boundary stops,
  planner acceptance loop with spot-checks (grep sorry/audit lines,
  diff-scope, discipline) before each commit.

## 5. Suggested first moves

1. Read `ExtendViaUniqueness.lean` whole (it is small): both sorries'
   exact statements + the Brick U consumer, so your uniqueness statement's
   regularity package matches what the consumer feeds.
2. Audit `StrongSolutionUniqueness.lean` (statement + verified status).
3. Real-`lake build` the four 07-19 drafts; repair per the №20-style
   guardrail (hygiene mechanical fixes fine; statement changes or genuine
   proof failures → planner decision).
4. Recon the gauge side: what exists for harmonic-map heat flow / DeTurck
   vector field ODE / pullback of flows (`Pullback/` tree,
   `solWindowData_pullback`, `isSolutionOn_pullback` are committed
   producers from earlier phases).
5. Then the route decision (§3), likely via a Pro consult, then brick
   dispatches.
