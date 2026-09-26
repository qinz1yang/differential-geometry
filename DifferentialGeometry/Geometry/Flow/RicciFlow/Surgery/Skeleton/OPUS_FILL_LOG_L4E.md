# L4e / L6e fill log (endpoint forms of L4 and L6)

## 2026-09-26 entry 1 (start)

Read: AGENTS.md, NAMING.md §2–6, logs C3B (failure 1: endpoint form), L6, L4; L4
(`WindowedWitnessPerturbation.lean`), L2/L3, `FiniteHornGeometry.lean` (witness fields), L6.

Finding: `WindowedModelWitness` needs only `time_mem : t ∈ D.carrier` and
`window_mem : Icc … t ⊆ D.carrier`; no regularity at the witness time. In L4 the regularity is
used only through the slab `(a, c, b)` of `exists_common_source_slab` (`a < c < t − w < t < b`,
`Icc a b ⊆ carrier`, `Ioo a b ⊆ regular`). Every slab consumer
(`exists_closedWindow_pullback_metric_time_tower`, `exists_closedWindow_metric_time_fields`,
`partial_pullback_time_tower_contDiffOn_closed`, `uniform_pullback_time_tower_chart_jets_…`)
takes `a < c < b` with closed `Icc c b` jets, and `t < b` is only used as `t ≤ b`. So the slab
may end AT `t` (`b := t`): no open time neighbourhood of `t` is needed. No obstruction expected.
L6 is committed (950618ee3) and its olean is newer than the source, so in-place
`lake env lean` compiles are possible (no scratch module needed).

## 2026-09-26 entry 2 (delivered; both bricks proved, no obstruction)

Files (new, not registered in the root aggregate, nothing else edited, no git writes, no
`lake build`):
- `Perelman/CanonicalNeighborhood/WindowedWitnessEndpointPerturbation.lean` (321 lines, one
  public theorem). Imports only `WindowedWitnessPerturbation`.
- `Perelman/StandardSolution/StandardClosenessEndpointWitness.lean` (809 lines, one public
  theorem). Imports L6's imports with `WindowedWitnessPerturbation` replaced by the L4e file;
  it does NOT import L6.

L4e, `WindowedModelWitness.eventually_strict_of_tendsto_flows_endpoint`: L4's statement with
`hwindow : Icc (t − w) t ⊆ D.regular` replaced by a slab closed AT the witness time,
`{t₀} (ha : t₀ < t − (eps·R₀)⁻¹) (hslab : Icc t₀ t ⊆ D.carrier) (hreg : Ioo t₀ t ⊆ D.regular)`,
`hconv` required only for `τ ∈ Icc t₀ t`; conclusion = L4's minus the (now meaningless)
`window ⊆ D.regular` conjunct (the witness's own `window_mem ⊆ D.carrier` is inside `W'`).
For `D = closed a b` with `t = b` this is exactly the endpoint case (`Ioo t₀ b ⊆ Ioo a b`).
Proof = L4's proof with the slab `(t₀, c, t)`, `c` from `exists_between ha`, in place of
`exists_common_source_slab`'s `(a, c, b)` with `t < b`. Why it works: every slab consumer
(`exists_closedWindow_metric_time_fields`, `exists_closedWindow_pullback_metric_time_tower`,
`partial_pullback_time_tower_contDiffOn_closed`, `uniform_pullback_time_tower_chart_jets_…`,
hence `uniform_ordinary_metric_jets_of_metric_convergence_on_closed_interval`) already works
with one-sided `derivWithin (Icc c b)` jets on the closed slab and needs only `Icc a b ⊆
carrier`, `Ioo a b ⊆ regular`; L4 used `t < b` only as `t ≤ b`. No helper needed an open time
neighbourhood of `t`. Duplication: the proof body is a near-verbatim copy of L4's
(`WindowedWitnessPerturbation.lean:764–1057`); L4 is the corollary (its `hwindow` gives the
slab via `exists_common_source_slab` restricted to `[a, t]`), so on acceptance L4 can be
re-proved from L4e and the copy dropped.

L6e, `exists_uniform_orientedWitness_of_standard_close_endpoint`: statement is C3B entry 2's
quoted form verbatim (`∀ (Θ r : ℝ), Θ < 1 →`, `S` on `closed 0 T hT`, closeness on `Icc 0 T`,
witness at `T`). Proof = L6's contradiction argument with `T' = T`: common interval
`closed (−b) 0` (`b = 2/(δR∞)`), witness time `0` = its right endpoint, L4e with
`t₀ = −b` (`−b < −1/(δR∞)`), slab/regular inclusions by `fun _ h => h`; L5 is called with
`T n` itself (`J = Icc (T₀ − b) T₀`).
Duplicates (private, same names as in L6, module-private so no clash): all of L6's sections
`Orientation`, `WitnessGeometry`, `StandardAge`, `WindowConvergence`, `StandardImage` and the
first four helpers of `Core` (L6 lines 31–433), copied verbatim; the two core helpers are copies
with `_endpoint` suffixes. `open private … from <L6>` was tried and works, but the module name
line is 105 characters (longLine warning), so the helpers were copied instead. On acceptance:
L6 (margin form, `μ > 0`) is the special case of running this proof with `0 ≤ μ`; the cleanest
dedup is to generalize L6's two core helpers to `0 ≤ μ` via L4e and derive both public forms.

Compile: L4e in place, `LEAN_NUM_THREADS=2 lake env lean -DmaxSynthPendingDepth=3
-Dweak.linter.mathlibStandardSet=true` → no output. L6e: scratch module pattern (C3B), dir
`scratchpad/l4e`: L4e copied as `L4eScratch.Perturbation` and compiled with `-o`; L6e copy whose
only difference is that import line (checked with `diff`) compiled against it (explicit toolchain
binary `~/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean`, since plain `lean` outside the
repo picks another toolchain) → no output. `#print axioms` (scratch copies), both public theorems:
`propext`, `Classical.choice`, `Quot.sound`. `#lint` (14 linters): L4e 0 errors, L6e 0 errors.
Lines ≤ 100 except imports, no comments, no sorry, no option overrides. Names grep-unique.
