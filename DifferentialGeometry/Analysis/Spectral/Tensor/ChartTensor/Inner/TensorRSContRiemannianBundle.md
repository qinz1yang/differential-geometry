# TensorRSContRiemannianBundle

## TensorRS TotalSpace topology-instance diamond dedup (GPT Pro ruling, 2026-07-24)

Spec: `Geometry/Flow/RicciFlow/ShortTime/UNIF_DIAMOND_PRO_RULING.md`.
Root problem: the `(r,s)`-tensor bundle had TWO registered total-space
`TopologicalSpace` instances (a canonical one in `RSTensor/Defs`, and a
redundant eta-contracted alias here), plus the higher-layer `FiberBundle` /
`VectorBundle` aliases here. Downstream `FiberBundle`-typed spellings froze the
selected topology, so `.ext`/section synthesis in `LieCorr0Split`/`LieCorr0LowJet`
could not unify. Fix = keep ONE canonical total-space instance; demote the
higher-layer aliases to plain `def`s.

### Edit B applied (this file)
Changed EXACTLY three declarations from `instance` to `def` (names, types,
bodies unchanged; they live inside the file's `noncomputable section`, so no
`noncomputable` keyword needed):

- `tensorRSSpace_totalSpace_topologicalSpace` (was the redundant total-space
  topology alias -> `Tensor0SBundle.tensorRSBundle_topology`)
- `tensorRSSpace_fiberBundle`
- `tensorRSSpace_vectorBundle`

`tensorRS_isContinuousRiemannianBundle` stays a registered `instance` (it is the
intended continuous-Riemannian-bundle endpoint of this file).

These three names are referenced only in `.md`/plan notes, never as explicit
terms in `.lean` code, so demotion changes instance resolution only — no term
reference breaks.

### Edit A (in `Tensor/RSTensor/Defs.lean`)
`tensorRSBundle_fiber` hardened: its trailing inferred pointwise fiber-topology
family `_` (the `[∀ b, TopologicalSpace (E b)]` slot of `@FiberBundle`) is now
the explicit canonical family `fun x : M => tensorRSSpace_topologicalSpace r s x`.
The five canonical `Defs` instances are retained. See `RSTensor/Defs.md`.

### Edit C (type-based audit) — no additional demotion
Grep for every declaration whose RESULT type is
`TopologicalSpace (Bundle.TotalSpace (TensorRSModel …) …)` across
`DifferentialGeometry/`. Only two global declarations exist:
`Tensor0SBundle.tensorRSBundle_topology` (canonical, kept) and the
`tensorRSSpace_totalSpace_topologicalSpace` alias (demoted by Edit B). Every
other hit is a proof-local `letI :` pin (not a global alias). No additional
global FiberBundle/VectorBundle alias for the TensorRS bundle exists outside
this file. So Edit C found nothing further to demote.

## Verification

- Phase 1 minimal-import probe (`RSTensor/Defs` only): `#synth` of the TotalSpace
  `TopologicalSpace` / `FiberBundle` / `VectorBundle` resolves to the CANONICAL
  `tensorRSBundle_topology` / `_fiber` / `_vector` in BOTH eta spellings
  (`fun x => TensorRSSpace …` and `TensorRSSpace … (M := M)`); both
  `inferInstance = tensorRSBundle_topology 2 2` rfl checks pass. Stop signal 1
  cleared.
- LESSON (probe hygiene): a bare `#synth NormedSpace ℝ (TensorRSModel r s ℝ E)`
  (hence `#synth VectorBundle …`) FAILS unless the probe sets
  `set_option backward.isDefEq.respectTransparency false` — the same file-local
  option `Defs.lean` uses. This is a model-fiber-normed defeq-transparency
  matter, ORTHOGONAL to the total-space topology dedup and independent of these
  edits. With the option set, the minimal probe is fully green.
- Phase 1b rich probe (imports this file, wrappers demoted): AGREES with the
  minimal probe — synthesis resolves to the CANONICAL `tensorRSBundle_topology`
  / `_fiber` / `_vector` in both eta spellings, both rfl checks pass. The
  demoted wrappers are invisible to synthesis. Stop signals 2/3/4/6 cleared.
- Phase 2b: `lake build +Defs +…TensorRSContRiemannianBundle` GREEN (2743 jobs)
  — the whole Defs→Riemannian cone, incl. Edit B, compiles.
- Phase 4 regression: `lake build +DeTurckLieKernelL2JetBound
  +OperatorFieldFibreNormJet +IteratedCovGradFibreNormPermutationInvariance
  +TensorRSRiemannianBundle` GREEN (9388 jobs). Dedup is REGRESSION-FREE across
  the rich-import consumer cone.
- Phase 3: `+LieCorr0Split` GREEN (needs an extra mechanical `set_option
  backward.isDefEq.respectTransparency false` in the consumer; see
  `LieCorr0Split.md`). `+LieCorr0LowJet` still RED but only on PRE-EXISTING deep
  WIP (syntax errors, sorries, missing imports, proof failures) — its bundle
  synthesis is fixed; see `LieCorr0LowJet.md`.
- Phase 5 `lake build DifferentialGeometry`: cannot be fully green because the
  library has scattered pre-existing WIP modules (e.g.
  `Geometry/Metric/TensorInner/CoerciveBilinInverse.lean` fails on
  `FiniteDimensional ℝ (StrongDual ℝ E)` synth + a cross-file `private
  gramCLM_isUnit` reference — UNRELATED to the topology dedup; and LowJet).
  In Phase 5's built portion, CoerciveBilinInverse was the ONLY module with real
  `error:` lines; no FiberBundle/topology synth failure appears anywhere. So the
  dedup introduces NO regression; remaining reds are pre-existing WIP.

Probe files: scratchpad `ProbeMinimal.lean` / `ProbeRich.lean` / `ProbeLieCtx.lean`.
