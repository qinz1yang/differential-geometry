# Lane C2L: the two C2 leaves (H8 monotonicity, H9 local upper bound) written into the tree

2026-09-26. Worker in `D:\differential-geometry-pc3` (branch `codex/pc-target-c-psf`, HEAD e68bf6466).
Read-only compiles (direct `lean` with the lakefile options, as C2W's `sc.sh`), scratch modules
`C2l.*` under the session scratchpad `c2l/`, LEAN_PATH = `c2l/olean ; c2w/olean (C2W's five, as
C2w.*) ; h7f/olean (H7b's 17, as H7f.*) ; pc3 build`. No lake build, no git writes, root aggregate
and skeleton untouched. New files only.

## Start (12:50 PDT)

Read: pc3 AGENTS.md, OPUS_FILL_LOG_C2W.md, C2W's assembly probe `c2w/probe/Probe.lean`, the leaf
defs (`NoncollapsingThroughSurgeryLeaves.lean:96,101`, `P₀` only, no `g₀`), skeleton leaves
(`PoincareEndgame.lean:23,27`). Supplier scratch oleans checked current: H7b tree sources identical
to `h7f/src` (sed-renamed), C2W oleans newer than their tree sources.

Plan: `Surgery/Topology/HistoryReducedVolumeMonotone.lean` (H8 chain + `…_holds`),
`Surgery/Topology/HistoryReducedVolumeLocalUpperBound.lean` (H9 `…_holds`). Leaf theorem names
follow the tree precedent `smoothPoincareConjecture_holds` (the skeleton already owns the bare
lowerCamel names `historyReducedVolumeMonotone` / `historyReducedVolumeLocalUpperBound` in the same
namespace).

## Progress 1 (13:05 PDT) — both leaves proved in the tree; DONE

Files (new, untracked):
- `Surgery/Topology/HistoryReducedVolumeMonotone.lean` (202 lines): H8 chain
  `ObservedHistory.lintegral_image_historyMinDomain_le_of_lt`,
  `RetainedCoreHistory.reducedVolume_le_of_lt_of_mem_Ico`, and
  `historyReducedVolumeMonotone_holds (P₀) : HistoryReducedVolumeMonotone P₀`.
  Imports: HistoryLGeometry.{JacobianComparison, SeamBase, ExponentialClosedStart,
  MinDomainMeasurable}, HistoryScalarFloor, HistoryHorizonExtension,
  Parametric.{AreaInequality, InjectiveAreaInequality}.
- `Surgery/Topology/HistoryReducedVolumeLocalUpperBound.lean` (98 lines):
  `historyReducedVolumeLocalUpperBound_holds (P₀) : HistoryReducedVolumeLocalUpperBound P₀`.
  Imports: HistoryLGeometry.{ReducedVolumeTail, SeamBase, CoreIntegralBound}, HistoryScalarFloor,
  HistoryHorizonExtension, Perelman.LGeometry.Jacobian.MetricGaussianTail.
Both carry the file-local `borel` instances on stage carriers and `ThreeSpace` (as G7/TailG/C9/T9).
Statements are the leaf `def`s themselves (`P₀` only).

Deltas against C2W's probe (all in my files): the probe's two call-site edits (H7b+ without `hT`,
`mem_Icc_zero_horizon_of_mem_stageDomain`) kept; added the `AreaInequality` import (the probe got
G7 transitively through `ReducedVolumeTail`); dropped the probe's redundant
`open DifferentialGeometry.Geometry.Curvature in` (selective `open … (metricScalarAt)` suffices);
one >100-char line in H9 rewritten as
`RetainedCoreHistory.exists_reducedVolume_eq_lintegral_image_historyMinDomain_of_mem_Ico (H.extendHorizon …)`.
No mathematical change.

Checks (scratch `C2l.*`, lakefile options, `-Dweak.linter.mathlibStandardSet=true`):
- Compile: both files 0 errors, 0 warnings, 0 info.
- `#lint` on scratch copies: all passed (7 + 5 declarations).
- Axioms (scratch probe `c2l/probe/Axioms.lean`, never in the tree): `historyReducedVolumeMonotone_holds`,
  `historyReducedVolumeLocalUpperBound_holds`, `reducedVolume_le_of_lt_of_mem_Ico`,
  `lintegral_image_historyMinDomain_le_of_lt`: all `[propext, Classical.choice, Quot.sound]`.
- Skeleton edit probe (`c2l/probe/Leaves.lean`: the two skeleton theorems with the edit text
  below, importing both modules): compiles clean.
- Public names grepped library-wide: no clash. No comments/docstrings, no sorry/axiom/nolint/
  set_option beyond `autoImplicit false`; only import lines exceed 100 characters.

Skeleton edit (`Surgery/Skeleton/PoincareEndgame.lean`, acceptance lane): add
```
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryReducedVolumeMonotone
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryReducedVolumeLocalUpperBound
```
and replace the two leaves by
```
theorem historyReducedVolumeMonotone (P₀ : OrientedThreeStage.{u}) :
    HistoryReducedVolumeMonotone P₀ :=
  historyReducedVolumeMonotone_holds P₀

theorem historyReducedVolumeLocalUpperBound (P₀ : OrientedThreeStage.{u}) :
    HistoryReducedVolumeLocalUpperBound P₀ :=
  historyReducedVolumeLocalUpperBound_holds P₀
```

Root-aggregate registration order (24 modules, prefix
`DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.`):
H7b (17): HistoryLGeometry.AntitoneOffFinite, .FamilyChain, .FamilyChainSections, .AdaptedFieldIcc,
.FamilyChainJacobi, .FamilyChainTrace, .FamilyChainGram, .FamilyChainClosure, .FamilyChainCover,
.FamilyChainExists, .FamilyChainConjugate, .ActionSplit, .JacobianAlong, .JacobianDerivative,
.JacobianSeam, .JacobianEndpoint, .JacobianMonotone;
C2W (5): HistoryLGeometry.JacobianClosedStart, .JacobianComparison, .SeamBaseJacobian,
.JacobianGaussian, .ReducedVolumeTail;
C2L (2): HistoryReducedVolumeMonotone, HistoryReducedVolumeLocalUpperBound.
