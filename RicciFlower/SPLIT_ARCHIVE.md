# RicciFlower Split Archive

This file records large-file splits and warning-cleanup status.

## 2026-05-23 Analysis/Volume/Family

- Split `RicciFlower.Analysis.Volume.Family` into `Family.Base` and `Family.Variation`.
- Kept `Family.lean` as a compatibility umbrella importing both modules.
- Line counts after split: umbrella 14, `Family.Base` 1383, `Family.Variation` 1350.
- Verification status: focused checks passed for both new modules and the umbrella; targeted builds passed for `Family.Base`, `Family.Variation`, and `Family`.
- Warning status: no warnings were emitted by the checked split modules in this pass.

## 2026-05-23 GlobalGeometry/Lecture07/SurfaceCalculus

- Split `RicciFlower.GlobalGeometry.Lecture07.SurfaceCalculus` into `SurfaceCalculus.Base` and `SurfaceCalculus.MixedFields`.
- Kept `SurfaceCalculus.lean` as a compatibility umbrella importing both modules.
- Line counts after split: umbrella 10, `SurfaceCalculus.Base` 1570, `SurfaceCalculus.MixedFields` 600.
- Verification status: focused checks passed for both new modules and the umbrella; targeted build passed for `SurfaceCalculus.Base`.
- Warning status: local warnings in `SurfaceCalculus.Base` were cleared; warnings replayed from `PullbackConnection` and older dependencies are left for their owning batches.

## 2026-05-23 GlobalGeometry/Lecture07/PullbackConnection

- Split `RicciFlower.GlobalGeometry.Lecture07.PullbackConnection` into `PullbackConnection.Base`, `PullbackConnection.Frame`, and `PullbackConnection.Curves`.
- Kept `PullbackConnection.lean` as a compatibility umbrella importing all three modules.
- Line counts after split: umbrella 9, `PullbackConnection.Base` 185, `PullbackConnection.Frame` 1019, `PullbackConnection.Curves` 1261.
- Verification status: focused checks passed for all three new modules and the umbrella; targeted builds passed for `PullbackConnection.Base`, `PullbackConnection.Frame`, `PullbackConnection.Curves`, and the umbrella.
- Warning status: local `PullbackConnection` warnings were cleared by removing unused public `DecidableEq` hypotheses and replacing the flexible frame-sum `simp` with directed rewrites; the remaining replayed warning is from `VectorBundle/LocalFrameRegularity.lean`.

## 2026-05-23 Riemann/Basic

- Split `RicciFlower.Riemann.Basic` into `Basic.Field`, `Basic.Pointwise`, and `Basic.Sections`.
- Kept `Basic.lean` as a compatibility umbrella importing all three modules.
- Line counts after split: umbrella 9, `Basic.Field` 976, `Basic.Pointwise` 671, `Basic.Sections` 632.
- Verification status: focused checks passed for all three new modules and the umbrella; targeted builds passed for `Basic.Field`, `Basic.Pointwise`, `Basic.Sections`, and the umbrella.
- Warning status: no local warnings were emitted by the split modules in this pass.
- API note: the tangent-constant helper family in `Basic.Field` was made non-private because the pointwise/smooth modules need those exact helpers across the new module boundary and `tangentConstAt` already appears in existing public theorem statements.

## 2026-05-23 Coordinates/MetricCompatibility

- Split `RicciFlower.Coordinates.MetricCompatibility` into `MetricCompatibility.Inverse`, `MetricCompatibility.Covariant`, and `MetricCompatibility.Coordinate`.
- Kept `MetricCompatibility.lean` as a compatibility umbrella importing all three modules.
- Line counts after split: umbrella 9, `MetricCompatibility.Inverse` 723, `MetricCompatibility.Covariant` 1081, `MetricCompatibility.Coordinate` 426.
- Verification status: focused checks passed for all three new modules and the umbrella; targeted builds passed for `MetricCompatibility.Inverse`, `MetricCompatibility.Covariant`, `MetricCompatibility.Coordinate`, and the umbrella.
- Warning status: no local warnings were emitted by the split modules; builds replayed the pre-existing `Operators.lean` flexible-simp warning.
- API note: `inverseMetric_derivative_solve` was made non-private because the final coordinate wrapper consumes the algebraic derivative solver across the new module boundary.

## 2026-05-23 Coordinates/Normal

- Split `RicciFlower.Coordinates.Normal` into `Normal.Base`, `Normal.Spray`, `Normal.Flow`, `Normal.Existence`, and `Normal.Data`.
- Kept `Normal.lean` as a compatibility umbrella importing all five modules.
- Line counts after split: umbrella 11, `Normal.Base` 307, `Normal.Spray` 1025, `Normal.Flow` 1202, `Normal.Existence` 801, `Normal.Data` 669.
- Verification status: focused checks passed for all five new modules and the umbrella; targeted builds passed for `Normal.Base`, `Normal.Spray`, `Normal.Flow`, `Normal.Existence`, `Normal.Data`, and the umbrella.
- Warning status: local flexible-simp/style warnings introduced by the split were cleared; `Normal.Data` retains the pre-existing `expAt_localDiffeomorph` `sorry` frontier, moved from the old file line 3786 to `Normal/Data.lean`.
- API note: private helpers in the spray/flow proof stack were made non-private in the new lower modules because later split modules consume the same ODE/Picard estimates across module boundaries.

## 2026-05-23 Tensor/RSTensor/Tensor0SRiemannian

- Split `RicciFlower.Tensor.RSTensor.Tensor0SRiemannian` into `Tensor0SRiemannian.Basic`, `Tensor0SRiemannian.Coordinate`, `Tensor0SRiemannian.Product`, and `Tensor0SRiemannian.Smooth`.
- Kept `Tensor0SRiemannian.lean` as a compatibility umbrella importing all four modules.
- Line counts after split: umbrella 10, `Tensor0SRiemannian.Basic` 509, `Tensor0SRiemannian.Coordinate` 1029, `Tensor0SRiemannian.Product` 1003, `Tensor0SRiemannian.Smooth` 1276.
- Verification status: focused checks passed for all four new modules and the umbrella; targeted builds passed for `Tensor0SRiemannian.Basic`, `Tensor0SRiemannian.Coordinate`, `Tensor0SRiemannian.Product`, `Tensor0SRiemannian.Smooth`, and the umbrella.
- Warning status: no local warnings were emitted by the split modules; builds replayed the pre-existing `Operators.lean` flexible-simp warning.
- API note: helper lemmas in lower coordinate/product modules were made non-private where later split modules consume the same finite-sum algebra across module boundaries.

## 2026-05-23 RicciFlow/Evolution/Metric

- Split `RicciFlower.RicciFlow.Evolution.Metric` into `Metric.Basic`, `Metric.InverseSmooth`, `Metric.Covariant`, and `Metric.Evolution`.
- Kept `Metric.lean` as a compatibility umbrella importing all four modules.
- Line counts after split: umbrella 10, `Metric.Basic` 260, `Metric.InverseSmooth` 807, `Metric.Covariant` 961, `Metric.Evolution` 300.
- Verification status: focused checks passed for all four new modules and the umbrella; targeted builds passed for `Metric.Basic`, `Metric.InverseSmooth`, `Metric.Covariant`, `Metric.Evolution`, and the umbrella.
- Warning status: split-local warnings are limited to intentional deprecation warnings in `Metric.Basic` and `Metric.InverseSmooth`, where compatibility wrappers still mention the deprecated global inverse-component predicates.  The umbrella build replayed older warnings from lower dependencies and from the still-unsplit `RicciFlow.Basic`.
- API note: inverse-smoothness helper definitions and `inverseMetric_derivative_row_eq` were made non-private because the split covariant/evolution modules consume them across the new module boundary.

## 2026-05-23 RicciFlow/Basic

- Split `RicciFlower.RicciFlow.Basic` into `Basic.Core`, `Basic.Components`, and `Basic.RicciNorm`.
- Kept `Basic.lean` as a compatibility umbrella importing all three modules.
- Line counts after split: umbrella 11, `Basic.Core` 1014, `Basic.Components` 1563, `Basic.RicciNorm` 549.
- Verification status: focused checks passed for all three new modules and the umbrella; targeted builds passed for `Basic.Core`, `Basic.Components`, `Basic.RicciNorm`, and the umbrella.
- Warning status: local `RicciFlow.Basic` warnings were cleared by replacing the old flexible `ricciNormSq_basis` simp with a directed `simp only` and by rewriting two unnecessary time-shift `simpa` proofs.  The umbrella build still replays older warnings from lower dependency modules.
- API note: no public theorem or definition names were renamed.  The split adds only module-level import paths and keeps the original `RicciFlow.Basic` import surface intact.

## 2026-05-23 RicciFlow/Evolution/Ricci

- Split `RicciFlower.RicciFlow.Evolution.Ricci` into `Ricci.Trace`, `Ricci.GammaAlgebra`, `Ricci.GammaCoord`, `Ricci.Bianchi`, `Ricci.Commutator`, `Ricci.CoordinateRegularity`, `Ricci.CoordinateIdentities`, and `Ricci.Lichnerowicz`.
- Kept `Ricci.lean` as a compatibility umbrella importing all eight modules.
- Line counts after split: umbrella 16, `Ricci.Trace` 460, `Ricci.GammaAlgebra` 972, `Ricci.GammaCoord` 949, `Ricci.Bianchi` 701, `Ricci.Commutator` 1280, `Ricci.CoordinateRegularity` 1333, `Ricci.CoordinateIdentities` 989, `Ricci.Lichnerowicz` 773.
- Verification status: focused checks passed for all eight new modules and the umbrella; targeted builds passed for each new module and the umbrella.
- Warning status: local unused-variable warnings in `Ricci.CoordinateIdentities` were cleared.  Remaining split-local warnings are deprecated compatibility-route uses in `Ricci.Commutator` and `Ricci.Lichnerowicz`; these are retained for a future local/pointwise-frame migration rather than changed during the large-file split.
- API note: a small set of former private helper lemmas was made non-private where the new module boundary requires reuse, mostly inverse-basis and gamma trace algebra helpers.  Public theorem and definition names were otherwise preserved.

## 2026-05-23 RicciFlow/Evolution/ImprovedPinching

- Split `RicciFlower.RicciFlow.Evolution.ImprovedPinching` into `ImprovedPinching.Definitions`, `ImprovedPinching.TfHeatCore`, `ImprovedPinching.Quotient`, `ImprovedPinching.HamiltonRHS`, `ImprovedPinching.TfHeatAssembly`, `ImprovedPinching.BookData`, and `ImprovedPinching.Wrappers`.
- Kept `ImprovedPinching.lean` as a compatibility umbrella importing all seven modules.
- Line counts after split: umbrella 16, `Definitions` 1625, `TfHeatCore` 271, `Quotient` 622, `HamiltonRHS` 1029, `TfHeatAssembly` 1374, `BookData` 913, `Wrappers` 286.
- Verification status: focused checks passed for all seven new modules and the umbrella; targeted builds passed for each new module and the umbrella.
- Warning status: proof-local warnings that were safely mechanical were cleared.  Remaining split-local warnings are unused public instance hypotheses in `Definitions` and one non-mechanical flexible `simp` in `HamiltonRHS`; both are retained to avoid changing the public call surface or opening a separate algebra cleanup frontier during the split.
- API note: `scalar_eq_diag` was made non-private because the split assembly module consumes it across the new module boundary.  Public theorem and definition names were otherwise preserved.

## 2026-05-23 MaximumPrinciple/TensorWeak

- Split `RicciFlower.MaximumPrinciple.TensorWeak` into `TensorWeak.Basic`, `TensorWeak.BarrierCore`, `TensorWeak.FirstNull`, `TensorWeak.Compactness`, `TensorWeak.Limit`, `TensorWeak.Certification`, and `TensorWeak.Final`.
- Kept `TensorWeak.lean` as a compatibility umbrella importing all seven modules.
- Line counts after split: umbrella 16, `Basic` 687, `BarrierCore` 626, `FirstNull` 1542, `Compactness` 1315, `Limit` 846, `Certification` 436, `Final` 417.
- Verification status: focused checks passed for all seven new modules and the umbrella; targeted builds passed for each new module and the umbrella.
- Warning status: no split-local warnings were emitted.  The umbrella build replayed older warnings from lower dependencies including `Operators`, `RoughLaplacian`, `Tensor.RSTensor.Metric`, and `VectorBundle.LocalFrameRegularity`.
- API note: a small set of former private helpers was made non-private because later split modules consume the same section-evaluation, repeated-slot, time-slab continuity, first-null kernel, Hessian-slot, and barrier-limit closure bridges across module boundaries.  Public theorem and definition names were otherwise preserved.

## 2026-05-23 RicciFlow/Perelman/F

- Split `RicciFlower.RicciFlow.Perelman.F` into `F.Functional`, `F.Geometry`, `F.Formula510Core`, `F.GeometryFormulaCore`, `F.TraceAlgebra`, `F.ChartTrace`, `F.ConnectionTrace`, `F.Producer`, and `F.Final`.
- Kept `F.lean` as a compatibility umbrella importing all nine modules.
- Line counts after split: umbrella 17, `Functional` 201, `Geometry` 844, `Formula510Core` 526, `GeometryFormulaCore` 839, `TraceAlgebra` 652, `ChartTrace` 403, `ConnectionTrace` 920, `Producer` 748, `Final` 83.
- Verification status: focused checks passed for all nine new modules and the umbrella; targeted builds passed for each new module and the umbrella.
- Warning status: no split-local warnings were emitted.  The umbrella build replayed older warnings from lower dependencies, including the dirty divergence-theorem files that were intentionally not edited in this pass.
- API note: `GeometryFormula510` is reopened in several modules so its Borel instances remain local; `rawDivTraceAlg` and `traceNablaAlg` were made non-private because the connection-trace module consumes them across the new module boundary.  Public theorem and definition names were otherwise preserved.

## 2026-05-23 LeviCivita/Variation

- Split `RicciFlower.LeviCivita.Variation` into `Variation.Connection`, `Variation.RicciCoord`, and `Variation.ScalarHessian`.
- Kept `Variation.lean` as a compatibility umbrella importing all three modules.
- Line counts after split: umbrella 11, `Connection` 1235, `RicciCoord` 971, `ScalarHessian` 832.
- Verification status: focused checks passed for all three new modules and the umbrella; targeted builds passed for each new module and the umbrella.
- Warning status: no split-local warnings were emitted.  The umbrella build replayed older warnings from lower dependencies including `Operators`, `RoughLaplacian`, `Tensor.RSTensor.Metric`, `VectorBundle.LocalFrameRegularity`, and `Curvature.Components.Christoffel`.
- API note: no public theorem or definition names were renamed, and no helper visibility changes were needed.

## 2026-05-23 LeviCivita/Curvature

- Split `RicciFlower.LeviCivita.Curvature` into `Curvature.LeviCivita` and `Curvature.Realized`.
- Kept `Curvature.lean` as a compatibility umbrella importing both modules.
- Line counts after split: umbrella 10, `Curvature.LeviCivita` 1622, `Curvature.Realized` 1220.
- Verification status: focused checks passed for both new modules and the umbrella; targeted builds passed for both new modules and the umbrella.
- Warning status: the split-local unnecessary `simpa` warning in `Curvature.Realized` was cleared.  The umbrella build replayed older warnings from lower dependencies including `Operators`, `RoughLaplacian`, `Tensor.RSTensor.Metric`, `VectorBundle.LocalFrameRegularity`, `Curvature.Components.Christoffel`, `Bianchi`, and Levi-Civita smoothness modules.
- API note: no public theorem or definition names were renamed, and no helper visibility changes were needed.

## 2026-05-23 Final Audit

- Line-count audit: no `RicciFlower/**/*.lean` file remains over 2000 lines.
- Full verification: `RicciFlower` full Lake build passed after the split.
- Split-file `sorry`/`admit` audit: the only match in the split target set is the pre-existing `expAt_localDiffeomorph` frontier now located at `Coordinates/Normal/Data.lean`.
- Remaining warning classes from the full build:
  - pre-existing flexible `simp`/style warnings in lower operator, tensor, Bianchi, dimension-three, and Levi-Civita smoothness modules;
  - pre-existing `sorry` warnings in Ricci-flow long-time/existence/rescaling/evolution roadmap files and `HamiltonPositiveRicci`;
  - deprecated compatibility-route warnings in split Ricci-flow metric/Ricci modules and scalar-side consumers;
  - intentional unused public instance warnings in `ImprovedPinching.Definitions`;
  - one retained non-mechanical flexible `simp` in `ImprovedPinching.HamiltonRHS`;
  - dirty divergence-theorem warning replay from files intentionally left untouched in this pass.

## 2026-05-23 1000-Line Audit Batch

- Split `RicciFlower.Tensor.RSTensor.MetricTrace` into
  `MetricTrace.Connection`, `MetricTrace.Trace04`, `MetricTrace.NablaTrace02`,
  and `MetricTrace.Higher`; kept the original module as an umbrella.
- Split `RicciFlower.RicciFlow.Evolution.Connection` into
  `Connection.Components`, `Connection.Pairing`, `Connection.Christoffel`, and
  `Connection.Producers`; kept the original module as an umbrella.
- Split `RicciFlower.VectorBundle.PartialMfderiv` into
  `PartialMfderiv.Basic`, `PartialMfderiv.ModelMixed`, and
  `PartialMfderiv.FixedBase`; kept the original module as an umbrella.
- Split `RicciFlower.Tensor.RSTensor.QuadraticBounds` into
  `QuadraticBounds.Unit` and `QuadraticBounds.TimeSlab`; kept the original
  module as an umbrella.
- Split `RicciFlower.RicciFlow.Evolution.Scalar` into `Scalar.Basic`,
  `Scalar.TraceAlgebra`, `Scalar.RmTrace`, and `Scalar.Assembly`; kept the
  original module as an umbrella.
- Split `RicciFlower.GlobalGeometry.Jacobi` into `Jacobi.Surface`,
  `Jacobi.FrameCurvature`, `Jacobi.Variation`, and `Jacobi.Final`; kept the
  original module as an umbrella.
- Verification status: focused checks passed for all new submodules and all
  umbrellas in this batch.  Targeted builds passed for the new modules where
  downstream `.olean` files were needed.
- Warning cleanup: cleared split-local naming and visibility issues, removed
  unused `DecidableEq` hypotheses in `Scalar.RmTrace`, and removed unused
  `DecidableEq` hypotheses in two private `Jacobi.FrameCurvature` helpers.
  `Scalar.Assembly` intentionally retains deprecated-route warnings because it
  is still a compatibility consumer of the older local-frame Ricci route.
- Tooling note: the first `Scalar.Basic` targeted build exceeded the short
  timeout and left orphan `lake`/`lean` subprocesses; they were stopped before a
  longer single build was rerun successfully.

## 2026-05-23 1000-Line Retained Files

The following >1000-line files were inspected and retained in this batch
because their current size is either a cohesive single proof route, a just-split
submodule from the 2000-line pass, an endpoint/roadmap file, or an unrelated
dirty file outside the current scope:

- `RicciFlower/ScalarBochner.lean` and `RicciFlower/Bochner.lean`: still large
  and plausible future split candidates, but each is a tightly coupled
  Bochner-proof route with long internal proof blocks; not split in this batch
  to avoid opening a second high-risk algebra/module-boundary pass.
- New submodules produced by the 2000-line pass, including
  `ImprovedPinching.Definitions`, `LeviCivita.Curvature.LeviCivita`,
  `SurfaceCalculus.Base`, `RicciFlow.Basic.Components`,
  `TensorWeak.FirstNull`, `TensorWeak.Compactness`,
  `Analysis.Volume.Family.Base`, `Analysis.Volume.Family.Variation`,
  `RicciFlow.Evolution.Ricci.CoordinateRegularity`,
  `RicciFlow.Evolution.Ricci.Commutator`,
  `Tensor0SRiemannian.Smooth`, `PullbackConnection.Curves`,
  `LeviCivita.Variation.Connection`, `LeviCivita.Curvature.Realized`,
  `Coordinates.Normal.Flow`, `MetricCompatibility.Covariant`,
  `Tensor0SRiemannian.Coordinate`, `Tensor0SRiemannian.Product`,
  `ImprovedPinching.HamiltonRHS`, `Coordinates.Normal.Spray`,
  `PullbackConnection.Frame`, `RicciFlow.Basic.Core`: retained because they are
  coherent post-split proof families near the previous target threshold.
- `Bianchi.lean`, `MaximumPrinciple/ScalarWeak.lean`,
  `VectorBundle/Equiv.lean`, `Tensor/RSTensor/Contract.lean`,
  `SprayChartPush.lean`, `Analysis/Volume/Invariance.lean`,
  `Tensor/Multilinear/Dual.lean`, `LeviCivita/Koszul.lean`,
  `Analysis/DivergenceTheorem/Ibp.lean`,
  `Tensor/RSTensor/NablaOnTensors/Regularity/Derivation.lean`,
  `GlobalGeometry/Lecture07/CoordinateEquation.lean`,
  `Tensor/Auxiliary/ShuffleDecomposition.lean`,
  `Tensor/RicciIdentity/Tensor0S/Formula.lean`,
  `Tensor/Multilinear/BundleSmoothEval.lean`, and
  `RicciFlow/Evolution/RicciPreservation.lean`: retained after audit because
  each is either a cohesive theorem family, a single long proof pipeline, or
  not worth splitting without a more targeted API-cleanup task.
- `Analysis/DivergenceTheorem/Gradient.lean` was left untouched because it was
  already dirty from unrelated work.
