import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Bounds.BoundedGeometry
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Bounds.InjectivityRadius
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.Restriction
import DifferentialGeometry.Geometry.Metric.Restriction
import DifferentialGeometry.Topology.SigmaCompactOpen
import DifferentialGeometry.Bundle.FiberBundleHausdorff

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace DifferentialGeometry.CheegerGromovCompactness

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  (X : PointedRiemannianManifold I)

local instance : TopologicalSpace X.M := X.topology
local instance : ChartedSpace H X.M := X.charted
local instance : IsManifold I ∞ X.M := X.smooth
local instance : SigmaCompactSpace X.M := X.sigmaCompact
local instance : T2Space X.M := X.t2

def PointedRiemannianManifold.restrictOpen
    (U : TopologicalSpace.Opens X.M) (hp : X.basepoint ∈ U) : PointedRiemannianManifold I := by
  let : SigmaCompactSpace U :=
    isSigmaCompact_iff_sigmaCompactSpace.mp (Geometry.isSigmaCompact_of_isOpen I U.isOpen)
  exact { M := U, basepoint := ⟨X.basepoint, hp⟩, metric := X.metric.restrictOpen U }

theorem PointedRiemannianManifold.restrictOpen_metric
    (U : TopologicalSpace.Opens X.M) (hp : X.basepoint ∈ U) :
    (X.restrictOpen U hp).metric = X.metric.restrictOpen U := rfl

theorem PointedRiemannianManifold.restrictOpen_basepoint_coe
    (U : TopologicalSpace.Opens X.M) (hp : X.basepoint ∈ U) :
    ((show U from (X.restrictOpen U hp).basepoint) : X.M) = X.basepoint := rfl

theorem metricComplete_restrictOpen
    (U : TopologicalSpace.Opens X.M) (hp : X.basepoint ∈ U)
    (hU : IsClosed (U : Set X.M)) (hX : MetricComplete X) :
    MetricComplete (X.restrictOpen U hp) := by
  let : SigmaCompactSpace U := hU.sigmaCompactSpace
  have hg : RiemannianMetricComplete X.metric := ⟨MetricComplete.complete X hX⟩
  exact (hg.restrictOpen U hU).complete

theorem PointedRiemannianManifold.emetricSpace_restrictOpen_of_isClosed
    (U : TopologicalSpace.Opens X.M) (hp : X.basepoint ∈ U) (hU : IsClosed (U : Set X.M)) :
    letI : EMetricSpace X.M := X.emetricSpace
    (X.restrictOpen U hp).emetricSpace = (inferInstance : EMetricSpace U) := by
  let : EMetricSpace X.M := X.emetricSpace
  apply EMetricSpace.ext
  ext x y
  change riemannianEDistOf (X.metric.restrictOpen U) x y =
    riemannianEDistOf X.metric (Subtype.val (show U from x)) (Subtype.val (show U from y))
  exact riemannianEDistOf_restrictOpen_of_isClosed X.metric U hU x y

theorem hasCurvDerivBound_restrictOpen
    (U : TopologicalSpace.Opens X.M) (hp : X.basepoint ∈ U) (k : ℕ) (C : ℝ)
    (hX : HasCurvDerivBound X k C) : HasCurvDerivBound (X.restrictOpen U hp) k C := by
  change ∀ x : U, curvDerivNorm k (X.metric.restrictOpen U) x ≤ C
  intro x
  exact (curvDerivNorm_restrictOpen X.metric U k x).trans_le (hX (x : X.M))

end Normed

section InnerProduct

open Geometry.Riemannian Geometry.Riemannian.NormalCoordinates

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (X : PointedRiemannianManifold I)

local instance : TopologicalSpace X.M := X.topology
local instance : ChartedSpace H X.M := X.charted
local instance : IsManifold I ∞ X.M := X.smooth
local instance : IsManifold I 1 X.M := IsManifold.of_le (n := ∞) (by decide)
local instance : SigmaCompactSpace X.M := X.sigmaCompact
local instance : T2Space X.M := X.t2

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace in
theorem PointedRiemannianManifold.intrinsicInjRadius_restrictOpen_of_isClosed
    (U : TopologicalSpace.Opens X.M) (hp : X.basepoint ∈ U)
    (hU : IsClosed (U : Set X.M)) (hX : MetricComplete X)
    (hR : MetricComplete (X.restrictOpen U hp)) (x : U) :
    (X.restrictOpen U hp).intrinsicInjRadius hR x = X.intrinsicInjRadius hX (x : X.M) := by
  let : RiemannianBundle (fun y : X.M => TangentSpace I y) := X.riemBundle
  let : IsContinuousRiemannianBundle E (fun y : X.M => TangentSpace I y) := X.riemBundle_cont
  let : EMetricSpace X.M := X.emetricSpace
  let : CompleteSpace X.M := MetricComplete.complete X hX
  let : SigmaCompactSpace U := hU.sigmaCompactSpace
  let : RiemannianBundle (fun y : U => TangentSpace I y) :=
    ⟨(X.metric.restrictOpen U).toRiemannianMetric⟩
  let hN : IsMetricNorm X.metric := isMetricNorm_of_riemannianBundle X.metric
  let hNU : IsMetricNorm (X.metric.restrictOpen U) :=
    isMetricNorm_of_riemannianBundle (X.metric.restrictOpen U)
  let : IsContinuousRiemannianBundle E (fun y : U => TangentSpace I y) :=
    hNU.isContinuousRiemannianBundle
  let : CompleteSpace U := hU.isComplete.completeSpace_coe
  let : IsRiemannianManifold I U := by
    constructor
    intro a b
    change Manifold.riemannianEDist I (a : X.M) (b : X.M) = _
    rw [← riemannianEDistOf_eq_riemannianEDist X.metric hN,
      ← riemannianEDistOf_eq_riemannianEDist (X.metric.restrictOpen U) hNU]
    exact (riemannianEDistOf_restrictOpen_of_isClosed X.metric U hU a b).symm
  unfold PointedRiemannianManifold.intrinsicInjRadius
  dsimp only
  exact intrinsicInjRadius_restrictOpen X.metric hN U hNU x

theorem hasInjRadiusAt_restrictOpen_iff
    (U : TopologicalSpace.Opens X.M) (hp : X.basepoint ∈ U)
    (hU : IsClosed (U : Set X.M)) (hX : MetricComplete X) (x : U) (ρ : ℝ) :
    HasInjRadiusAt (X.restrictOpen U hp) x ρ ↔ HasInjRadiusAt X (x : X.M) ρ := by
  constructor
  · intro hρ
    refine ⟨hρ.1, fun hM => ?_⟩
    have hr := hρ.2 (metricComplete_restrictOpen X U hp hU hX)
    rwa [PointedRiemannianManifold.intrinsicInjRadius_restrictOpen_of_isClosed
      X U hp hU hM] at hr
  · intro hρ
    refine ⟨hρ.1, fun hR => ?_⟩
    rw [PointedRiemannianManifold.intrinsicInjRadius_restrictOpen_of_isClosed
      X U hp hU hX hR x]
    exact hρ.2 hX

end InnerProduct

namespace PointedRiemannianSeq

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  (S : PointedRiemannianSeq I)

local instance (i : ℕ) : TopologicalSpace (S.obj i).M := (S.obj i).topology

def restrictOpen (U : ∀ i, TopologicalSpace.Opens (S.obj i).M)
    (hp : ∀ i, (S.obj i).basepoint ∈ U i) : PointedRiemannianSeq I where
  obj i := (S.obj i).restrictOpen (U i) (hp i)

end PointedRiemannianSeq

end DifferentialGeometry.CheegerGromovCompactness
