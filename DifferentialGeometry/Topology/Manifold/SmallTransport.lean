import DifferentialGeometry.Topology.Manifold.Small
import DifferentialGeometry.Topology.Manifold.Homeomorph.Transport
import DifferentialGeometry.Topology.Manifold.OrientationDiffeomorphTransport
import DifferentialGeometry.Geometry.Metric.PullbackCompleteness
import Mathlib.Topology.Instances.Shrink
import Mathlib.Topology.MetricSpace.TransferInstance

/-!
A second countable manifold over a small model has one actual small smooth model.
The same diffeomorphism transports its Riemannian metric and tangent orientation.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry
open scoped Manifold ContDiff

namespace DifferentialGeometry.Manifold

universe u

variable {E H : Type} [i1 : NormedAddCommGroup E] [i2 : NormedSpace ℝ E]
  [i3 : FiniteDimensional ℝ E] [i4 : TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  (M : Type u) [i5 : TopologicalSpace M] [i6 : ChartedSpace H M] [i7 : IsManifold I ∞ M]

structure SmallManifoldModel where
  Carrier : Type
  topology : TopologicalSpace Carrier
  charts : @ChartedSpace H _ Carrier topology
  smooth : @IsManifold ℝ _ E _ _ H _ I ∞ Carrier topology charts
  secondCountable : @SecondCountableTopology Carrier topology
  hausdorff : @T2Space Carrier topology
  diffeo : letI _sourceTopology := topology
    letI _sourceCharts := charts
    Carrier ≃ₘ⟮I, I⟯ M

attribute [instance] SmallManifoldModel.topology SmallManifoldModel.charts
  SmallManifoldModel.smooth SmallManifoldModel.secondCountable SmallManifoldModel.hausdorff

variable {M}

def smallManifoldModel [i8 : SecondCountableTopology M] [i9 : T2Space M] :
    SmallManifoldModel (I := I) M := by
  letI smallSource : Small.{0} M := ChartedSpace.small_of_lindelofSpace H M
  let h : Shrink.{0} M ≃ₜ M := (Shrink.homeomorph M).symm
  letI smallCharts : ChartedSpace H (Shrink.{0} M) :=
    Homeomorph.pullbackChartedSpace h
  letI smallSmooth : IsManifold I ∞ (Shrink.{0} M) :=
    Homeomorph.instIsManifoldPullback h
  exact ⟨Shrink.{0} M, inferInstance, smallCharts, smallSmooth,
    h.secondCountableTopology, h.symm.t2Space, Homeomorph.pullbackDiffeomorph h⟩

namespace SmallManifoldModel

variable (S : SmallManifoldModel (I := I) M)

def metric (g : SmoothRiemannianMetric I M) : SmoothRiemannianMetric I S.Carrier :=
  Diffeomorph.pullbackMetricCross g S.diffeo

theorem metric_inner (g : SmoothRiemannianMetric I M) (x : S.Carrier)
    (v w : TangentSpace I x) :
    (S.metric g).inner x v w = g.inner (S.diffeo x)
      (mfderiv I I S.diffeo x v) (mfderiv I I S.diffeo x w) :=
  Diffeomorph.pullbackMetricCross_inner g S.diffeo x v w

theorem metric_edist (g : SmoothRiemannianMetric I M) (x y : S.Carrier) :
    riemannianEDistOf (S.metric g) x y = riemannianEDistOf g (S.diffeo x) (S.diffeo y) :=
  riemannianEDistOf_pullbackMetricCross g S.diffeo x y

theorem exists_orientation {n : ℕ} (o : ManifoldOrientation I M n) :
    ∃ oS : ManifoldOrientation I S.Carrier n,
      S.diffeo.symm.preservesOrientation o oS := by
  obtain ⟨oS, hoS⟩ :=
    Topology.Manifold.exists_manifoldOrientation_diffeomorph_map S.diffeo.symm o
  refine ⟨oS, fun x => ?_⟩
  rw [show oS.orientation = _ from hoS]
  change Orientation.map (Fin n)
      (S.diffeo.symm.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv
      (o.orientation x) =
    Orientation.map (Fin n)
      (S.diffeo.symm.mfderivToContinuousLinearEquiv (by simp)
        (S.diffeo (S.diffeo.symm x))).toLinearEquiv
      (o.orientation (S.diffeo (S.diffeo.symm x)))
  rw [S.diffeo.apply_symm_apply]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem function_square {Y : Type*} (f : M → Y) (x : M) :
    (f ∘ S.diffeo) (S.diffeo.symm x) = f x := by
  simp only [Function.comp_apply, Diffeomorph.apply_symm_apply]

end SmallManifoldModel

section MetricSpace

variable {E H : Type} [i10 : NormedAddCommGroup E] [i11 : NormedSpace ℝ E]
  [i12 : FiniteDimensional ℝ E] [i13 : TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type u} [i14 : MetricSpace M] [i15 : ChartedSpace H M] [i16 : IsManifold I ∞ M]
  (S : SmallManifoldModel (I := I) M)

@[instance_reducible] def SmallManifoldModel.metricSpace : MetricSpace S.Carrier :=
  S.diffeo.toHomeomorph.isEmbedding.comapMetricSpace S.diffeo

def SmallManifoldModel.isometryEquiv :
    letI _smallMetric := S.metricSpace
    S.Carrier ≃ᵢ M := by
  letI _smallMetric := S.metricSpace
  exact ⟨S.diffeo.toEquiv, fun x y => rfl⟩

theorem SmallManifoldModel.metric_aligned (g : SmoothRiemannianMetric I M)
    (hmetric : ∀ x y : M, riemannianEDistOf g x y = ENNReal.ofReal (dist x y)) :
    letI _smallMetric := S.metricSpace
    ∀ x y : S.Carrier, riemannianEDistOf (S.metric g) x y = ENNReal.ofReal (dist x y) := by
  let _smallMetric := S.metricSpace
  intro x y
  rw [S.metric_edist g, hmetric]
  rfl

end MetricSpace

end DifferentialGeometry.Manifold
