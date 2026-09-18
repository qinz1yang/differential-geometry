import DifferentialGeometry.Geometry.Metric.Family.QuadraticBounds
import DifferentialGeometry.Geometry.Metric.Family.Stationary
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Bounds

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open Set
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]

theorem exists_metric_uniform_equivalent_on_compact
    [T2Space M]
    (G : ℝ → SmoothRiemannianMetric I M)
    (R : SmoothRiemannianMetric I M)
    {J : Set ℝ} (hJ : IsCompact J) {K : Set M} (hK : IsCompact K)
    (hG : tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 J
      (fun t x => Tensor0SBundle.metricTensorField (I := I) (G t) x)) :
    ∃ L : ℝ, 1 ≤ L ∧
      ∀ t ∈ J, MetricUniformEquivalentOn (I := I) K R (G t) L := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let DRef := RealTimeInterval.univ 0
  let GRef := (stationaryMetricFamily (I := I) (M := M) R).metric
  have hGRef : MetricFamilySmoothOn (I := I) (M := M) DRef GRef := by
    simpa only [GRef] using
      metricFamilySmoothOn_stationary (I := I) (M := M) R DRef
  have hR : tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 J
      (fun _ x => Tensor0SBundle.metricTensorField (I := I) R x) := by
    have h := metricTensor_cont_restrict_of_metricFamilySmoothOn
      (I := I) (M := M) (K := J) GRef hGRef (fun _ _ => Set.mem_univ _)
    simpa only [GRef, stationaryMetricFamily] using h
  obtain ⟨C₁, -, hupper⟩ :=
    exists_tensor_quadratic_bound_on_compact (I := I) (M := M)
      GRef (fun t x => Tensor0SBundle.metricTensorField (I := I) (G t) x)
      hJ hK hR hG
  obtain ⟨C₂, -, hlower⟩ :=
    exists_tensor_quadratic_bound_on_compact (I := I) (M := M)
      G (fun _ x => Tensor0SBundle.metricTensorField (I := I) R x)
      hJ hK hG hR
  let L : ℝ := max 1 (max C₁ C₂)
  have hL : 1 ≤ L := le_max_left _ _
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hC₁L : C₁ ≤ L :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hC₂L : C₂ ≤ L :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨L, hL, ?_⟩
  intro t ht
  refine ⟨hL, ?_⟩
  intro x hx v
  have hRnonneg : 0 ≤ R.inner x v v := by
    by_cases hv : v = 0
    · subst v
      simp
    · exact (R.pos x v hv).le
  have hGnonneg : 0 ≤ (G t).inner x v v := by
    by_cases hv : v = 0
    · subst v
      simp
    · exact ((G t).pos x v hv).le
  have hu0 := hupper t ht x hx v
  have hl0 := hlower t ht x hx v
  have huAbs : |(G t).inner x v v| ≤ C₁ * R.inner x v v := by
    simpa only [quad02, Tensor0SBundle.metricTensorField_apply, GRef,
      stationaryMetricFamily] using hu0
  have hlAbs : |R.inner x v v| ≤ C₂ * (G t).inner x v v := by
    simpa only [quad02, Tensor0SBundle.metricTensorField_apply, GRef,
      stationaryMetricFamily] using hl0
  have hu : (G t).inner x v v ≤ C₁ * R.inner x v v :=
    (le_abs_self _).trans huAbs
  have hl : R.inner x v v ≤ C₂ * (G t).inner x v v :=
    (le_abs_self _).trans hlAbs
  have huL : (G t).inner x v v ≤ L * R.inner x v v :=
    hu.trans (mul_le_mul_of_nonneg_right hC₁L hRnonneg)
  have hlL : R.inner x v v ≤ L * (G t).inner x v v :=
    hl.trans (mul_le_mul_of_nonneg_right hC₂L hGnonneg)
  constructor
  · calc
      L⁻¹ * R.inner x v v ≤ L⁻¹ * (L * (G t).inner x v v) :=
        mul_le_mul_of_nonneg_left hlL (inv_nonneg.mpr hLpos.le)
      _ = (G t).inner x v v := by simp [hLpos.ne']
  · exact huL

theorem exists_metric_uniform_equivalent_on_compact_of_metricFamilySmoothOn
    [T2Space M]
    {D : RealTimeInterval}
    (G : ℝ → SmoothRiemannianMetric I M)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G)
    {J : Set ℝ} (hJ : IsCompact J) (hJD : J ⊆ D.carrier)
    {K : Set M} (hK : IsCompact K)
    (R : SmoothRiemannianMetric I M) :
    ∃ L : ℝ, 1 ≤ L ∧
      ∀ t ∈ J, MetricUniformEquivalentOn (I := I) K R (G t) L :=
  exists_metric_uniform_equivalent_on_compact (I := I) (M := M)
    G R hJ hK
    (metricTensor_cont_restrict_of_metricFamilySmoothOn
      (I := I) (M := M) G hG hJD)

end CheegerGromovCompactness
end DifferentialGeometry
