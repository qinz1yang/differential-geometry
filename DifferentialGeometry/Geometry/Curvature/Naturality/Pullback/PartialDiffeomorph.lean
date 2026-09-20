import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Opens
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.LocalCross
import DifferentialGeometry.Geometry.Curvature.Algebraic.CurvatureOperatorConeMetric

noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.CheegerGromovCompactness

open DifferentialGeometry.Geometry.Curvature

variable {E H M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [T2Space N]

omit [I.Boundaryless] in
private theorem partialDiffeomorph_restriction_metric_eq_pullback
    (Phi : PartialDiffeomorph I I M N ∞) (U : TopologicalSpace.Opens M)
    (hU : (U : Set M) ⊆ Phi.source)
    (g : SmoothRiemannianMetric I U) (h : SmoothRiemannianMetric I N)
    (hmet : ∀ x : U, ∀ v w : TangentSpace I x,
      g.inner x v w = h.inner (Phi x) (mfderiv I I (Phi : M → N) x v)
        (mfderiv I I (Phi : M → N) x w)) :
    g = Diffeomorph.pullbackMetricCross
      (h.restrictOpen ⟨Phi '' (U : Set M), image_opens_isOpen Phi hU⟩)
      (PartialDiffeomorph.toOpensDiffeo Phi hU) := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [Diffeomorph.pullbackMetricCross_inner, SmoothRiemannianMetric.restrictOpen_inner]
  exact (hmet x v w).trans
    (congrArg₂ (fun v' w' => h.inner (Phi (x : M)) v' w')
      (PartialDiffeomorph.mfderiv_toOpensDiffeo Phi hU x v)
      (PartialDiffeomorph.mfderiv_toOpensDiffeo Phi hU x w)).symm

theorem metricScalarAt_eq_of_partialDiffeomorph_restriction
    (Phi : PartialDiffeomorph I I M N ∞) (U : TopologicalSpace.Opens M)
    (hU : (U : Set M) ⊆ Phi.source)
    (g : SmoothRiemannianMetric I U) (h : SmoothRiemannianMetric I N)
    (hmet : ∀ x : U, ∀ v w : TangentSpace I x,
      g.inner x v w = h.inner (Phi x) (mfderiv I I (Phi : M → N) x v)
        (mfderiv I I (Phi : M → N) x w)) (x : U) :
    metricScalarAt g x = metricScalarAt h (Phi x) := by
  rw [partialDiffeomorph_restriction_metric_eq_pullback Phi U hU g h hmet,
    Diffeomorph.pullbackMetricCross_eq_localPullMetric, metricScalarAt_localPull,
    ← localPullMetric_subtype_val h ⟨Phi '' (U : Set M), image_opens_isOpen Phi hU⟩,
    metricScalarAt_localPull]
  rfl

omit [I.Boundaryless] in
theorem curvatureOperatorLowerBoundAt_of_partialDiffeomorph_restriction
    (Phi : PartialDiffeomorph I I M N ∞) (U : TopologicalSpace.Opens M)
    (hU : (U : Set M) ⊆ Phi.source)
    (g : SmoothRiemannianMetric I U) (h : SmoothRiemannianMetric I N)
    (hmet : ∀ x : U, ∀ v w : TangentSpace I x,
      g.inner x v w = h.inner (Phi x) (mfderiv I I (Phi : M → N) x v)
        (mfderiv I I (Phi : M → N) x w)) (x : U) (K : ℝ)
    (hbound : curvatureOperatorLowerBoundAt h (Phi x)
      (metricAlgebraicCurvatureTensorAt h (Phi x)) K) :
    curvatureOperatorLowerBoundAt g x (metricAlgebraicCurvatureTensorAt g x) K := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)
  let _ : IsManifold I 1 N := IsManifold.of_le (n := ∞) (by decide)
  have hrm (a b c d : TangentSpace I x) :
      metricRm04StandardAt g x a b c d =
        metricRm04StandardAt h (Phi x) (mfderiv I I Phi x a)
          (mfderiv I I Phi x b) (mfderiv I I Phi x c) (mfderiv I I Phi x d) := by
    rw [partialDiffeomorph_restriction_metric_eq_pullback Phi U hU g h hmet,
      metricRm04Standard_pullbackCross, metricRm04StandardAt_restrictOpen]
    simp only [PartialDiffeomorph.mfderiv_toOpensDiffeo]
    rw [mfderiv_subtype_val (I := I)
      (⟨Phi '' (U : Set M), image_opens_isOpen Phi hU⟩ : TopologicalSpace.Opens N)]
    rfl
  intro n a v w
  have hb := hbound n a (fun i => mfderiv I I Phi x (v i))
    (fun i => mfderiv I I Phi x (w i))
  change 0 ≤ (∑ i, ∑ j, a i * a j * metricRm04StandardAt g x (v i) (w i) (w j) (v j)) + _
  simp_rw [hrm]
  change 0 ≤ (∑ i, ∑ j, a i * a j * metricRm04StandardAt h (Phi x)
    (mfderiv I I Phi x (v i)) (mfderiv I I Phi x (w i))
    (mfderiv I I Phi x (w j)) (mfderiv I I Phi x (v j))) + _ at hb
  simpa only [algebraicCurvatureIdentityQuadraticEval, hmet] using hb

end DifferentialGeometry.CheegerGromovCompactness
