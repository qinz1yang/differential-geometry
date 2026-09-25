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


open Manifold

namespace DifferentialGeometry.Geometry.Curvature

variable {E F H H' M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N] [T2Space N]

theorem metricRm04StandardAt_eq_of_partialDiffeomorph_restriction
    (Phi : PartialDiffeomorph I J M N ∞) (U : TopologicalSpace.Opens M)
    (hU : (U : Set M) ⊆ Phi.source)
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (hmet : ∀ x : U, ∀ v w : TangentSpace I x,
      g.inner x.val v w = h.inner (Phi x.val) (mfderiv I J (Phi : M → N) x.val v)
        (mfderiv I J (Phi : M → N) x.val w))
    (x : U) (a b c d : TangentSpace I x) :
    metricRm04StandardAt g x.val a b c d =
      metricRm04StandardAt h (Phi x.val) (mfderiv I J Phi x.val a)
        (mfderiv I J Phi x.val b) (mfderiv I J Phi x.val c)
        (mfderiv I J Phi x.val d) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : CompleteSpace F := FiniteDimensional.complete ℝ F
  let _ : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)
  let _ : IsManifold J 1 N := IsManifold.of_le (n := ∞) (by decide)
  let V : TopologicalSpace.Opens N := ⟨Phi '' (U : Set M), image_opens_isOpen Phi hU⟩
  let Ψ := PartialDiffeomorph.toOpensDiffeo Phi hU
  have hmetric : g.restrictOpen U = Diffeomorph.pullbackMetricCross (h.restrictOpen V) Ψ := by
    apply SmoothRiemannianMetric.ext_inner
    intro y v w
    rw [Diffeomorph.pullbackMetricCross_inner, SmoothRiemannianMetric.restrictOpen_inner]
    exact (hmet y v w).trans
      (congrArg₂ (fun v' w' => h.inner (Phi y.val) v' w')
        (PartialDiffeomorph.mfderiv_toOpensDiffeo Phi hU y v)
        (PartialDiffeomorph.mfderiv_toOpensDiffeo Phi hU y w)).symm
  have hr := metricRm04StandardAt_restrictOpen g U x a b c d
  simp only [mfderiv_subtype_val_apply] at hr
  rw [← hr, hmetric, metricRm04Standard_pullbackCross,
    metricRm04StandardAt_restrictOpen]
  simp only [mfderiv_subtype_val_apply]
  change metricRm04StandardAt h (Phi x.val) (mfderiv I J Ψ x a)
    (mfderiv I J Ψ x b) (mfderiv I J Ψ x c) (mfderiv I J Ψ x d) = _
  rw [show mfderiv I J Ψ x a = mfderiv I J Phi x.val a from
      PartialDiffeomorph.mfderiv_toOpensDiffeo Phi hU x a,
    show mfderiv I J Ψ x b = mfderiv I J Phi x.val b from
      PartialDiffeomorph.mfderiv_toOpensDiffeo Phi hU x b,
    show mfderiv I J Ψ x c = mfderiv I J Phi x.val c from
      PartialDiffeomorph.mfderiv_toOpensDiffeo Phi hU x c,
    show mfderiv I J Ψ x d = mfderiv I J Phi x.val d from
      PartialDiffeomorph.mfderiv_toOpensDiffeo Phi hU x d]

end DifferentialGeometry.Geometry.Curvature
