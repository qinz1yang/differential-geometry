import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Projection
import DifferentialGeometry.Analysis.Calculus.TimeJet.SpatialDerivatives

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {D : RealTimeInterval}

theorem inner_X_self_contDiffOn (c : ProductCurve M)
    (g : ℝ → SmoothRiemannianMetric I M)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g)
    (lambda : ℝ) {J : Set ℝ} (hJ : UniqueDiffOn ℝ J) (hreg : J ⊆ D.regular)
    (hc : c.SmoothOn (I := I) J) :
    ContDiffOn ℝ ∞
      (fun p : ℝ × ℝ => c.inner g lambda p.1 p.2 (c.X p.1 p.2) (c.X p.1 p.2))
      (univ ×ˢ J) := by
  have hX := CurveMap.Field.smoothOn_X c.projection J hc.1
  have hinner := CurveMap.Field.smoothOn_inner g hG hreg c.projection hc.1
    (c.projection.X (I := I)) (c.projection.X (I := I)) hX hX
  have hy : ContDiffOn ℝ ∞
      (fun p : ℝ × ℝ => deriv (fun x => c.y x p.2) p.1) (univ ×ˢ J) :=
    DifferentialGeometry.Analysis.contDiffOn_deriv_fst isOpen_univ hJ hc.2
  have hsum := hinner.add ((contDiffOn_const (c := lambda ^ 2)).mul (hy.pow 2))
  exact hsum.congr fun p _ => c.inner_X_self g lambda p.1 p.2

theorem speed_contDiffOn (c : ProductCurve M)
    (g : ℝ → SmoothRiemannianMetric I M)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g)
    (lambda : ℝ) (hlambda : 0 < lambda) {J : Set ℝ}
    (hJ : UniqueDiffOn ℝ J) (hreg : J ⊆ D.regular)
    (hc : c.SmoothOn (I := I) J) (hi : c.ImmersedOn (I := I) J) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => c.speed g lambda p.1 p.2) (univ ×ˢ J) := by
  have hinner := c.inner_X_self_contDiffOn g hG lambda hJ hreg hc
  change ContDiffOn ℝ ∞
    (fun p : ℝ × ℝ => Real.sqrt
      (c.inner g lambda p.1 p.2 (c.X p.1 p.2) (c.X p.1 p.2))) (univ ×ˢ J)
  refine hinner.sqrt ?_
  intro p hp
  rw [← c.speed_sq g lambda p.1 p.2]
  exact ne_of_gt (pow_pos (c.speed_pos_of_immersedOn g lambda hlambda hi p.1 p.2 hp.2) 2)

theorem angle_contDiffOn (c : ProductCurve M)
    (g : ℝ → SmoothRiemannianMetric I M)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g)
    (lambda : ℝ) (hlambda : 0 < lambda) {J : Set ℝ}
    (hJ : UniqueDiffOn ℝ J) (hreg : J ⊆ D.regular)
    (hc : c.SmoothOn (I := I) J) (hi : c.ImmersedOn (I := I) J) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => c.angle g lambda p.1 p.2) (univ ×ˢ J) := by
  have hs := c.speed_contDiffOn g hG lambda hlambda hJ hreg hc hi
  have hinv := hs.inv fun p hp =>
    ne_of_gt (c.speed_pos_of_immersedOn g lambda hlambda hi p.1 p.2 hp.2)
  have hy : ContDiffOn ℝ ∞
      (fun p : ℝ × ℝ => deriv (fun x => c.y x p.2) p.1) (univ ×ˢ J) :=
    DifferentialGeometry.Analysis.contDiffOn_deriv_fst isOpen_univ hJ hc.2
  exact ((contDiffOn_const (c := lambda)).mul hinv |>.mul hy).congr
    fun p _ => c.angle_eq g lambda p.1 p.2

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve
