import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StaticCap
import DifferentialGeometry.Geometry.Curvature.RicciRestriction
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingFromOpen

noncomputable section

open Manifold
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M] [T2Space M]
  {g : SmoothRiemannianMetric ThreeModel M} {U : TopologicalSpace.Opens M}
  {δ : ℝ} {k : ℕ}

def toAmbient (N : NormalizedNeck (g.restrictOpen U) δ k) : NormalizedNeck g δ k where
  delta_pos := N.delta_pos
  delta_lt_one := N.delta_lt_one
  sphereMark := N.sphereMark
  center := N.center.val
  chart := ⟨Subtype.val ∘ N.chart, continuous_subtype_val.comp N.chart.continuous⟩
  chart_smooth := DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_fromOpen
    NeckCylinderModel ThreeModel U N.chart N.chart_smooth
  marked := congrArg Subtype.val N.marked
  scale := N.scale
  scale_pos := N.scale_pos
  scale_scalar := N.scale_scalar.trans (metricScalarAt_restrictOpen g U N.center)
  normalizedMetric := N.normalizedMetric
  normalized_inner := by
    intro x v w
    rw [N.normalized_inner, SmoothRiemannianMetric.restrictOpen_inner]
    have hd := mfderiv_comp x
      ((contMDiff_subtype_val (I := ThreeModel) (U := U) (n := ∞)).mdifferentiableAt (by simp))
      (N.chart_smooth.contMDiff.mdifferentiableAt (by simp))
    rw [DifferentialGeometry.mfderiv_subtype_val] at hd
    change _ = N.scale * g.inner (N.chart x).val
      (mfderiv NeckCylinderModel ThreeModel (Subtype.val ∘ N.chart) x v)
      (mfderiv NeckCylinderModel ThreeModel (Subtype.val ∘ N.chart) x w)
    rw [hd]
    rfl
  closeness := N.closeness

@[simp] theorem toAmbient_center (N : NormalizedNeck (g.restrictOpen U) δ k) :
    N.toAmbient.center = N.center.val := rfl

@[simp] theorem toAmbient_chart (N : NormalizedNeck (g.restrictOpen U) δ k) :
    (N.toAmbient.chart : neckBuffer δ → M) = Subtype.val ∘ N.chart := rfl

@[simp] theorem toAmbient_scale (N : NormalizedNeck (g.restrictOpen U) δ k) :
    N.toAmbient.scale = N.scale := rfl

@[simp] theorem toAmbient_sphereMark (N : NormalizedNeck (g.restrictOpen U) δ k) :
    N.toAmbient.sphereMark = N.sphereMark := rfl

@[simp] theorem toAmbient_normalizedMetric (N : NormalizedNeck (g.restrictOpen U) δ k) :
    N.toAmbient.normalizedMetric = N.normalizedMetric := rfl

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.NormalizedNeck
