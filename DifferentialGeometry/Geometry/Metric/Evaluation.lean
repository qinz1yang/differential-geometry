import DifferentialGeometry.Geometry.Metric.Basic
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection

noncomputable section
open Bundle
open DifferentialGeometry
open scoped Manifold ContDiff

namespace Poincare.Geometry.Metric

theorem contMDiff_metric_inner
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (g : SmoothRiemannianMetric I M)
    (X Y : ContMDiffSection I E ∞ (TangentSpace I : M → Type _)) :
    ContMDiff I 𝓘(ℝ) ∞ (fun x ↦ g.inner x (X x) (Y x)) := by
  have ht : ContMDiff I (I.prod 𝓘(ℝ)) ∞
      (fun x ↦ TotalSpace.mk' ℝ (E := fun _ : M ↦ ℝ) x (g.inner x (X x) (Y x))) :=
    ContMDiff.clm_bundle_apply₂ (E₁ := TangentSpace I) (E₂ := TangentSpace I)
      (E₃ := fun _ : M ↦ ℝ) (b := id) (ψ := fun x ↦ g.inner x)
      (v := fun x ↦ X x) (w := fun x ↦ Y x)
      g.contMDiff X.contMDiff Y.contMDiff
  intro x
  exact (contMDiffAt_totalSpace.mp (ht x)).2

end Poincare.Geometry.Metric
