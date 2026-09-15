import DifferentialGeometry.Geometry.Measure.Area.ManifoldMeasurable
import DifferentialGeometry.Bundle.TangentMap

noncomputable section

open Bundle Manifold Filter Set
open scoped Bundle Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def pullbackAreaDensity (g : SmoothRiemannianMetric I M) (r : F → M)
    (y : F) (A : ℂ →L[ℝ] F) : ℝ :=
  tangentTwoJacobian g (mfderiv 𝓘(ℝ, F) I r y (A 1))
    (mfderiv 𝓘(ℝ, F) I r y (A Complex.I))

theorem continuousOn_pullbackAreaDensity (g : SmoothRiemannianMetric I M)
    {r : F → M} {U : Set F} (hU : IsOpen U) (hr : ContMDiffOn 𝓘(ℝ, F) I 1 r U) :
    ContinuousOn (fun q : F × (ℂ →L[ℝ] F) => pullbackAreaDensity g r q.1 q.2)
      (Prod.fst ⁻¹' U) :=
  continuousOn_tangentTwoJacobian g (hr.continuousOn_mfderiv_apply hU 1)
    (hr.continuousOn_mfderiv_apply hU Complex.I)

theorem riemannianAreaDensity_comp_eq_pullbackAreaDensity (g : SmoothRiemannianMetric I M)
    {r : F → M} {v : ℂ → F} {z : ℂ} (hr : MDifferentiableAt 𝓘(ℝ, F) I r (v z))
    (hv : DifferentiableAt ℝ v z) :
    riemannianAreaDensity g (r ∘ v) z = pullbackAreaDensity g r (v z) (fderiv ℝ v z) := by
  unfold riemannianAreaDensity pullbackAreaDensity
  rw [mfderiv_comp z hr (mdifferentiableAt_iff_differentiableAt.mpr hv), mfderiv_eq_fderiv]
  rfl

end DifferentialGeometry.Geometry
