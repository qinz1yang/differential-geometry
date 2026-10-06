import DifferentialGeometry.Geometry.Measure.Area.Manifold
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.MeasureTheory.Measure.OpenPos

set_option autoImplicit false

noncomputable section

open Bundle Manifold DifferentialGeometry Filter Set MeasureTheory
open scoped Bundle Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- An injective differential has strictly positive two-dimensional area density. -/
theorem riemannianAreaDensity_pos_of_injective_mfderiv
    (g : SmoothRiemannianMetric I M) {u : ℂ → M} {z : ℂ}
    (hu : Function.Injective (mfderiv 𝓘(ℝ, ℂ) I u z)) :
    0 < riemannianAreaDensity g u z := by
  have hli : LinearIndependent ℝ
      ![mfderiv 𝓘(ℝ, ℂ) I u z (1 : ℂ), mfderiv 𝓘(ℝ, ℂ) I u z Complex.I] := by
    convert Complex.basisOneI.linearIndependent.map'
      (mfderiv 𝓘(ℝ, ℂ) I u z).toLinearMap (LinearMap.ker_eq_bot.mpr hu) using 1
    ext i
    fin_cases i <;> simp [Complex.coe_basisOneI] <;> rfl
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  change 0 < twoJacobian (mfderiv 𝓘(ℝ, ℂ) I u z (1 : ℂ))
    (mfderiv 𝓘(ℝ, ℂ) I u z Complex.I)
  rw [twoJacobian_eq_sqrt_det_gram]
  exact Real.sqrt_pos.mpr (Matrix.posDef_gram_of_linearIndependent hli).det_pos

/-- A `C¹` parametrized surface on a compact domain has positive area if it is
immersed at one interior point. No minimizing property is required. -/
theorem riemannianArea_pos_of_injective_mfderiv
    (g : SmoothRiemannianMetric I M) {u : ℂ → M} {s K : Set ℂ} {z : ℂ}
    (hs : IsOpen s) (hu : ContMDiffOn 𝓘(ℝ, ℂ) I 1 u s)
    (hK : IsCompact K) (hKs : K ⊆ s) (hz : z ∈ interior K)
    (hinj : Function.Injective (mfderiv 𝓘(ℝ, ℂ) I u z)) :
    0 < riemannianArea g u K := by
  have hint := integrableOn_riemannianAreaDensity_of_contMDiffOn g hs hu hK hKs
  have hcont : ContinuousAt (riemannianAreaDensity g u) z :=
    (continuousOn_riemannianAreaDensity g hs hu).continuousAt
      (hs.mem_nhds (hKs (interior_subset hz)))
  have hpos := riemannianAreaDensity_pos_of_injective_mfderiv g hinj
  apply (setIntegral_pos_iff_support_of_nonneg_ae
    (Eventually.of_forall fun w => riemannianAreaDensity_nonneg g u w) hint).2
  exact Measure.measure_pos_of_mem_nhds volume
    (inter_mem (hcont.eventually_ne hpos.ne') (mem_interior_iff_mem_nhds.mp hz))

end DifferentialGeometry.Geometry
