import DifferentialGeometry.Geometry.Measure.Product
import DifferentialGeometry.Geometry.Metric.Sphere.Round.TotalArea
import DifferentialGeometry.Geometry.Metric.RoundCylinder
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Scaling

noncomputable section

open Set Manifold MeasureTheory
open DifferentialGeometry DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry.Geometry.Measure

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev S2 := Metric.sphere (0 : E3) 1
private instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩
private instance : MeasurableSpace S2 := borel S2
private instance : BorelSpace S2 := ⟨rfl⟩

private theorem cast_measure_apply {X : Type*} {m₁ m₂ : MeasurableSpace X}
    (hm : m₁ = m₂) (μ : @Measure X m₁) (S : Set X) :
    (cast (congrArg (fun m : MeasurableSpace X => @Measure X m) hm) μ) S = μ S := by
  cases hm
  rfl

theorem riemannianVolumeMeasure_roundCylinder_interval (a b : ℝ) :
    riemannianVolumeMeasure ((𝓡 2).prod 𝓘(ℝ)) (S2 × ℝ)
      (Metric.roundCylinderMetric (E := E3) (n := 2)) (univ ×ˢ Icc a b) =
      ENNReal.ofReal (8 * Real.pi) * ENNReal.ofReal (b - a) := by
  let h := scaleMetric 2 (by norm_num : (0 : ℝ) < 2) (roundMetric (E := E3) (n := 2))
  have hp (y : S2) (s : ℝ) (v w : TangentSpace (𝓡 2) y) (r t : ℝ) :
      (Metric.roundCylinderMetric (E := E3) (n := 2)).inner (y, s) (v, r) (w, t) =
        h.inner y v w + r * t := by
    change (Metric.roundCylinderMetric (E := E3) (n := 2)).inner (y, s)
      ((show EuclideanSpace ℝ (Fin 2) from v), r)
      ((show EuclideanSpace ℝ (Fin 2) from w), t) = _
    exact Metric.cylinderMetric_inner _ (y, s) _ _
  rw [PDE.RicciFlow.Perelman.KappaSolutions.riemannianVolumeMeasure_product_real_of_inner_eq
    h _ hp, cast_measure_apply
      (@BorelSpace.measurable_eq (S2 × ℝ) _ (@Prod.instMeasurableSpace S2 ℝ _ _) inferInstance)]
  rw [Measure.prod_prod, Real.volume_Icc]
  congr 1
  rw [volume_scale_apply]
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2 := by simp
  rw [hdim, ← ENNReal.ofReal_pow (Real.sqrt_nonneg _) 2, Real.sq_sqrt (by norm_num),
    riemannianVolumeMeasure_roundMetric_sphere_univ_eq, ← ENNReal.ofReal_mul (by norm_num)]
  congr 1
  ring

end DifferentialGeometry.Geometry.Measure
