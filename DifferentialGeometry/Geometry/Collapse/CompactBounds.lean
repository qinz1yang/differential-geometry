import DifferentialGeometry.Geometry.Collapse.CurvatureScale
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Properties
set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Collapse GC.Endpoint MeasureTheory
open scoped ENNReal
namespace DifferentialGeometry.Geometry.Collapse
universe u
theorem exists_radius_bound_of_volume_lower (W : CompactCarrier.{u}) (g : SmoothRiemannianMetric W.model W.Carrier)
    (w : ℝ) (hw : 0 < w) :
    ∃ R : ℝ, 0 < R ∧ ∀ (p : W.Carrier) (r : ℝ), 0 < r →
      ENNReal.ofReal (w * r ^ 3) ≤ ballVolume g p r → r ≤ R := by
  let μ := Integral.Measure.riemannianVolumeMeasure W.model W.Carrier g
  have : IsFiniteMeasure μ := Integral.Measure.riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g
  let V : ℝ := (μ Set.univ).toReal
  refine ⟨max 1 (V / w), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro p r hr hvol
  have htotal : ENNReal.ofReal (w * r ^ 3) ≤ μ Set.univ :=
    hvol.trans (measure_mono (Set.subset_univ _))
  have hreal := ENNReal.toReal_mono (measure_lt_top μ Set.univ).ne htotal
  rw [ENNReal.toReal_ofReal (mul_nonneg hw.le (pow_nonneg hr.le 3))] at hreal
  have hcube : r ^ 3 ≤ V / w := (le_div_iff₀ hw).mpr (by simpa [mul_comm, V] using hreal)
  by_cases hsmall : r ≤ 1
  · exact hsmall.trans (le_max_left _ _)
  · have hrone : 1 ≤ r := le_of_not_ge hsmall
    have hpow : r ≤ r ^ 3 := by nlinarith [sq_nonneg (r - 1)]
    exact hpow.trans (hcube.trans (le_max_right _ _))

end DifferentialGeometry.Geometry.Collapse
