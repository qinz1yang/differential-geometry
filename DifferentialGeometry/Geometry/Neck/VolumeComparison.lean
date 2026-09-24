import DifferentialGeometry.Geometry.Neck.InsertionChart
import DifferentialGeometry.Geometry.Measure.MetricComparison
import DifferentialGeometry.Geometry.Measure.LocalIsometry
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Scaling
import DifferentialGeometry.Topology.SigmaCompactOpen

noncomputable section

open Set Function TopologicalSpace Manifold MeasureTheory
open DifferentialGeometry DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Metric
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry.Geometry.Neck

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)
private instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩
private instance {B : ℝ} : MeasurableSpace (openCylinder B) := borel (openCylinder B)
private instance {B : ℝ} : BorelSpace (openCylinder B) := ⟨rfl⟩
private instance {δ : ℝ} : MeasurableSpace (bufferedCylinder δ) := borel (bufferedCylinder δ)
private instance {δ : ℝ} : BorelSpace (bufferedCylinder δ) := ⟨rfl⟩
private instance {δ : ℝ} : SigmaCompactSpace (bufferedCylinder δ) :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen IC (bufferedCylinder δ).isOpen)
private instance {B : ℝ} : SigmaCompactSpace (openCylinder B) :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen IC (openCylinder B).isOpen)

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [SigmaCompactSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩
private local instance (U : Opens M) : MeasurableSpace U := borel U
private local instance (U : Opens M) : BorelSpace U := ⟨rfl⟩

namespace normalizedDatum

variable {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}

theorem volume_controlled_image_eq (d : normalizedDatum g x₀ δ k)
    {S : Set (openCylinder δ⁻¹)} (hS : MeasurableSet S) :
    riemannianVolumeMeasure I M g (d.controlledMap '' S) =
      ENNReal.ofReal (Real.sqrt (metricScalarAt g x₀)⁻¹) ^ 3 *
        riemannianVolumeMeasure IC (openCylinder δ⁻¹) d.controlledMetric S := by
  let h := scaleMetric (metricScalarAt g x₀)⁻¹ (inv_pos.mpr d.scalar_pos) d.controlledMetric
  have hm (q : openCylinder δ⁻¹) (v w : TangentSpace IC q) :
      h.inner q v w = g.inner (d.controlledMap q)
        (mfderiv IC I d.controlledMap q v) (mfderiv IC I d.controlledMap q w) := by
    change (metricScalarAt g x₀)⁻¹ * d.controlledMetric.inner q v w = _
    rw [d.controlledMetric_inner, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt d.scalar_pos), one_mul]
  have heq := DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_image_eq_of_injective_local_isometry
    h g d.controlledMap d.controlledMap_isLocalDiffeomorph d.controlledMap_isOpenEmbedding.injective hm hS
  rw [← heq, volume_scale_apply]
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ) = 3 := by simp
  rw [hdim]

theorem volume_image_eq (d : normalizedDatum g x₀ δ k)
    {S : Set (bufferedCylinder δ)} (hS : MeasurableSet S) :
    riemannianVolumeMeasure I M g (d.map '' S) =
      ENNReal.ofReal (Real.sqrt (metricScalarAt g x₀)⁻¹) ^ 3 *
        riemannianVolumeMeasure IC (bufferedCylinder δ) d.normalizedMetric S := by
  let h := scaleMetric (metricScalarAt g x₀)⁻¹ (inv_pos.mpr d.scalar_pos) d.normalizedMetric
  have hm (q : bufferedCylinder δ) (v w : TangentSpace IC q) :
      h.inner q v w = g.inner (d.map q)
        (mfderiv IC I d.map q v) (mfderiv IC I d.map q w) := by
    change (metricScalarAt g x₀)⁻¹ * d.normalizedMetric.inner q v w = _
    rw [d.normalizedMetric_inner, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt d.scalar_pos), one_mul]
  have hlocal : IsLocalDiffeomorph IC I ∞ d.map :=
    DifferentialGeometry.Topology.Manifold.isLocalDiffeomorph_of_injective_mfderiv d.map d.smooth d.immersion
      (by rw [show Module.finrank ℝ E = 3 from Fact.out]; simp)
  have heq := DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_image_eq_of_injective_local_isometry
    h g d.map hlocal d.injective hm hS
  rw [← heq, volume_scale_apply]
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ) = 3 := by simp
  rw [hdim]

private theorem sqrt_cube_eq_rpow (c : ℝ) (hc : 0 ≤ c) :
    ENNReal.ofReal (Real.sqrt c) ^ 3 = ENNReal.ofReal (c ^ (3 / 2 : ℝ)) := by
  rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _) 3]
  congr 1
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast hc]
  congr 1
  ring

theorem volume_controlled_image_ge (d : normalizedDatum g x₀ δ k)
    {S : Set (openCylinder δ⁻¹)} (hS : MeasurableSet S) :
    ENNReal.ofReal ((metricScalarAt g x₀) ^ (-3 / 2 : ℝ)) *
      ENNReal.ofReal ((1 - δ) ^ (3 / 2 : ℝ)) *
        riemannianVolumeMeasure IC (openCylinder δ⁻¹)
          ((roundCylinderMetric (E := E3) (n := 2)).restrictOpen (openCylinder δ⁻¹)) S ≤
      riemannianVolumeMeasure I M g (d.controlledMap '' S) := by
  let g₀ := (roundCylinderMetric (E := E3) (n := 2)).restrictOpen (openCylinder δ⁻¹)
  have hpos : 0 < 1 - δ := sub_pos.mpr d.precision_lt_one
  have hinner (q : openCylinder δ⁻¹) (_ : q ∈ S) (v : TangentSpace IC q) :
      (scaleMetric (1 - δ) hpos g₀).inner q v v ≤ 1 * d.controlledMetric.inner q v v := by
    rw [scaleMetric_inner, one_mul]
    exact (inner_bounds_of_metricDerivENormSupOn_lt g₀ d.controlledMetric
      d.controlledMetric_error_lt (mem_univ q) v).1
  have hb := DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_apply_le_of_inner_le
    d.controlledMetric (scaleMetric (1 - δ) hpos g₀) zero_lt_one hS hinner
  rw [volume_scale_apply] at hb
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ) = 3 := by simp
  rw [hdim, sqrt_cube_eq_rpow (1 - δ) hpos.le] at hb
  simp only [one_pow, Real.sqrt_one, ENNReal.ofReal_one, one_mul] at hb
  rw [volume_controlled_image_eq d hS, sqrt_cube_eq_rpow _ (inv_nonneg.mpr d.scalar_pos.le)]
  have hscale : (metricScalarAt g x₀)⁻¹ ^ (3 / 2 : ℝ) =
      (metricScalarAt g x₀) ^ (-3 / 2 : ℝ) := by
    rw [← Real.rpow_neg_eq_inv_rpow]
    congr 1
    ring
  rw [hscale, mul_assoc]
  exact mul_le_mul' le_rfl hb


theorem volume_image_ge (d : normalizedDatum g x₀ δ k)
    {S : Set (bufferedCylinder δ)} (hS : MeasurableSet S) (hcontrol : S ⊆ controlledCylinder δ) :
    ENNReal.ofReal ((metricScalarAt g x₀) ^ (-3 / 2 : ℝ)) *
      ENNReal.ofReal ((1 - δ) ^ (3 / 2 : ℝ)) *
        riemannianVolumeMeasure IC (bufferedCylinder δ)
          ((roundCylinderMetric (E := E3) (n := 2)).restrictOpen (bufferedCylinder δ)) S ≤
      riemannianVolumeMeasure I M g (d.map '' S) := by
  let g₀ := (roundCylinderMetric (E := E3) (n := 2)).restrictOpen (bufferedCylinder δ)
  have hpos : 0 < 1 - δ := sub_pos.mpr d.precision_lt_one
  have hinner (q : bufferedCylinder δ) (hq : q ∈ S) (v : TangentSpace IC q) :
      (scaleMetric (1 - δ) hpos g₀).inner q v v ≤ 1 * d.normalizedMetric.inner q v v := by
    rw [scaleMetric_inner, one_mul]
    exact (inner_bounds_of_metricDerivENormSupOn_lt g₀ d.normalizedMetric
      d.normalizedMetric_error_lt (hcontrol hq) v).1
  have hb := DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_apply_le_of_inner_le
    d.normalizedMetric (scaleMetric (1 - δ) hpos g₀) zero_lt_one hS hinner
  rw [volume_scale_apply] at hb
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ) = 3 := by simp
  rw [hdim, sqrt_cube_eq_rpow (1 - δ) hpos.le] at hb
  simp only [one_pow, Real.sqrt_one, ENNReal.ofReal_one, one_mul] at hb
  rw [volume_image_eq d hS, sqrt_cube_eq_rpow _ (inv_nonneg.mpr d.scalar_pos.le)]
  have hscale : (metricScalarAt g x₀)⁻¹ ^ (3 / 2 : ℝ) =
      (metricScalarAt g x₀) ^ (-3 / 2 : ℝ) := by
    rw [← Real.rpow_neg_eq_inv_rpow]
    congr 1
    ring
  rw [hscale, mul_assoc]
  exact mul_le_mul' le_rfl hb

end normalizedDatum
end DifferentialGeometry.Geometry.Neck
