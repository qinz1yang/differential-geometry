import DifferentialGeometry.Geometry.Neck.VolumeComparison
import DifferentialGeometry.Geometry.Measure.RoundCylinderVolume
import DifferentialGeometry.Geometry.Measure.OpenSubtypeVolume

noncomputable section

open Set Function TopologicalSpace Manifold MeasureTheory
open DifferentialGeometry DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Metric
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry.Geometry.Neck

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev S2 := Metric.sphere (0 : E3) 1
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)
private instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩
private instance {δ : ℝ} : MeasurableSpace (bufferedCylinder δ) := borel (bufferedCylinder δ)
private instance {δ : ℝ} : BorelSpace (bufferedCylinder δ) := ⟨rfl⟩
private instance {δ : ℝ} : SigmaCompactSpace (bufferedCylinder δ) :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen IC (bufferedCylinder δ).isOpen)
private instance : MeasurableSpace (S2 × ℝ) := borel (S2 × ℝ)
private instance : BorelSpace (S2 × ℝ) := ⟨rfl⟩

private theorem referenceMetric_negative_closed_band_volume (δ : ℝ) :
    riemannianVolumeMeasure IC (bufferedCylinder δ) (referenceMetric δ)
      {q | q.val.2 ∈ Icc (-δ⁻¹) (-1 : ℝ)} =
      ENNReal.ofReal (8 * Real.pi) * ENNReal.ofReal (δ⁻¹ - 1) := by
  have hS : MeasurableSet ((univ : Set S2) ×ˢ Icc (-δ⁻¹) (-1 : ℝ)) :=
    (isClosed_univ.prod isClosed_Icc).measurableSet
  have hfit : (univ : Set S2) ×ˢ Icc (-δ⁻¹) (-1 : ℝ) ⊆ bufferedCylinder δ := by
    intro q hq
    change -δ⁻¹ - 1 < q.2 ∧ q.2 < δ⁻¹ + 1
    constructor <;> linarith [hq.2.1, hq.2.2]
  have heq := DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_restrictOpen_preimage_of_subset
    (roundCylinderMetric (E := E3) (n := 2)) (bufferedCylinder δ) hS hfit
  have hset : (Subtype.val : bufferedCylinder δ → S2 × ℝ) ⁻¹'
      (univ ×ˢ Icc (-δ⁻¹) (-1 : ℝ)) = {q | q.val.2 ∈ Icc (-δ⁻¹) (-1 : ℝ)} := by
    ext q
    simp only [mem_preimage, mem_prod, mem_univ, true_and, mem_ofPred_eq]
  rw [hset] at heq
  change riemannianVolumeMeasure IC (bufferedCylinder δ)
    ((roundCylinderMetric (E := E3) (n := 2)).restrictOpen (bufferedCylinder δ)) _ = _
  rw [heq, DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_roundCylinder_interval]
  congr 2
  ring

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [SigmaCompactSpace M]
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

namespace normalizedDatum

variable {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}

theorem negative_closed_band_volume_ge (d : normalizedDatum g x₀ δ k) (hδ : δ ≤ 1 / 4) :
    ENNReal.ofReal (2 * Real.pi / δ) * ENNReal.ofReal ((metricScalarAt g x₀) ^ (-3 / 2 : ℝ)) ≤
      riemannianVolumeMeasure I M g (d.map ''
        {q : bufferedCylinder δ | q.val.2 ∈ Icc (-δ⁻¹) (-1 : ℝ)}) := by
  have hS : MeasurableSet {q : bufferedCylinder δ | q.val.2 ∈ Icc (-δ⁻¹) (-1 : ℝ)} :=
    isClosed_Icc.measurableSet.preimage (continuous_snd.comp continuous_subtype_val).measurable
  have hcontrol : {q : bufferedCylinder δ | q.val.2 ∈ Icc (-δ⁻¹) (-1 : ℝ)} ⊆
      controlledCylinder δ := by
    intro q hq
    exact ⟨hq.1, hq.2.trans (by linarith [inv_pos.mpr d.precision_pos])⟩
  have hv := d.volume_image_ge hS hcontrol
  have href := referenceMetric_negative_closed_band_volume δ
  change riemannianVolumeMeasure IC (bufferedCylinder δ)
    ((roundCylinderMetric (E := E3) (n := 2)).restrictOpen (bufferedCylinder δ)) _ = _ at href
  rw [href] at hv
  have hh : 1 / 2 ≤ (1 - δ) ^ (3 / 2 : ℝ) := by
    rw [Real.rpow_div_two_eq_sqrt 3 (by linarith : 0 ≤ 1 - δ)]
    norm_num only [Real.rpow_ofNat]
    have hs : (4 / 5 : ℝ) ≤ Real.sqrt (1 - δ) :=
      (Real.le_sqrt (by norm_num) (by linarith)).mpr (by nlinarith)
    calc
      (1 / 2 : ℝ) ≤ (4 / 5 : ℝ) ^ 3 := by norm_num
      _ ≤ Real.sqrt (1 - δ) ^ 3 := pow_le_pow_left₀ (by norm_num) hs 3
  have hi : 4 ≤ δ⁻¹ := by
    rw [inv_eq_one_div]
    exact (le_div_iff₀ d.precision_pos).mpr (by linarith)
  have hl : (1 / 2 : ℝ) * δ⁻¹ ≤ δ⁻¹ - 1 := by linarith
  have hreal : 2 * Real.pi / δ ≤ (1 - δ) ^ (3 / 2 : ℝ) *
      (8 * Real.pi) * (δ⁻¹ - 1) := by
    have hc := mul_le_mul hh hl (by positivity)
      (Real.rpow_nonneg (by linarith : 0 ≤ 1 - δ) _)
    have hm := mul_le_mul_of_nonneg_left hc (show 0 ≤ 8 * Real.pi by positivity)
    calc
      2 * Real.pi / δ = (8 * Real.pi) * ((1 / 2) * ((1 / 2) * δ⁻¹)) := by ring
      _ ≤ (8 * Real.pi) * ((1 - δ) ^ (3 / 2 : ℝ) * (δ⁻¹ - 1)) := hm
      _ = _ := by ring
  calc
    _ ≤ ENNReal.ofReal ((1 - δ) ^ (3 / 2 : ℝ) * (8 * Real.pi) * (δ⁻¹ - 1)) *
        ENNReal.ofReal ((metricScalarAt g x₀) ^ (-3 / 2 : ℝ)) :=
      mul_le_mul' (ENNReal.ofReal_le_ofReal hreal) le_rfl
    _ = _ := by
      rw [ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg (by linarith) _) (by positivity)),
        ENNReal.ofReal_mul (Real.rpow_nonneg (by linarith) _)]
      ac_rfl
    _ ≤ _ := hv

end normalizedDatum
end DifferentialGeometry.Geometry.Neck
