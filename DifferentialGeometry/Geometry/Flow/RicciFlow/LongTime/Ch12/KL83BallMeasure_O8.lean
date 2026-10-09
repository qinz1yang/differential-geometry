import DifferentialGeometry.Analysis.Integration.Measure.NormalizedHausdorffMeasure
import DifferentialGeometry.Geometry.Comparison.Volume.Model
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# CH12-O8, package P4b: Lipschitz images of Euclidean balls bound the Hausdorff volume

If `f` is `K`-Lipschitz on `s` with values in `ℝ³` and `f '' s ⊇ B(v, ρ)`, then the normalized
three-dimensional Hausdorff measure of `s` is at least `ω₃ ρ³ / K³`.
-/

set_option autoImplicit false

noncomputable section

open Set Metric MeasureTheory
open scoped NNReal ENNReal
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison

namespace GC.LongTime.Ch12

theorem volume_euclidean_ball_three_O8 (v : EuclideanSpace ℝ (Fin 3)) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    volume (ball v ρ) = ENNReal.ofReal (euclideanUnitBallVolume 3 * ρ ^ 3) := by
  rw [EuclideanSpace.volume_ball, Fintype.card_fin]
  have hω : 0 ≤ euclideanUnitBallVolume 3 := by
    unfold euclideanUnitBallVolume
    exact div_nonneg (by positivity) (Real.Gamma_nonneg_of_nonneg (by positivity))
  rw [ENNReal.ofReal_mul hω, ← ENNReal.ofReal_pow hρ, mul_comm]
  congr 2

theorem ball_le_normalizedHausdorffMeasure_three_O8
    {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {f : X → EuclideanSpace ℝ (Fin 3)} {s : Set X} {K : ℝ≥0}
    (hf : LipschitzOnWith K f s) (hK : 0 < K)
    {v : EuclideanSpace ℝ (Fin 3)} {ρ : ℝ} (hρ : 0 ≤ ρ) (himage : ball v ρ ⊆ f '' s) :
    ENNReal.ofReal (euclideanUnitBallVolume 3 * ρ ^ 3) / (K : ℝ≥0∞) ^ 3 ≤
      normalizedHausdorffMeasure 3 s := by
  have h := (measure_mono (μ := normalizedHausdorffMeasure 3) himage).trans
    (normalizedHausdorffMeasure_image_le hf 3)
  rw [normalizedHausdorffMeasure_euclidean, volume_euclidean_ball_three_O8 v hρ] at h
  apply (ENNReal.div_le_iff_le_mul (Or.inl (pow_ne_zero _ (by exact_mod_cast hK.ne')))
    (Or.inl (ENNReal.pow_ne_top ENNReal.coe_ne_top))).mpr
  simpa only [mul_comm] using h

end GC.LongTime.Ch12
