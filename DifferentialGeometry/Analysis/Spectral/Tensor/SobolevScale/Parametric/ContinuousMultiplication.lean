import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Scalar.ContinuousMultiplier
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Operator.Basic

noncomputable section

open MeasureTheory
open scoped ENNReal Manifold ContDiff

namespace DifferentialGeometry.Analysis.Spectral

open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (∞ : WithTop ℕ∞) M]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem exists_scalarH0_timeL2_mul (g : SmoothRiemannianMetric I M) {T : ℝ}
    (a : ℝ → C(M, ℝ)) (ha : AEStronglyMeasurable a (timeMeasure T))
    (C : NNReal) (hC : ∀ᵐ t ∂timeMeasure T, ‖a t‖ ≤ (C : ℝ)) :
    ∃ L : timeL2 (TensorHs g 0 0 0) T →L[ℝ] timeL2 (TensorHs g 0 0 0) T,
      ‖L‖ ≤ (C : ℝ) ∧
      ∀ W : timeL2 (TensorHs g 0 0 0) T,
        (L W =ᵐ[timeMeasure T] fun t => scalarH0ContinuousMul g (a t) (W t)) ∧
        (∀ᵐ t ∂timeMeasure T,
          scalarH0EquivLp g (L W t) =ᵐ[riemannianVolumeMeasure I M g]
            fun x => a t x * scalarH0EquivLp g (W t) x) ∧
        ‖L W‖ ≤ (C : ℝ) * ‖W‖ := by
  let A : ℝ → TensorHs g 0 0 0 →L[ℝ] TensorHs g 0 0 0 :=
    fun t => scalarH0ContinuousMul g (a t)
  have hA : AEStronglyMeasurable A (timeMeasure T) :=
    (scalarH0ContinuousMul g).continuous.comp_aestronglyMeasurable ha
  have hAb : ∀ᵐ t ∂timeMeasure T, ‖A t‖ ≤ (C : ℝ) := by
    filter_upwards [hC] with t ht
    exact ((scalarH0ContinuousMul g).le_opNorm (a t)).trans
      ((mul_le_mul_of_nonneg_right (norm_scalarH0ContinuousMul_le g) (norm_nonneg _)).trans
        (by simpa only [one_mul] using ht))
  let L := timeOp A hA C hAb
  have hL : ‖L‖ ≤ (C : ℝ) := timeOp_norm_le A hA C hAb
  refine ⟨L, hL, ?_⟩
  intro W
  have hLW : L W =ᵐ[timeMeasure T] fun t => A t (W t) := timeOp_apply_ae A hA C hAb W
  refine ⟨hLW, ?_, (L.le_opNorm W).trans (mul_le_mul_of_nonneg_right hL (norm_nonneg _))⟩
  filter_upwards [hLW] with t ht
  rw [ht]
  exact scalarH0EquivLp_scalarH0ContinuousMul g (a t) (W t)

end DifferentialGeometry.Analysis.Spectral
end
