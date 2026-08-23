import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.ZeroDuhamelCross
import DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.TimeL2InterpolationLimit

noncomputable section

open Bundle Manifold MeasureTheory Filter
open scoped Manifold Topology ContDiff ENNReal

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace QuasiLinear

open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Spectral

theorem memLp_clm_affine
    {T : ℝ} {X Y Z : Type*}
    [NormedAddCommGroup X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (u : timeL2 X T) (A : ℝ → Y →L[ℝ] Z)
    (hA : AEStronglyMeasurable A (timeMeasure T))
    {L Z₀ : ℝ} (hL : 0 ≤ L) (hZ₀ : 0 ≤ Z₀)
    (hbound : ∀ᵐ t ∂timeMeasure T, ‖A t‖ ≤ Z₀ + L * ‖u t‖) :
    ∃ hmem : MemLp A 2 (timeMeasure T),
      ‖hmem.toLp A‖ ≤ L * ‖u‖ + Real.sqrt T * Z₀ := by
  let U : ℝ → ℝ := fun t => ‖(u : ℝ → X) t‖
  let C : ℝ → ℝ := fun _ => Z₀
  have hU : MemLp U 2 (timeMeasure T) := by
    simpa only [U] using (Lp.memLp u).norm
  have hC : MemLp C 2 (timeMeasure T) := by
    simpa only [C] using (memLp_const (μ := timeMeasure T) Z₀)
  have hCU : MemLp (C + L • U) 2 (timeMeasure T) :=
    hC.add (hU.const_smul L)
  have hmajor :
      ∀ᵐ t ∂timeMeasure T, ‖A t‖ ≤ ‖(C + L • U) t‖ := by
    filter_upwards [hbound] with t ht
    have hnonneg : 0 ≤ Z₀ + L * ‖u t‖ :=
      add_nonneg hZ₀ (mul_nonneg hL (norm_nonneg _))
    simpa only [C, U, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Real.norm_eq_abs, abs_of_nonneg hnonneg] using ht
  let hmem : MemLp A 2 (timeMeasure T) := hCU.mono hA hmajor
  refine ⟨hmem, ?_⟩
  have hdom :
      ∀ᵐ t ∂timeMeasure T,
        ‖(hmem.toLp A) t‖ ≤ ‖(hCU.toLp (C + L • U)) t‖ := by
    filter_upwards [hmem.coeFn_toLp, hCU.coeFn_toLp, hmajor] with t hAt hCUt ht
    simpa only [hAt, hCUt] using ht
  have hCnorm : ‖hC.toLp C‖ = Real.sqrt T * Z₀ := by
    have heq :
        hC.toLp C = TimeSobolev.const T Z₀ := by
      unfold TimeSobolev.const
      apply MemLp.toLp_congr
      exact Filter.Eventually.of_forall (fun _ => rfl)
    rw [heq, TimeSobolev.norm_const, Real.norm_eq_abs, abs_of_nonneg hZ₀]
  have hUnorm : ‖hU.toLp U‖ = ‖u‖ := by
    rw [Lp.norm_toLp, Lp.norm_def]
    simp only [U, eLpNorm_norm]
  calc
    ‖hmem.toLp A‖ ≤ ‖hCU.toLp (C + L • U)‖ :=
      Lp.norm_le_norm_of_ae_le hdom
    _ = ‖hC.toLp C + L • hU.toLp U‖ := by
      rw [hC.toLp_add (hU.const_smul L), hU.toLp_const_smul]
    _ ≤ ‖hC.toLp C‖ + ‖L • hU.toLp U‖ := norm_add_le _ _
    _ = L * ‖u‖ + Real.sqrt T * Z₀ := by
      rw [hCnorm, norm_smul, Real.norm_eq_abs, abs_of_nonneg hL, hUnorm]
      ac_rfl

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem duhamel_incl
    {g : SmoothRiemannianMetric I M} {r s : ℕ} {a T : ℝ}
    (hT : 0 < T) (hT1 : T ≤ 1)
    (hcompact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (u₀ : tensorHs (I := I) (M := M) g r s (a + 2))
    (f : timeL2 (tensorHs (I := I) (M := M) g r s a) T) :
    timeL2Inclusion (I := I) (M := M) (g := g) (r := r) (s := s)
        (show a + 1 ≤ a + 2 by linarith)
        (maxRegDuhamelSolField (I := I) (M := M)
          a hT u₀ f) =
      maxRegDuhamelSolFieldHa1 (I := I) (M := M)
        a hT u₀ f := by
  refine timeModeCoeff_injective (I := I) (M := M) hcompact (fun i => ?_)
  rw [timeModeCoeff_timeL2Inclusion (I := I) (M := M),
    maxRegDuhamelSolField, maxRegDuhamelSolFieldHa1,
    timeModeCoeff_add (I := I) (M := M),
    timeModeCoeff_add (I := I) (M := M),
    maxRegHomogeneousSolField_timeModeCoeff (I := I) (M := M)
      (a := a) (T := T) hT.le u₀ i,
    maxRegHomogeneousSolFieldHa1_timeModeCoeff (I := I) (M := M)
      (a := a) (T := T) hT.le u₀ i,
    maximalRegularitySolField_timeModeCoeff (I := I) (M := M)
      (h_compact := hcompact) (a := a) hT.le f i,
    maximalRegularitySolFieldHa1_timeModeCoeff (I := I) (M := M)
      (h_compact := hcompact) (a := a) hT hT1 f i]

end QuasiLinear
end Parabolic
end Analysis
end DifferentialGeometry

end
