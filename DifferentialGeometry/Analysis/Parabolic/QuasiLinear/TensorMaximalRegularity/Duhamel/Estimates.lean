import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Solution.TimeSupremumTrace

noncomputable section

open Bundle MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace NNReal

namespace DifferentialGeometry.Analysis.Parabolic

open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Spectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M]
  [SigmaCompactSpace M]

variable {g₀ : SmoothRiemannianMetric I M}

omit [BoundarylessManifold I M] in
theorem timeL2Inclusion_maximalRegularityDuhamelSolutionField {a : ℝ} {T : ℝ}
    (hT : 0 < T) (hT1 : T ≤ 1) {r s : ℕ}
    (u₀ : TensorHs (I := I) (M := M) g₀ r s (a + 2))
    (gforce : timeL2 (TensorHs (I := I) (M := M) g₀ r s a) T) :
    timeL2Inclusion (I := I) (M := M) (g := g₀) (r := r) (s := s)
        (show a + 1 ≤ a + 2 by linarith)
        (maximalRegularityDuhamelSolutionField (I := I) (M := M) (g := g₀) (r := r) (s := s)
          (T := T) a hT u₀ gforce) =
      maximalRegularityDuhamelSolutionFieldHa1 (I := I) (M := M) (g := g₀) (r := r) (s := s)
        (T := T) a hT u₀ gforce := by
  have h_compact := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ r s
  refine timeModeCoeff_injective (I := I) (M := M) h_compact (fun i => ?_)
  rw [timeModeCoeff_timeL2Inclusion (I := I) (M := M) (g := g₀) (r := r) (s := s)]
  rw [maximalRegularityDuhamelSolutionField, maximalRegularityDuhamelSolutionFieldHa1,
    timeModeCoeff_add (I := I) (M := M), timeModeCoeff_add (I := I) (M := M),
    maximalRegularityHomogeneousSolutionField_timeModeCoeff (I := I) (M := M) (a := a) (T := T) hT.le u₀ i,
    maximalRegularityHomogeneousSolutionFieldHa1_timeModeCoeff (I := I) (M := M) (a := a) (T := T) hT.le u₀ i,
    maximalRegularitySolutionField_timeModeCoeff (I := I) (M := M)
      (h_compact := h_compact) (a := a) hT.le gforce i,
    maximalRegularitySolutionFieldHa1_timeModeCoeff (I := I) (M := M)
      (h_compact := h_compact) (a := a) hT hT1 gforce i]

omit [BoundarylessManifold I M] in
theorem norm_maximalRegularityDuhamelSolutionField_zero_le {a : ℝ} {T : ℝ}
    (hT : 0 < T) {r s : ℕ}
    (F : timeL2 (TensorHs (I := I) (M := M) g₀ r s a) T) :
    ‖maximalRegularityDuhamelSolutionField (I := I) (M := M) (g := g₀) (r := r) (s := s)
        (T := T) a hT
        (0 : TensorHs (I := I) (M := M) g₀ r s (a + 2)) F‖ ≤ (1 + T) * ‖F‖ := by
  have h_compact := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ r s
  rw [maximalRegularityDuhamelSolutionField]
  refine le_trans (norm_add_le _ _) ?_
  have hhom : ‖maximalRegularityHomogeneousSolutionField (I := I) (M := M) a T
      (0 : TensorHs (I := I) (M := M) g₀ r s (a + 2))‖ ≤
      Real.sqrt T * ‖(0 : TensorHs (I := I) (M := M) g₀ r s (a + 2))‖ :=
    maximalRegularityHomogeneousSolutionField_norm_le (I := I) (M := M)
      (h_compact := h_compact) _ hT.le
  rw [norm_zero, mul_zero] at hhom
  have hreg : ‖maximalRegularitySolutionField (I := I) (M := M) a hT.le F‖ ≤
      (1 + T) * ‖F‖ :=
    maximalRegularitySolutionField_norm_le (I := I) (M := M)
      (h_compact := h_compact) hT.le F
  have hhom0 : ‖maximalRegularityHomogeneousSolutionField (I := I) (M := M) a T
      (0 : TensorHs (I := I) (M := M) g₀ r s (a + 2))‖ = 0 :=
    le_antisymm hhom (norm_nonneg _)
  rw [hhom0, zero_add]
  exact hreg

omit [BoundarylessManifold I M] in
theorem maximalRegularityDuhamelSolutionField_zero_zero {a : ℝ} {T : ℝ}
    (hT : 0 < T) {r s : ℕ} :
    maximalRegularityDuhamelSolutionField (I := I) (M := M) (g := g₀) (r := r) (s := s)
        (T := T) a hT
        (0 : TensorHs (I := I) (M := M) g₀ r s (a + 2))
        (0 : timeL2 (TensorHs (I := I) (M := M) g₀ r s a) T) = 0 := by
  have h := norm_maximalRegularityDuhamelSolutionField_zero_le (I := I) (M := M) (g₀ := g₀)
    hT (0 : timeL2 (TensorHs (I := I) (M := M) g₀ r s a) T)
  rw [norm_zero, mul_zero] at h
  exact norm_le_zero_iff.mp h

end DifferentialGeometry.Analysis.Parabolic

end
