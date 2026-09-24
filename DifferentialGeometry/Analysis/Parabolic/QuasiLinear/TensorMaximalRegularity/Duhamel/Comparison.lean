import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Duhamel.StrongBackwardIdentification
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Duhamel.Estimates
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Parametric.ContinuousMultiplication
import DifferentialGeometry.Analysis.Parabolic.TensorHeat.Duhamel.ConstantSource

noncomputable section
open scoped Manifold ContDiff

namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear

open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Spectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
  {g : SmoothRiemannianMetric I M} {r s : ℕ} {a T : ℝ}

theorem maximalRegularityDuhamelMap_caloric_comparison (hT : 0 < T)
    (u : timeH1 (TensorHs g r s a) T)
    (U : timeL2 (TensorHs g r s (a + 2)) T)
    (hU : timeL2Inclusion (g := g) (r := r) (s := s)
      (show a ≤ a + 2 by linarith) U = timeH1.toTimeL2 _ T u) :
    let F := timeH1.timeDeriv _ T u - timeScaleLaplacian a U
    let v := maximalRegularityDuhamelMap a hT (0 : TensorHs g r s (a + 2)) F
    let V := maximalRegularityDuhamelSolutionField a hT (0 : TensorHs g r s (a + 2)) F
    timeH1.trace0 _ T v = 0 ∧
      timeL2Inclusion (g := g) (r := r) (s := s)
        (show a ≤ a + 2 by linarith) V = timeH1.toTimeL2 _ T v ∧
      ‖V‖ ≤ (1 + T) * ‖F‖ ∧
      timeH1.timeDeriv _ T v = timeScaleLaplacian a V + F ∧
      timeL2Inclusion (g := g) (r := r) (s := s)
        (show a ≤ a + 2 by linarith) (U - V) = timeH1.toTimeL2 _ T (u - v) ∧
      timeH1.timeDeriv _ T (u - v) = timeScaleLaplacian a (U - V) := by
  dsimp
  let F := timeH1.timeDeriv _ T u - timeScaleLaplacian a U
  let v := maximalRegularityDuhamelMap a hT (0 : TensorHs g r s (a + 2)) F
  let V := maximalRegularityDuhamelSolutionField a hT (0 : TensorHs g r s (a + 2)) F
  have hc := tensorResolventL2_isCompactOperator (I := I) (M := M) g r s
  have hV : timeL2Inclusion (g := g) (r := r) (s := s)
      (show a ≤ a + 2 by linarith) V = timeH1.toTimeL2 _ T v :=
    duhamelField_pin hT hc (0 : TensorHs g r s (a + 2)) F
  have hv : timeH1.timeDeriv _ T v = timeScaleLaplacian a V + F :=
    maximalRegularityDuhamelMap_timeDeriv_eq hT hc
      (0 : TensorHs g r s (a + 2)) F
  refine ⟨?_, hV, ?_, hv, ?_, ?_⟩
  · change timeH1.trace0 _ T v = 0
    simpa only [map_zero] using maximalRegularityDuhamelMap_trace0 hT
      (0 : TensorHs g r s (a + 2)) F
  · exact norm_maximalRegularityDuhamelSolutionField_zero_le hT F
  · change timeL2Inclusion (g := g) (r := r) (s := s)
        (show a ≤ a + 2 by linarith) (U - V) = timeH1.toTimeL2 _ T (u - v)
    rw [map_sub, map_sub, hU, hV]
  · change timeH1.timeDeriv _ T (u - v) = timeScaleLaplacian a (U - V)
    rw [map_sub, hv, map_sub]
    dsimp only [F]
    abel

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear
end

noncomputable section
open MeasureTheory
open scoped Manifold ContDiff NNReal

namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear

open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Spectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
  {g : SmoothRiemannianMetric I M} {T : ℝ}

theorem exists_heat_comparison_of_coefficient_oscillation (hT : 0 < T)
    (u : timeH1 (TensorHs g 0 0 0) T)
    (U : timeL2 (TensorHs g 0 0 ((0 : ℝ) + 2)) T)
    (hU : timeL2Inclusion (g := g) (r := 0) (s := 0)
      (show (0 : ℝ) ≤ 0 + 2 by norm_num) U = timeH1.toTimeL2 _ T u)
    (a : ℝ → C(M, ℝ)) (ha : AEStronglyMeasurable a (timeMeasure T))
    (B : NNReal) (hB : ∀ᵐ t ∂timeMeasure T, ‖a t - 1‖ ≤ (B : ℝ))
    (R : timeL2 (TensorHs g 0 0 0) T)
    (heq : u.deriv =ᵐ[timeMeasure T] fun t =>
      scalarH0ContinuousMul g (a t) (tensorScaleLaplacian 0 (U t)) + R t) :
    ∃ F : timeL2 (TensorHs g 0 0 0) T,
      (F =ᵐ[timeMeasure T] fun t =>
        scalarH0ContinuousMul g (a t - 1) (tensorScaleLaplacian 0 (U t)) + R t) ∧
      ‖F‖ ≤ (B : ℝ) * ‖timeScaleLaplacian 0 U‖ + ‖R‖ ∧
      let v := maximalRegularityDuhamelMap 0 hT (0 : TensorHs g 0 0 ((0 : ℝ) + 2)) F
      let V := maximalRegularityDuhamelSolutionField 0 hT
        (0 : TensorHs g 0 0 ((0 : ℝ) + 2)) F
      timeH1.trace0 _ T v = 0 ∧
        timeL2Inclusion (g := g) (r := 0) (s := 0)
          (show (0 : ℝ) ≤ 0 + 2 by norm_num) V = timeH1.toTimeL2 _ T v ∧
        ‖V‖ ≤ (1 + T) * ((B : ℝ) * ‖timeScaleLaplacian 0 U‖ + ‖R‖) ∧
        timeH1.timeDeriv _ T v = timeScaleLaplacian 0 V + F ∧
        timeL2Inclusion (g := g) (r := 0) (s := 0)
          (show (0 : ℝ) ≤ 0 + 2 by norm_num) (U - V) = timeH1.toTimeL2 _ T (u - v) ∧
        timeH1.timeDeriv _ T (u - v) = timeScaleLaplacian 0 (U - V) := by
  let W := timeScaleLaplacian 0 U
  obtain ⟨L, _, hL⟩ := exists_scalarH0_timeL2_mul g (fun t => a t - 1)
    (ha.sub aestronglyMeasurable_const) B hB
  let F := L W + R
  have hW : W =ᵐ[timeMeasure T] fun t => tensorScaleLaplacian 0 (U t) :=
    timeScaleLaplacian_coeFn U
  have hF : F =ᵐ[timeMeasure T] fun t =>
      scalarH0ContinuousMul g (a t - 1) (tensorScaleLaplacian 0 (U t)) + R t := by
    filter_upwards [Lp.coeFn_add (L W) R, (hL W).1, hW] with t ht htL htW
    rw [ht, Pi.add_apply, htL, htW]
  have hFnorm : ‖F‖ ≤ (B : ℝ) * ‖W‖ + ‖R‖ :=
    (norm_add_le _ _).trans (add_le_add (hL W).2.2 le_rfl)
  have hone (S : TensorHs g 0 0 0) : scalarH0ContinuousMul g 1 S = S := by
    rw [show (1 : C(M, ℝ)) = ContinuousMap.const M 1 from by ext; rfl]
    simpa only [one_smul] using scalarH0ContinuousMul_const g 1 S
  have hderiv : timeH1.timeDeriv _ T u = W + F := by
    apply Lp.ext
    filter_upwards [heq, hW, hF, Lp.coeFn_add W F] with t ht htW htF htAdd
    change u.deriv t = _
    rw [ht, htAdd, Pi.add_apply, htW, htF, map_sub, sub_apply, hone]
    abel
  have hres : timeH1.timeDeriv _ T u - timeScaleLaplacian 0 U = F := by
    rw [hderiv]
    change W + F - W = F
    abel
  have hcomp := maximalRegularityDuhamelMap_caloric_comparison hT u U hU
  dsimp only at hcomp
  rw [hres] at hcomp
  obtain ⟨hzero, hpin, hnorm, hpde, hsubpin, hsubpde⟩ := hcomp
  refine ⟨F, hF, hFnorm, hzero, hpin, ?_, hpde, hsubpin, hsubpde⟩
  exact hnorm.trans (mul_le_mul_of_nonneg_left hFnorm (by linarith))

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear
end

noncomputable section
open MeasureTheory
open scoped Manifold ContDiff NNReal

namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear

open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Sobolev

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]
  {g : SmoothRiemannianMetric I M} {T : ℝ}

theorem exists_heat_comparison_sub_constant_source (hT : 0 < T)
    (u : timeH1 (TensorHs g 0 0 0) T)
    (U : timeL2 (TensorHs g 0 0 ((0 : ℝ) + 2)) T)
    (hU : timeL2Inclusion (g := g) (r := 0) (s := 0)
      (show (0 : ℝ) ≤ 0 + 2 by norm_num) U = timeH1.toTimeL2 _ T u)
    (a : ℝ → C(M, ℝ)) (ha : AEStronglyMeasurable a (timeMeasure T))
    (B : NNReal) (hB : ∀ᵐ t ∂timeMeasure T, ‖a t - 1‖ ≤ (B : ℝ))
    (f : timeL2 (TensorHs g 0 0 0) T) (f₀ : ℝ)
    (heq : u.deriv =ᵐ[timeMeasure T] fun t =>
      scalarH0ContinuousMul g (a t) (tensorScaleLaplacian 0 (U t)) + f t) :
    let h := constantHeatResponse g 0 T f₀
    let H := constantHeatResponseField g 0 T f₀
    let fconstant := timeH1.timeDeriv _ T h
    ∃ F : timeL2 (TensorHs g 0 0 0) T,
      (F =ᵐ[timeMeasure T] fun t =>
        scalarH0ContinuousMul g (a t - 1) (tensorScaleLaplacian 0 (U t)) +
          (f - fconstant) t) ∧
      ‖F‖ ≤ (B : ℝ) * ‖timeScaleLaplacian 0 U‖ + ‖f - fconstant‖ ∧
      let v := maximalRegularityDuhamelMap 0 hT (0 : TensorHs g 0 0 ((0 : ℝ) + 2)) F
      let V := maximalRegularityDuhamelSolutionField 0 hT
        (0 : TensorHs g 0 0 ((0 : ℝ) + 2)) F
      timeH1.trace0 _ T v = 0 ∧
        timeL2Inclusion (g := g) (r := 0) (s := 0)
          (show (0 : ℝ) ≤ 0 + 2 by norm_num) V = timeH1.toTimeL2 _ T v ∧
        ‖V‖ ≤ (1 + T) * ((B : ℝ) * ‖timeScaleLaplacian 0 U‖ + ‖f - fconstant‖) ∧
        timeH1.timeDeriv _ T v = timeScaleLaplacian 0 V + F ∧
        timeL2Inclusion (g := g) (r := 0) (s := 0)
          (show (0 : ℝ) ≤ 0 + 2 by norm_num) (U - V - H) =
            timeH1.toTimeL2 _ T (u - v - h) ∧
        timeH1.timeDeriv _ T (u - v - h) = timeScaleLaplacian 0 (U - V - H) := by
  let h := constantHeatResponse g 0 T f₀
  let H := constantHeatResponseField g 0 T f₀
  let fconstant := timeH1.timeDeriv _ T h
  let u' := u - h
  let U' := U - H
  have hH : timeL2Inclusion (g := g) (r := 0) (s := 0)
      (show (0 : ℝ) ≤ 0 + 2 by norm_num) H = timeH1.toTimeL2 _ T h :=
    constantHeatResponseField_inclusion g 0 T f₀
  have hHzero : timeScaleLaplacian 0 H = 0 := constantHeatResponseField_laplacian g 0 T f₀
  have hU' : timeL2Inclusion (g := g) (r := 0) (s := 0)
      (show (0 : ℝ) ≤ 0 + 2 by norm_num) U' = timeH1.toTimeL2 _ T u' := by
    change timeL2Inclusion _ (U - H) = timeH1.toTimeL2 _ T (u - h)
    rw [map_sub, map_sub, hU, hH]
  have hLap : timeScaleLaplacian 0 U' = timeScaleLaplacian 0 U := by
    change timeScaleLaplacian 0 (U - H) = _
    rw [map_sub, hHzero, sub_zero]
  have hpoint : (fun t => tensorScaleLaplacian 0 (U' t)) =ᵐ[timeMeasure T]
      fun t => tensorScaleLaplacian 0 (U t) := by
    have hleft := timeScaleLaplacian_coeFn U'
    have hright := timeScaleLaplacian_coeFn U
    rw [hLap] at hleft
    exact hleft.symm.trans hright
  have hu'deriv : u'.deriv = u.deriv - fconstant := rfl
  have heq' : u'.deriv =ᵐ[timeMeasure T] fun t =>
      scalarH0ContinuousMul g (a t) (tensorScaleLaplacian 0 (U' t)) + (f - fconstant) t := by
    rw [hu'deriv]
    filter_upwards [Lp.coeFn_sub u.deriv fconstant, heq, hpoint,
      Lp.coeFn_sub f fconstant] with t ht htEq htPoint htF
    rw [ht, Pi.sub_apply, htEq, htPoint, htF, Pi.sub_apply]
    abel
  obtain ⟨F, hF, hFnorm, hzero, hpin, hnorm, hpde, hsubpin, hsubpde⟩ :=
    exists_heat_comparison_of_coefficient_oscillation hT u' U' hU' a ha B hB
      (f - fconstant) heq'
  have hF' : F =ᵐ[timeMeasure T] fun t =>
      scalarH0ContinuousMul g (a t - 1) (tensorScaleLaplacian 0 (U t)) + (f - fconstant) t := by
    filter_upwards [hF, hpoint] with t ht htPoint
    rw [ht, htPoint]
  rw [hLap] at hFnorm hnorm
  refine ⟨F, hF', hFnorm, hzero, hpin, hnorm, hpde, ?_, ?_⟩
  · convert hsubpin using 1 <;> dsimp only [u', U'] <;> congr 1 <;> abel
  · convert hsubpde using 1 <;> dsimp only [u', U'] <;> congr 1 <;> abel

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear
end
