import DifferentialGeometry.Analysis.ODE.LinearIntegralEquation
import DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.Semigroup.SobolevInclusion
import DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.Semigroup.TimeRegularity
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Duhamel.StrongBackwardIdentification

noncomputable section
open MeasureTheory Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Spectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
  {g : SmoothRiemannianMetric I M} {r s : ℕ} {a T : ℝ}

private theorem coeff_eq_integral_of_heat_equation
    (u : timeH1 (TensorHs g r s a) T)
    (U : timeL2 (TensorHs g r s (a + 2)) T)
    (hU : timeL2Inclusion (g := g) (r := r) (s := s)
      (show a ≤ a + 2 by linarith) U = timeH1.toTimeL2 _ T u)
    (heq : timeH1.timeDeriv _ T u = timeScaleLaplacian a U)
    (i : TensorEigenIdx g r s) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    (u.toFun t).coeff i = u.initial.coeff i +
      ∫ q in (0 : ℝ)..t, -TensorEigenIdx.lambda i * (u.toFun q).coeff i := by
  let x := strongCross U u hU
  have hmode : ∀ᵐ q ∂timeMeasure T,
      (u.deriv q).coeff i = -TensorEigenIdx.lambda i * x.coeffFun i q := by
    have hderiv : u.deriv = timeScaleLaplacian a U := heq
    have hDelta := timeScaleLaplacian_coeFn U
    filter_upwards [hDelta, x.ae_coeffFun_eq_hiL2] with q hq hx
    rw [hderiv, hq, tensorScaleLaplacian_coeff, hx i]
    rfl
  have hsub : Ioc (0 : ℝ) t ⊆ Icc (0 : ℝ) T :=
    fun q hq => ⟨hq.1.le, hq.2.trans ht.2⟩
  have hint : (∫ q in (0 : ℝ)..t, (u.deriv q).coeff i) =
      ∫ q in (0 : ℝ)..t, -TensorEigenIdx.lambda i * x.coeffFun i q := by
    rw [intervalIntegral.integral_of_le ht.1, intervalIntegral.integral_of_le ht.1]
    exact integral_congr_ae
      (ae_restrict_of_ae_restrict_of_subset (μ := volume) hsub hmode)
  have h := x.coeffFun_eq_integral i ht
  change (u.toFun t).coeff i = u.initial.coeff i +
    ∫ q in (0 : ℝ)..t, (u.deriv q).coeff i at h
  rw [hint] at h
  exact h

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear
end

noncomputable section
open MeasureTheory Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Spectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
  {g : SmoothRiemannianMetric I M} {r s : ℕ} {a T : ℝ}

theorem strongPair_toFun_eq_heatSemigroup
    (u : timeH1 (TensorHs g r s a) T)
    (U : timeL2 (TensorHs g r s (a + 2)) T)
    (hU : timeL2Inclusion (g := g) (r := r) (s := s)
      (show a ≤ a + 2 by linarith) U = timeH1.toTimeL2 _ T u)
    (heq : timeH1.timeDeriv _ T u = timeScaleLaplacian a U)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    u.toFun t = tensorHeatSemigroupHsExt (I := I) (M := M) g r s a t u.initial := by
  apply TensorHs.ext
  funext i
  rw [tensorHeatSemigroupHsExt_coeff ht.1]
  apply DifferentialGeometry.Analysis.ODE.eq_exp_mul_of_integral_eq (ht.1.trans ht.2)
    (f := fun q => (u.toFun q).coeff i)
  · exact (strongCross U u hU).continuousOn_coeffFun i
  · exact fun q hq => coeff_eq_integral_of_heat_equation u U hU heq i hq
  · exact ht

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear
end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
open scoped Manifold ContDiff

namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear

open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Spectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
  {g : SmoothRiemannianMetric I M} {r s : ℕ} {a T : ℝ}

theorem strongPair_tensorHeatSemigroupHs_inclusion
    (u : timeH1 (TensorHs g r s a) T)
    (U : timeL2 (TensorHs g r s (a + 2)) T)
    (hU : timeL2Inclusion (g := g) (r := r) (s := s)
      (show a ≤ a + 2 by linarith) U = timeH1.toTimeL2 _ T u)
    (heq : timeH1.timeDeriv _ T u = timeScaleLaplacian a U)
    {b t : ℝ} (hab : a ≤ b) (ht : 0 < t) (htT : t ≤ T) :
    tensorHsInclusion hab
        (tensorHeatSemigroupHs (g := g) (r := r) (s := s) ht
          (a := a) (b := b) u.initial) = u.toFun t := by
  rw [tensorHsInclusion_tensorHeatSemigroupHs,
    ← tensorHeatSemigroupHsExt_of_pos ht]
  exact (strongPair_toFun_eq_heatSemigroup u U hU heq ⟨ht.le, htT⟩).symm

theorem strongPair_field_eq_heatSemigroup_ae
    (u : timeH1 (TensorHs g r s a) T)
    (U : timeL2 (TensorHs g r s (a + 2)) T)
    (hU : timeL2Inclusion (g := g) (r := r) (s := s)
      (show a ≤ a + 2 by linarith) U = timeH1.toTimeL2 _ T u)
    (heq : timeH1.timeDeriv _ T u = timeScaleLaplacian a U) :
    ∀ᵐ t ∂timeMeasure T, ∀ ht : 0 < t,
      U t = tensorHeatSemigroupHs (g := g) (r := r) (s := s) ht
        (a := a) (b := a + 2) u.initial := by
  let x := strongCross U u hU
  filter_upwards [x.link, ae_restrict_mem measurableSet_Icc] with t hlink hmem ht
  apply tensorHsInclusion_injective (show a ≤ a + 2 by linarith)
  change tensorHsInclusion _ (U t) = _ at hlink ⊢
  rw [hlink]
  exact (strongPair_tensorHeatSemigroupHs_inclusion u U hU heq
    (show a ≤ a + 2 by linarith) ht hmem.2).symm

theorem strongPair_exists_sobolev_smoothing
    (u : timeH1 (TensorHs g r s a) T)
    (U : timeL2 (TensorHs g r s (a + 2)) T)
    (hU : timeL2Inclusion (g := g) (r := r) (s := s)
      (show a ≤ a + 2 by linarith) U = timeH1.toTimeL2 _ T u)
    (heq : timeH1.timeDeriv _ T u = timeScaleLaplacian a U)
    {b t : ℝ} (hab : a ≤ b) (ht : 0 < t) (htT : t ≤ T) (ht1 : t ≤ 1) :
    ∃ V : TensorHs g r s b,
      V = tensorHeatSemigroupHs (g := g) (r := r) (s := s) ht
        (a := a) (b := b) u.initial ∧
      tensorHsInclusion hab V = u.toFun t ∧
      ‖V‖ ≤ Real.sqrt (tensorSmoothingConst (b - a)) *
        t ^ (-((b - a) / 2)) * ‖u.initial‖ := by
  refine ⟨tensorHeatSemigroupHs ht u.initial, rfl,
    strongPair_tensorHeatSemigroupHs_inclusion u U hU heq hab ht htT, ?_⟩
  exact ((tensorHeatSemigroupHs ht).le_opNorm u.initial).trans
    (mul_le_mul_of_nonneg_right (tensorHeatSemigroupHs_opNorm_le hab ht ht1)
      (norm_nonneg _))

theorem strongPair_hasDerivAt
    (u : timeH1 (TensorHs g r s a) T)
    (U : timeL2 (TensorHs g r s (a + 2)) T)
    (hU : timeL2Inclusion (g := g) (r := r) (s := s)
      (show a ≤ a + 2 by linarith) U = timeH1.toTimeL2 _ T u)
    (heq : timeH1.timeDeriv _ T u = timeScaleLaplacian a U)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    HasDerivAt u.toFun
      (tensorScaleLaplacian a
        (tensorHeatSemigroupHs (g := g) (r := r) (s := s) ht.1
          (a := a) (b := a + 2) u.initial)) t := by
  have hsemigroup := hasDerivAt_tensorHeatSemigroupHsExt_eq_tensorScaleLaplacian
    (I := I) (M := M) g r s ht.1 u.initial
  apply hsemigroup.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with q hq
  exact strongPair_toFun_eq_heatSemigroup u U hU heq ⟨hq.1.le, hq.2.le⟩

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear
end
