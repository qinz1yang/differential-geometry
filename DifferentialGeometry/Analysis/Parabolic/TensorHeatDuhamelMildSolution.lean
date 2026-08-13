import DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.SemigroupTimeRegularity
import DifferentialGeometry.Analysis.Parabolic.AbstractSemigroup.AbstractSpectralDuhamel
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.Semigroup.DuhamelMap
import DifferentialGeometry.Analysis.Calculus.HilbertBasisDerivative

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

namespace TensorHeatEquation

def tensorHeatMildSolutionHs
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (σ : ℝ)
    (T₀ : tensorHs (I := I) (M := M) g r s σ)
    (F : ℝ → tensorHs (I := I) (M := M) g r s σ) (t : ℝ) :
    tensorHs (I := I) (M := M) g r s σ :=
  duhamel (tensorHsBoundedC0Semigroup (I := I) (M := M) g r s σ) T₀ F t

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorHeatMildSolutionHs_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (σ : ℝ)
    (T₀ : tensorHs (I := I) (M := M) g r s σ)
    (F : ℝ → tensorHs (I := I) (M := M) g r s σ) (t : ℝ) :
    tensorHeatMildSolutionHs (I := I) (M := M) g r s σ T₀ F t =
      tensorHeatSemigroupHsExt (I := I) (M := M) g r s σ t T₀ +
        ∫ τ in (0 : ℝ)..t,
          tensorHeatSemigroupHsExt (I := I) (M := M) g r s σ (t - τ) (F τ) :=
  rfl

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorHeatMildSolutionHs_eq_abstractSpectralDuhamel
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (σ : ℝ)
    (T₀ : tensorHs (I := I) (M := M) g r s σ)
    (F : ℝ → tensorHs (I := I) (M := M) g r s σ)
    {t : ℝ} (ht : 0 ≤ t) :
    tensorHeatMildSolutionHs (I := I) (M := M) g r s σ T₀ F t =
      abstractSpectralDuhamel
        (tensorHsHilbertBasis (I := I) (M := M)
          (g := g) (r := r) (s := s) σ)
        (fun i => tensor_lambda_nonneg (I := I) (M := M) i) T₀ F t := by
  rw [tensorHeatMildSolutionHs_apply]
  unfold abstractSpectralDuhamel duhamel
  rw [tensorHeatSemigroupHsExt_eq_abstractSpectralSemigroup
    (I := I) (M := M) ht]
  congr 1
  apply intervalIntegral.integral_congr
  intro τ hτ
  rw [Set.uIcc_of_le ht] at hτ
  exact congrArg (fun A => A (F τ))
    (tensorHeatSemigroupHsExt_eq_abstractSpectralSemigroup
      (I := I) (M := M) (g := g) (r := r) (s := s) (σ := σ)
      (sub_nonneg.mpr hτ.2))

omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem tensorHeatMildSolutionHs_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (σ : ℝ)
    (T₀ : tensorHs (I := I) (M := M) g r s σ)
    (F : ℝ → tensorHs (I := I) (M := M) g r s σ) :
    tensorHeatMildSolutionHs (I := I) (M := M) g r s σ T₀ F 0 = T₀ :=
  duhamel_zero
    (tensorHsBoundedC0Semigroup (I := I) (M := M) g r s σ) T₀ F

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorHeatMildSolutionHs_integrable
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (σ : ℝ)
    {F : ℝ → tensorHs (I := I) (M := M) g r s σ} (hF : Continuous F)
    {t : ℝ} (ht : 0 ≤ t) :
    IntervalIntegrable (fun τ : ℝ =>
      tensorHeatSemigroupHsExt (I := I) (M := M) g r s σ (t - τ) (F τ))
      MeasureTheory.volume 0 t :=
  duhamel_integrable
    (tensorHsBoundedC0Semigroup (I := I) (M := M) g r s σ) hF ht

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorHsInclusion_tensorHeatMildSolutionHs
    (g : SmoothRiemannianMetric I M) (r s : ℕ) {τ σ : ℝ}
    (hτσ : τ ≤ σ)
    (T₀ : tensorHs (I := I) (M := M) g r s σ)
    {F : ℝ → tensorHs (I := I) (M := M) g r s σ} (hF : Continuous F)
    {t : ℝ} (ht : 0 ≤ t) :
    tensorHsInclusion (I := I) (M := M)
        (g := g) (r := r) (s := s) hτσ
        (tensorHeatMildSolutionHs (I := I) (M := M) g r s σ T₀ F t) =
      tensorHeatMildSolutionHs (I := I) (M := M) g r s τ
        (tensorHsInclusion (I := I) (M := M)
          (g := g) (r := r) (s := s) hτσ T₀)
        (fun q => tensorHsInclusion (I := I) (M := M)
          (g := g) (r := r) (s := s) hτσ (F q)) t := by
  rw [tensorHeatMildSolutionHs_apply, tensorHeatMildSolutionHs_apply, map_add,
    tensorHsInclusion_tensorHeatSemigroupHsExt
      (I := I) (M := M) hτσ ht]
  have h_integrable := tensorHeatMildSolutionHs_integrable
    (I := I) (M := M) g r s σ hF ht
  rw [← (tensorHsInclusion (I := I) (M := M)
    (g := g) (r := r) (s := s) hτσ).intervalIntegral_comp_comm h_integrable]
  congr 1
  apply intervalIntegral.integral_congr
  intro q hq
  rw [Set.uIcc_of_le ht] at hq
  exact tensorHsInclusion_tensorHeatSemigroupHsExt
    (I := I) (M := M) hτσ (sub_nonneg.mpr hq.2) (F q)

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorHeatMildSolutionHs_continuousOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (σ : ℝ)
    (T₀ : tensorHs (I := I) (M := M) g r s σ)
    {F : ℝ → tensorHs (I := I) (M := M) g r s σ} (hF : Continuous F) :
    ContinuousOn
      (tensorHeatMildSolutionHs (I := I) (M := M) g r s σ T₀ F)
      (Set.Ici 0) :=
  duhamel_continuousOn
    (tensorHsBoundedC0Semigroup (I := I) (M := M) g r s σ) T₀ hF

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorHeatMildSolutionHs_hasDerivAt_of_strong_data
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (σ : ℝ)
    (T₀ : tensorHs (I := I) (M := M) g r s (σ + 2))
    {F : ℝ → tensorHs (I := I) (M := M) g r s (σ + 2)}
    (hF : Continuous F) {t : ℝ} (ht : 0 < t) :
    HasDerivAt
      (fun q : ℝ =>
        tensorHsInclusion (I := I) (M := M)
          (g := g) (r := r) (s := s) (show σ ≤ σ + 2 by linarith)
          (tensorHeatMildSolutionHs (I := I) (M := M)
            g r s (σ + 2) T₀ F q))
      (tensorScaleLaplacian (I := I) (M := M) σ
          (tensorHeatMildSolutionHs (I := I) (M := M)
            g r s (σ + 2) T₀ F t) +
        tensorHsInclusion (I := I) (M := M)
          (g := g) (r := r) (s := s) (show σ ≤ σ + 2 by linarith)
          (F t)) t := by
  let hσ : σ ≤ σ + 2 := by linarith
  let J := tensorHsInclusion (I := I) (M := M)
    (g := g) (r := r) (s := s) hσ
  let A := tensorScaleLaplacian (I := I) (M := M)
    (g := g) (r := r) (s := s) σ
  let U := tensorHeatMildSolutionHs (I := I) (M := M)
    g r s (σ + 2) T₀ F
  let b := tensorHsHilbertBasis (I := I) (M := M)
    (g := g) (r := r) (s := s) σ
  change HasDerivAt (fun q : ℝ => J (U q)) (A (U t) + J (F t)) t
  have hU : ContinuousOn U (Set.Ici 0) := by
    exact tensorHeatMildSolutionHs_continuousOn
      (I := I) (M := M) g r s (σ + 2) T₀ hF
  have hFJ : Continuous (fun q : ℝ => J (F q)) := J.continuous.comp hF
  have hv : ContinuousOn (fun q : ℝ => A (U q) + J (F q)) (Set.Ioi 0) :=
    (A.continuous.comp_continuousOn
      (hU.mono Set.Ioi_subset_Ici_self)).add hFJ.continuousOn
  have hstate : ∀ q : ℝ, 0 ≤ q →
      abstractSpectralDuhamel b
          (fun i => tensor_lambda_nonneg (I := I) (M := M) i)
          (J T₀) (fun x => J (F x)) q = J (U q) := by
    intro q hq
    have habstract := tensorHeatMildSolutionHs_eq_abstractSpectralDuhamel
      (I := I) (M := M) g r s σ (J T₀) (fun x => J (F x)) hq
    have hinclusion := tensorHsInclusion_tensorHeatMildSolutionHs
      (I := I) (M := M) g r s hσ T₀ hF hq
    exact habstract.symm.trans hinclusion.symm
  refine hasDerivAt_of_inner_hilbertBasis b isOpen_Ioi hv ?_ ht
  intro q hq i
  have hmodal := abstractSpectralDuhamel_hasDerivAt_repr_apply b
    (fun j => tensor_lambda_nonneg (I := I) (M := M) j)
    (J T₀) hFJ hq i
  have heq : (fun x : ℝ =>
      (b.repr (abstractSpectralDuhamel b
        (fun j => tensor_lambda_nonneg (I := I) (M := M) j)
        (J T₀) (fun y => J (F y)) x) :
          TensorEigenIdx (I := I) (M := M) g r s → ℝ) i) =ᶠ[nhds q]
      (fun x : ℝ => ⟪b i, J (U x)⟫_ℝ) := by
    filter_upwards [Ioi_mem_nhds hq] with x hx
    rw [b.repr_apply_apply, hstate x hx.le]
  have hder := hmodal.congr_of_eventuallyEq heq.symm
  apply hder.congr_deriv
  rw [hstate q hq.le]
  rw [← b.repr_apply_apply]
  rw [show b = tensorHsHilbertBasis (I := I) (M := M)
      (g := g) (r := r) (s := s) σ from rfl]
  rw [tensorHsHilbertBasis_repr_apply_apply,
    tensorHsHilbertBasis_repr_apply_apply,
    tensorHsHilbertBasis_repr_apply_apply]
  simp only [J, A, tensorHs.add_coeff,
    tensorHsInclusion_coeff_apply, tensorScaleLaplacian_coeff]
  ring

omit [NeZero (Module.finrank ℝ E)] in
theorem deriv_tensorHeatMildSolutionHs_eq_tensorScaleLaplacian_add_of_strong_data
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (σ : ℝ)
    (T₀ : tensorHs (I := I) (M := M) g r s (σ + 2))
    {F : ℝ → tensorHs (I := I) (M := M) g r s (σ + 2)}
    (hF : Continuous F) {t : ℝ} (ht : 0 < t) :
    deriv
        (fun q : ℝ =>
          tensorHsInclusion (I := I) (M := M)
            (g := g) (r := r) (s := s) (show σ ≤ σ + 2 by linarith)
            (tensorHeatMildSolutionHs (I := I) (M := M)
              g r s (σ + 2) T₀ F q)) t =
      tensorScaleLaplacian (I := I) (M := M) σ
          (tensorHeatMildSolutionHs (I := I) (M := M)
            g r s (σ + 2) T₀ F t) +
        tensorHsInclusion (I := I) (M := M)
          (g := g) (r := r) (s := s) (show σ ≤ σ + 2 by linarith)
          (F t) :=
  (tensorHeatMildSolutionHs_hasDerivAt_of_strong_data
    (I := I) (M := M) g r s σ T₀ hF ht).deriv

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorHeatMildSolutionHs_differentiableOn_of_strong_data
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (σ : ℝ)
    (T₀ : tensorHs (I := I) (M := M) g r s (σ + 2))
    {F : ℝ → tensorHs (I := I) (M := M) g r s (σ + 2)}
    (hF : Continuous F) :
    DifferentiableOn ℝ
      (fun q : ℝ =>
        tensorHsInclusion (I := I) (M := M)
          (g := g) (r := r) (s := s) (show σ ≤ σ + 2 by linarith)
          (tensorHeatMildSolutionHs (I := I) (M := M)
            g r s (σ + 2) T₀ F q))
      (Set.Ioi 0) := by
  intro t ht
  exact (tensorHeatMildSolutionHs_hasDerivAt_of_strong_data
    (I := I) (M := M) g r s σ T₀ hF ht).differentiableAt.differentiableWithinAt

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorHeatMildSolutionHs_zero_forcing
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (σ t : ℝ)
    (T₀ : tensorHs (I := I) (M := M) g r s σ) :
    tensorHeatMildSolutionHs (I := I) (M := M) g r s σ T₀ (fun _ => 0) t =
      tensorHeatSemigroupHsExt (I := I) (M := M) g r s σ t T₀ := by
  rw [tensorHeatMildSolutionHs_apply]
  have hzero : (fun τ : ℝ =>
      tensorHeatSemigroupHsExt (I := I) (M := M) g r s σ (t - τ)
        ((fun _ => 0) τ)) =
      (fun _ => (0 : tensorHs (I := I) (M := M) g r s σ)) := by
    funext τ
    exact (tensorHeatSemigroupHsExt (I := I) (M := M)
      g r s σ (t - τ)).map_zero
  rw [hzero, intervalIntegral.integral_zero, add_zero]

end TensorHeatEquation

end Parabolic
end Analysis
end DifferentialGeometry

end
