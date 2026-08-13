import DifferentialGeometry.Analysis.Parabolic.TensorHeatDuhamelMildSolution
import DifferentialGeometry.Analysis.Parabolic.AbstractSemigroup.AbstractSpectralDuhamelHolderRegularity
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.GraphNorm

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators NNReal
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
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SobolevScale
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

namespace TensorHeatEquation

def tensorHeatMildSolutionHsHolderDeriv
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (σ : ℝ)
    (T₀ : tensorHs (I := I) (M := M) g r s σ)
    (F : ℝ → tensorHs (I := I) (M := M) g r s σ) (t : ℝ) :
    tensorHs (I := I) (M := M) g r s σ :=
  abstractSpectralDuhamelHolderDeriv
    (tensorHsHilbertBasis (I := I) (M := M)
      (g := g) (r := r) (s := s) σ)
    (fun i => tensor_lambda_nonneg (I := I) (M := M) i) T₀ F t

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorHeatMildSolutionHsHolderDeriv_coeff
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (σ : ℝ)
    (T₀ : tensorHs (I := I) (M := M) g r s σ)
    {F : ℝ → tensorHs (I := I) (M := M) g r s σ}
    {K α : NNReal} (hα : 0 < α) (hF : HolderWith K α F)
    {t : ℝ} (ht : 0 < t) (i : TensorEigenIdx (I := I) (M := M) g r s) :
    (tensorHeatMildSolutionHsHolderDeriv (I := I) (M := M)
      g r s σ T₀ F t).coeff i =
      -(TensorEigenIdx.lambda (I := I) (M := M) i) *
          (tensorHeatMildSolutionHs (I := I) (M := M)
            g r s σ T₀ F t).coeff i +
        (F t).coeff i := by
  let b := tensorHsHilbertBasis (I := I) (M := M)
    (g := g) (r := r) (s := s) σ
  have hrepr := abstractSpectralDuhamelHolderDeriv_repr_apply b
    (fun j => tensor_lambda_nonneg (I := I) (M := M) j) T₀ hα hF ht i
  rw [← tensorHeatMildSolutionHs_eq_abstractSpectralDuhamel
    (I := I) (M := M) g r s σ T₀ F ht.le] at hrepr
  simp only [b, tensorHsHilbertBasis_repr_apply_apply] at hrepr
  have hsqrt_ne : Real.sqrt
      (tensorSobolevWeight (I := I) (M := M) i σ) ≠ 0 :=
    (Real.sqrt_pos.mpr
      (tensorSobolevWeight_pos (I := I) (M := M) i σ)).ne'
  apply mul_left_cancel₀ hsqrt_ne
  calc
    Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ) *
          (tensorHeatMildSolutionHsHolderDeriv (I := I) (M := M)
            g r s σ T₀ F t).coeff i =
        -(TensorEigenIdx.lambda (I := I) (M := M) i) *
            (Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ) *
              (tensorHeatMildSolutionHs (I := I) (M := M)
                g r s σ T₀ F t).coeff i) +
          Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ) *
            (F t).coeff i := hrepr
    _ = Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ) *
        (-(TensorEigenIdx.lambda (I := I) (M := M) i) *
            (tensorHeatMildSolutionHs (I := I) (M := M)
              g r s σ T₀ F t).coeff i + (F t).coeff i) := by ring

def tensorHeatMildSolutionHsLiftOfHolder
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (σ : ℝ)
    (T₀ : tensorHs (I := I) (M := M) g r s σ)
    (F : ℝ → tensorHs (I := I) (M := M) g r s σ)
    {K α : NNReal} (hα : 0 < α) (hF : HolderWith K α F)
    (t : ℝ) (ht : 0 < t) :
    tensorHs (I := I) (M := M) g r s (σ + 2) := by
  let U := tensorHeatMildSolutionHs (I := I) (M := M) g r s σ T₀ F t
  let D := tensorHeatMildSolutionHsHolderDeriv (I := I) (M := M)
    g r s σ T₀ F t
  let Z := U - D + F t
  have hZcoeff : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      Z.coeff i =
        (1 + TensorEigenIdx.lambda (I := I) (M := M) i) * U.coeff i := by
    intro i
    simp only [Z, sub_eq_add_neg, tensorHs.add_coeff, tensorHs.neg_coeff]
    rw [tensorHeatMildSolutionHsHolderDeriv_coeff
      (I := I) (M := M) g r s σ T₀ hα hF ht]
    ring
  exact tensorHsAddTwoOfOneAddLambdaMul (I := I) (M := M) σ U Z hZcoeff

omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem tensorHeatMildSolutionHsLiftOfHolder_coeff
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (σ : ℝ)
    (T₀ : tensorHs (I := I) (M := M) g r s σ)
    (F : ℝ → tensorHs (I := I) (M := M) g r s σ)
    {K α : NNReal} (hα : 0 < α) (hF : HolderWith K α F)
    (t : ℝ) (ht : 0 < t) (i : TensorEigenIdx (I := I) (M := M) g r s) :
    (tensorHeatMildSolutionHsLiftOfHolder (I := I) (M := M)
      g r s σ T₀ F hα hF t ht).coeff i =
      (tensorHeatMildSolutionHs (I := I) (M := M)
        g r s σ T₀ F t).coeff i :=
  rfl

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorHsInclusion_tensorHeatMildSolutionHsLiftOfHolder
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (σ : ℝ)
    (T₀ : tensorHs (I := I) (M := M) g r s σ)
    (F : ℝ → tensorHs (I := I) (M := M) g r s σ)
    {K α : NNReal} (hα : 0 < α) (hF : HolderWith K α F)
    (t : ℝ) (ht : 0 < t) :
    tensorHsInclusion (I := I) (M := M)
        (g := g) (r := r) (s := s) (show σ ≤ σ + 2 by linarith)
        (tensorHeatMildSolutionHsLiftOfHolder (I := I) (M := M)
          g r s σ T₀ F hα hF t ht) =
      tensorHeatMildSolutionHs (I := I) (M := M) g r s σ T₀ F t := by
  apply tensorHs.ext
  funext i
  rw [tensorHsInclusion_coeff_apply,
    tensorHeatMildSolutionHsLiftOfHolder_coeff]

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorHeatMildSolutionHsHolderDeriv_eq_tensorScaleLaplacian_add
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (σ : ℝ)
    (T₀ : tensorHs (I := I) (M := M) g r s σ)
    {F : ℝ → tensorHs (I := I) (M := M) g r s σ}
    {K α : NNReal} (hα : 0 < α) (hF : HolderWith K α F)
    {t : ℝ} (ht : 0 < t) :
    tensorHeatMildSolutionHsHolderDeriv (I := I) (M := M)
        g r s σ T₀ F t =
      tensorScaleLaplacian (I := I) (M := M) σ
          (tensorHeatMildSolutionHsLiftOfHolder (I := I) (M := M)
            g r s σ T₀ F hα hF t ht) + F t := by
  apply tensorHs.ext
  funext i
  rw [tensorHeatMildSolutionHsHolderDeriv_coeff
      (I := I) (M := M) g r s σ T₀ hα hF ht]
  change _ =
    (tensorScaleLaplacian (I := I) (M := M) σ
      (tensorHeatMildSolutionHsLiftOfHolder (I := I) (M := M)
        g r s σ T₀ F hα hF t ht)).coeff i + (F t).coeff i
  rw [tensorScaleLaplacian_coeff,
    tensorHeatMildSolutionHsLiftOfHolder_coeff]

omit [NeZero (Module.finrank ℝ E)] in
private theorem tensorHeatMildSolutionHs_hasDerivAt_holder_candidate
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (σ : ℝ)
    (T₀ : tensorHs (I := I) (M := M) g r s σ)
    {F : ℝ → tensorHs (I := I) (M := M) g r s σ}
    {K α : NNReal} (hα : 0 < α) (hF : HolderWith K α F)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt
      (tensorHeatMildSolutionHs (I := I) (M := M) g r s σ T₀ F)
      (tensorHeatMildSolutionHsHolderDeriv (I := I) (M := M)
        g r s σ T₀ F t) t := by
  let b := tensorHsHilbertBasis (I := I) (M := M)
    (g := g) (r := r) (s := s) σ
  have habstract := abstractSpectralDuhamel_hasDerivAt_of_holder b
    (fun i => tensor_lambda_nonneg (I := I) (M := M) i) T₀ hα hF ht
  have heq :
      tensorHeatMildSolutionHs (I := I) (M := M) g r s σ T₀ F =ᶠ[𝓝 t]
        abstractSpectralDuhamel b
          (fun i => tensor_lambda_nonneg (I := I) (M := M) i) T₀ F := by
    filter_upwards [Ioi_mem_nhds ht] with q hq
    exact tensorHeatMildSolutionHs_eq_abstractSpectralDuhamel
      (I := I) (M := M) g r s σ T₀ F hq.le
  simpa only [b, tensorHeatMildSolutionHsHolderDeriv] using
    habstract.congr_of_eventuallyEq heq

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorHeatMildSolutionHs_hasDerivAt_of_holder
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (σ : ℝ)
    (T₀ : tensorHs (I := I) (M := M) g r s σ)
    {F : ℝ → tensorHs (I := I) (M := M) g r s σ}
    {K α : NNReal} (hα : 0 < α) (hF : HolderWith K α F)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt
      (tensorHeatMildSolutionHs (I := I) (M := M) g r s σ T₀ F)
      (tensorScaleLaplacian (I := I) (M := M) σ
          (tensorHeatMildSolutionHsLiftOfHolder (I := I) (M := M)
            g r s σ T₀ F hα hF t ht) + F t) t := by
  have hcandidate := tensorHeatMildSolutionHs_hasDerivAt_holder_candidate
    (I := I) (M := M) g r s σ T₀ hα hF ht
  apply hcandidate.congr_deriv
  exact tensorHeatMildSolutionHsHolderDeriv_eq_tensorScaleLaplacian_add
    (I := I) (M := M) g r s σ T₀ hα hF ht

omit [NeZero (Module.finrank ℝ E)] in
theorem deriv_tensorHeatMildSolutionHs_eq_tensorScaleLaplacian_add_of_holder
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (σ : ℝ)
    (T₀ : tensorHs (I := I) (M := M) g r s σ)
    {F : ℝ → tensorHs (I := I) (M := M) g r s σ}
    {K α : NNReal} (hα : 0 < α) (hF : HolderWith K α F)
    {t : ℝ} (ht : 0 < t) :
    deriv (tensorHeatMildSolutionHs (I := I) (M := M) g r s σ T₀ F) t =
      tensorScaleLaplacian (I := I) (M := M) σ
          (tensorHeatMildSolutionHsLiftOfHolder (I := I) (M := M)
            g r s σ T₀ F hα hF t ht) + F t :=
  (tensorHeatMildSolutionHs_hasDerivAt_of_holder
    (I := I) (M := M) g r s σ T₀ hα hF ht).deriv

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorHeatMildSolutionHs_differentiableOn_of_holder
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (σ : ℝ)
    (T₀ : tensorHs (I := I) (M := M) g r s σ)
    {F : ℝ → tensorHs (I := I) (M := M) g r s σ}
    {K α : NNReal} (hα : 0 < α) (hF : HolderWith K α F) :
    DifferentiableOn ℝ
      (tensorHeatMildSolutionHs (I := I) (M := M) g r s σ T₀ F)
      (Set.Ioi 0) := by
  intro t ht
  exact (tensorHeatMildSolutionHs_hasDerivAt_of_holder
    (I := I) (M := M) g r s σ T₀ hα hF ht).differentiableAt.differentiableWithinAt

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorHeatMildSolutionHsHolderDeriv_continuousOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (σ : ℝ)
    (T₀ : tensorHs (I := I) (M := M) g r s σ)
    {F : ℝ → tensorHs (I := I) (M := M) g r s σ}
    {K α : NNReal} (hα : 0 < α) (hF : HolderWith K α F) :
    ContinuousOn
      (tensorHeatMildSolutionHsHolderDeriv (I := I) (M := M)
        g r s σ T₀ F)
      (Set.Ioi 0) := by
  simpa only [tensorHeatMildSolutionHsHolderDeriv] using
    abstractSpectralDuhamelHolderDeriv_continuousOn
      (tensorHsHilbertBasis (I := I) (M := M)
        (g := g) (r := r) (s := s) σ)
      (fun i => tensor_lambda_nonneg (I := I) (M := M) i)
      T₀ hα hF

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorHeatMildSolutionHs_contDiffOn_one_of_holder
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (σ : ℝ)
    (T₀ : tensorHs (I := I) (M := M) g r s σ)
    {F : ℝ → tensorHs (I := I) (M := M) g r s σ}
    {K α : NNReal} (hα : 0 < α) (hF : HolderWith K α F) :
    ContDiffOn ℝ 1
      (tensorHeatMildSolutionHs (I := I) (M := M) g r s σ T₀ F)
      (Set.Ioi 0) := by
  rw [show (1 : WithTop ℕ∞) = (0 : WithTop ℕ∞) + 1 by rfl,
    contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
  refine ⟨tensorHeatMildSolutionHs_differentiableOn_of_holder
    (I := I) (M := M) g r s σ T₀ hα hF, ?_, ?_⟩
  · simp only [WithTop.zero_ne_top, false_implies]
  · rw [contDiffOn_zero]
    refine (tensorHeatMildSolutionHsHolderDeriv_continuousOn
      (I := I) (M := M) g r s σ T₀ hα hF).congr ?_
    intro t ht
    exact (tensorHeatMildSolutionHs_hasDerivAt_holder_candidate
      (I := I) (M := M) g r s σ T₀ hα hF ht).deriv

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorHeatMildSolutionHsHolderDeriv_coeff_of_holderOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (σ : ℝ)
    (T₀ : tensorHs (I := I) (M := M) g r s σ)
    {F : ℝ → tensorHs (I := I) (M := M) g r s σ}
    {T : ℝ} {K α : NNReal} (hα : 0 < α)
    (hF : HolderOnWith K α F (Set.Icc 0 T))
    {t : ℝ} (ht : t ∈ Set.Ioo 0 T)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    (tensorHeatMildSolutionHsHolderDeriv (I := I) (M := M)
      g r s σ T₀ F t).coeff i =
      -(TensorEigenIdx.lambda (I := I) (M := M) i) *
          (tensorHeatMildSolutionHs (I := I) (M := M)
            g r s σ T₀ F t).coeff i +
        (F t).coeff i := by
  let b := tensorHsHilbertBasis (I := I) (M := M)
    (g := g) (r := r) (s := s) σ
  have hrepr := abstractSpectralDuhamelHolderDeriv_repr_apply_of_holderOn b
    (fun j => tensor_lambda_nonneg (I := I) (M := M) j) T₀ hα hF ht i
  rw [← tensorHeatMildSolutionHs_eq_abstractSpectralDuhamel
    (I := I) (M := M) g r s σ T₀ F ht.1.le] at hrepr
  simp only [b, tensorHsHilbertBasis_repr_apply_apply] at hrepr
  have hsqrt_ne : Real.sqrt
      (tensorSobolevWeight (I := I) (M := M) i σ) ≠ 0 :=
    (Real.sqrt_pos.mpr
      (tensorSobolevWeight_pos (I := I) (M := M) i σ)).ne'
  apply mul_left_cancel₀ hsqrt_ne
  calc
    Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ) *
          (tensorHeatMildSolutionHsHolderDeriv (I := I) (M := M)
            g r s σ T₀ F t).coeff i =
        -(TensorEigenIdx.lambda (I := I) (M := M) i) *
            (Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ) *
              (tensorHeatMildSolutionHs (I := I) (M := M)
                g r s σ T₀ F t).coeff i) +
          Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ) *
            (F t).coeff i := hrepr
    _ = Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ) *
        (-(TensorEigenIdx.lambda (I := I) (M := M) i) *
            (tensorHeatMildSolutionHs (I := I) (M := M)
              g r s σ T₀ F t).coeff i + (F t).coeff i) := by ring

def tensorHeatMildSolutionHsLiftOfHolderOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (σ : ℝ)
    (T₀ : tensorHs (I := I) (M := M) g r s σ)
    (F : ℝ → tensorHs (I := I) (M := M) g r s σ)
    {T : ℝ} {K α : NNReal} (hα : 0 < α)
    (hF : HolderOnWith K α F (Set.Icc 0 T))
    (t : ℝ) (ht : t ∈ Set.Ioo 0 T) :
    tensorHs (I := I) (M := M) g r s (σ + 2) := by
  let U := tensorHeatMildSolutionHs (I := I) (M := M) g r s σ T₀ F t
  let D := tensorHeatMildSolutionHsHolderDeriv (I := I) (M := M)
    g r s σ T₀ F t
  let Z := U - D + F t
  have hZcoeff : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      Z.coeff i =
        (1 + TensorEigenIdx.lambda (I := I) (M := M) i) * U.coeff i := by
    intro i
    simp only [Z, sub_eq_add_neg, tensorHs.add_coeff, tensorHs.neg_coeff]
    rw [tensorHeatMildSolutionHsHolderDeriv_coeff_of_holderOn
      (I := I) (M := M) g r s σ T₀ hα hF ht]
    ring
  exact tensorHsAddTwoOfOneAddLambdaMul (I := I) (M := M) σ U Z hZcoeff

omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem tensorHeatMildSolutionHsLiftOfHolderOn_coeff
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (σ : ℝ)
    (T₀ : tensorHs (I := I) (M := M) g r s σ)
    (F : ℝ → tensorHs (I := I) (M := M) g r s σ)
    {T : ℝ} {K α : NNReal} (hα : 0 < α)
    (hF : HolderOnWith K α F (Set.Icc 0 T))
    (t : ℝ) (ht : t ∈ Set.Ioo 0 T)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    (tensorHeatMildSolutionHsLiftOfHolderOn (I := I) (M := M)
      g r s σ T₀ F hα hF t ht).coeff i =
      (tensorHeatMildSolutionHs (I := I) (M := M)
        g r s σ T₀ F t).coeff i :=
  rfl

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorHsInclusion_tensorHeatMildSolutionHsLiftOfHolderOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (σ : ℝ)
    (T₀ : tensorHs (I := I) (M := M) g r s σ)
    (F : ℝ → tensorHs (I := I) (M := M) g r s σ)
    {T : ℝ} {K α : NNReal} (hα : 0 < α)
    (hF : HolderOnWith K α F (Set.Icc 0 T))
    (t : ℝ) (ht : t ∈ Set.Ioo 0 T) :
    tensorHsInclusion (I := I) (M := M)
        (g := g) (r := r) (s := s) (show σ ≤ σ + 2 by linarith)
        (tensorHeatMildSolutionHsLiftOfHolderOn (I := I) (M := M)
          g r s σ T₀ F hα hF t ht) =
      tensorHeatMildSolutionHs (I := I) (M := M) g r s σ T₀ F t := by
  apply tensorHs.ext
  funext i
  rw [tensorHsInclusion_coeff_apply,
    tensorHeatMildSolutionHsLiftOfHolderOn_coeff]

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorHeatMildSolutionHsHolderDeriv_eq_tensorScaleLaplacian_add_of_holderOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (σ : ℝ)
    (T₀ : tensorHs (I := I) (M := M) g r s σ)
    {F : ℝ → tensorHs (I := I) (M := M) g r s σ}
    {T : ℝ} {K α : NNReal} (hα : 0 < α)
    (hF : HolderOnWith K α F (Set.Icc 0 T))
    {t : ℝ} (ht : t ∈ Set.Ioo 0 T) :
    tensorHeatMildSolutionHsHolderDeriv (I := I) (M := M)
        g r s σ T₀ F t =
      tensorScaleLaplacian (I := I) (M := M) σ
          (tensorHeatMildSolutionHsLiftOfHolderOn (I := I) (M := M)
            g r s σ T₀ F hα hF t ht) + F t := by
  apply tensorHs.ext
  funext i
  rw [tensorHeatMildSolutionHsHolderDeriv_coeff_of_holderOn
      (I := I) (M := M) g r s σ T₀ hα hF ht]
  change _ =
    (tensorScaleLaplacian (I := I) (M := M) σ
      (tensorHeatMildSolutionHsLiftOfHolderOn (I := I) (M := M)
        g r s σ T₀ F hα hF t ht)).coeff i + (F t).coeff i
  rw [tensorScaleLaplacian_coeff,
    tensorHeatMildSolutionHsLiftOfHolderOn_coeff]

omit [NeZero (Module.finrank ℝ E)] in
private theorem tensorHeatMildSolutionHs_hasDerivAt_holderOn_candidate
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (σ : ℝ)
    (T₀ : tensorHs (I := I) (M := M) g r s σ)
    {F : ℝ → tensorHs (I := I) (M := M) g r s σ}
    {T : ℝ} {K α : NNReal} (hα : 0 < α)
    (hF : HolderOnWith K α F (Set.Icc 0 T))
    {t : ℝ} (ht : t ∈ Set.Ioo 0 T) :
    HasDerivAt
      (tensorHeatMildSolutionHs (I := I) (M := M) g r s σ T₀ F)
      (tensorHeatMildSolutionHsHolderDeriv (I := I) (M := M)
        g r s σ T₀ F t) t := by
  let b := tensorHsHilbertBasis (I := I) (M := M)
    (g := g) (r := r) (s := s) σ
  have habstract := abstractSpectralDuhamel_hasDerivAt_of_holderOn b
    (fun i => tensor_lambda_nonneg (I := I) (M := M) i) T₀ hα hF ht
  have heq :
      tensorHeatMildSolutionHs (I := I) (M := M) g r s σ T₀ F =ᶠ[nhds t]
        abstractSpectralDuhamel b
          (fun i => tensor_lambda_nonneg (I := I) (M := M) i) T₀ F := by
    filter_upwards [Ioi_mem_nhds ht.1] with q hq
    exact tensorHeatMildSolutionHs_eq_abstractSpectralDuhamel
      (I := I) (M := M) g r s σ T₀ F hq.le
  simpa only [b, tensorHeatMildSolutionHsHolderDeriv] using
    habstract.congr_of_eventuallyEq heq

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorHeatMildSolutionHs_hasDerivAt_of_holderOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (σ : ℝ)
    (T₀ : tensorHs (I := I) (M := M) g r s σ)
    {F : ℝ → tensorHs (I := I) (M := M) g r s σ}
    {T : ℝ} {K α : NNReal} (hα : 0 < α)
    (hF : HolderOnWith K α F (Set.Icc 0 T))
    {t : ℝ} (ht : t ∈ Set.Ioo 0 T) :
    HasDerivAt
      (tensorHeatMildSolutionHs (I := I) (M := M) g r s σ T₀ F)
      (tensorScaleLaplacian (I := I) (M := M) σ
          (tensorHeatMildSolutionHsLiftOfHolderOn (I := I) (M := M)
            g r s σ T₀ F hα hF t ht) + F t) t := by
  have hcandidate := tensorHeatMildSolutionHs_hasDerivAt_holderOn_candidate
    (I := I) (M := M) g r s σ T₀ hα hF ht
  apply hcandidate.congr_deriv
  exact tensorHeatMildSolutionHsHolderDeriv_eq_tensorScaleLaplacian_add_of_holderOn
    (I := I) (M := M) g r s σ T₀ hα hF ht

omit [NeZero (Module.finrank ℝ E)] in
theorem deriv_tensorHeatMildSolutionHs_eq_tensorScaleLaplacian_add_of_holderOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (σ : ℝ)
    (T₀ : tensorHs (I := I) (M := M) g r s σ)
    {F : ℝ → tensorHs (I := I) (M := M) g r s σ}
    {T : ℝ} {K α : NNReal} (hα : 0 < α)
    (hF : HolderOnWith K α F (Set.Icc 0 T))
    {t : ℝ} (ht : t ∈ Set.Ioo 0 T) :
    deriv (tensorHeatMildSolutionHs (I := I) (M := M) g r s σ T₀ F) t =
      tensorScaleLaplacian (I := I) (M := M) σ
          (tensorHeatMildSolutionHsLiftOfHolderOn (I := I) (M := M)
            g r s σ T₀ F hα hF t ht) + F t :=
  (tensorHeatMildSolutionHs_hasDerivAt_of_holderOn
    (I := I) (M := M) g r s σ T₀ hα hF ht).deriv

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorHeatMildSolutionHs_differentiableOn_of_holderOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (σ : ℝ)
    (T₀ : tensorHs (I := I) (M := M) g r s σ)
    {F : ℝ → tensorHs (I := I) (M := M) g r s σ}
    {T : ℝ} {K α : NNReal} (hα : 0 < α)
    (hF : HolderOnWith K α F (Set.Icc 0 T)) :
    DifferentiableOn ℝ
      (tensorHeatMildSolutionHs (I := I) (M := M) g r s σ T₀ F)
      (Set.Ioo 0 T) := by
  intro t ht
  exact (tensorHeatMildSolutionHs_hasDerivAt_of_holderOn
    (I := I) (M := M) g r s σ T₀ hα hF ht).differentiableAt.differentiableWithinAt

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorHeatMildSolutionHsHolderDeriv_continuousOn_of_holderOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (σ : ℝ)
    (T₀ : tensorHs (I := I) (M := M) g r s σ)
    {F : ℝ → tensorHs (I := I) (M := M) g r s σ}
    {T : ℝ} {K α : NNReal} (hα : 0 < α)
    (hF : HolderOnWith K α F (Set.Icc 0 T)) :
    ContinuousOn
      (tensorHeatMildSolutionHsHolderDeriv (I := I) (M := M)
        g r s σ T₀ F)
      (Set.Ioo 0 T) := by
  simpa only [tensorHeatMildSolutionHsHolderDeriv] using
    abstractSpectralDuhamelHolderDeriv_continuousOn_of_holderOn
      (tensorHsHilbertBasis (I := I) (M := M)
        (g := g) (r := r) (s := s) σ)
      (fun i => tensor_lambda_nonneg (I := I) (M := M) i)
      T₀ hα hF

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorHeatMildSolutionHs_contDiffOn_one_of_holderOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (σ : ℝ)
    (T₀ : tensorHs (I := I) (M := M) g r s σ)
    {F : ℝ → tensorHs (I := I) (M := M) g r s σ}
    {T : ℝ} {K α : NNReal} (hα : 0 < α)
    (hF : HolderOnWith K α F (Set.Icc 0 T)) :
    ContDiffOn ℝ 1
      (tensorHeatMildSolutionHs (I := I) (M := M) g r s σ T₀ F)
      (Set.Ioo 0 T) := by
  rw [show (1 : WithTop ℕ∞) = (0 : WithTop ℕ∞) + 1 by rfl,
    contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo]
  refine ⟨tensorHeatMildSolutionHs_differentiableOn_of_holderOn
    (I := I) (M := M) g r s σ T₀ hα hF, ?_, ?_⟩
  · simp only [WithTop.zero_ne_top, false_implies]
  · rw [contDiffOn_zero]
    refine (tensorHeatMildSolutionHsHolderDeriv_continuousOn_of_holderOn
      (I := I) (M := M) g r s σ T₀ hα hF).congr ?_
    intro t ht
    exact (tensorHeatMildSolutionHs_hasDerivAt_holderOn_candidate
      (I := I) (M := M) g r s σ T₀ hα hF ht).deriv

end TensorHeatEquation

end Parabolic
end Analysis
end DifferentialGeometry

end
