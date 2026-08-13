import DifferentialGeometry.Analysis.Parabolic.TensorHeatDuhamelMildSolution
import DifferentialGeometry.Analysis.Parabolic.AbstractSemigroup.AbstractSpectralDuhamelTimeRegularity
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.GraphNorm

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
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SobolevScale
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

namespace TensorHeatEquation

def tensorHeatMildSolutionHsDeriv
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (σ : ℝ)
    (T₀ : tensorHs (I := I) (M := M) g r s σ)
    (F F' : ℝ → tensorHs (I := I) (M := M) g r s σ) (t : ℝ) :
    tensorHs (I := I) (M := M) g r s σ :=
  abstractSpectralDuhamelDeriv
    (tensorHsHilbertBasis (I := I) (M := M)
      (g := g) (r := r) (s := s) σ)
    (fun i => tensor_lambda_nonneg (I := I) (M := M) i) T₀ F F' t

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorHeatMildSolutionHsDeriv_coeff
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (σ : ℝ)
    (T₀ : tensorHs (I := I) (M := M) g r s σ)
    {F F' : ℝ → tensorHs (I := I) (M := M) g r s σ}
    (hF : ∀ q, HasDerivAt F (F' q) q) (hF' : Continuous F')
    {t : ℝ} (ht : 0 < t) (i : TensorEigenIdx (I := I) (M := M) g r s) :
    (tensorHeatMildSolutionHsDeriv (I := I) (M := M)
      g r s σ T₀ F F' t).coeff i =
      -(TensorEigenIdx.lambda (I := I) (M := M) i) *
          (tensorHeatMildSolutionHs (I := I) (M := M)
            g r s σ T₀ F t).coeff i +
        (F t).coeff i := by
  let b := tensorHsHilbertBasis (I := I) (M := M)
    (g := g) (r := r) (s := s) σ
  have hrepr := abstractSpectralDuhamelDeriv_repr_apply b
    (fun j => tensor_lambda_nonneg (I := I) (M := M) j) T₀ hF hF' ht i
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
          (tensorHeatMildSolutionHsDeriv (I := I) (M := M)
            g r s σ T₀ F F' t).coeff i =
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

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorHeatMildSolutionHs_hasDerivAt_of_hasDerivAt_aux
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (σ : ℝ)
    (T₀ : tensorHs (I := I) (M := M) g r s σ)
    {F F' : ℝ → tensorHs (I := I) (M := M) g r s σ}
    (hF : ∀ q, HasDerivAt F (F' q) q) (hF' : Continuous F')
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt
      (tensorHeatMildSolutionHs (I := I) (M := M) g r s σ T₀ F)
      (tensorHeatMildSolutionHsDeriv (I := I) (M := M)
        g r s σ T₀ F F' t) t := by
  let b := tensorHsHilbertBasis (I := I) (M := M)
    (g := g) (r := r) (s := s) σ
  have habstract := abstractSpectralDuhamel_hasDerivAt_of_hasDerivAt b
    (fun i => tensor_lambda_nonneg (I := I) (M := M) i) T₀ hF hF' ht
  have heq :
      tensorHeatMildSolutionHs (I := I) (M := M) g r s σ T₀ F =ᶠ[𝓝 t]
        abstractSpectralDuhamel b
          (fun i => tensor_lambda_nonneg (I := I) (M := M) i) T₀ F := by
    filter_upwards [Ioi_mem_nhds ht] with q hq
    exact tensorHeatMildSolutionHs_eq_abstractSpectralDuhamel
      (I := I) (M := M) g r s σ T₀ F hq.le
  simpa only [b, tensorHeatMildSolutionHsDeriv] using
    habstract.congr_of_eventuallyEq heq

def tensorHeatMildSolutionHsLiftOfHasDerivAt
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (σ : ℝ)
    (T₀ : tensorHs (I := I) (M := M) g r s σ)
    (F F' : ℝ → tensorHs (I := I) (M := M) g r s σ)
    (hF : ∀ q, HasDerivAt F (F' q) q) (hF' : Continuous F')
    (t : ℝ) (ht : 0 < t) :
    tensorHs (I := I) (M := M) g r s (σ + 2) := by
  let U := tensorHeatMildSolutionHs (I := I) (M := M) g r s σ T₀ F t
  let D := tensorHeatMildSolutionHsDeriv (I := I) (M := M)
    g r s σ T₀ F F' t
  let Z := U - D + F t
  have hZcoeff : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      Z.coeff i =
        (1 + TensorEigenIdx.lambda (I := I) (M := M) i) * U.coeff i := by
    intro i
    simp only [Z, sub_eq_add_neg, tensorHs.add_coeff, tensorHs.neg_coeff]
    rw [tensorHeatMildSolutionHsDeriv_coeff
      (I := I) (M := M) g r s σ T₀ hF hF' ht]
    ring
  exact tensorHsAddTwoOfOneAddLambdaMul (I := I) (M := M) σ U Z hZcoeff

omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem tensorHeatMildSolutionHsLiftOfHasDerivAt_coeff
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (σ : ℝ)
    (T₀ : tensorHs (I := I) (M := M) g r s σ)
    (F F' : ℝ → tensorHs (I := I) (M := M) g r s σ)
    (hF : ∀ q, HasDerivAt F (F' q) q) (hF' : Continuous F')
    (t : ℝ) (ht : 0 < t) (i : TensorEigenIdx (I := I) (M := M) g r s) :
    (tensorHeatMildSolutionHsLiftOfHasDerivAt (I := I) (M := M)
      g r s σ T₀ F F' hF hF' t ht).coeff i =
      (tensorHeatMildSolutionHs (I := I) (M := M)
        g r s σ T₀ F t).coeff i :=
  rfl

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorHsInclusion_tensorHeatMildSolutionHsLiftOfHasDerivAt
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (σ : ℝ)
    (T₀ : tensorHs (I := I) (M := M) g r s σ)
    (F F' : ℝ → tensorHs (I := I) (M := M) g r s σ)
    (hF : ∀ q, HasDerivAt F (F' q) q) (hF' : Continuous F')
    (t : ℝ) (ht : 0 < t) :
    tensorHsInclusion (I := I) (M := M)
        (g := g) (r := r) (s := s) (show σ ≤ σ + 2 by linarith)
        (tensorHeatMildSolutionHsLiftOfHasDerivAt (I := I) (M := M)
          g r s σ T₀ F F' hF hF' t ht) =
      tensorHeatMildSolutionHs (I := I) (M := M) g r s σ T₀ F t := by
  apply tensorHs.ext
  funext i
  rw [tensorHsInclusion_coeff_apply,
    tensorHeatMildSolutionHsLiftOfHasDerivAt_coeff]

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorHeatMildSolutionHs_hasDerivAt_of_hasDerivAt
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (σ : ℝ)
    (T₀ : tensorHs (I := I) (M := M) g r s σ)
    {F F' : ℝ → tensorHs (I := I) (M := M) g r s σ}
    (hF : ∀ q, HasDerivAt F (F' q) q) (hF' : Continuous F')
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt
      (tensorHeatMildSolutionHs (I := I) (M := M) g r s σ T₀ F)
      (tensorScaleLaplacian (I := I) (M := M) σ
          (tensorHeatMildSolutionHsLiftOfHasDerivAt (I := I) (M := M)
            g r s σ T₀ F F' hF hF' t ht) + F t) t := by
  have haux := tensorHeatMildSolutionHs_hasDerivAt_of_hasDerivAt_aux
    (I := I) (M := M) g r s σ T₀ hF hF' ht
  apply haux.congr_deriv
  apply tensorHs.ext
  funext i
  rw [tensorHeatMildSolutionHsDeriv_coeff
      (I := I) (M := M) g r s σ T₀ hF hF' ht]
  change _ =
    (tensorScaleLaplacian (I := I) (M := M) σ
      (tensorHeatMildSolutionHsLiftOfHasDerivAt (I := I) (M := M)
        g r s σ T₀ F F' hF hF' t ht)).coeff i + (F t).coeff i
  rw [tensorScaleLaplacian_coeff,
    tensorHeatMildSolutionHsLiftOfHasDerivAt_coeff]

omit [NeZero (Module.finrank ℝ E)] in
theorem deriv_tensorHeatMildSolutionHs_eq_tensorScaleLaplacian_add_of_hasDerivAt
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (σ : ℝ)
    (T₀ : tensorHs (I := I) (M := M) g r s σ)
    {F F' : ℝ → tensorHs (I := I) (M := M) g r s σ}
    (hF : ∀ q, HasDerivAt F (F' q) q) (hF' : Continuous F')
    {t : ℝ} (ht : 0 < t) :
    deriv (tensorHeatMildSolutionHs (I := I) (M := M) g r s σ T₀ F) t =
      tensorScaleLaplacian (I := I) (M := M) σ
          (tensorHeatMildSolutionHsLiftOfHasDerivAt (I := I) (M := M)
            g r s σ T₀ F F' hF hF' t ht) + F t :=
  (tensorHeatMildSolutionHs_hasDerivAt_of_hasDerivAt
    (I := I) (M := M) g r s σ T₀ hF hF' ht).deriv

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorHeatMildSolutionHs_differentiableOn_of_hasDerivAt
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (σ : ℝ)
    (T₀ : tensorHs (I := I) (M := M) g r s σ)
    {F F' : ℝ → tensorHs (I := I) (M := M) g r s σ}
    (hF : ∀ q, HasDerivAt F (F' q) q) (hF' : Continuous F') :
    DifferentiableOn ℝ
      (tensorHeatMildSolutionHs (I := I) (M := M) g r s σ T₀ F)
      (Set.Ioi 0) := by
  intro t ht
  exact (tensorHeatMildSolutionHs_hasDerivAt_of_hasDerivAt
    (I := I) (M := M) g r s σ T₀ hF hF' ht).differentiableAt.differentiableWithinAt

def tensorHeatMildSolutionHsLiftOfContDiff
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (σ : ℝ)
    (T₀ : tensorHs (I := I) (M := M) g r s σ)
    (F : ℝ → tensorHs (I := I) (M := M) g r s σ)
    (hF : ContDiff ℝ 1 F) (t : ℝ) (ht : 0 < t) :
    tensorHs (I := I) (M := M) g r s (σ + 2) :=
  tensorHeatMildSolutionHsLiftOfHasDerivAt (I := I) (M := M)
    g r s σ T₀ F (deriv F)
      (fun q => (hF.differentiable one_ne_zero q).hasDerivAt)
      hF.continuous_deriv_one t ht

omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem tensorHeatMildSolutionHsLiftOfContDiff_coeff
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (σ : ℝ)
    (T₀ : tensorHs (I := I) (M := M) g r s σ)
    (F : ℝ → tensorHs (I := I) (M := M) g r s σ)
    (hF : ContDiff ℝ 1 F) (t : ℝ) (ht : 0 < t)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    (tensorHeatMildSolutionHsLiftOfContDiff (I := I) (M := M)
      g r s σ T₀ F hF t ht).coeff i =
      (tensorHeatMildSolutionHs (I := I) (M := M)
        g r s σ T₀ F t).coeff i :=
  rfl

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorHsInclusion_tensorHeatMildSolutionHsLiftOfContDiff
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (σ : ℝ)
    (T₀ : tensorHs (I := I) (M := M) g r s σ)
    (F : ℝ → tensorHs (I := I) (M := M) g r s σ)
    (hF : ContDiff ℝ 1 F) (t : ℝ) (ht : 0 < t) :
    tensorHsInclusion (I := I) (M := M)
        (g := g) (r := r) (s := s) (show σ ≤ σ + 2 by linarith)
        (tensorHeatMildSolutionHsLiftOfContDiff (I := I) (M := M)
          g r s σ T₀ F hF t ht) =
      tensorHeatMildSolutionHs (I := I) (M := M) g r s σ T₀ F t := by
  apply tensorHs.ext
  funext i
  rw [tensorHsInclusion_coeff_apply,
    tensorHeatMildSolutionHsLiftOfContDiff_coeff]

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorHeatMildSolutionHs_hasDerivAt_of_contDiff
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (σ : ℝ)
    (T₀ : tensorHs (I := I) (M := M) g r s σ)
    {F : ℝ → tensorHs (I := I) (M := M) g r s σ}
    (hF : ContDiff ℝ 1 F) {t : ℝ} (ht : 0 < t) :
    HasDerivAt
      (tensorHeatMildSolutionHs (I := I) (M := M) g r s σ T₀ F)
      (tensorScaleLaplacian (I := I) (M := M) σ
          (tensorHeatMildSolutionHsLiftOfContDiff (I := I) (M := M)
            g r s σ T₀ F hF t ht) + F t) t := by
  simpa only [tensorHeatMildSolutionHsLiftOfContDiff] using
    tensorHeatMildSolutionHs_hasDerivAt_of_hasDerivAt
      (I := I) (M := M) g r s σ T₀
      (fun q => (hF.differentiable one_ne_zero q).hasDerivAt)
      hF.continuous_deriv_one ht

omit [NeZero (Module.finrank ℝ E)] in
theorem deriv_tensorHeatMildSolutionHs_eq_tensorScaleLaplacian_add_of_contDiff
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (σ : ℝ)
    (T₀ : tensorHs (I := I) (M := M) g r s σ)
    {F : ℝ → tensorHs (I := I) (M := M) g r s σ}
    (hF : ContDiff ℝ 1 F) {t : ℝ} (ht : 0 < t) :
    deriv (tensorHeatMildSolutionHs (I := I) (M := M) g r s σ T₀ F) t =
      tensorScaleLaplacian (I := I) (M := M) σ
          (tensorHeatMildSolutionHsLiftOfContDiff (I := I) (M := M)
            g r s σ T₀ F hF t ht) + F t :=
  (tensorHeatMildSolutionHs_hasDerivAt_of_contDiff
    (I := I) (M := M) g r s σ T₀ hF ht).deriv

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorHeatMildSolutionHs_differentiableOn_of_contDiff
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (σ : ℝ)
    (T₀ : tensorHs (I := I) (M := M) g r s σ)
    {F : ℝ → tensorHs (I := I) (M := M) g r s σ}
    (hF : ContDiff ℝ 1 F) :
    DifferentiableOn ℝ
      (tensorHeatMildSolutionHs (I := I) (M := M) g r s σ T₀ F)
      (Set.Ioi 0) := by
  intro t ht
  exact (tensorHeatMildSolutionHs_hasDerivAt_of_contDiff
    (I := I) (M := M) g r s σ T₀ hF ht).differentiableAt.differentiableWithinAt

end TensorHeatEquation

end Parabolic
end Analysis
end DifferentialGeometry

end
