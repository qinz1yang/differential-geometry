import DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.OperatorEquation
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.Semigroup.BoundedC0Semigroup
import DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.SmoothingHs
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.TimeDeriv

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorHeatEquation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

def tensorHeatSemigroupHsExt
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (σ t : ℝ) :
    tensorHs (I := I) (M := M) g r s σ →L[ℝ]
      tensorHs (I := I) (M := M) g r s σ :=
  if h : 0 < t then
    tensorHeatSemigroupHs (I := I) (M := M)
      (g := g) (r := r) (s := s) h (a := σ) (b := σ)
  else
    ContinuousLinearMap.id ℝ (tensorHs (I := I) (M := M) g r s σ)

omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem tensorHeatSemigroupHsExt_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (σ : ℝ) :
    tensorHeatSemigroupHsExt (I := I) (M := M) g r s σ 0 =
      ContinuousLinearMap.id ℝ
        (tensorHs (I := I) (M := M) g r s σ) := by
  unfold tensorHeatSemigroupHsExt
  simp

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorHeatSemigroupHsExt_of_pos
    {g : SmoothRiemannianMetric I M} {r s : ℕ} {σ t : ℝ} (ht : 0 < t) :
    tensorHeatSemigroupHsExt (I := I) (M := M) g r s σ t =
      tensorHeatSemigroupHs (I := I) (M := M)
        (g := g) (r := r) (s := s) ht (a := σ) (b := σ) := by
  unfold tensorHeatSemigroupHsExt
  simp [ht]

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorHeatSemigroupHsExt_of_nonpos
    {g : SmoothRiemannianMetric I M} {r s : ℕ} {σ t : ℝ} (ht : t ≤ 0) :
    tensorHeatSemigroupHsExt (I := I) (M := M) g r s σ t =
      ContinuousLinearMap.id ℝ
        (tensorHs (I := I) (M := M) g r s σ) := by
  unfold tensorHeatSemigroupHsExt
  simp [not_lt.mpr ht]

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorHeatSemigroupHsExt_add
    {g : SmoothRiemannianMetric I M} {r s : ℕ} {σ t u : ℝ}
    (ht : 0 ≤ t) (hu : 0 ≤ u) :
    tensorHeatSemigroupHsExt (I := I) (M := M) g r s σ (t + u) =
      (tensorHeatSemigroupHsExt (I := I) (M := M) g r s σ t).comp
        (tensorHeatSemigroupHsExt (I := I) (M := M) g r s σ u) := by
  rcases eq_or_lt_of_le ht with rfl | ht
  · simp
  rcases eq_or_lt_of_le hu with rfl | hu
  · simp
  have htu : 0 < t + u := add_pos ht hu
  rw [tensorHeatSemigroupHsExt_of_pos (I := I) (M := M) htu,
    tensorHeatSemigroupHsExt_of_pos (I := I) (M := M) ht,
    tensorHeatSemigroupHsExt_of_pos (I := I) (M := M) hu]
  exact tensorHeatSemigroupHs_add_comp (I := I) (M := M) ht hu

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorHeatSemigroupHsExt_opNorm_le_one
    {g : SmoothRiemannianMetric I M} {r s : ℕ} {σ t : ℝ} (ht : 0 ≤ t) :
    ‖tensorHeatSemigroupHsExt (I := I) (M := M) g r s σ t‖ ≤ 1 := by
  rcases eq_or_lt_of_le ht with rfl | ht
  · rw [tensorHeatSemigroupHsExt_zero]
    exact ContinuousLinearMap.norm_id_le
  rw [tensorHeatSemigroupHsExt_of_pos (I := I) (M := M) ht]
  exact tensorHeatSemigroupHs_opNorm_le_one (I := I) (M := M) ht

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorHeatSemigroupHsExt_coeff
    {g : SmoothRiemannianMetric I M} {r s : ℕ} {σ t : ℝ} (ht : 0 ≤ t)
    (T : tensorHs (I := I) (M := M) g r s σ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    (tensorHeatSemigroupHsExt (I := I) (M := M) g r s σ t T).coeff i =
      Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) *
        T.coeff i := by
  rcases eq_or_lt_of_le ht with rfl | ht
  · rw [tensorHeatSemigroupHsExt_zero]
    change T.coeff i = _
    simp
  rw [tensorHeatSemigroupHsExt_of_pos (I := I) (M := M) ht]
  exact tensorHeatSemigroupHs_coeff (I := I) (M := M) ht T i

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorHsInclusion_tensorHeatSemigroupHsExt
    {g : SmoothRiemannianMetric I M} {r s : ℕ} {τ σ t : ℝ}
    (hτσ : τ ≤ σ) (ht : 0 ≤ t)
    (T : tensorHs (I := I) (M := M) g r s σ) :
    tensorHsInclusion (I := I) (M := M)
        (g := g) (r := r) (s := s) hτσ
        (tensorHeatSemigroupHsExt (I := I) (M := M) g r s σ t T) =
      tensorHeatSemigroupHsExt (I := I) (M := M) g r s τ t
        (tensorHsInclusion (I := I) (M := M)
          (g := g) (r := r) (s := s) hτσ T) := by
  apply tensorHs.ext
  funext i
  rw [tensorHsInclusion_coeff_apply,
    tensorHeatSemigroupHsExt_coeff (I := I) (M := M) ht,
    tensorHeatSemigroupHsExt_coeff (I := I) (M := M) ht,
    tensorHsInclusion_coeff_apply]

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorHeatSemigroupHsExt_eq_abstractSpectralSemigroup
    {g : SmoothRiemannianMetric I M} {r s : ℕ} {σ t : ℝ} (ht : 0 ≤ t) :
    tensorHeatSemigroupHsExt (I := I) (M := M) g r s σ t =
      abstractSpectralSemigroup
        (tensorHsHilbertBasis (I := I) (M := M)
          (g := g) (r := r) (s := s) σ)
        (fun i => tensor_lambda_nonneg (I := I) (M := M) i) t := by
  apply ContinuousLinearMap.ext
  intro T
  apply tensorHs.ext
  funext i
  set b := tensorHsHilbertBasis (I := I) (M := M)
    (g := g) (r := r) (s := s) σ with hb
  have habs := abstractSpectralSemigroup_repr_apply b
    (fun i => tensor_lambda_nonneg (I := I) (M := M) i) ht T i
  rw [hb, tensorHsHilbertBasis_repr_apply_apply,
    tensorHsHilbertBasis_repr_apply_apply] at habs
  have hsqrt_ne : Real.sqrt
      (tensorSobolevWeight (I := I) (M := M) i σ) ≠ 0 :=
    (Real.sqrt_pos.mpr
      (tensorSobolevWeight_pos (I := I) (M := M) i σ)).ne'
  apply mul_left_cancel₀ hsqrt_ne
  rw [tensorHeatSemigroupHsExt_coeff (I := I) (M := M) ht]
  rw [heatCoeff_def] at habs
  calc
    Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ) *
          (Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) *
            T.coeff i) =
        Real.exp (-(TensorEigenIdx.lambda (I := I) (M := M) i) * t) *
          (Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ) *
            T.coeff i) := by ring
    _ = Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ) *
          (abstractSpectralSemigroup b
            (fun i => tensor_lambda_nonneg (I := I) (M := M) i) t T).coeff i :=
      habs.symm

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorHeatSemigroupHsExt_continuousOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (σ : ℝ)
    (T : tensorHs (I := I) (M := M) g r s σ) :
    ContinuousOn (fun t : ℝ =>
      tensorHeatSemigroupHsExt (I := I) (M := M) g r s σ t T)
      (Set.Ici 0) := by
  set b := tensorHsHilbertBasis (I := I) (M := M)
    (g := g) (r := r) (s := s) σ
  refine (abstractSpectralSemigroup_continuousOn b
    (fun i => tensor_lambda_nonneg (I := I) (M := M) i) T).congr ?_
  intro t ht
  exact congrArg (fun A => A T)
    (tensorHeatSemigroupHsExt_eq_abstractSpectralSemigroup
      (I := I) (M := M) (g := g) (r := r) (s := s) (σ := σ) ht)

omit [NeZero (Module.finrank ℝ E)] in
theorem hasDerivAt_tensorHeatSemigroupHsExt_eq_tensorScaleLaplacian
    (g : SmoothRiemannianMetric I M) (r s : ℕ) {σ t : ℝ} (ht : 0 < t)
    (T : tensorHs (I := I) (M := M) g r s σ) :
    HasDerivAt
      (fun u : ℝ =>
        tensorHeatSemigroupHsExt (I := I) (M := M) g r s σ u T)
      (tensorScaleLaplacian (I := I) (M := M) σ
        (tensorHeatSemigroupHs (I := I) (M := M)
          (g := g) (r := r) (s := s) ht (a := σ) (b := σ + 2) T)) t := by
  set b := tensorHsHilbertBasis (I := I) (M := M)
    (g := g) (r := r) (s := s) σ with hb
  have habs := abstractSpectralSemigroup_hasDerivAt b
    (fun i => tensor_lambda_nonneg (I := I) (M := M) i) ht T
  have heq : (fun u : ℝ =>
      tensorHeatSemigroupHsExt (I := I) (M := M) g r s σ u T) =ᶠ[𝓝 t]
      (fun u : ℝ => abstractSpectralSemigroup b
        (fun i => tensor_lambda_nonneg (I := I) (M := M) i) u T) := by
    filter_upwards [Ioi_mem_nhds ht] with u hu
    exact congrArg (fun A => A T)
      (tensorHeatSemigroupHsExt_eq_abstractSpectralSemigroup
        (I := I) (M := M) (g := g) (r := r) (s := s) (σ := σ) hu.le)
  have hderiv := habs.congr_of_eventuallyEq heq
  apply hderiv.congr_deriv
  apply b.repr.injective
  apply lp.ext
  funext i
  rw [abstractSpectralSemigroupDeriv_repr_apply b
      (fun i => tensor_lambda_nonneg (I := I) (M := M) i) ht,
    hb, tensorHsHilbertBasis_repr_apply_apply,
    tensorHsHilbertBasis_repr_apply_apply,
    tensorScaleLaplacian_coeff, tensorHeatSemigroupHs_coeff,
    heatDerivCoeff_def]
  ring

omit [NeZero (Module.finrank ℝ E)] in
theorem deriv_tensorHeatSemigroupHsExt_eq_tensorScaleLaplacian
    (g : SmoothRiemannianMetric I M) (r s : ℕ) {σ t : ℝ} (ht : 0 < t)
    (T : tensorHs (I := I) (M := M) g r s σ) :
    deriv (fun u : ℝ =>
      tensorHeatSemigroupHsExt (I := I) (M := M) g r s σ u T) t =
      tensorScaleLaplacian (I := I) (M := M) σ
        (tensorHeatSemigroupHs (I := I) (M := M)
          (g := g) (r := r) (s := s) ht (a := σ) (b := σ + 2) T) :=
  (hasDerivAt_tensorHeatSemigroupHsExt_eq_tensorScaleLaplacian
    (I := I) (M := M) g r s ht T).deriv

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorHeatSemigroupHsExt_differentiableOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (σ : ℝ)
    (T : tensorHs (I := I) (M := M) g r s σ) :
    DifferentiableOn ℝ (fun t : ℝ =>
      tensorHeatSemigroupHsExt (I := I) (M := M) g r s σ t T)
      (Set.Ioi 0) := by
  intro t ht
  exact (hasDerivAt_tensorHeatSemigroupHsExt_eq_tensorScaleLaplacian
    (I := I) (M := M) g r s ht T).differentiableAt.differentiableWithinAt

def tensorHsBoundedC0Semigroup
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (σ : ℝ) :
    BoundedC0Semigroup (tensorHs (I := I) (M := M) g r s σ) where
  toFun := tensorHeatSemigroupHsExt (I := I) (M := M) g r s σ
  apply_zero := tensorHeatSemigroupHsExt_zero (I := I) (M := M) g r s σ
  apply_add := fun _ _ ht hu =>
    tensorHeatSemigroupHsExt_add (I := I) (M := M) ht hu
  opNorm_le_one := fun _ ht =>
    tensorHeatSemigroupHsExt_opNorm_le_one (I := I) (M := M) ht
  continuousOn_apply := fun T =>
    tensorHeatSemigroupHsExt_continuousOn (I := I) (M := M) g r s σ T

omit [NeZero (Module.finrank ℝ E)] in
@[simp] theorem tensorHsBoundedC0Semigroup_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (σ t : ℝ) :
    tensorHsBoundedC0Semigroup (I := I) (M := M) g r s σ t =
      tensorHeatSemigroupHsExt (I := I) (M := M) g r s σ t :=
  rfl

end TensorHeatEquation
end Parabolic
end Analysis
end DifferentialGeometry

end
