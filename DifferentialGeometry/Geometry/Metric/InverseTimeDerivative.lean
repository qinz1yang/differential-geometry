import DifferentialGeometry.Geometry.Metric.TensorInner.Cotangent.InverseMetric
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Ricci.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Normed.Module.FiniteDimension

set_option autoImplicit false
noncomputable section
open Set Bundle Manifold DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff BigOperators Matrix.Norms.Elementwise
namespace DifferentialGeometry.Geometry.Metric

private def matrixOperator {ι : Type*} [Fintype ι] [DecidableEq ι] :
    Matrix ι ι ℝ ≃L[ℝ] ((ι → ℝ) →L[ℝ] (ι → ℝ)) :=
  (Matrix.toLin'.trans LinearMap.toContinuousLinearMap).toContinuousLinearEquiv

private theorem matrixOperator_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℝ) : matrixOperator (A * B) = matrixOperator A * matrixOperator B := by
  ext v i
  change Matrix.toLin' (A * B) v i = Matrix.toLin' A (Matrix.toLin' B v) i
  rw [Matrix.toLin'_mul]
  rfl

private theorem matrixOperator_one {ι : Type*} [Fintype ι] [DecidableEq ι] :
    matrixOperator (1 : Matrix ι ι ℝ) = 1 := by
  ext v i
  change Matrix.toLin' (1 : Matrix ι ι ℝ) v i = v i
  rw [Matrix.toLin'_one]
  rfl

private theorem inverse_matrix_time {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : ℝ → Matrix ι ι ℝ) (Adot : Matrix ι ι ℝ) (J : Set ℝ) (t : ℝ)
    (hAB : ∀ r, A r * B r = 1) (hBA : ∀ r, B r * A r = 1)
    (hA : HasDerivWithinAt A Adot J t) :
    HasDerivWithinAt B (-(B t * Adot * B t)) J t := by
  let C : Matrix ι ι ℝ ≃L[ℝ] ((ι → ℝ) →L[ℝ] (ι → ℝ)) := matrixOperator
  let U (r : ℝ) : (((ι → ℝ) →L[ℝ] (ι → ℝ)))ˣ :=
    { val := C (A r)
      inv := C (B r)
      val_inv := by rw [← matrixOperator_mul, hAB r, matrixOperator_one]
      inv_val := by rw [← matrixOperator_mul, hBA r, matrixOperator_one] }
  have hC : HasDerivWithinAt (fun r => C (A r)) (C Adot) J t :=
    C.toContinuousLinearMap.hasFDerivAt.comp_hasDerivWithinAt (f := A) t hA
  have hi := (hasFDerivAt_ringInverse (U t)).comp_hasDerivWithinAt t hC
  have he (r : ℝ) : Ring.inverse (C (A r)) = C (B r) := Ring.inverse_unit (U r)
  have hB : HasDerivWithinAt (fun r => C (B r)) (-(C (B t) * C Adot * C (B t))) J t := by
    apply hi.congr
    · intro r _
      exact (he r).symm
    · exact (he t).symm
  have hh := C.symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivWithinAt
    (f := fun r => C (B r)) t hB
  have hc : -(C (B t) * C Adot * C (B t)) = C (-(B t * Adot * B t)) := by
    simp only [map_neg, C, matrixOperator_mul]
  rw [hc] at hh
  change HasDerivWithinAt (fun r => C.symm (C (B r))) (C.symm (C (-(B t * Adot * B t)))) J t at hh
  simpa only [ContinuousLinearEquiv.symm_apply_apply] using hh

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem basisInvMetric_hasDerivWithinAt {ι : Type*} [Fintype ι]
    (g : ℝ → SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis ι ℝ (TangentSpace I x)) (gdot : ι → ι → ℝ)
    (J : Set ℝ) (t : ℝ)
    (hg : ∀ i j, HasDerivWithinAt (fun r => (g r).inner x (basis i) (basis j)) (gdot i j) J t)
    (i j : ι) :
    HasDerivWithinAt (fun r => basisInvMetric (g r) x basis i j)
      (-(∑ a : ι, ∑ b : ι, basisInvMetric (g t) x basis i a * gdot a b * basisInvMetric (g t) x basis b j)) J t := by
  classical
  let A : ℝ → Matrix ι ι ℝ := fun r i j => (g r).inner x (basis i) (basis j)
  let B : ℝ → Matrix ι ι ℝ := fun r => basisInvMetric (g r) x basis
  have hAB (r : ℝ) : A r * B r = 1 := by
    ext a b
    exact (basisInvMetric_isInverse (g r) x basis a b).2
  have hBA (r : ℝ) : B r * A r = 1 := by
    ext a b
    exact (basisInvMetric_isInverse (g r) x basis a b).1
  have hA : HasDerivWithinAt A gdot J t :=
    hasDerivWithinAt_pi.mpr fun a => hasDerivWithinAt_pi.mpr fun b => hg a b
  have hh := inverse_matrix_time A B gdot J t hAB hBA hA
  have he := hasDerivWithinAt_pi.mp (hasDerivWithinAt_pi.mp hh i) j
  apply he.congr_deriv
  change -(∑ b : ι, (∑ a : ι, B t i a * gdot a b) * B t b j) = _
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]

variable [T2Space M] [BoundarylessManifold I M]

theorem basisInvMetric_hasDerivWithinAt_ricciFlow {ι : Type*} [Fintype ι]
    (g : ℝ → SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis ι ℝ (TangentSpace I x)) (J : Set ℝ) (t : ℝ)
    (hflow : ∀ v w : TangentSpace I x,
      HasDerivWithinAt (fun r => (g r).inner x v w) (-2 * ricciTensor (g t) x v w) J t)
    (i j : ι) :
    HasDerivWithinAt (fun r => basisInvMetric (g r) x basis i j)
      (2 * ∑ a : ι, ∑ b : ι, basisInvMetric (g t) x basis i a *
        basisInvMetric (g t) x basis j b * ricciTensor (g t) x (basis a) (basis b)) J t := by
  classical
  have hh := basisInvMetric_hasDerivWithinAt g x basis
    (fun a b => -2 * ricciTensor (g t) x (basis a) (basis b)) J t (fun a b => hflow (basis a) (basis b)) i j
  apply hh.congr_deriv
  simp only [Finset.mul_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [basisInvMetric_symm (g t) x basis b j]
  ring
end DifferentialGeometry.Geometry.Metric
