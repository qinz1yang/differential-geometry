import DifferentialGeometry.Analysis.Sobolev.Nirenberg.H2Regularity
import DifferentialGeometry.Analysis.Sobolev.Chart.Defs
import DifferentialGeometry.Geometry.Laplacian

/-!
# Chart-local elliptic bilinear forms for the variational Laplacian on a
Riemannian manifold

This module supplies the foundational chart-local divergence-form bilinear
form needed to apply the Euclidean second-order interior regularity theorem
`h2_loc_smooth_solution` to chart-pushed scalar functions on a smooth
manifold equipped with a smooth Riemannian metric.

The construction is the **constant-identity** chart-local form, which
realises the Euclidean Laplacian as a `SmoothEllipticBilinearForm` on
`EuclideanSpace ℝ (Fin (Module.finrank ℝ E))`. It is the universal building
block that does not depend on the manifold's metric structure: every
manifold-side variational Laplacian, after chart-localisation, reduces to a
divergence-form Euclidean equation, and the constant-identity form is the
simplest concrete instance whose coefficient data satisfies the
`SmoothEllipticBilinearForm` structure.

Concretely we exhibit:

* `chartLocalEuclideanForm Ω` — the `SmoothEllipticBilinearForm` with `a` the
  identity matrix, `c = 0`, and ellipticity constants `lam = capLam = 1`,
  defined on any open subset `Ω` of the model Euclidean space.

The principal integrand of `chartLocalEuclideanForm Ω` agrees with
`∑_i (∂_i u) (∂_i v)`, the standard Euclidean Dirichlet integrand.

## Mathematical context

The variational Laplacian `Δ_g u = div_g(grad_g u)` chart-localises to the
Euclidean divergence-form operator
`(1/√det g) · ∂_i(√det g · g^{ij} · ∂_j ũ)`, where `ũ := u ∘ chart^{-1}`.
The associated bilinear form integrand is `√det g · g^{ij} · ∂_i ũ ∂_j ṽ`.
On a precompact open subset of the chart range where the Gram matrix is
uniformly positive definite, this defines a `SmoothEllipticBilinearForm`
modulo a smooth global extension off the precompact subset.

The full geometric construction (with the matrix-valued coefficient
`√det g · g^{ij}` smoothly extended off the chart range) requires substantial
additional infrastructure: a smooth global extension to all of
`EuclideanSpace ℝ (Fin _)` matching `√det g · g^{ij}` on a precompact open
subset of the chart range and remaining uniformly elliptic globally. This
will be developed in subsequent modules. The present module supplies the
constant-coefficient form, which already establishes the `SmoothEllipticBilinearForm`
API on the chart side and demonstrates the connection with
`h2_loc_smooth_solution`.
-/

noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold
open scoped Manifold ContDiff ENNReal NNReal Matrix

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace EllipticRegularity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]

/-- The constant identity bilinear form on any open set
`Ω : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))`. This packages the
Euclidean Laplacian's divergence-form data as a `SmoothEllipticBilinearForm`,
with matrix coefficient the identity and zeroth-order coefficient zero. -/
def chartLocalEuclideanForm
    (Ω : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))) :
    DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm
      (Module.finrank ℝ E) Ω where
  a := fun _ => (1 : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ)
  c := fun _ => 0
  symm := by
    intro _ i j
    by_cases hij : i = j
    · subst hij; rfl
    · simp [hij, Ne.symm hij]
  smooth_a := by
    intro i j
    by_cases hij : i = j
    · subst hij
      have hone : (fun _ : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
          (1 : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ) i i) =
          (fun _ => (1 : ℝ)) := by
        funext _
        simp
      rw [hone]
      exact contDiff_const
    · have hzero : (fun _ : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
          (1 : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ) i j) =
          (fun _ => (0 : ℝ)) := by
        funext _
        simp [hij]
      rw [hzero]
      exact contDiff_const
  smooth_c := contDiff_const
  lam := 1
  capLam := 1
  hlam_pos := by norm_num
  hlam_le_capLam := le_refl _
  coercive := by
    intro x _hx ξ
    have h_id_action :
        DeGiorgi.matMulE
          (1 : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ) ξ = ξ := by
      ext i
      rw [DeGiorgi.matMulE_apply]
      rw [Matrix.one_mulVec]
    rw [h_id_action]
    rw [one_mul, real_inner_self_eq_norm_mul_norm, sq]

@[simp] lemma chartLocalEuclideanForm_a_apply
    (Ω : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))))
    (x : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    (chartLocalEuclideanForm (E := E) Ω).a x =
      (1 : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ) := rfl

@[simp] lemma chartLocalEuclideanForm_c_apply
    (Ω : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))))
    (x : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    (chartLocalEuclideanForm (E := E) Ω).c x = 0 := rfl

@[simp] lemma chartLocalEuclideanForm_lam
    (Ω : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))) :
    (chartLocalEuclideanForm (E := E) Ω).lam = 1 := rfl

@[simp] lemma chartLocalEuclideanForm_capLam
    (Ω : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))) :
    (chartLocalEuclideanForm (E := E) Ω).capLam = 1 := rfl

/-- The principal integrand of the constant-identity form is the standard
Euclidean Dirichlet pairing `∑_i (∂_i u) (∂_i v)`. -/
theorem chartLocalEuclideanForm_principalIntegrand
    (Ω : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))))
    (u v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ)
    (x : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.principalIntegrand
      (chartLocalEuclideanForm (E := E) Ω) u v x =
      ∑ i : Fin (Module.finrank ℝ E),
        ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
          ((fderiv ℝ v x) (EuclideanSpace.single i 1)) := by
  classical
  unfold DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.principalIntegrand
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [Finset.sum_eq_single i]
  · simp [chartLocalEuclideanForm_a_apply]
  · intro j _ hji
    have h1 : (chartLocalEuclideanForm (E := E) Ω).a x i j = 0 := by
      rw [chartLocalEuclideanForm_a_apply]
      simp [hji.symm]
    rw [h1]; ring
  · intro hk
    exact absurd (Finset.mem_univ i) hk

/-- The principal integrand of the constant-identity form, evaluated at
`u = v`, equals the squared norm of the gradient vector. -/
theorem chartLocalEuclideanForm_principalIntegrand_self
    (Ω : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))))
    (u : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ)
    (x : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.principalIntegrand
      (chartLocalEuclideanForm (E := E) Ω) u u x =
      ∑ i : Fin (Module.finrank ℝ E),
        ((fderiv ℝ u x) (EuclideanSpace.single i 1)) ^ 2 := by
  rw [chartLocalEuclideanForm_principalIntegrand]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [sq]

/-- The principal integrand of the constant-identity form at `u = v` equals
the squared norm of `gradientVec`, the Euclidean-vector packaging of the
gradient. -/
theorem chartLocalEuclideanForm_principalIntegrand_self_eq_gradient_sq
    (Ω : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))))
    (u : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ)
    (x : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.principalIntegrand
      (chartLocalEuclideanForm (E := E) Ω) u u x =
      ‖DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.gradientVec
        (chartLocalEuclideanForm (E := E) Ω) u x‖ ^ 2 := by
  rw [chartLocalEuclideanForm_principalIntegrand_self]
  rw [DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.gradientVec_norm_sq_eq_sum]

/-- The bilinear form of the constant-identity chart-local form is the
standard Euclidean Dirichlet bilinear form, integrated over `Ω`. -/
theorem chartLocalEuclideanForm_bilin
    (Ω : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))))
    (u v : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ) :
    DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.bilin
      (chartLocalEuclideanForm (E := E) Ω) u v =
      ∫ x in Ω,
        (∑ i : Fin (Module.finrank ℝ E),
          ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
            ((fderiv ℝ v x) (EuclideanSpace.single i 1)))
        ∂(volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))) := by
  unfold DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.bilin
  refine integral_congr_ae ?_
  refine Filter.Eventually.of_forall ?_
  intro x
  change DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean.SmoothEllipticBilinearForm.principalIntegrand
      (chartLocalEuclideanForm (E := E) Ω) u v x +
      (chartLocalEuclideanForm (E := E) Ω).c x * u x * v x =
      ∑ i : Fin (Module.finrank ℝ E),
        ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
          ((fderiv ℝ v x) (EuclideanSpace.single i 1))
  rw [chartLocalEuclideanForm_principalIntegrand, chartLocalEuclideanForm_c_apply]
  ring

end EllipticRegularity
end Laplacian
end Analysis
end DifferentialGeometry
