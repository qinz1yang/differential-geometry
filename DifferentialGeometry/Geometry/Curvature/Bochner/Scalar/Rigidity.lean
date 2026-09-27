import DifferentialGeometry.Geometry.Curvature.Bochner.Scalar.CoordinateFormula
import DifferentialGeometry.Geometry.Operator.Laplacian.LeviCivitaIdentification

set_option autoImplicit false
noncomputable section
open Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Operator

namespace DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem covariantDerivative_gradFun_eq_zero_of_laplacian_normGradSqFun_nonpos
    (g : SmoothRiemannianMetric I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M)
    (hnorm : ΔG g ⟨normGradSqFun g f, normGradSqFun_contMDiff g hf⟩ x ≤ 0)
    (hRic : 0 ≤ ricciTensor g x (gradFun g f x) (gradFun g f x))
    (hlap : 0 ≤ g.inner x (gradFun g f x) (gradFun g (ΔG g ⟨f, hf⟩) x)) :
    (LeviCivita g).toFun (fun y => gradFun g f y) x = 0 := by
  by_cases hd : Module.finrank ℝ E = 0
  · let : Subsingleton E := Module.finrank_zero_iff.mp hd
    ext v
    exact @Subsingleton.elim E _ _ _
  · let : NeZero (Module.finrank ℝ E) := ⟨hd⟩
    apply (frobeniusSqGradVector_eq_zero_iff g (fun y => gradFun g f y) x).mp
    have hbochner := bochner_pointwise_grad_normSq_of_boundaryless g hf x
    have hnonneg := frobeniusSq_grad_vector_nonneg g (fun y => gradFun g f y) x
    linarith

theorem covariantDerivative_gradFun_eq_zero_of_harmonic_of_locally_constant_norm
    (g : SmoothRiemannianMetric I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M) {c : ℝ}
    (hnorm : normGradSqFun g f =ᶠ[𝓝 x] fun _ => c)
    (hlap : ΔG g ⟨f, hf⟩ =ᶠ[𝓝 x] fun _ => 0)
    (hRic : 0 ≤ ricciTensor g x (gradFun g f x) (gradFun g f x)) :
    (LeviCivita g).toFun (fun y => gradFun g f y) x = 0 := by
  apply covariantDerivative_gradFun_eq_zero_of_laplacian_normGradSqFun_nonpos g hf x
  · have heq := Δ_g_congr_of_eventuallyEq g (normGradSqFun_contMDiff g hf)
      contMDiff_const hnorm
    exact (heq.trans (Δ_g_const g c x)).le
  · exact hRic
  · have hgrad : gradFun g (ΔG g ⟨f, hf⟩) x = 0 := by
      apply gradFun_eq_zero_of_mfderiv_eq_zero
      rw [hlap.mfderiv_eq, mfderiv_const]
      rfl
    rw [hgrad, map_zero]

end DifferentialGeometry.Geometry.Curvature
