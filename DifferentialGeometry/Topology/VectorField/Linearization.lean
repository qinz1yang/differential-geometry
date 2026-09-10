import Mathlib.Analysis.Calculus.VectorField
import Mathlib.LinearAlgebra.Determinant

open Filter ContinuousLinearMap
open scoped Topology

namespace Poincare.VectorField

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

theorem pullback_eq_zero_iff_of_isInvertible {f : E → F} (V : F → F) {x : E}
    (hinv : (fderiv 𝕜 f x).IsInvertible) :
    _root_.VectorField.pullback 𝕜 f V x = 0 ↔ V (f x) = 0 := by
  obtain ⟨e, he⟩ := hinv
  simp [_root_.VectorField.pullback, ← he]

variable [CompleteSpace E]

theorem fderiv_pullback_of_eq_zero {f : E → F} {V : F → F} {x : E}
    (hf : ContDiffAt 𝕜 2 f x) (hinv : (fderiv 𝕜 f x).IsInvertible)
    (hV : DifferentiableAt 𝕜 V (f x)) (hzero : V (f x) = 0) :
    fderiv 𝕜 (_root_.VectorField.pullback 𝕜 f V) x =
      (fderiv 𝕜 f x).inverse ∘L fderiv 𝕜 V (f x) ∘L fderiv 𝕜 f x := by
  obtain ⟨N, _, hNs, hN, _⟩ := exists_continuousLinearEquiv_fderiv_symm_eq hf hinv
  have hNx : (N x : E →L[𝕜] F) = fderiv 𝕜 f x := hN.self_of_nhds
  have heq : _root_.VectorField.pullback 𝕜 f V =ᶠ[𝓝 x]
      (fun y => (N y).symm (V (f y))) := by
    filter_upwards [hN] with y hy
    exact _root_.VectorField.pullback_eq_of_fderiv_eq hy V
  rw [heq.fderiv_eq]
  change fderiv 𝕜 (fun y => ((N y).symm : F →L[𝕜] E) ((V ∘ f) y)) x = _
  rw [fderiv_clm_apply (hNs.differentiableAt one_ne_zero)
    (hV.comp x (hf.differentiableAt two_ne_zero)),
    fderiv_comp x hV (hf.differentiableAt two_ne_zero)]
  simp [hzero, ← hNx]

theorem det_fderiv_pullback_of_eq_zero {f : E → F} {V : F → F} {x : E}
    (hf : ContDiffAt 𝕜 2 f x) (hinv : (fderiv 𝕜 f x).IsInvertible)
    (hV : DifferentiableAt 𝕜 V (f x)) (hzero : V (f x) = 0) :
    LinearMap.det (fderiv 𝕜 (_root_.VectorField.pullback 𝕜 f V) x).toLinearMap =
      LinearMap.det (fderiv 𝕜 V (f x)).toLinearMap := by
  rw [fderiv_pullback_of_eq_zero hf hinv hV hzero]
  obtain ⟨e, he⟩ := hinv
  rw [← he, ContinuousLinearMap.inverse_equiv]
  exact LinearMap.det_conj (fderiv 𝕜 V (f x)).toLinearMap e.symm.toLinearEquiv

end Poincare.VectorField
