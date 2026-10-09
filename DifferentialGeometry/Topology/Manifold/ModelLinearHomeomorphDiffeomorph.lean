import DifferentialGeometry.Topology.Manifold.ModelImmersion
import Mathlib.Geometry.Manifold.Diffeomorph

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff

namespace DifferentialGeometry.Manifold

variable {𝕜 E F H K : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [TopologicalSpace H] [TopologicalSpace K]



def modelLinearHomeomorphDiffeomorph
    (I : ModelWithCorners 𝕜 E H) (J : ModelWithCorners 𝕜 F K)
    (e : H ≃ₜ K) (L : E ≃L[𝕜] F) (hc : ∀ x, J (e x) = L (I x)) :
    Diffeomorph I J H K ∞ where
  toEquiv := e.toEquiv
  contMDiff_toFun := by
    apply (ContMDiff.iff_comp_isImmersion (J.isImmersion_coe ∞)).mpr
    refine ⟨e.continuous, ?_⟩
    exact (L.contDiff.contMDiff.comp I.contMDiff).congr hc
  contMDiff_invFun := by
    apply (ContMDiff.iff_comp_isImmersion (I.isImmersion_coe ∞)).mpr
    refine ⟨e.symm.continuous, ?_⟩
    apply (L.symm.contDiff.contMDiff.comp J.contMDiff).congr
    intro y
    apply L.injective
    change L (I (e.symm y)) = L (L.symm (J y))
    rw [L.apply_symm_apply, ← hc, e.apply_symm_apply]

theorem modelLinearHomeomorphDiffeomorph_apply
    (I : ModelWithCorners 𝕜 E H) (J : ModelWithCorners 𝕜 F K)
    (e : H ≃ₜ K) (L : E ≃L[𝕜] F) (hc : ∀ x, J (e x) = L (I x)) (x : H) :
    modelLinearHomeomorphDiffeomorph I J e L hc x = e x := rfl

theorem modelLinearHomeomorphDiffeomorph_symm_apply
    (I : ModelWithCorners 𝕜 E H) (J : ModelWithCorners 𝕜 F K)
    (e : H ≃ₜ K) (L : E ≃L[𝕜] F) (hc : ∀ x, J (e x) = L (I x)) (y : K) :
    (modelLinearHomeomorphDiffeomorph I J e L hc).symm y = e.symm y := rfl

end DifferentialGeometry.Manifold
