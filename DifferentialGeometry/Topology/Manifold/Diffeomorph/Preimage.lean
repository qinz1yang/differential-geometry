import DifferentialGeometry.Topology.Manifold.ContMDiff.OpenSubtype
import Mathlib.Geometry.Manifold.Diffeomorph

set_option autoImplicit false
open Set Function Manifold TopologicalSpace
open scoped ContDiff Topology
noncomputable section
namespace Poincare.Manifold.Diffeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E H M : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {F G N : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [TopologicalSpace G] [TopologicalSpace N] [ChartedSpace G N]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F G} {n : ℕ∞ω}

def preimage (e : Diffeomorph I J M N n) (U : Opens N) :
    Diffeomorph I J (⟨e ⁻¹' U, U.isOpen.preimage e.continuous⟩ : Opens M) U n := by
  let S : Opens M := ⟨e ⁻¹' U, U.isOpen.preimage e.continuous⟩
  let h : S ≃ₜ U := e.toHomeomorph.subtype (fun _ => Iff.rfl)
  have hf : ContMDiff I J n h := by
    apply (Poincare.Manifold.contMDiff_subtypeVal_comp_iff U h).mp
    exact e.contMDiff.comp contMDiff_subtype_val
  have hg : ContMDiff J I n h.symm := by
    apply (Poincare.Manifold.contMDiff_subtypeVal_comp_iff S h.symm).mp
    exact e.symm.contMDiff.comp contMDiff_subtype_val
  exact ⟨h.toEquiv, hf, hg⟩


theorem preimage_apply (e : Diffeomorph I J M N n) (U : Opens N)
    (x : (⟨e ⁻¹' U, U.isOpen.preimage e.continuous⟩ : Opens M)) :
    (preimage e U x : N) = e x.val := rfl


theorem preimage_symm_apply (e : Diffeomorph I J M N n) (U : Opens N) (y : U) :
    ((preimage e U).symm y : M) = e.symm y.val := rfl

end Poincare.Manifold.Diffeomorph
