import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapAtlas

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]

def modelThreeDiffeomorph (hdim : Module.finrank ℝ E = 3) : H ≃ₘ⟮I, 𝓡 3⟯ E3 where
  toEquiv := (modelThreeHomeomorph I hdim).toEquiv
  contMDiff_toFun := by
    exact ((LinearEquiv.ofFinrankEq (R := ℝ) E E3 (by simpa using hdim)).toContinuousLinearEquiv.contDiff.contMDiff).comp I.contMDiff
  contMDiff_invFun := by
    have hs : ContMDiff 𝓘(ℝ, E) I ∞ I.symm := by
      rw [← contMDiffOn_univ, ← I.range_eq_univ]
      exact I.contMDiffOn_symm
    exact hs.comp ((LinearEquiv.ofFinrankEq (R := ℝ) E E3 (by simpa using hdim)).toContinuousLinearEquiv.symm.contDiff.contMDiff)

theorem modelThreeDiffeomorph_apply (hdim : Module.finrank ℝ E = 3) (x : H) :
    modelThreeDiffeomorph I hdim x = modelThreeHomeomorph I hdim x := rfl

theorem modelThreeDiffeomorph_symm_apply (hdim : Module.finrank ℝ E = 3) (x : E3) :
    (modelThreeDiffeomorph I hdim).symm x = (modelThreeHomeomorph I hdim).symm x := rfl
end DifferentialGeometry.Topology.ThreeManifold.Surgery
