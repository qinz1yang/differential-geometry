import DifferentialGeometry.Geometry.Collapse.EdgeCylinderSourceChart

/-!
# Consumer: the flat cylinder chart into `E3`

`S = E2`, `N = X = E3`, `Θ = L⁻¹ : ℝ × E2 → E3` for the fixed identification `L : E3 ≃ ℝ × E2`,
`j = id`, any nonempty open `U ⊆ ℝ × E2` and `O = E3`: B3 gives a `C^∞` partial diffeomorphism
`U → E3` for the common model `𝓘(ℝ, ℝ).prod (𝓡 2)` with source `univ` and target `L⁻¹(U)`
(`flatEdgeCylinder_source_partialDiffeomorph`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Manifold

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E2" => EuclideanSpace ℝ (Fin 2)

/-- The inverse identification `ℝ × E2 → E3` as a smooth diffeomorphism for the product model. -/
def flatEdgeCylinderDiffeomorph :
    Diffeomorph (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) (ℝ × E2) E3 ∞ where
  toEquiv := euclideanThreeProdEquiv.symm.toEquiv
  contMDiff_toFun := euclideanThreeProdEquiv.symm.contDiff.contMDiff.comp
    (contMDiff_fst.prodMk_space contMDiff_snd)
  contMDiff_invFun :=
    ((ContinuousLinearMap.fst ℝ ℝ E2).contDiff.comp euclideanThreeProdEquiv.contDiff).contMDiff.prodMk
      ((ContinuousLinearMap.snd ℝ ℝ E2).contDiff.comp euclideanThreeProdEquiv.contDiff).contMDiff

/-- **Concrete consumer.** The flat cylinder chart: for every nonempty open `U ⊆ ℝ × E2` the map
`x ↦ L⁻¹ x` is a smooth partial diffeomorphism `U → E3` for the common product model, with source
`univ` and target its image. -/
theorem flatEdgeCylinder_source_partialDiffeomorph (U : TopologicalSpace.Opens (ℝ × E2))
    (hU : Nonempty U) :
    letI := chartedSpaceTransHomeomorph (M := (⊤ : TopologicalSpace.Opens E3))
      euclideanThreeProdHomeomorph
    ∃ J : PartialDiffeomorph (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓘(ℝ, ℝ).prod (𝓡 2)) U
        (⊤ : TopologicalSpace.Opens E3) ∞,
      J.source = univ ∧ (∀ x : U, ((J x : (⊤ : TopologicalSpace.Opens E3)) : E3) =
        euclideanThreeProdEquiv.symm x) ∧
      ∀ y : (⊤ : TopologicalSpace.Opens E3),
        y ∈ J.target ↔ ∃ x : U, euclideanThreeProdEquiv.symm x = y := by
  exact exists_edgeCylinder_source_partialDiffeomorph flatEdgeCylinderDiffeomorph
    (Diffeomorph.refl 𝓘(ℝ, E3) E3 ∞).toPartialDiffeomorph U hU ⊤
    (fun x _ => ⟨mem_univ _, trivial⟩)

end DifferentialGeometry.Geometry.Collapse
