import DifferentialGeometry.Topology.Manifold.EuclideanHalfSpaceInteriorCoordinates
import DifferentialGeometry.Topology.Manifold.ModelLinearHomeomorphDiffeomorph
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph

set_option autoImplicit false
noncomputable section
open Set Manifold DifferentialGeometry.Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.Manifold

private abbrev E2 := EuclideanSpace ℝ (Fin 2)
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

private def halfSpaceThreeSplitDiffeomorph :
    Diffeomorph (𝓡 3) (𝓘(ℝ).prod (𝓡 2)) E3 (ℝ × E2) ∞ where
  toEquiv := halfSpaceThreeSplit.toEquiv
  contMDiff_toFun := by
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
    exact halfSpaceThreeSplit.contDiff.contMDiff
  contMDiff_invFun := by
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
    exact halfSpaceThreeSplit.symm.contDiff.contMDiff

private def halfSpaceInteriorPartialDiffeomorph (a : ℝ) :
    _root_.PartialDiffeomorph 𝓘(ℝ) (𝓡∂ 1) ℝ (EuclideanHalfSpace 1) ∞ where
  __ := halfSpaceInteriorChart a
  contMDiffOn_toFun := halfSpaceInteriorChart_contMDiffOn a
  contMDiffOn_invFun := (halfSpaceInteriorChart_symm_contMDiff a).contMDiffOn

private def halfSpaceThreeModelDiffeomorph :
    Diffeomorph ((𝓡∂ 1).prod (𝓡 2)) (𝓡∂ 3)
      (ModelProd (EuclideanHalfSpace 1) E2) (EuclideanHalfSpace 3) ∞ :=
  modelLinearHomeomorphDiffeomorph ((𝓡∂ 1).prod (𝓡 2)) (𝓡∂ 3)
    (euclideanHalfSpaceProdLeftHomeomorph 0 2)
    (euclideanHalfSpaceProdLeftCoordinates 0 2)
    (euclideanHalfSpaceProdLeftHomeomorph_model 0 2)

private def halfSpaceThreeProductDiffeomorph :
    Diffeomorph ((𝓡∂ 1).prod (𝓡 2)) (𝓡∂ 3)
      (EuclideanHalfSpace 1 × E2) (EuclideanHalfSpace 3) ∞ where
  toEquiv := halfSpaceThreeModelDiffeomorph.toEquiv
  contMDiff_toFun := by
    rw [chartedSpaceSelf_prod]
    exact halfSpaceThreeModelDiffeomorph.contMDiff
  contMDiff_invFun := by
    rw [chartedSpaceSelf_prod]
    exact halfSpaceThreeModelDiffeomorph.symm.contMDiff

def halfSpaceThreeInteriorPartialDiffeomorph (a : ℝ) :
    _root_.PartialDiffeomorph (𝓡 3) (𝓡∂ 3) E3 (EuclideanHalfSpace 3) ∞ :=
  (halfSpaceThreeSplitDiffeomorph.toPartialDiffeomorph.trans
    (DifferentialGeometry.Topology.PartialDiffeomorph.prod
      (halfSpaceInteriorPartialDiffeomorph a)
      (Diffeomorph.refl (𝓡 2) E2 ∞).toPartialDiffeomorph)).trans
        halfSpaceThreeProductDiffeomorph.toPartialDiffeomorph

theorem halfSpaceThreeInteriorPartialDiffeomorph_toOpen (a : ℝ) :
    (halfSpaceThreeInteriorPartialDiffeomorph a).toOpenPartialHomeomorph =
      halfSpaceThreeInteriorChart a := rfl

theorem halfSpaceThreeInteriorChart_contMDiffOn (a : ℝ) :
    ContMDiffOn (𝓡 3) (𝓡∂ 3) ∞ (halfSpaceThreeInteriorChart a)
      (halfSpaceThreeInteriorChart a).source :=
  (halfSpaceThreeInteriorPartialDiffeomorph a).contMDiffOn_toFun

theorem halfSpaceThreeInteriorChart_symm_contMDiffOn (a : ℝ) :
    ContMDiffOn (𝓡∂ 3) (𝓡 3) ∞ (halfSpaceThreeInteriorChart a).symm
      (halfSpaceThreeInteriorChart a).target :=
  (halfSpaceThreeInteriorPartialDiffeomorph a).contMDiffOn_invFun

end DifferentialGeometry.Topology.Manifold
