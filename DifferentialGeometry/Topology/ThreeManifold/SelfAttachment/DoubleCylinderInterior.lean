import DifferentialGeometry.Topology.ThreeManifold.SelfAttachment.DoubleCylinderMappingTorus

set_option autoImplicit false
noncomputable section
open Set Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.DoubleCylinder

private abbrev IC := (𝓡 2).prod 𝓘(ℝ, ℝ)

abbrev Interior := sphereMappingTorusInteriorDomain

def interiorCore (f : SphereTwo ≃ₘ⟮𝓡 2, 𝓡 2⟯ SphereTwo) (p : Interior) : Space f :=
  core f (p.val.1, ⟨p.val.2, p.property.2.1.le, p.property.2.2.le⟩)

def interiorBand (f : SphereTwo ≃ₘ⟮𝓡 2, 𝓡 2⟯ SphereTwo) (p : Interior) : Space f :=
  band f (p.val.1, ⟨p.val.2, p.property.2.1.le, p.property.2.2.le⟩)

private def halfParameter (p : Interior) : sphereMappingTorusInteriorDomain :=
  ⟨(p.val.1, p.val.2 / 2), mem_univ _, by constructor <;> linarith [p.property.2.1, p.property.2.2]⟩

private def reverseParameter (f : SphereTwo ≃ₘ⟮𝓡 2, 𝓡 2⟯ SphereTwo)
    (p : Interior) : sphereMappingTorusInteriorDomain :=
  ⟨(f.symm p.val.1, 1 - p.val.2 / 2), mem_univ _,
    by constructor <;> linarith [p.property.2.1, p.property.2.2]⟩

private def halfDiffeomorph : Diffeomorph IC IC (SphereTwo × ℝ) (SphereTwo × ℝ) ∞ where
  toFun p := (p.1, p.2 / 2)
  invFun p := (p.1, 2 * p.2)
  left_inv p := by refine Prod.ext rfl ?_; dsimp; ring
  right_inv p := by refine Prod.ext rfl ?_; dsimp; ring
  contMDiff_toFun := contMDiff_fst.prodMk (contMDiff_snd.div_const 2)
  contMDiff_invFun := contMDiff_fst.prodMk (contMDiff_const.mul contMDiff_snd)

private def reverseDiffeomorph (f : SphereTwo ≃ₘ⟮𝓡 2, 𝓡 2⟯ SphereTwo) :
    Diffeomorph IC IC (SphereTwo × ℝ) (SphereTwo × ℝ) ∞ where
  toFun p := (f.symm p.1, 1 - p.2 / 2)
  invFun p := (f p.1, 2 - 2 * p.2)
  left_inv p := by refine Prod.ext (f.apply_symm_apply _) ?_; dsimp; ring
  right_inv p := by refine Prod.ext (f.symm_apply_apply _) ?_; dsimp; ring
  contMDiff_toFun := (f.symm.contMDiff.comp contMDiff_fst).prodMk
    (contMDiff_const.sub (contMDiff_snd.div_const 2))
  contMDiff_invFun := (f.contMDiff.comp contMDiff_fst).prodMk
    (contMDiff_const.sub (contMDiff_const.mul contMDiff_snd))

private theorem halfParameter_isLocalDiffeomorph : IsLocalDiffeomorph IC IC ∞ halfParameter := by
  have hloc := DifferentialGeometry.isLocalDiffeomorph_restrict_open Interior
    (halfDiffeomorph.isLocalDiffeomorph.isLocalDiffeomorphOn Interior)
  intro p
  exact DifferentialGeometry.isLocalDiffeomorphAt_subtypeCodRestrict
    (fun q : Interior => (halfParameter q).property) (hloc p)

private theorem reverseParameter_isLocalDiffeomorph
    (f : SphereTwo ≃ₘ⟮𝓡 2, 𝓡 2⟯ SphereTwo) : IsLocalDiffeomorph IC IC ∞ (reverseParameter f) := by
  have hloc := DifferentialGeometry.isLocalDiffeomorph_restrict_open Interior
    ((reverseDiffeomorph f).isLocalDiffeomorph.isLocalDiffeomorphOn Interior)
  intro p
  exact DifferentialGeometry.isLocalDiffeomorphAt_subtypeCodRestrict
    (fun q : Interior => (reverseParameter f q).property) (hloc p)

theorem interiorCore_isLocalDiffeomorph (D : SphereMappingTorusIsotopy)
    (hD : ContMDiff IC (𝓡 2) ∞ (fun p : SphereTwo × ℝ => D.isotopy p.2 p.1))
    (hDi : ContMDiff IC (𝓡 2) ∞ (fun p : SphereTwo × ℝ => (D.isotopy p.2).symm p.1)) :
    let _ := sphereMappingTorusChartedSpace D.flatten
    let _ := DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace
      (H := ModelProd (EuclideanSpace ℝ (Fin 2)) ℝ) (mappingTorusHomeomorph D.target)
    IsLocalDiffeomorph IC IC ∞ (interiorCore D.target) := by
  let _ := sphereMappingTorusChartedSpace D.flatten
  let _ := DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace
    (H := ModelProd (EuclideanSpace ℝ (Fin 2)) ℝ) (mappingTorusHomeomorph D.target)
  have h := DifferentialGeometry.isLocalDiffeomorph_comp
    (DifferentialGeometry.Manifold.Homeomorph.pullbackDiffeomorph
      (I := IC) (n := ∞) (mappingTorusHomeomorph D.target)).symm.isLocalDiffeomorph
    (DifferentialGeometry.isLocalDiffeomorph_comp
      (sphereMappingTorusInterior_isLocalDiffeomorph D.flatten
        (D.contMDiff_flatten_apply hD) (D.contMDiff_flatten_symm_apply hDi))
      halfParameter_isLocalDiffeomorph)
  have heq : (DifferentialGeometry.Manifold.Homeomorph.pullbackDiffeomorph
      (I := IC) (n := ∞) (mappingTorusHomeomorph D.target)).symm ∘
      (sphereMappingTorusInterior D.target ∘ halfParameter) = interiorCore D.target := by
    funext p
    apply (mappingTorusHomeomorph D.target).injective
    change mappingTorusHomeomorph D.target ((mappingTorusHomeomorph D.target).symm _) = _
    rw [Homeomorph.apply_symm_apply]
    rfl
  rw [heq] at h
  exact h

theorem interiorBand_isLocalDiffeomorph (D : SphereMappingTorusIsotopy)
    (hD : ContMDiff IC (𝓡 2) ∞ (fun p : SphereTwo × ℝ => D.isotopy p.2 p.1))
    (hDi : ContMDiff IC (𝓡 2) ∞ (fun p : SphereTwo × ℝ => (D.isotopy p.2).symm p.1)) :
    let _ := sphereMappingTorusChartedSpace D.flatten
    let _ := DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace
      (H := ModelProd (EuclideanSpace ℝ (Fin 2)) ℝ) (mappingTorusHomeomorph D.target)
    IsLocalDiffeomorph IC IC ∞ (interiorBand D.target) := by
  let _ := sphereMappingTorusChartedSpace D.flatten
  let _ := DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace
    (H := ModelProd (EuclideanSpace ℝ (Fin 2)) ℝ) (mappingTorusHomeomorph D.target)
  have h := DifferentialGeometry.isLocalDiffeomorph_comp
    (DifferentialGeometry.Manifold.Homeomorph.pullbackDiffeomorph
      (I := IC) (n := ∞) (mappingTorusHomeomorph D.target)).symm.isLocalDiffeomorph
    (DifferentialGeometry.isLocalDiffeomorph_comp
      (sphereMappingTorusInterior_isLocalDiffeomorph D.flatten
        (D.contMDiff_flatten_apply hD) (D.contMDiff_flatten_symm_apply hDi))
      (reverseParameter_isLocalDiffeomorph D.target))
  have heq : (DifferentialGeometry.Manifold.Homeomorph.pullbackDiffeomorph
      (I := IC) (n := ∞) (mappingTorusHomeomorph D.target)).symm ∘
      (sphereMappingTorusInterior D.target ∘ reverseParameter D.target) = interiorBand D.target := by
    funext p
    apply (mappingTorusHomeomorph D.target).injective
    change mappingTorusHomeomorph D.target ((mappingTorusHomeomorph D.target).symm _) = _
    rw [Homeomorph.apply_symm_apply]
    rfl
  rw [heq] at h
  exact h

end DifferentialGeometry.Topology.DoubleCylinder
