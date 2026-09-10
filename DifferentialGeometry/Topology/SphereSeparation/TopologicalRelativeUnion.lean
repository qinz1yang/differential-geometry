import DifferentialGeometry.Topology.SphereSeparation.SphereCellularComparison
import DifferentialGeometry.Topology.SphereSeparation.SmallChainsPrism

set_option autoImplicit false

open CategoryTheory
open CategoryTheory.Limits

namespace Poincare.Topology.SphereSeparation

def topologicalIntersectionToRight
    {X : Type} [TopologicalSpace X] (A B : Set X) :
    TopCat.of (A ∩ B : Set X) ⟶ TopCat.of B :=
  TopCat.ofHom
    ⟨fun x ↦ ⟨x.1, x.2.2⟩, by fun_prop⟩


def topologicalIntersectionToLeft
    {X : Type} [TopologicalSpace X] (A B : Set X) :
    TopCat.of (A ∩ B : Set X) ⟶ TopCat.of A :=
  TopCat.ofHom
    ⟨fun x ↦ ⟨x.1, x.2.1⟩, by fun_prop⟩

set_option backward.isDefEq.respectTransparency false in
theorem singularChainsIntersectionToRight_eq_chainMap
    {X : Type} [TopologicalSpace X] (A B : Set X) :
    singularChainsIntersectionToRight A B =
      integerSingularChainMap (topologicalIntersectionToRight A B) := by
  change singularChainsIntersectionToRight A B =
    SSet.chainComplexMap
      (TopCat.toSSet.map (topologicalIntersectionToRight A B))
      (ModuleCat.of ℤ ℤ)
  apply HomologicalComplex.hom_ext
  intro n
  apply SSet.chainComplex_hom_ext
  intro s
  simp [singularChainsIntersectionToRight,
    singularChainsIntersectionInfIso, singularChainsSubspaceRangeIso,
    topologicalIntersectionToRight]
  congr 1

set_option backward.isDefEq.respectTransparency false in
theorem singularChainsIntersectionToLeft_eq_chainMap
    {X : Type} [TopologicalSpace X] (A B : Set X) :
    singularChainsIntersectionToLeft A B =
      integerSingularChainMap (topologicalIntersectionToLeft A B) := by
  change singularChainsIntersectionToLeft A B =
    SSet.chainComplexMap
      (TopCat.toSSet.map (topologicalIntersectionToLeft A B))
      (ModuleCat.of ℤ ℤ)
  apply HomologicalComplex.hom_ext
  intro n
  apply SSet.chainComplex_hom_ext
  intro s
  simp [singularChainsIntersectionToLeft,
    singularChainsIntersectionInfIso, singularChainsSubspaceRangeIso,
    topologicalIntersectionToLeft]
  congr 1

set_option backward.isDefEq.respectTransparency false in
theorem singularChainsLeftToSmall_comp_inclusion
    {X : Type} [TopologicalSpace X] (A B : Set X) :
    singularChainsLeftToSmall A B ≫
        smallSingularChainInclusion (TopCat.of X) A B =
      integerSingularChainMap (topologicalSubspaceInclusion A) := by
  change singularChainsLeftToSmall A B ≫
      SSet.chainComplexMap
        (smallSingularSubcomplex (TopCat.of X) A B).ι
        (ModuleCat.of ℤ ℤ) =
    SSet.chainComplexMap
      (TopCat.toSSet.map (topologicalSubspaceInclusion A))
      (ModuleCat.of ℤ ℤ)
  apply HomologicalComplex.hom_ext
  intro n
  apply SSet.chainComplex_hom_ext
  intro s
  simp [singularChainsLeftToSmall, singularChainsSubspaceRangeIso,
    smallSingularSubcomplex]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
theorem singularChainsRightToSmall_comp_inclusion
    {X : Type} [TopologicalSpace X] (A B : Set X) :
    singularChainsRightToSmall A B ≫
        smallSingularChainInclusion (TopCat.of X) A B =
      integerSingularChainMap (topologicalSubspaceInclusion B) := by
  change singularChainsRightToSmall A B ≫
      SSet.chainComplexMap
        (smallSingularSubcomplex (TopCat.of X) A B).ι
        (ModuleCat.of ℤ ℤ) =
    SSet.chainComplexMap
      (TopCat.toSSet.map (topologicalSubspaceInclusion B))
      (ModuleCat.of ℤ ℤ)
  apply HomologicalComplex.hom_ext
  intro n
  apply SSet.chainComplex_hom_ext
  intro s
  simp [singularChainsRightToSmall, singularChainsSubspaceRangeIso,
    smallSingularSubcomplex]



def subspaceOutsideHomeomorphInterCompl
    {X : Type} [TopologicalSpace X] (A U : Set X) :
    subspaceOutside A U ≃ₜ (A ∩ Uᶜ : Set X) :=
  subspaceOutsideHomeomorphDiff A U

def subspaceOutsideToIntersection
    {X : Type} [TopologicalSpace X] (A U : Set X) :
    TopCat.of (subspaceOutside A U) ⟶ TopCat.of (A ∩ Uᶜ : Set X) :=
  (TopCat.isoOfHomeo (subspaceOutsideHomeomorphInterCompl A U)).hom

theorem subspaceOutside_intersection_comm
    {X : Type} [TopologicalSpace X] (A U : Set X) :
    topologicalSubspaceInclusion (subspaceOutside A U) ≫
        𝟙 (TopCat.of (Uᶜ : Set X)) =
      subspaceOutsideToIntersection A U ≫
        topologicalIntersectionToRight A Uᶜ := by
  rfl

noncomputable def relativeSubspaceOutsideToIntersection
    {X : Type} [TopologicalSpace X] (A U : Set X) :
    relativeSingularChainComplex
        (topologicalSubspaceInclusion (subspaceOutside A U)) ⟶
      relativeSingularChainComplex
        (topologicalIntersectionToRight A Uᶜ) :=
  relativeSingularChainMap
    (topologicalSubspaceInclusion (subspaceOutside A U))
    (topologicalIntersectionToRight A Uᶜ)
    (subspaceOutsideToIntersection A U)
    (𝟙 (TopCat.of (Uᶜ : Set X)))
    (subspaceOutside_intersection_comm A U)

theorem isIso_relativeSubspaceOutsideToIntersection
    {X : Type} [TopologicalSpace X] (A U : Set X) :
    IsIso (relativeSubspaceOutsideToIntersection A U) := by
  let _ : IsIso (subspaceOutsideToIntersection A U) := by
    unfold subspaceOutsideToIntersection
    infer_instance
  let _ : IsIso (𝟙 (TopCat.of (Uᶜ : Set X))) := by infer_instance
  exact isIso_relativeSingularChainMap
    (topologicalSubspaceInclusion (subspaceOutside A U))
    (topologicalIntersectionToRight A Uᶜ)
    (subspaceOutsideToIntersection A U)
    (𝟙 (TopCat.of (Uᶜ : Set X)))
    (subspaceOutside_intersection_comm A U)

noncomputable def relativeSubspaceOutsideIsoMayerVietoris
    {X : Type} [TopologicalSpace X] (A U : Set X) :
    relativeSingularChainComplex
        (topologicalSubspaceInclusion (subspaceOutside A U)) ≅
      cokernel (integerSingularChainMap
        (topologicalIntersectionToRight A Uᶜ)) := by
  let _ := isIso_relativeSubspaceOutsideToIntersection A U
  exact asIso (relativeSubspaceOutsideToIntersection A U)

@[reassoc]
theorem relativeProjection_comp_relativeSubspaceOutsideIsoMayerVietoris_hom
    {X : Type} [TopologicalSpace X] (A U : Set X) :
    relativeSingularChainProjection
          (topologicalSubspaceInclusion (subspaceOutside A U)) ≫
        (relativeSubspaceOutsideIsoMayerVietoris A U).hom =
      integerSingularChainMap (𝟙 (TopCat.of (Uᶜ : Set X))) ≫
        cokernel.π (integerSingularChainMap
          (topologicalIntersectionToRight A Uᶜ)) := by
  change relativeSingularChainProjection
          (topologicalSubspaceInclusion (subspaceOutside A U)) ≫
        relativeSubspaceOutsideToIntersection A U = _
  exact relativeSingularChainProjection_naturality
    (topologicalSubspaceInclusion (subspaceOutside A U))
    (topologicalIntersectionToRight A Uᶜ)
    (subspaceOutsideToIntersection A U)
    (𝟙 (TopCat.of (Uᶜ : Set X)))
    (subspaceOutside_intersection_comm A U)

noncomputable def topologicalRelativeUnionComparison
    {X : Type} [TopologicalSpace X] (A B : Set X) :
    cokernel (integerSingularChainMap
        (topologicalIntersectionToRight A B)) ⟶
      cokernel (singularChainsLeftToSmall A B) :=
  cokernel.map _ _
    (integerSingularChainMap (topologicalIntersectionToLeft A B))
    (singularChainsRightToSmall A B) (by
      rw [← singularChainsIntersectionToRight_eq_chainMap,
        ← singularChainsIntersectionToLeft_eq_chainMap]
      exact (integerSingularChains_isPushout_subspaces A B).w.symm)

@[reassoc (attr := simp)]
theorem topologicalRelativeUnionComparison_projection
    {X : Type} [TopologicalSpace X] (A B : Set X) :
    cokernel.π (integerSingularChainMap
          (topologicalIntersectionToRight A B)) ≫
        topologicalRelativeUnionComparison A B =
      singularChainsRightToSmall A B ≫
        cokernel.π (singularChainsLeftToSmall A B) := by
  simp [topologicalRelativeUnionComparison]


theorem isIso_topologicalRelativeUnionComparison
    {X : Type} [TopologicalSpace X] (A B : Set X) :
    IsIso (topologicalRelativeUnionComparison A B) := by
  have h₀ := integerSingularChains_isPushout_subspaces A B
  rw [singularChainsIntersectionToRight_eq_chainMap,
    singularChainsIntersectionToLeft_eq_chainMap] at h₀
  let h := h₀.flip
  exact isIso_cokernel_map_of_isPushout h


noncomputable def topologicalRelativeUnionIso
    {X : Type} [TopologicalSpace X] (A B : Set X) :
    cokernel (integerSingularChainMap
        (topologicalIntersectionToRight A B)) ≅
      cokernel (singularChainsLeftToSmall A B) := by
  let _ := isIso_topologicalRelativeUnionComparison A B
  exact asIso (topologicalRelativeUnionComparison A B)

noncomputable def excisionSourceRelativeIsoSmallRelative
    {X : Type} [TopologicalSpace X] (A U : Set X) :
    relativeSingularChainComplex
        (topologicalSubspaceInclusion (subspaceOutside A U)) ≅
      cokernel (singularChainsLeftToSmall A Uᶜ) :=
  relativeSubspaceOutsideIsoMayerVietoris A U ≪≫
    topologicalRelativeUnionIso A Uᶜ

@[reassoc]
theorem excisionSourceRelativeIsoSmallRelative_projection
    {X : Type} [TopologicalSpace X] (A U : Set X) :
    relativeSingularChainProjection
          (topologicalSubspaceInclusion (subspaceOutside A U)) ≫
        (excisionSourceRelativeIsoSmallRelative A U).hom =
      singularChainsRightToSmall A Uᶜ ≫
        cokernel.π (singularChainsLeftToSmall A Uᶜ) := by
  change relativeSingularChainProjection
          (topologicalSubspaceInclusion (subspaceOutside A U)) ≫
        (relativeSubspaceOutsideIsoMayerVietoris A U).hom ≫
          (topologicalRelativeUnionIso A Uᶜ).hom = _
  rw [← Category.assoc,
    relativeProjection_comp_relativeSubspaceOutsideIsoMayerVietoris_hom,
    integerSingularChainMap_id, Category.id_comp]
  change cokernel.π (integerSingularChainMap
        (topologicalIntersectionToRight A Uᶜ)) ≫
      topologicalRelativeUnionComparison A Uᶜ = _
  exact topologicalRelativeUnionComparison_projection A Uᶜ

noncomputable def smallRelativeToFullRelativeChainMap
    {X : Type} [TopologicalSpace X] (A B : Set X) :
    cokernel (singularChainsLeftToSmall A B) ⟶
      relativeSingularChainComplex (topologicalSubspaceInclusion A) :=
  cokernel.map
    (singularChainsLeftToSmall A B)
    (integerSingularChainMap (topologicalSubspaceInclusion A))
    (𝟙 (integerSingularChains (TopCat.of A)))
    (smallSingularChainInclusion (TopCat.of X) A B)
    (by simpa using singularChainsLeftToSmall_comp_inclusion A B)

@[reassoc (attr := simp)]
theorem smallRelativeToFullRelativeChainMap_projection
    {X : Type} [TopologicalSpace X] (A B : Set X) :
    cokernel.π (singularChainsLeftToSmall A B) ≫
        smallRelativeToFullRelativeChainMap A B =
      smallSingularChainInclusion (TopCat.of X) A B ≫
        relativeSingularChainProjection (topologicalSubspaceInclusion A) := by
  simp only [smallRelativeToFullRelativeChainMap, cokernel.π_desc]
  rfl

theorem quasiIso_smallRelativeToFullRelativeChainMap
    {X : Type} [TopologicalSpace X] (A B : Set X)
    (hsmall : QuasiIso
      (smallSingularChainInclusion (TopCat.of X) A B)) :
    QuasiIso (smallRelativeToFullRelativeChainMap A B) := by
  let j := SSet.Subcomplex.homOfLE
    (le_sup_left : singularSubspaceRange (A := A) ≤
      singularSubspaceRange (A := A) ⊔ singularSubspaceRange (A := B))
  let _ : Mono (SSet.chainComplexMap j (ModuleCat.of ℤ ℤ)) :=
    mono_integerSimplicialChainMap j
  let _ : Mono (singularChainsLeftToSmall A B) := by
    dsimp [singularChainsLeftToSmall]
    infer_instance
  let _ : Mono
      (integerSingularChainMap (topologicalSubspaceInclusion A)) :=
    mono_integerSingularChainMap_subspace A
  apply quasiIso_cokernelMap
    (singularChainsLeftToSmall A B)
    (integerSingularChainMap (topologicalSubspaceInclusion A))
    (𝟙 (integerSingularChains (TopCat.of A)))
    (smallSingularChainInclusion (TopCat.of X) A B)
    (by simpa using singularChainsLeftToSmall_comp_inclusion A B)
  · infer_instance
  · exact hsmall



noncomputable def excisionRelativeSingularChainMapViaSmall
    {X : Type} [TopologicalSpace X] (A U : Set X) :
    relativeSingularChainComplex
        (topologicalSubspaceInclusion (subspaceOutside A U)) ⟶
      relativeSingularChainComplex (topologicalSubspaceInclusion A) :=
  (excisionSourceRelativeIsoSmallRelative A U).hom ≫
    smallRelativeToFullRelativeChainMap A Uᶜ

set_option backward.isDefEq.respectTransparency false in
theorem excisionRelativeSingularChainMapViaSmall_eq
    {X : Type} [TopologicalSpace X] (A U : Set X) :
    excisionRelativeSingularChainMapViaSmall A U =
      excisionRelativeSingularChainMap A U := by
  apply (cancel_epi (relativeSingularChainProjection
    (topologicalSubspaceInclusion (subspaceOutside A U)))).1
  rw [excisionRelativeSingularChainMapViaSmall,
    excisionSourceRelativeIsoSmallRelative_projection_assoc,
    smallRelativeToFullRelativeChainMap_projection,
    singularChainsRightToSmall_comp_inclusion_assoc]
  simp [excisionRelativeSingularChainMap,
    relativeSingularChainMapOfSubspaces]
  rfl

theorem quasiIso_excisionRelativeSingularChainMap
    {X : Type} [TopologicalSpace X] (A U : Set X)
    (h : closure U ⊆ interior A) :
    QuasiIso (excisionRelativeSingularChainMap A U) := by
  rw [← excisionRelativeSingularChainMapViaSmall_eq A U]
  let _ : QuasiIso
      ((excisionSourceRelativeIsoSmallRelative A U).hom) := by
    infer_instance
  have hsmall : QuasiIso
      (smallSingularChainInclusion (TopCat.of X) A Uᶜ) :=
    quasiIso_smallSingularChainInclusion_of_openCover_refines
      (TopCat.of X)
      (isOpen_excisionCoverNear A)
      (isOpen_excisionCoverFar U)
      (excisionCover_union h)
      (excisionCoverNear_subset A)
      (excisionCoverFar_subset U)
  let _ : QuasiIso (smallRelativeToFullRelativeChainMap A Uᶜ) :=
    quasiIso_smallRelativeToFullRelativeChainMap A Uᶜ hsmall
  change QuasiIso
    ((excisionSourceRelativeIsoSmallRelative A U).hom ≫
      smallRelativeToFullRelativeChainMap A Uᶜ)
  exact inferInstance

theorem singularExcisionFor
    {X : Type} [TopologicalSpace X] (A U : Set X) :
    SingularExcisionFor A U := by
  intro h n
  let _ : QuasiIso (excisionRelativeSingularChainMap A U) :=
    quasiIso_excisionRelativeSingularChainMap A U h
  change IsIso (HomologicalComplex.homologyMap
    (excisionRelativeSingularChainMap A U) n)
  rw [← quasiIsoAt_iff_isIso_homologyMap]
  infer_instance

end Poincare.Topology.SphereSeparation
