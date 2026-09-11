import DifferentialGeometry.Topology.SphereSeparation.TopologicalRelativeUnion

set_option autoImplicit false

open CategoryTheory
open CategoryTheory.Limits

namespace DifferentialGeometry.Topology.SphereSeparation

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
theorem singularHomologyZeroAugmentation_naturality
    {X Y : TopCat} (f : X ⟶ Y) :
    HomologicalComplex.homologyMap (integerSingularChainMap f) 0 ≫
        Y.singularHomology₀ε (ModuleCat.of ℤ ℤ) =
      X.singularHomology₀ε (ModuleCat.of ℤ ℤ) := by
  let K := integerSingularChainComplex X
  let L := integerSingularChainComplex Y
  apply (cancel_epi (K.homologyπ 0)).1
  rw [HomologicalComplex.homologyπ_naturality_assoc]
  apply (cancel_epi K.cycles₀Iso.inv).1
  apply Sigma.hom_ext
  intro x
  let SX := TopCat.toSSet.obj X
  have hlift :
      SX.ιChainComplex x ≫ K.cycles₀Iso.inv =
        K.liftCycles (SX.ιChainComplex x) 0 (by simp) (by simp) := by
    apply (cancel_mono (K.iCycles 0)).1
    rw [HomologicalComplex.liftCycles_i]
    change SX.ιChainComplex x ≫
      (K.cycles₀Iso.inv ≫ K.cycles₀Iso.hom) = SX.ιChainComplex x
    rw [K.cycles₀Iso.inv_hom_id]
    exact Category.comp_id _
  change SX.ιChainComplex x ≫ K.cycles₀Iso.inv ≫
      HomologicalComplex.cyclesMap (integerSingularChainMap f) 0 ≫
        L.homologyπ 0 ≫ Y.singularHomology₀ε (ModuleCat.of ℤ ℤ) =
    SX.ιChainComplex x ≫ K.cycles₀Iso.inv ≫
      K.homologyπ 0 ≫ X.singularHomology₀ε (ModuleCat.of ℤ ℤ)
  rw [← Category.assoc, hlift,
    HomologicalComplex.liftCycles_comp_cyclesMap_assoc]
  calc
    _ = 𝟙 (ModuleCat.of ℤ ℤ) := by
      change HomologicalComplex.liftCycles
          ((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of ℤ ℤ))
          ((TopCat.toSSet.obj X).ιChainComplex x ≫
            (SSet.chainComplexMap (TopCat.toSSet.map f)
              (ModuleCat.of ℤ ℤ)).f 0)
          0 (by simp) (by simp) ≫
        HomologicalComplex.homologyπ
            ((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of ℤ ℤ)) 0 ≫
          (TopCat.toSSet.obj Y).homology₀ε (ModuleCat.of ℤ ℤ) =
        𝟙 (ModuleCat.of ℤ ℤ)
      simpa only [SSet.ι_chainComplexMap_f] using
        SSet.liftCycles_ιChainComplex_homologyπ_homology₀ε
          (TopCat.toSSet.obj Y) (ModuleCat.of ℤ ℤ)
          ((TopCat.toSSet.map f).app _ x)
    _ = SX.ιChainComplex x ≫ K.cycles₀Iso.inv ≫
          K.homologyπ 0 ≫ X.singularHomology₀ε (ModuleCat.of ℤ ℤ) := by
      rw [← Category.assoc, hlift]
      symm
      exact SSet.liftCycles_ιChainComplex_homologyπ_homology₀ε
        (TopCat.toSSet.obj X) (ModuleCat.of ℤ ℤ) x

@[reassoc]
theorem subspaceSingularHomologyMap_comp_augmentation
    {X : Type} [TopologicalSpace X] (A : Set X) :
    subspaceSingularHomologyMap A 0 ≫
        (TopCat.of X).singularHomology₀ε (ModuleCat.of ℤ ℤ) =
      (TopCat.of A).singularHomology₀ε (ModuleCat.of ℤ ℤ) :=
  singularHomologyZeroAugmentation_naturality
    (topologicalSubspaceInclusion A)

noncomputable def reducedSingularH0IsoKernelSubspaceMap
    {X : Type} [TopologicalSpace X] [PathConnectedSpace X] (A : Set X) :
    reducedSingularH0 (TopCat.of A) ≅
      kernel (subspaceSingularHomologyMap A 0) :=
  kernel.mapIso
    (f := (TopCat.of A).singularHomology₀ε (ModuleCat.of ℤ ℤ))
    (f' := subspaceSingularHomologyMap A 0)
    (p := Iso.refl _)
    (q := (asIso ((TopCat.of X).singularHomology₀ε
      (ModuleCat.of ℤ ℤ))).symm)
    (by
      apply (cancel_mono ((TopCat.of X).singularHomology₀ε
        (ModuleCat.of ℤ ℤ))).1
      change (((TopCat.of A).singularHomology₀ε (ModuleCat.of ℤ ℤ) ≫
          inv ((TopCat.of X).singularHomology₀ε (ModuleCat.of ℤ ℤ))) ≫
            (TopCat.of X).singularHomology₀ε (ModuleCat.of ℤ ℤ)) =
        ((𝟙 _ ≫ subspaceSingularHomologyMap A 0) ≫
          (TopCat.of X).singularHomology₀ε (ModuleCat.of ℤ ℤ))
      rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id,
        Category.id_comp, subspaceSingularHomologyMap_comp_augmentation])

noncomputable def relativeBoundaryToKernelSubspaceMap
    {X : Type} [TopologicalSpace X] (A : Set X) :
    relativeSingularHomologyOfSubspace A 1 ⟶
      kernel (subspaceSingularHomologyMap A 0) :=
  kernel.lift
    (subspaceSingularHomologyMap A 0)
    (relativeSingularBoundary A 0)
    (by
      exact (relativeSingularChainSequence_shortExact A).δ_comp
        1 0 (by simp))

theorem epi_relativeBoundaryToKernelSubspaceMap
    {X : Type} [TopologicalSpace X] (A : Set X) :
    Epi (relativeBoundaryToKernelSubspaceMap A) := by
  exact (relativeSingularHomology_exact_at_subspace A 0).epi_kernelLift

theorem mono_relativeBoundaryToKernelSubspaceMap
    {X : Type} [TopologicalSpace X] (A : Set X)
    (hH1 : IsZero (integerSingularHomology (TopCat.of X) 1)) :
    Mono (relativeBoundaryToKernelSubspaceMap A) := by
  have habs : absoluteToRelativeSingularHomology A 1 = 0 :=
    hH1.eq_of_src _ _
  let _ : Mono (relativeSingularBoundary A 0) :=
    (relativeSingularHomology_exact_at_relative A 0).mono_g habs
  exact mono_of_mono_fac
    (kernel.lift_ι
      (subspaceSingularHomologyMap A 0)
      (relativeSingularBoundary A 0)
      (by
        exact (relativeSingularChainSequence_shortExact A).δ_comp
          1 0 (by simp)))

theorem isIso_relativeBoundaryToKernelSubspaceMap
    {X : Type} [TopologicalSpace X] (A : Set X)
    (hH1 : IsZero (integerSingularHomology (TopCat.of X) 1)) :
    IsIso (relativeBoundaryToKernelSubspaceMap A) := by
  let _ : Epi (relativeBoundaryToKernelSubspaceMap A) :=
    epi_relativeBoundaryToKernelSubspaceMap A
  let _ : Mono (relativeBoundaryToKernelSubspaceMap A) :=
    mono_relativeBoundaryToKernelSubspaceMap A hH1
  exact isIso_of_mono_of_epi _

noncomputable def relativeH1IsoReducedH0
    {X : Type} [TopologicalSpace X] [PathConnectedSpace X] (A : Set X)
    (hH1 : IsZero (integerSingularHomology (TopCat.of X) 1)) :
    relativeSingularHomologyOfSubspace A 1 ≅
      reducedSingularH0 (TopCat.of A) := by
  let _ := isIso_relativeBoundaryToKernelSubspaceMap A hH1
  exact asIso (relativeBoundaryToKernelSubspaceMap A) ≪≫
    (reducedSingularH0IsoKernelSubspaceMap A).symm

theorem reducedSingularH0IsoInt_of_relativeH1
    {X : Type} [TopologicalSpace X] [PathConnectedSpace X] (A : Set X)
    (hH1 : IsZero (integerSingularHomology (TopCat.of X) 1))
    (hrel : Nonempty
      (relativeSingularHomologyOfSubspace A 1 ≅ ModuleCat.of ℤ ℤ)) :
    Nonempty
      (reducedSingularH0 (TopCat.of A) ≅ ModuleCat.of ℤ ℤ) := by
  obtain ⟨e⟩ := hrel
  exact ⟨(relativeH1IsoReducedH0 A hH1).symm ≪≫ e⟩


theorem isZero_integerSingularHomology_one_of_contractible
    (X : Type) [TopologicalSpace X] [ContractibleSpace X] :
    IsZero (integerSingularHomology (TopCat.of X) 1) := by
  let e := singularChainsHomotopyEquivSingleZeroOfContractible X
  exact IsZero.of_iso
    (HomologicalComplex.isZero_single_obj_homology
      (ComplexShape.down ℕ) 0
      (ModuleCat.of ℤ ℤ) 1 (by omega))
    (e.toHomologyIso 1)

theorem hasAlexanderDualityH0Certificate_of_relativeH1
    (e : SphereTwo → EuclideanThree)
    (hrel : Nonempty
      (relativeSingularHomologyOfSubspace
          ({x : EuclideanThree | x ∉ Set.range e} : Set EuclideanThree) 1 ≅
        ModuleCat.of ℤ ℤ)) :
    HasAlexanderDualityH0Certificate e := by
  exact reducedSingularH0IsoInt_of_relativeH1
    ({x : EuclideanThree | x ∉ Set.range e} : Set EuclideanThree)
    (isZero_integerSingularHomology_one_of_contractible EuclideanThree)
    hrel

end DifferentialGeometry.Topology.SphereSeparation
