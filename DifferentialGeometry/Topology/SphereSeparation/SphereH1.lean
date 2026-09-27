import DifferentialGeometry.Topology.SphereSeparation.ContractibleAmbient
import DifferentialGeometry.Topology.SphereSeparation.CircleComparison

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

namespace DifferentialGeometry.Topology.SphereSeparation

theorem isZero_mayerVietorisMiddleHomology_one
    {X : Type} [TopologicalSpace X] (A B : Set X)
    (hA : IsZero (integerSingularHomology (TopCat.of A) 1))
    (hB : IsZero (integerSingularHomology (TopCat.of B) 1)) :
    IsZero
      ((integerSingularChains_isPushout_subspaces A B).shortComplex.X₂.homology 1) := by
  let H := HomologicalComplex.homologyFunctor
    (ModuleCat ℤ) (ComplexShape.down ℕ) 1
  let : H.Additive := inferInstance
  let : PreservesFiniteBiproducts H :=
    Functor.preservesFiniteBiproductsOfAdditive H
  let : PreservesBinaryBiproduct
      (integerSingularChainComplex (TopCat.of A))
      (integerSingularChainComplex (TopCat.of B)) H :=
    preservesBinaryBiproduct_of_preservesBiproduct H _ _
  apply IsZero.of_iso _
    (H.mapBiprod
      (integerSingularChainComplex (TopCat.of A))
      (integerSingularChainComplex (TopCat.of B)))
  exact (biprod_isZero_iff _ _).2 ⟨hA, hB⟩

theorem mono_homologyMap_intersectionToLeft_zero
    {X : Type} [TopologicalSpace X] (A B : Set X)
    [PathConnectedSpace (A ∩ B : Set X)] :
    Mono (HomologicalComplex.homologyMap
      (singularChainsIntersectionToLeft A B) 0) := by
  rw [singularChainsIntersectionToLeft_eq_chainMap]
  let f := topologicalIntersectionToLeft A B
  let : IsIso ((TopCat.of (A ∩ B : Set X)).singularHomology₀ε
      (ModuleCat.of ℤ ℤ)) := inferInstance
  let hεmono : Mono ((TopCat.of (A ∩ B : Set X)).singularHomology₀ε
      (ModuleCat.of ℤ ℤ)) := IsIso.mono_of_iso _
  exact @mono_of_mono_fac _ _ _ _ _ _ _ _ hεmono
    (singularHomologyZeroAugmentation_naturality f)

theorem mono_mayerVietorisIntersectionHomologyMap_zero
    {X : Type} [TopologicalSpace X] (A B : Set X)
    [PathConnectedSpace (A ∩ B : Set X)] :
    Mono (HomologicalComplex.homologyMap
      (integerSingularChains_isPushout_subspaces A B).shortComplex.f 0) := by
  let left := singularChainsIntersectionToLeft A B
  let right := singularChainsIntersectionToRight A B
  change Mono (HomologicalComplex.homologyMap
    (biprod.lift left (-right)) 0)
  let p :
      (integerSingularChains (TopCat.of A) ⊞
          integerSingularChains (TopCat.of B)) ⟶
        integerSingularChains (TopCat.of A) := biprod.fst
  have : Mono (HomologicalComplex.homologyMap left 0) :=
    mono_homologyMap_intersectionToLeft_zero A B
  have hcomp :
      HomologicalComplex.homologyMap
          (biprod.lift left (-right)) 0 ≫
        HomologicalComplex.homologyMap p 0 =
      HomologicalComplex.homologyMap left 0 := by
    rw [← HomologicalComplex.homologyMap_comp]
    rw [biprod.lift_fst]
  have : Mono
      (HomologicalComplex.homologyMap
          (biprod.lift left (-right)) 0 ≫
        HomologicalComplex.homologyMap p 0) := by
    rw [hcomp]
    infer_instance
  exact mono_of_mono_fac hcomp

noncomputable def singularMayerVietorisBoundaryOneZero
    {X : Type} [TopologicalSpace X] (A B : Set X) :
    (smallSingularChainComplex (TopCat.of X) A B).homology 1 ⟶
      (integerSingularChainComplex (TopCat.of (A ∩ B : Set X))).homology 0 :=
  (integerSingularChains_mayerVietoris_shortExact_subspaces A B).δ
    1 0 (by simp)

theorem mono_singularMayerVietorisBoundaryOneZero_of_memberVanishing
    {X : Type} [TopologicalSpace X] (A B : Set X)
    (hA : IsZero (integerSingularHomology (TopCat.of A) 1))
    (hB : IsZero (integerSingularHomology (TopCat.of B) 1)) :
    Mono (singularMayerVietorisBoundaryOneZero A B) := by
  let hS := integerSingularChains_mayerVietoris_shortExact_subspaces A B
  apply (hS.homology_exact₃ 1 0 (by simp)).mono_g
  exact (isZero_mayerVietorisMiddleHomology_one A B hA hB).eq_of_src _ _

@[reassoc]
theorem singularMayerVietorisBoundaryOneZero_comp
    {X : Type} [TopologicalSpace X] (A B : Set X) :
    singularMayerVietorisBoundaryOneZero A B ≫
        HomologicalComplex.homologyMap
          (integerSingularChains_isPushout_subspaces A B).shortComplex.f 0 = 0 := by
  exact (integerSingularChains_mayerVietoris_shortExact_subspaces A B).δ_comp
    1 0 (by simp)

theorem singularMayerVietorisBoundaryOneZero_eq_zero
    {X : Type} [TopologicalSpace X] (A B : Set X)
    [PathConnectedSpace (A ∩ B : Set X)] :
    singularMayerVietorisBoundaryOneZero A B = 0 := by
  exact
    ((integerSingularChains_mayerVietoris_shortExact_subspaces A B
      ).homology_exact₁ 1 0 (by simp)).mono_g_iff.mp
        (mono_mayerVietorisIntersectionHomologyMap_zero A B)

theorem isZero_smallSingularHomology_one_of_memberVanishing
    (X : TopCat) (A B : Set X)
    [PathConnectedSpace (A ∩ B : Set X)]
    (hA : IsZero (integerSingularHomology (TopCat.of A) 1))
    (hB : IsZero (integerSingularHomology (TopCat.of B) 1)) :
    IsZero ((smallSingularChainComplex X A B).homology 1) := by
  let δ := singularMayerVietorisBoundaryOneZero A B
  have : Mono δ :=
    mono_singularMayerVietorisBoundaryOneZero_of_memberVanishing A B hA hB
  have hδzero : δ = 0 :=
    singularMayerVietorisBoundaryOneZero_eq_zero A B
  rw [IsZero.iff_id_eq_zero]
  apply (cancel_mono δ).1
  simp [hδzero]

theorem isZero_integerSingularHomology_one_of_openCover
    (X : TopCat) (A B : Set X)
    (hAopen : IsOpen A) (hBopen : IsOpen B)
    (hcover : A ∪ B = Set.univ)
    [PathConnectedSpace (A ∩ B : Set X)]
    (hA : IsZero (integerSingularHomology (TopCat.of A) 1))
    (hB : IsZero (integerSingularHomology (TopCat.of B) 1)) :
    IsZero (integerSingularHomology X 1) := by
  have hsmall : IsZero ((smallSingularChainComplex X A B).homology 1) :=
    isZero_smallSingularHomology_one_of_memberVanishing X A B hA hB
  have hq : QuasiIso (smallSingularChainInclusion X A B) :=
    quasiIso_smallSingularChainInclusion X A B hAopen hBopen hcover
  let : QuasiIso (smallSingularChainInclusion X A B) := hq
  let : IsIso (HomologicalComplex.homologyMap
      (smallSingularChainInclusion X A B) 1) := inferInstance
  exact IsZero.of_iso hsmall
    (asIso (HomologicalComplex.homologyMap
      (smallSingularChainInclusion X A B) 1)).symm




noncomputable def sphereTwoNorthPoint : SphereTwo :=
  ⟨EuclideanSpace.single 0 1, by simp [SphereTwo]⟩


noncomputable def sphereTwoSouthPoint : SphereTwo :=
  ⟨EuclideanSpace.single 0 (-1), by simp [SphereTwo]⟩


theorem sphereTwoNorthPoint_ne_southPoint :
    sphereTwoNorthPoint ≠ sphereTwoSouthPoint := by
  intro h
  have hcoord := congrArg (fun x : SphereTwo ↦ x.1 0) h
  norm_num [sphereTwoNorthPoint, sphereTwoSouthPoint] at hcoord

theorem sphereTwoPunctureIntersection_pathConnectedSpace
    (p q : SphereTwo) (hpq : p ≠ q) :
    PathConnectedSpace
      (({p}ᶜ : Set SphereTwo) ∩ {q}ᶜ : Set SphereTwo) := by
  let qp : ({p}ᶜ : Set SphereTwo) := ⟨q, by simp [hpq.symm]⟩
  let e := sphereTwoPunctureHomeomorph p
  let a : EuclideanPlane := e qp
  let er : ({qp}ᶜ : Set ({p}ᶜ : Set SphereTwo)) ≃ₜ
      ({a}ᶜ : Set EuclideanPlane) :=
    e.subtype (by
      intro x
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      constructor
      · intro hx h
        exact hx (e.injective h)
      · intro hx h
        exact hx (congrArg e h))
  let E : (({p}ᶜ : Set SphereTwo) ∩ {q}ᶜ : Set SphereTwo) ≃ₜ
      ({a}ᶜ : Set EuclideanPlane) :=
    (Homeomorph.setCongr (sphereTwoPuncture_inter p q)).trans
      ((twoPointComplHomeomorphNestedCompl p q hpq).trans er)
  have hrank : 1 < Module.rank ℝ EuclideanPlane := by
    rw [← Module.finrank_eq_rank']
    norm_num [EuclideanPlane, Module.finrank_fin_fun]
  let : PathConnectedSpace ({a}ᶜ : Set EuclideanPlane) :=
    isPathConnected_iff_pathConnectedSpace.mp
      (isPathConnected_compl_singleton_of_one_lt_rank hrank a)
  exact E.symm.surjective.pathConnectedSpace E.symm.continuous

theorem isZero_integerSingularHomology_sphereTwo_one :
    IsZero (integerSingularHomology (TopCat.of SphereTwo) 1) := by
  let p := sphereTwoNorthPoint
  let q := sphereTwoSouthPoint
  have hpq : p ≠ q := sphereTwoNorthPoint_ne_southPoint
  let : ContractibleSpace ({p}ᶜ : Set SphereTwo) :=
    sphereTwoPuncture_contractible p
  let : ContractibleSpace ({q}ᶜ : Set SphereTwo) :=
    sphereTwoPuncture_contractible q
  let : PathConnectedSpace
      (({p}ᶜ : Set SphereTwo) ∩ {q}ᶜ : Set SphereTwo) :=
    sphereTwoPunctureIntersection_pathConnectedSpace p q hpq
  exact isZero_integerSingularHomology_one_of_openCover
    (TopCat.of SphereTwo) ({p}ᶜ : Set SphereTwo) {q}ᶜ
    (isOpen_sphereTwoPuncture p) (isOpen_sphereTwoPuncture q)
    (sphereTwoPunctureCover hpq)
    (isZero_integerSingularHomology_one_of_contractible _)
    (isZero_integerSingularHomology_one_of_contractible _)

end DifferentialGeometry.Topology.SphereSeparation
