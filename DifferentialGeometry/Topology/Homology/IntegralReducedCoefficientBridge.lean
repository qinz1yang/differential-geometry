import DifferentialGeometry.Topology.Homology.Reduced
import DifferentialGeometry.Topology.Homology.Reduced.Comparison
import DifferentialGeometry.Topology.Homology.Integral
import DifferentialGeometry.Topology.Homology.SquareBoundaryDegree
import DifferentialGeometry.Topology.LocalDegree.SphereDegree
import DifferentialGeometry.Topology.Homology.SphereGeneratorCriterion

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped Topology

namespace DifferentialGeometry.Topology

open DifferentialGeometry.Homology

def integralSingularCoefficientsIso : integralSingularCoefficients ≅ ModuleCat.of ℤ ℤ :=
  (ULift.moduleEquiv (M := ℤ)).toModuleIso

def integralSingularChainsCoeffIso (X : Type) [TopologicalSpace X] :
    (TopCat.toSSet.obj (TopCat.of X)).chainComplex integralSingularCoefficients ≅
      (TopCat.toSSet.obj (TopCat.of X)).chainComplex (ModuleCat.of ℤ ℤ) :=
  ((SSet.chainComplexFunctor (ModuleCat ℤ)).mapIso integralSingularCoefficientsIso).app
    (TopCat.toSSet.obj (TopCat.of X))

theorem integralSingularChainsCoeffIso_naturality {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) :
    (integralSingularChainsCoeffIso X).hom ≫
        SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom f)) (ModuleCat.of ℤ ℤ) =
      SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom f)) integralSingularCoefficients ≫
        (integralSingularChainsCoeffIso Y).hom :=
  (((SSet.chainComplexFunctor (ModuleCat ℤ)).mapIso integralSingularCoefficientsIso).hom.naturality
    (TopCat.toSSet.map (TopCat.ofHom f))).symm

def integralSingularHomologyCoeffIso (n : ℕ) (X : Type) [TopologicalSpace X] :
    integralSingularHomology n X ≅
      (TopCat.toSSet.obj (TopCat.of X)).homology (ModuleCat.of ℤ ℤ) n :=
  HomologicalComplex.homologyMapIso (integralSingularChainsCoeffIso X) n

theorem integralSingularHomologyCoeffIso_hom (n : ℕ) (X : Type) [TopologicalSpace X] :
    (integralSingularHomologyCoeffIso n X).hom =
      HomologicalComplex.homologyMap (integralSingularChainsCoeffIso X).hom n :=
  HomologicalComplex.homologyMapIso_hom _ n

theorem integralSingularHomologyMap_eq_homologyMap (n : ℕ) {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) (c : integralSingularHomology n X) :
    (HomologicalComplex.homologyMap (SSet.chainComplexMap
        (TopCat.toSSet.map (TopCat.ofHom f)) integralSingularCoefficients) n) c =
      integralSingularHomologyMap n f c :=
  rfl

theorem integralSingularHomologyCoeffIso_hom_naturality (n : ℕ) {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) :
    (integralSingularHomologyCoeffIso n X).hom ≫
        (HomologicalComplex.homologyMap (SSet.chainComplexMap
          (TopCat.toSSet.map (TopCat.ofHom f)) (ModuleCat.of ℤ ℤ)) n) =
      (HomologicalComplex.homologyMap (SSet.chainComplexMap
          (TopCat.toSSet.map (TopCat.ofHom f)) integralSingularCoefficients) n) ≫
        (integralSingularHomologyCoeffIso n Y).hom := by
  have h := congrArg (fun k => HomologicalComplex.homologyMap k n)
    (integralSingularChainsCoeffIso_naturality f)
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at h
  rw [integralSingularHomologyCoeffIso_hom, integralSingularHomologyCoeffIso_hom]
  exact h

theorem integralSingularHomologyCoeffIso_naturality (n : ℕ) {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) (c : integralSingularHomology n X) :
    (integralSingularHomologyCoeffIso n Y).hom (integralSingularHomologyMap n f c) =
      (HomologicalComplex.homologyMap (SSet.chainComplexMap
        (TopCat.toSSet.map (TopCat.ofHom f)) (ModuleCat.of ℤ ℤ)) n)
        ((integralSingularHomologyCoeffIso n X).hom c) := by
  have h := congrArg (fun k => k c) (integralSingularHomologyCoeffIso_hom_naturality n f)
  simp only [ModuleCat.comp_apply] at h
  rw [integralSingularHomologyCoeffIso_hom]
  rw [← integralSingularHomologyMap_eq_homologyMap n f c]
  exact h.symm

def integralReducedSingularHomologyIso (n : ℕ) (X : Type) [TopologicalSpace X] :
    integralSingularHomology (n + 1) X ≅
      reducedSingularHomology (ModuleCat.of ℤ ℤ) (TopCat.of X) (n + 1) :=
  integralSingularHomologyCoeffIso (n + 1) X ≪≫
    (reducedSingularHomologySuccIso (ModuleCat.of ℤ ℤ) (TopCat.of X) n).symm

def integralReducedSingularHomologyEquiv (n : ℕ) (X : Type) [TopologicalSpace X] :
    integralSingularHomology (n + 1) X ≃ₗ[ℤ]
      reducedSingularHomology (ModuleCat.of ℤ ℤ) (TopCat.of X) (n + 1) :=
  (integralReducedSingularHomologyIso n X).toLinearEquiv

theorem integralReducedSingularHomologyEquiv_naturality (n : ℕ) {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y))
    (c : integralSingularHomology (n + 1) X) :
    reducedSingularHomologyMap (ModuleCat.of ℤ ℤ) (TopCat.ofHom f) (n + 1)
        (integralReducedSingularHomologyEquiv n X c) =
      integralReducedSingularHomologyEquiv n Y (integralSingularHomologyMap (n + 1) f c) := by
  have h1 : reducedSingularHomologyMap (ModuleCat.of ℤ ℤ) (TopCat.ofHom f) (n + 1)
      ((reducedSingularHomologySuccIso (ModuleCat.of ℤ ℤ) (TopCat.of X) n).inv
        ((integralSingularHomologyCoeffIso (n + 1) X).hom c)) =
      (reducedSingularHomologySuccIso (ModuleCat.of ℤ ℤ) (TopCat.of Y) n).inv
        ((HomologicalComplex.homologyMap (SSet.chainComplexMap
          (TopCat.toSSet.map (TopCat.ofHom f)) (ModuleCat.of ℤ ℤ)) (n + 1))
            ((integralSingularHomologyCoeffIso (n + 1) X).hom c)) := by
    have h := congrArg (fun k => k ((reducedSingularHomologySuccIso (ModuleCat.of ℤ ℤ)
      (TopCat.of X) n).inv ((integralSingularHomologyCoeffIso (n + 1) X).hom c)))
      (reducedSingularHomologySuccIso_naturality (ModuleCat.of ℤ ℤ) (TopCat.ofHom f) n)
    simp only [ModuleCat.comp_apply] at h
    rw [Iso.inv_hom_id_apply] at h
    have h2 := congrArg (fun z => (reducedSingularHomologySuccIso (ModuleCat.of ℤ ℤ)
      (TopCat.of Y) n).inv z) h
    simpa only [Iso.hom_inv_id_apply] using h2
  have h2 : (HomologicalComplex.homologyMap (SSet.chainComplexMap
        (TopCat.toSSet.map (TopCat.ofHom f)) (ModuleCat.of ℤ ℤ)) (n + 1))
          ((integralSingularHomologyCoeffIso (n + 1) X).hom c) =
      (integralSingularHomologyCoeffIso (n + 1) Y).hom
        (integralSingularHomologyMap (n + 1) f c) :=
    (integralSingularHomologyCoeffIso_naturality (n + 1) f c).symm
  exact h1.trans (congrArg (fun z => (reducedSingularHomologySuccIso (ModuleCat.of ℤ ℤ)
    (TopCat.of Y) n).inv z) h2)

theorem exists_linearMap_eq_one_iff_exists_reducedLinearMap (n : ℕ) (X : Type) [TopologicalSpace X]
    (c : integralSingularHomology (n + 1) X) :
    (∃ φ : integralSingularHomology (n + 1) X →ₗ[ℤ] ℤ, φ c = 1) ↔
      ∃ ψ : reducedSingularHomology (ModuleCat.of ℤ ℤ) (TopCat.of X) (n + 1) →ₗ[ℤ] ℤ,
        ψ (integralReducedSingularHomologyEquiv n X c) = 1 := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨φ, hφ⟩ := h
    refine ⟨φ.comp (integralReducedSingularHomologyEquiv n X).symm.toLinearMap, ?_⟩
    exact (congrArg φ (LinearEquiv.symm_apply_apply
      (integralReducedSingularHomologyEquiv n X) c)).trans hφ
  · obtain ⟨ψ, hψ⟩ := h
    refine ⟨ψ.comp (integralReducedSingularHomologyEquiv n X).toLinearMap, ?_⟩
    rw [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, hψ]

private noncomputable def moduleCatIsoAddEquiv {A B : ModuleCat ℤ} (e : A ≅ B) : A ≃+ B where
  toFun := fun x => e.hom x
  invFun := fun y => e.inv y
  left_inv := fun x => by
    change e.inv (e.hom x) = x
    rw [Iso.hom_inv_id_apply]
  right_inv := fun y => by
    change e.hom (e.inv y) = y
    rw [Iso.inv_hom_id_apply]
  map_add' := fun x y => map_add (ConcreteCategory.hom e.hom) x y

noncomputable def liftedSphereReducedHomologyEquiv :
    reducedSingularHomology (ModuleCat.of ℤ ℤ) (TopCat.of (liftedHomotopySphere 1)) 2 ≃+ ℤ :=
  (moduleCatIsoAddEquiv (reducedSingularHomologyIso (ModuleCat.of ℤ ℤ)
      (Homeomorph.ulift.toHomotopyEquiv) 2)).trans
    (DifferentialGeometry.LocalDegree.euclideanSphereTopReducedHomologyEquiv 2)

theorem exists_reducedFunctional_integralLiftedSphereGenerator :
    ∃ ψ : reducedSingularHomology (ModuleCat.of ℤ ℤ)
        (TopCat.of (liftedHomotopySphere.{0} 1)) 2 →ₗ[ℤ] ℤ,
      ψ (integralReducedSingularHomologyEquiv 1 (liftedHomotopySphere.{0} 1)
        (integralLiftedSphereGenerator.{0} 1)) = 1 :=
  (exists_linearMap_eq_one_iff_exists_reducedLinearMap 1 (liftedHomotopySphere.{0} 1)
    (integralLiftedSphereGenerator.{0} 1)).mp
      ⟨integralLiftedSphereTopEquiv.{0} 1, integralLiftedSphereGenerator_coordinate.{0} 1⟩

theorem isSphereHomologyGenerator_squareSphereFundamentalClass_iff_exists_reducedFunctional :
    IsSphereHomologyGenerator.{0} 1 squareSphereFundamentalClass.{0} ↔
      ∃ ψ : reducedSingularHomology (ModuleCat.of ℤ ℤ)
          (TopCat.of (liftedHomotopySphere.{0} 1)) 2 →ₗ[ℤ] ℤ,
        ψ (integralReducedSingularHomologyEquiv 1 (liftedHomotopySphere.{0} 1)
          squareSphereFundamentalClass.{0}) = 1 := by
  have hgen : IsSphereHomologyGenerator.{0} 1 squareSphereFundamentalClass.{0} ↔
      ∃ φ : integralSingularHomology 2 (liftedHomotopySphere.{0} 1) →ₗ[ℤ] ℤ,
        φ squareSphereFundamentalClass.{0} = 1 :=
    isSphereHomologyGenerator_iff_exists_functional 1 squareSphereFundamentalClass.{0}
  exact hgen.trans (exists_linearMap_eq_one_iff_exists_reducedLinearMap 1
    (liftedHomotopySphere.{0} 1) squareSphereFundamentalClass.{0})

end DifferentialGeometry.Topology
