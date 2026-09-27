import DifferentialGeometry.Topology.Homology.SimplexBoundaryLocalClass
import DifferentialGeometry.Topology.Homology.SpherePunctureHomology
import DifferentialGeometry.Topology.Homology.SimplexBoundaryChain
import DifferentialGeometry.Topology.Homology.EuclideanSimplexGenerator
import DifferentialGeometry.Topology.Homology.HurewiczOnePathLoopBridge

noncomputable section

open CategoryTheory AlgebraicTopology
open scoped Simplicial

namespace DifferentialGeometry.Topology

universe u

private def tetrahedronBoundaryMap :
    C(ULift.{u} (Simplex.boundary (Fin 4)), SimplexDegree.puncturedThreeSpace.{u}) :=
  ⟨fun p => ⟨SimplexDegree.standardTetrahedronSimplex p.down.val, by
    intro hz
    have hz' : DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.positiveTetrahedron p.down.val = 0 :=
      ULift.up_inj.mp hz
    obtain ⟨i, hi⟩ := p.down.property
    exact DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.positiveTetrahedron_face_ne_zero
      p.down.val i hi hz'⟩,
    by
      apply Continuous.subtype_mk
      exact SimplexDegree.standardTetrahedronSimplex.continuous.comp
        (continuous_subtype_val.comp continuous_uliftDown)⟩

private theorem tetrahedronBoundaryMap_chain :
    (integralSingularChainMap tetrahedronBoundaryMap).f 2 (simplexBoundaryChain.{u} 1) =
      SimplexDegree.euclideanStandardSimplexBoundaryChain.{u} (ULift.up 1) := by
  rw [simplexBoundaryChain, map_sum]
  simp only [map_zsmul]
  change (∑ i : Fin 4, (-1 : ℤ) ^ i.val •
    (integralSingularChainMap tetrahedronBoundaryMap).f 2
      (integralSimplexChain 2 ((integralSingularSimplexEquiv 2 _).symm
        (simplexBoundaryFace 1 i)))) = _
  simp only [SimplexDegree.euclideanStandardSimplexBoundaryChain,
    SimplexDegree.puncturedSimplexBoundary]
  change _ = (∑ i : Fin 4, (-1 : ℤ) ^ i.val •
    (SimplexDegree.integralSimplexChain 2 _).hom) (ULift.up 1)
  rw [LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [integralSimplexChain_map]
  rfl

private def sphereTetrahedronBoundaryMap :
    C(liftedHomotopySphere.{u} 1, SimplexDegree.puncturedThreeSpace.{u}) :=
  tetrahedronBoundaryMap.comp
    ⟨fun p => ULift.up ((Simplex.stdSimplexNormedBoundarySphereHomeomorph
        (EuclideanSpace.equiv (Fin 3) ℝ).symm).symm p.down),
      continuous_uliftUp.comp ((Simplex.stdSimplexNormedBoundarySphereHomeomorph
        (EuclideanSpace.equiv (Fin 3) ℝ).symm).symm.continuous.comp continuous_uliftDown)⟩

private theorem sphereTetrahedronBoundaryMap_comp :
    sphereTetrahedronBoundaryMap.comp (simplexBoundarySphereMap.{u} 1) =
      tetrahedronBoundaryMap := by
  apply ContinuousMap.ext
  intro p
  change tetrahedronBoundaryMap (ULift.up
    ((Simplex.stdSimplexNormedBoundarySphereHomeomorph
      (EuclideanSpace.equiv (Fin 3) ℝ).symm).symm
        (Simplex.stdSimplexNormedBoundarySphereHomeomorph
          (EuclideanSpace.equiv (Fin 3) ℝ).symm p.down))) = _
  rw [Homeomorph.symm_apply_apply]

private theorem sphereTetrahedronBoundaryMap_chain :
    (integralSingularChainMap sphereTetrahedronBoundaryMap).f 2
      (simplexBoundarySphereChain.{u} 1) =
        SimplexDegree.euclideanStandardSimplexBoundaryChain.{u} (ULift.up 1) := by
  have hc := congrArg (fun k => k.f 2)
    (integralSingularChainMap_comp (simplexBoundarySphereMap.{u} 1) sphereTetrahedronBoundaryMap)
  change (integralSingularChainMap (sphereTetrahedronBoundaryMap.comp
    (simplexBoundarySphereMap.{u} 1))).f 2 =
    (integralSingularChainMap (simplexBoundarySphereMap.{u} 1)).f 2 ≫
      (integralSingularChainMap sphereTetrahedronBoundaryMap).f 2 at hc
  change (integralSingularChainMap sphereTetrahedronBoundaryMap).f 2
    ((integralSingularChainMap (simplexBoundarySphereMap.{u} 1)).f 2
      (simplexBoundaryChain.{u} 1)) = _
  rw [← ModuleCat.comp_apply, ← hc, sphereTetrahedronBoundaryMap_comp]
  exact tetrahedronBoundaryMap_chain

private theorem sphereTetrahedronBoundaryMap_class :
    integralSingularHomologyMap 2 sphereTetrahedronBoundaryMap
      (simplexBoundarySphereClass.{u} 1) =
        SimplexDegree.euclideanStandardSimplexBoundaryClass.{u} := by
  rw [simplexBoundarySphereClass, ← integralHomologyClass_eq_integralSingularCycleClass,
    integralSingularHomologyMap_integralHomologyClass]
  unfold integralHomologyClass
  rw [← SimplexDegree.euclideanStandardSimplexBoundaryClass_eq_classOf]
  apply integralHomologyClassOf_congr
  exact (SimplexDegree.integralChainHom_ext sphereTetrahedronBoundaryMap_chain.symm).symm

def simplexBoundarySphereDegree :
    integralSingularHomology 2 (liftedHomotopySphere.{u} 1) →ₗ[ℤ] ℤ :=
  SimplexDegree.euclideanSimplexBoundaryDegree.comp
    (integralSingularHomologyMap 2 sphereTetrahedronBoundaryMap)

theorem simplexBoundarySphereDegree_simplexBoundarySphereClass :
    simplexBoundarySphereDegree (simplexBoundarySphereClass.{u} 1) = 1 := by
  rw [simplexBoundarySphereDegree, LinearMap.comp_apply, sphereTetrahedronBoundaryMap_class]
  exact SimplexDegree.euclideanSimplexBoundaryDegree_euclideanStandardSimplexBoundaryClass

theorem isSphereHomologyGenerator_simplexBoundarySphereClass :
    IsSphereHomologyGenerator 1 (simplexBoundarySphereClass.{u} 1) :=
  (isSphereHomologyGenerator_iff_exists_functional 1 _).mpr
    ⟨simplexBoundarySphereDegree, simplexBoundarySphereDegree_simplexBoundarySphereClass⟩

end DifferentialGeometry.Topology

end

noncomputable section

open CategoryTheory Set

universe u

namespace DifferentialGeometry.Topology

private def simplexBoundarySphereHomeomorph (n : ℕ) :
    ULift.{u} (Simplex.boundary (Fin (n + 3))) ≃ₜ liftedHomotopySphere.{u} n :=
  Homeomorph.ulift.trans
    ((Simplex.stdSimplexNormedBoundarySphereHomeomorph
      (EuclideanSpace.equiv (Fin (n + 2)) ℝ).symm).trans Homeomorph.ulift.symm)

private theorem integralSingularHomologyMap_simplexBoundarySphereMap (n : ℕ) :
    integralSingularHomologyMap (n + 1) (simplexBoundarySphereMap.{u} n)
      (integralHomologyClass n (simplexBoundaryChain n) (simplexBoundaryChain_boundary n)) =
      simplexBoundarySphereClass n := by
  rw [simplexBoundarySphereClass, ← integralHomologyClass_eq_integralSingularCycleClass,
    integralSingularHomologyMap_integralHomologyClass]
  rfl

theorem isSphereHomologyGenerator_simplexBoundarySphereClass_three :
    IsSphereHomologyGenerator 2 (simplexBoundarySphereClass.{u} 2) := by
  let e := simplexBoundarySphereHomeomorph.{u} 2
  let p := simplexBoundaryFace.{u} 2 0 stdSimplex.barycenter
  let L := integralLocalHomologyHomeomorphIso 3 e p
  let g := integralAbsoluteToRelative 3 ({e p}ᶜ : Set (liftedHomotopySphere.{u} 2))
  let c := integralAbsoluteToRelative 3 ({p}ᶜ : Set (ULift.{u} (Simplex.boundary (Fin 5))))
    (integralHomologyClass 2 (simplexBoundaryChain 2) (simplexBoundaryChain_boundary 2))
  have hc : Function.Bijective (fun z : ℤ => z • c) := by
    dsimp only [c, p]
    rw [integralAbsoluteToRelative_simplexBoundaryChain_face_zero]
    exact simplexBoundaryFace_zero_localClass_generator
  have hg : Function.Bijective g :=
    integralAbsoluteToRelative_liftedSphere_puncture_bijective 2 1 (e p)
  have heq : L.hom.hom c = g (simplexBoundarySphereClass 2) := by
    have hnat := LinearMap.congr_fun (integralAbsoluteToRelative_natural 3
      (⟨e, e.continuous⟩ : C(ULift.{u} (Simplex.boundary (Fin 5)), liftedHomotopySphere.{u} 2))
      (show MapsTo e ({p}ᶜ : Set (ULift.{u} (Simplex.boundary (Fin 5))))
        ({e p}ᶜ : Set (liftedHomotopySphere.{u} 2)) from fun _ hx => e.injective.ne hx))
      (integralHomologyClass 2 (simplexBoundaryChain 2) (simplexBoundaryChain_boundary 2))
    change g (integralSingularHomologyMap 3 (simplexBoundarySphereMap 2)
      (integralHomologyClass 2 (simplexBoundaryChain 2) (simplexBoundaryChain_boundary 2))) =
      L.hom.hom c at hnat
    rw [integralSingularHomologyMap_simplexBoundarySphereMap] at hnat
    exact hnat.symm
  apply (isSphereHomologyGenerator_iff_forall_exists_zsmul 2
    (simplexBoundarySphereClass 2)).mpr
  intro y
  obtain ⟨a, ha⟩ := L.toLinearEquiv.surjective (g y)
  obtain ⟨k, hk⟩ := hc.2 a
  change k • c = a at hk
  refine ⟨k, hg.1 ?_⟩
  rw [map_zsmul, ← heq, ← map_zsmul, hk]
  exact ha.symm

end DifferentialGeometry.Topology
