import DifferentialGeometry.Topology.Homology.ConeSpherePairing

noncomputable section

open CategoryTheory AlgebraicTopology ContinuousMap
open scoped Simplicial

namespace DifferentialGeometry.Topology

universe u
variable {X : Type u} [TopologicalSpace X]

def integralSingularSphereFace
    (f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, X)) (i : Fin 4) :
    integralSingularSimplex 2 X :=
  integralSingularSimplexMap 2 (f.comp (liftedHomotopySphereDown 1))
    (integralSingularSimplexMap 2 (simplexBoundarySphereMap 1)
      ((integralSingularSimplexEquiv 2 _).symm (simplexBoundaryFace 1 i)))

theorem integralSingularSphereFace_apply
    (f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, X)) (i : Fin 4)
    (p : stdSimplex ℝ (Fin 3)) :
    integralSingularSimplexEquiv 2 X (integralSingularSphereFace f i) p =
      f (Simplex.stdSimplexNormedBoundarySphereHomeomorph
        (EuclideanSpace.equiv (Fin 3) ℝ).symm
        ⟨stdSimplex.map i.succAbove p, ⟨i, Simplex.map_succAbove_apply_pivot i p⟩⟩) := by
  simp only [integralSingularSphereFace, integralSingularSimplexMap_apply,
    Equiv.apply_symm_apply, ContinuousMap.comp_apply]
  rfl

theorem integralSingularChainMap_simplexBoundarySphereChain
    (f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, X)) :
    (integralSingularChainMap (f.comp (liftedHomotopySphereDown 1))).f 2
      (simplexBoundarySphereChain.{u} 1) =
      ∑ i : Fin 4, (-1 : ℤ) ^ i.val • integralSimplexChain 2 (integralSingularSphereFace f i) := by
  rw [simplexBoundarySphereChain, simplexBoundaryChain, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_zsmul, map_zsmul, integralSimplexChain_map, integralSimplexChain_map]
  rfl

variable [SimplyConnectedSpace X] (x : X)
    (hfaces : ∀ τ : integralSingularSimplex 3 X,
      integralSingularConeSphereClass x ((TopCat.toSSet.obj (TopCat.of X)).δ 0 τ) *
        integralSingularConeSphereClass x ((TopCat.toSSet.obj (TopCat.of X)).δ 2 τ) =
      integralSingularConeSphereClass x ((TopCat.toSSet.obj (TopCat.of X)).δ 1 τ) *
        integralSingularConeSphereClass x ((TopCat.toSSet.obj (TopCat.of X)).δ 3 τ))

include hfaces

theorem integralSingularConeSphereHomologyPairing_freeSphereHomologyImage
    (f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, X)) :
    integralSingularConeSphereHomologyPairing x hfaces
      (freeSphereHomologyImage 1 (simplexBoundarySphereClass.{u} 1) (ZerothHomotopy.mk f)) =
        ∑ i : Fin 4, (-1 : ℤ) ^ i.val •
          Additive.ofMul (integralSingularConeSphereClass x (integralSingularSphereFace f i)) := by
  rw [freeSphereHomologyImage_mk, simplexBoundarySphereClass, integralSingularCycleClass_map,
    integralSingularConeSphereHomologyPairing_cycle, integralSingularCycleMap_val,
    integralSingularChainMap_simplexBoundarySphereChain, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_zsmul, integralSingularConeSpherePairing_simplex]

end DifferentialGeometry.Topology
