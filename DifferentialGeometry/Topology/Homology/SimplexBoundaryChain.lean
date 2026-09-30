import DifferentialGeometry.Topology.Simplex.BoundaryGluing
import DifferentialGeometry.Topology.Homology.UniversalCoefficientsOne
import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SimplexMaps
import DifferentialGeometry.Topology.Homology.LiftedSphere

noncomputable section

open CategoryTheory AlgebraicTopology
open Convexity.StdSimplex (coordinateSet coordinateMap coordinateHomeomorph coordinateEquiv)
open scoped Simplicial

namespace DifferentialGeometry.Topology

universe u

variable {X : Type u} [TopologicalSpace X]

def simplexBoundaryFace (n : ℕ) (i : Fin (n + 3)) :
    C(Convexity.StdSimplex ℝ (Fin (n + 2)), ULift.{u} (Simplex.boundary (Fin (n + 3)))) :=
  ⟨fun p => ULift.up ⟨coordinateMap i.succAbove (coordinateEquiv ℝ _ p),
    ⟨i, Simplex.map_succAbove_apply_pivot i (coordinateEquiv ℝ _ p)⟩⟩,
    continuous_uliftUp.comp (((Convexity.StdSimplex.continuous_coordinateMap i.succAbove).comp
      (coordinateHomeomorph ℝ _).continuous).subtype_mk _)⟩

def simplexBoundaryChain (n : ℕ) :
    (integralSingularChains (ULift.{u} (Simplex.boundary (Fin (n + 3))))).X (n + 1) :=
  ∑ i : Fin (n + 3), (-1 : ℤ) ^ i.val • integralSimplexChain (n + 1)
    ((integralSingularSimplexEquiv (n + 1) _).symm (simplexBoundaryFace n i))

theorem integralSingularChainMap_boundaryDesc_simplexBoundaryChain (n : ℕ)
    (f : Fin (n + 3) → C(coordinateSet ℝ (Fin (n + 2)), X))
    (h : ∀ (i : Fin (n + 3)) (j : Fin (n + 2))
      (p : coordinateSet ℝ (Fin (n + 1))),
      f i (coordinateMap j.succAbove p) =
        f (i.succAbove j) (coordinateMap (j.predAbove i).succAbove p)) :
    (integralSingularChainMap
      ((Simplex.boundaryDesc f h).comp ⟨ULift.down, continuous_uliftDown⟩)).f (n + 1)
      (simplexBoundaryChain.{u} n) =
        ∑ i : Fin (n + 3), (-1 : ℤ) ^ i.val • integralSimplexChain (n + 1)
          ((integralSingularSimplexEquiv (n + 1) X).symm
            ((f i).comp ⟨coordinateEquiv ℝ _, (coordinateHomeomorph ℝ _).continuous⟩)) := by
  rw [simplexBoundaryChain, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_zsmul, integralSimplexChain_map]
  congr 2
  apply (integralSingularSimplexEquiv (n + 1) X).injective
  rw [integralSingularSimplexMap_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  ext p
  exact Simplex.boundaryDesc_face f h i (coordinateEquiv ℝ _ p)

def simplexBoundarySphereMap (n : ℕ) :
    C(ULift.{u} (Simplex.boundary (Fin (n + 3))), liftedHomotopySphere.{u} n) :=
  ⟨fun p => ULift.up (Simplex.stdSimplexNormedBoundarySphereHomeomorph
      (EuclideanSpace.equiv (Fin (n + 2)) ℝ).symm p.down),
    continuous_uliftUp.comp ((Simplex.stdSimplexNormedBoundarySphereHomeomorph
      (EuclideanSpace.equiv (Fin (n + 2)) ℝ).symm).continuous.comp continuous_uliftDown)⟩

def simplexBoundarySphereChain (n : ℕ) :
    (integralSingularChains (liftedHomotopySphere.{u} n)).X (n + 1) :=
  (integralSingularChainMap (simplexBoundarySphereMap n)).f (n + 1)
    (simplexBoundaryChain n)

theorem integralSingularChainMap_boundarySphereDesc_simplexBoundarySphereChain (n : ℕ)
    (f : Fin (n + 3) → C(coordinateSet ℝ (Fin (n + 2)), X))
    (h : ∀ (i : Fin (n + 3)) (j : Fin (n + 2))
      (p : coordinateSet ℝ (Fin (n + 1))),
      f i (coordinateMap j.succAbove p) =
        f (i.succAbove j) (coordinateMap (j.predAbove i).succAbove p)) :
    (integralSingularChainMap
      ((Simplex.boundarySphereDesc f h).comp ⟨ULift.down, continuous_uliftDown⟩)).f (n + 1)
      (simplexBoundarySphereChain.{u} n) =
        ∑ i : Fin (n + 3), (-1 : ℤ) ^ i.val • integralSimplexChain (n + 1)
          ((integralSingularSimplexEquiv (n + 1) X).symm
            ((f i).comp ⟨coordinateEquiv ℝ _, (coordinateHomeomorph ℝ _).continuous⟩)) := by
  let g : C(liftedHomotopySphere.{u} n, X) :=
    (Simplex.boundarySphereDesc f h).comp ⟨ULift.down, continuous_uliftDown⟩
  have he : g.comp (simplexBoundarySphereMap n) =
      (Simplex.boundaryDesc f h).comp ⟨ULift.down, continuous_uliftDown⟩ := by
    ext p
    change Simplex.boundaryDesc f h
      ((Simplex.stdSimplexNormedBoundarySphereHomeomorph
        (EuclideanSpace.equiv (Fin (n + 2)) ℝ).symm).symm
        (Simplex.stdSimplexNormedBoundarySphereHomeomorph
          (EuclideanSpace.equiv (Fin (n + 2)) ℝ).symm p.down)) = _
    rw [Homeomorph.symm_apply_apply]
    rfl
  have hc := congrArg (fun k => k.f (n + 1))
    (integralSingularChainMap_comp (simplexBoundarySphereMap n) g)
  change (integralSingularChainMap (g.comp (simplexBoundarySphereMap n))).f (n + 1) =
    (integralSingularChainMap (simplexBoundarySphereMap n)).f (n + 1) ≫
      (integralSingularChainMap g).f (n + 1) at hc
  change (integralSingularChainMap g).f (n + 1)
    ((integralSingularChainMap (simplexBoundarySphereMap n)).f (n + 1)
      (simplexBoundaryChain n)) = _
  rw [← ModuleCat.comp_apply, ← hc, he]
  exact integralSingularChainMap_boundaryDesc_simplexBoundaryChain n f h

end DifferentialGeometry.Topology

namespace DifferentialGeometry.Topology

universe u

private def simplexBoundaryAmbientInclusion (n : ℕ) :
    C(ULift.{u} (Simplex.boundary (Fin (n + 3))),
      ULift.{u} (coordinateSet ℝ (Fin (n + 3)))) :=
  ⟨fun p => ULift.up p.down.val,
    continuous_uliftUp.comp (continuous_subtype_val.comp continuous_uliftDown)⟩

private theorem simplexBoundaryAmbientInclusion_injective (n : ℕ) :
    Function.Injective (simplexBoundaryAmbientInclusion.{u} n) := by
  intro p q h
  exact ULift.ext (Subtype.ext (ULift.up_inj.mp h))

private theorem simplexBoundaryChain_inclusion (n : ℕ) :
    (integralSingularChainMap (simplexBoundaryAmbientInclusion n)).f (n + 1)
      (simplexBoundaryChain.{u} n) =
        (integralSingularChains (ULift.{u} (coordinateSet ℝ (Fin (n + 3))))).d (n + 2) (n + 1)
          (integralSimplexChain (n + 2)
            ((integralSingularSimplexEquiv (n + 2) _).symm
              ⟨fun p => ULift.up (coordinateEquiv ℝ _ p),
                continuous_uliftUp.comp (coordinateHomeomorph ℝ _).continuous⟩)) := by
  rw [simplexBoundaryChain, map_sum, integralSimplexChain_boundary]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_zsmul, integralSimplexChain_map]
  congr 2
  apply (integralSingularSimplexEquiv (n + 1) _).injective
  apply ContinuousMap.ext
  intro p
  change ULift.up (coordinateMap i.succAbove (coordinateEquiv ℝ _ p)) =
    ULift.up (coordinateEquiv ℝ _ (Convexity.StdSimplex.map i.succAbove p))
  exact congrArg ULift.up (Convexity.StdSimplex.coordinateEquiv_map i.succAbove p).symm

theorem simplexBoundaryChain_boundary (n : ℕ) :
    (integralSingularChains (ULift.{u} (Simplex.boundary (Fin (n + 3))))).d (n + 1) n
      (simplexBoundaryChain n) = 0 := by
  let j := simplexBoundaryAmbientInclusion.{u} n
  have : Mono (TopCat.ofHom j) :=
    (TopCat.mono_iff_injective _).mpr (simplexBoundaryAmbientInclusion_injective n)
  have : Mono (integralSingularChainMap j) := inferInstanceAs (Mono
    (((singularChainComplexFunctor (ModuleCat.{u} ℤ)).obj integralSingularCoefficients).map
      (TopCat.ofHom j)))
  apply ((ModuleCat.mono_iff_injective ((integralSingularChainMap j).f n)).mp inferInstance)
  have hc := congrArg (fun k => k (simplexBoundaryChain.{u} n))
    ((integralSingularChainMap j).comm (n + 1) n)
  change (integralSingularChains _).d (n + 1) n
    ((integralSingularChainMap j).f (n + 1) (simplexBoundaryChain.{u} n)) =
      (integralSingularChainMap j).f n ((integralSingularChains _).d (n + 1) n
        (simplexBoundaryChain.{u} n)) at hc
  rw [← hc, map_zero]
  change (integralSingularChains _).d (n + 1) n
    ((integralSingularChainMap (simplexBoundaryAmbientInclusion n)).f (n + 1)
      (simplexBoundaryChain.{u} n)) = 0
  rw [simplexBoundaryChain_inclusion]
  exact congrArg (fun k => k (integralSimplexChain (n + 2)
    ((integralSingularSimplexEquiv (n + 2) _).symm ⟨fun p => ULift.up (coordinateEquiv ℝ _ p),
                continuous_uliftUp.comp (coordinateHomeomorph ℝ _).continuous⟩)))
      ((integralSingularChains (ULift.{u} (coordinateSet ℝ (Fin (n + 3))))).d_comp_d
        (n + 2) (n + 1) n)

theorem simplexBoundarySphereChain_boundary (n : ℕ) :
    (integralSingularChains (liftedHomotopySphere.{u} n)).d (n + 1) n
      (simplexBoundarySphereChain n) = 0 := by
  have hc := congrArg (fun k => k (simplexBoundaryChain.{u} n))
    ((integralSingularChainMap (simplexBoundarySphereMap n)).comm (n + 1) n)
  change (integralSingularChains _).d (n + 1) n
    ((integralSingularChainMap (simplexBoundarySphereMap n)).f (n + 1)
      (simplexBoundaryChain.{u} n)) =
      (integralSingularChainMap (simplexBoundarySphereMap n)).f n
        ((integralSingularChains _).d (n + 1) n (simplexBoundaryChain.{u} n)) at hc
  change (integralSingularChains _).d (n + 1) n
    ((integralSingularChainMap (simplexBoundarySphereMap n)).f (n + 1)
      (simplexBoundaryChain.{u} n)) = 0
  rw [hc, simplexBoundaryChain_boundary, map_zero]

end DifferentialGeometry.Topology

namespace DifferentialGeometry.Topology

universe u

def simplexBoundarySphereClass (n : ℕ) :
    integralSingularHomology (n + 1) (liftedHomotopySphere.{u} n) :=
  integralSingularCycleClass n (liftedHomotopySphere.{u} n)
    ⟨simplexBoundarySphereChain n, simplexBoundarySphereChain_boundary n⟩

end DifferentialGeometry.Topology
