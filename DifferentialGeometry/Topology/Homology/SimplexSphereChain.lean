import DifferentialGeometry.Topology.Homology.SimplexBoundaryChain
import DifferentialGeometry.Topology.Simplex.Sphere

namespace DifferentialGeometry.Topology

universe u

variable {X : Type u} [TopologicalSpace X]

theorem integralSingularChainMap_simplexSphereMap_simplexBoundarySphereChain_of_even
    (n : ℕ) (hn : Even n) (g : C(stdSimplex ℝ (Fin (n + 2)), X)) (x : X)
    (hg : ∀ p ∈ Simplex.boundary (Fin (n + 2)), g p = x) :
    (integralSingularChainMap
      ((Simplex.simplexSphereMap g x hg).comp ⟨ULift.down, continuous_uliftDown⟩)).f (n + 1)
      (simplexBoundarySphereChain.{u} n) =
        integralSimplexChain (n + 1) ((integralSingularSimplexEquiv (n + 1) X).symm g) := by
  have h := integralSingularChainMap_boundarySphereDesc_simplexBoundarySphereChain n
    (Simplex.simplexSphereFaces g x) (Simplex.simplexSphereFaces_compatible g x hg)
  change (integralSingularChainMap
      ((Simplex.simplexSphereMap g x hg).comp ⟨ULift.down, continuous_uliftDown⟩)).f (n + 1)
      (simplexBoundarySphereChain.{u} n) = _ at h
  rw [h, Fin.sum_univ_succ]
  simp only [Simplex.simplexSphereFaces_zero, Simplex.simplexSphereFaces_succ,
    Fin.val_zero, pow_zero, one_zsmul, Fin.val_succ, pow_succ, mul_neg_one,
    neg_zsmul, Finset.sum_neg_distrib]
  have htail : (∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
      integralSimplexChain (n + 1)
        ((integralSingularSimplexEquiv (n + 1) X).symm (ContinuousMap.const _ x))) = 0 := by
    let c := integralSimplexChain (n + 1)
      ((integralSingularSimplexEquiv (n + 1) X).symm (ContinuousMap.const _ x))
    rw [show (∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • c) =
        (zmultiplesHom _ c) (∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val) by
      simp only [map_sum, zmultiplesHom_apply]]
    have hne : Even (n + 2) := hn.add (by decide)
    rw [Fin.sum_neg_one_pow, if_pos hne]
    exact map_zero _
  rw [htail]
  simp

theorem integralSimplexChain_boundary_eq_zero_of_even
    (n : ℕ) (hn : Even n) (g : C(stdSimplex ℝ (Fin (n + 2)), X)) (x : X)
    (hg : ∀ p ∈ Simplex.boundary (Fin (n + 2)), g p = x) :
    (integralSingularChains X).d (n + 1) n
      (integralSimplexChain (n + 1) ((integralSingularSimplexEquiv (n + 1) X).symm g)) = 0 := by
  rw [← integralSingularChainMap_simplexSphereMap_simplexBoundarySphereChain_of_even n hn g x hg]
  have hc := congrArg (fun k => k (simplexBoundarySphereChain.{u} n))
    ((integralSingularChainMap
      ((Simplex.simplexSphereMap g x hg).comp ⟨ULift.down, continuous_uliftDown⟩)).comm (n + 1) n)
  change (integralSingularChains X).d (n + 1) n
      ((integralSingularChainMap
        ((Simplex.simplexSphereMap g x hg).comp ⟨ULift.down, continuous_uliftDown⟩)).f (n + 1)
        (simplexBoundarySphereChain.{u} n)) =
    (integralSingularChainMap
      ((Simplex.simplexSphereMap g x hg).comp ⟨ULift.down, continuous_uliftDown⟩)).f n
      ((integralSingularChains (liftedHomotopySphere.{u} n)).d (n + 1) n
        (simplexBoundarySphereChain.{u} n)) at hc
  rw [hc, simplexBoundarySphereChain_boundary, map_zero]

end DifferentialGeometry.Topology
