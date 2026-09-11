import DifferentialGeometry.Topology.Homology.SingularSubdivisionIteration



noncomputable section

open CategoryTheory AlgebraicTopology ContinuousMap Set Module

universe u v

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X] {ι : Type v}



def integralSingularSubdivisionIterateHomotopy (n k : ℕ) :
    (integralSingularChains X).X n →ₗ[ℤ] (integralSingularChains X).X (n + 1) :=
  match k with
  | 0 => 0
  | k + 1 => integralSingularSubdivisionIterateHomotopy n k +
      (integralSingularSubdivisionHomotopy n).comp (integralSingularSubdivisionIterate n k)


theorem integralSingularSubdivisionIterateHomotopy_boundary (n k : ℕ)
    (c : (integralSingularChains X).X (n + 1)) :
    (integralSingularChains X).d (n + 2) (n + 1)
      (integralSingularSubdivisionIterateHomotopy (n + 1) k c) =
        c - integralSingularSubdivisionIterate (n + 1) k c -
          integralSingularSubdivisionIterateHomotopy n k ((integralSingularChains X).d (n + 1) n c) := by
  induction k with
  | zero =>
    change (integralSingularChains X).d (n + 2) (n + 1) 0 = c - c - 0
    simp only [map_zero, sub_self]
  | succ k ih =>
    simp only [integralSingularSubdivisionIterateHomotopy, LinearMap.add_apply, LinearMap.comp_apply,
      map_add] at ih ⊢
    rw [ih]
    have h := LinearMap.congr_fun (integralSingularSubdivisionHomotopy_boundary n)
      (integralSingularSubdivisionIterate (n + 1) k c)
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply] at h
    rw [h, integralSingularSubdivisionIterate_boundary, integralSingularSubdivisionIterate_succ]
    abel



theorem integralSingularSubdivisionIterateHomotopy_cycle (n k : ℕ)
    (c : (integralSingularChains X).X (n + 1)) (hc : (integralSingularChains X).d (n + 1) n c = 0) :
    (integralSingularChains X).d (n + 2) (n + 1)
      (integralSingularSubdivisionIterateHomotopy (n + 1) k c) =
        c - integralSingularSubdivisionIterate (n + 1) k c := by
  rw [integralSingularSubdivisionIterateHomotopy_boundary, hc, map_zero, sub_zero]


theorem integralSingularSubdivisionIterateHomotopy_mem (n k : ℕ) (A : Set X)
    {c : (integralSingularChains X).X n} (hc : c ∈ integralSingularChainsIn n A) :
    integralSingularSubdivisionIterateHomotopy n k c ∈ integralSingularChainsIn (n + 1) A := by
  induction k with
  | zero => exact Submodule.zero_mem _
  | succ k ih =>
    exact Submodule.add_mem _ ih (integralSingularSubdivisionHomotopy_mem n A
      (integralSingularSubdivisionIterate_mem n k A hc))



theorem integralSingularSubdivisionIterateHomotopy_small (n k : ℕ) (U : ι → Set X)
    {c : (integralSingularChains X).X n} (hc : c ∈ integralSingularSmallChains n U) :
    integralSingularSubdivisionIterateHomotopy n k c ∈ integralSingularSmallChains (n + 1) U := by
  induction k with
  | zero => exact Submodule.zero_mem _
  | succ k ih =>
    exact Submodule.add_mem _ ih (integralSingularSubdivisionHomotopy_small n U
      (integralSingularSubdivisionIterate_small n k U hc))

end DifferentialGeometry.Topology
