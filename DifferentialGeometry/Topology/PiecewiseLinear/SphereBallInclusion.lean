/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SphereInclusion
import DifferentialGeometry.Topology.PiecewiseLinear.GeneralPosition

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem IsPLSphere.not_subset_of_isPLBall {n : ℕ} {S B : Set E}
    (hS : IsPLSphere n S) (hB : IsPLBall n B) : ¬S ⊆ B := by
  classical
  intro hSB
  cases n with
  | zero =>
    obtain ⟨a, b, hab, rfl⟩ := isPLSphere_zero_iff.mp hS
    obtain ⟨p, rfl⟩ := isPLBall_zero_iff.mp hB
    have hap : a = p := hSB (mem_insert _ _)
    have hbp : b = p := hSB (mem_insert_of_mem _ (mem_singleton _))
    exact hab (hap.trans hbp.symm)
  | succ n =>
    obtain ⟨T, hT, hcard, -, -, -⟩ := exists_affineIndependent_openSimplex_subset
      (n := n) (by simp) (0 : EuclideanSpace ℝ (Fin (n + 1))) Filter.univ_mem
    obtain ⟨p, hp⟩ := isPLBall_convexHull_of_affineIndependent T hT hcard
    obtain ⟨q, hq⟩ := hB
    let f := p ∘ Function.invFunOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin (n + 2)))
    have hf : IsPLHomeomorphOn f B (convexHull ℝ (T : Set (EuclideanSpace ℝ (Fin (n + 1))))) :=
      hq.symm.trans hp
    obtain ⟨K, hfin, hKS⟩ := hS.isPolyhedron.exists_simplicialComplex
    let _ : Finite K.faces := hfin.to_subtype
    have hK : IsPLSphere (n + 1) K.space := hKS.symm ▸ hS
    let _ := combinatorialChartedSpace K hK.isCombinatorialManifold
    let _ : CompactSpace K.space := isCompact_iff_compactSpace.mp (isPolyhedron_space K).isCompact
    let _ : Nonempty K.space := hK.nonempty.to_subtype
    let g : K.space → EuclideanSpace ℝ (Fin (n + 1)) := fun x => f x
    have hg : Continuous g :=
      (hf.isPiecewiseAffineOn.continuousOn.mono (hKS.subset.trans hSB)).domRestrict
    have hinj : Function.Injective g := fun x y hxy =>
      Subtype.ext (hf.bijOn.injOn (hSB (hKS.subset x.2)) (hSB (hKS.subset y.2)) hxy)
    have hsurj := surjective_of_continuous_injective (E := EuclideanSpace ℝ (Fin (n + 1))) hg hinj
    exact (isCompact_range hg).ne_univ (Set.range_eq_univ.mpr hsurj)

end DifferentialGeometry.Topology.PiecewiseLinear
