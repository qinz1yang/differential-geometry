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

theorem IsCombinatorialManifold.not_subset_of_isPLBall {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold (n + 1) K) (hne : K.space.Nonempty)
    {B : Set E} (hB : IsPLBall (n + 1) B) : ¬ K.space ⊆ B := by
  classical
  intro hKB
  obtain ⟨T, hT, hcard, -, -, -⟩ := exists_affineIndependent_openSimplex_subset
    (n := n) (by simp) (0 : EuclideanSpace ℝ (Fin (n + 1))) Filter.univ_mem
  obtain ⟨p, hp⟩ := isPLBall_convexHull_of_affineIndependent T hT hcard
  obtain ⟨q, hq⟩ := hB
  let f := p ∘ Function.invFunOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin (n + 2)))
  have hf : IsPLHomeomorphOn f B (convexHull ℝ (T : Set (EuclideanSpace ℝ (Fin (n + 1))))) :=
    hq.symm.trans hp
  let _ := combinatorialChartedSpace K hK
  let _ : CompactSpace K.space := isCompact_iff_compactSpace.mp (isPolyhedron_space K).isCompact
  let _ : Nonempty K.space := hne.to_subtype
  let g : K.space → EuclideanSpace ℝ (Fin (n + 1)) := fun x => f x
  have hg : Continuous g := (hf.isPiecewiseAffineOn.continuousOn.mono hKB).domRestrict
  have hinj : Function.Injective g := fun x y hxy =>
    Subtype.ext (hf.bijOn.injOn (hKB x.property) (hKB y.property) hxy)
  have hsurj := surjective_of_continuous_injective (E := EuclideanSpace ℝ (Fin (n + 1))) hg hinj
  exact (isCompact_range hg).ne_univ (Set.range_eq_univ.mpr hsurj)

end DifferentialGeometry.Topology.PiecewiseLinear
