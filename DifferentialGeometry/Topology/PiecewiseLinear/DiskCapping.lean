/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SphericalDiskComplement
import DifferentialGeometry.Topology.PiecewiseLinear.BallHomotopy

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem IsPLSphere.exists_isPLHomeomorphOn_of_union_disk
    {A D : Set E} (hS : IsPLSphere 2 (A ∪ D)) {r : (Fin 3 → ℝ) → E}
    (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D)
    (hmeet : A ∩ D = r '' stdSimplexBoundary 2) :
    ∃ q : (Fin 3 → ℝ) → E, IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) A ∧
      q '' stdSimplexBoundary 2 = r '' stdSimplexBoundary 2 := by
  have hcl : closure ((A ∪ D) \ D) = A := by
    rw [hS.closure_sdiff_eq_sdiff_image_stdSimplexBoundary hr subset_union_right, ← hmeet]
    ext x
    constructor
    · rintro ⟨hxA | hxD, hx⟩
      · exact hxA
      · by_contra hxA
        exact hx ⟨hxD, fun h => hxA h.1⟩
    · exact fun hxA => ⟨Or.inl hxA, fun h => h.2 ⟨hxA, h.1⟩⟩
  obtain ⟨q, hq⟩ := hS.isPLBall_closure_sdiff ⟨r, hr⟩ subset_union_right
  have hqB := hS.image_stdSimplexBoundary_complement ⟨r, hr⟩ subset_union_right hq
  rw [hcl] at hq hqB
  exact ⟨q, hq, hqB.trans hmeet⟩

theorem IsPLSphere.nullhomotopic_inclusion_of_union_disk
    {A D S : Set E} (hSphere : IsPLSphere 2 (A ∪ D)) {r : (Fin 3 → ℝ) → E}
    (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D)
    (hmeet : A ∩ D = r '' stdSimplexBoundary 2) (hAS : A ⊆ S) :
    (⟨Set.inclusion ((hmeet.symm.subset.trans inter_subset_left).trans hAS),
      continuous_inclusion _⟩ : C(r '' stdSimplexBoundary 2, S)).Nullhomotopic := by
  obtain ⟨q, hq, _⟩ := hSphere.exists_isPLHomeomorphOn_of_union_disk hr hmeet
  exact (show IsPLBall 2 A from ⟨q, hq⟩).nullhomotopic_inclusion
    (hmeet.symm.subset.trans inter_subset_left) hAS

theorem IsPLSphere.nullhomotopic_inclusion_of_cylinder_into_complement
    {A D : Set E} (hSphere : IsPLSphere 2 (A ∪ D)) {r : (Fin 3 → ℝ) → E}
    (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D)
    (hmeet : A ∩ D = r '' stdSimplexBoundary 2)
    {C J S : Set F} {g : E → F} (hg : IsPLHomeomorphOn g A C)
    (hCS : C ⊆ S) (hJS : J ⊆ S) {ρ : F × ℝ → F}
    (hρ : ContinuousOn ρ (J ×ˢ Icc (0 : ℝ) 1))
    (hρS : MapsTo ρ (J ×ˢ Icc (0 : ℝ) 1) S)
    (hzero : ∀ x ∈ J, ρ (x, 0) = x) (hone : ∀ x ∈ J, ρ (x, 1) ∈ C) :
    (⟨Set.inclusion hJS, continuous_inclusion hJS⟩ : C(J, S)).Nullhomotopic := by
  obtain ⟨q, hq, _⟩ := hSphere.exists_isPLHomeomorphOn_of_union_disk hr hmeet
  have hC : IsPLBall 2 C := ⟨g ∘ q, hq.trans hg⟩
  exact hC.nullhomotopic_inclusion_of_cylinder hCS hJS hρ hρS hzero hone

end DifferentialGeometry.Topology.PiecewiseLinear
