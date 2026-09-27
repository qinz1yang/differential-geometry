/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ConicalGermExtension

open Set Topology Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

theorem IsPLHomeomorphOn.exists_homogeneous_preserving_radial_patterns
    {ι : Type*} {f : E → F} {U : Set E} {V : Set F}
    (hf : IsPLHomeomorphOn f U V) (hU : IsOpen U) (hV : IsOpen V) {x : E} (hx : x ∈ U)
    (S : ι → Set E) (T : ι → Set F)
    (hS : ∀ i v (t : ℝ), 0 < t → (x + t • v ∈ S i ↔ x + v ∈ S i))
    (hT : ∀ i w (t : ℝ), 0 < t → (f x + t • w ∈ T i ↔ f x + w ∈ T i))
    (hlocal : ∀ i z, z ∈ U → (z ∈ S i ↔ f z ∈ T i)) :
    ∃ (G : E → F) (ρ : ℝ), 0 < ρ ∧ ball x ρ ⊆ U ∧
      IsPLHomeomorphOn G univ univ ∧ EqOn G f (ball x ρ) ∧
      (∀ v (t : ℝ), 0 ≤ t → G (x + t • v) = G x + t • (G (x + v) - G x)) ∧
      (∀ i z, z ∈ S i ↔ G z ∈ T i) ∧ ∀ i, G '' S i = T i := by
  obtain ⟨G, ρ, hρ, hball, hG, hEq, hhom⟩ :=
    hf.exists_isPLHomeomorphOn_univ_homogeneous hU hV hx
  have hGx : G x = f x := hEq (mem_ball_self hρ)
  have hmem (i : ι) (z : E) : z ∈ S i ↔ G z ∈ T i := by
    apply forall_mem_iff_of_homogeneous hhom (hS i) ?_ hρ ?_ z
    · simpa only [hGx] using hT i
    · intro y hy
      rw [hEq hy]
      exact hlocal i y (hball hy)
  refine ⟨G, ρ, hρ, hball, hG, hEq, hhom, hmem, fun i => ?_⟩
  apply Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact (hmem i z).mp hz
  · intro y hy
    obtain ⟨z, -, rfl⟩ := hG.bijOn.surjOn (mem_univ y)
    exact ⟨z, (hmem i z).mpr hy, rfl⟩

end DifferentialGeometry.Topology.PiecewiseLinear
