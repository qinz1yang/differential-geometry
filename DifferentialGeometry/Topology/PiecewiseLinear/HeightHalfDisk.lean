/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Connected.LevelSet
import DifferentialGeometry.Topology.PiecewiseLinear.HeightFiberCircle

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_isPLHomeomorphOn_halfSpaces_of_heightIndex_eq_zero
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsPLSphere 2 K.space) (hdimE : Module.finrank ℝ E = 3)
    (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) (hinj : InjOn ℓ K.vertices)
    (hzero : heightIndex K.space ℓ = 0) (r : ℝ)
    (hbelow : ∃ y ∈ K.space, ℓ y < r) (habove : ∃ z ∈ K.space, r < ℓ z) :
    ∃ f g : (Fin 3 → ℝ) → E,
      IsPLHomeomorphOn f (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (K.space ∩ {x | ℓ x ≤ r}) ∧
      IsPLHomeomorphOn g (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (K.space ∩ {x | r ≤ ℓ x}) ∧
      f '' stdSimplexBoundary 2 = K.space ∩ {x | ℓ x = r} ∧
      g '' stdSimplexBoundary 2 = K.space ∩ {x | ℓ x = r} := by
  have hJ := isPLSphere_one_fiber_of_heightIndex_eq_zero K hK hdimE ℓ hℓ hinj hzero r hbelow habove
  obtain ⟨hcllow, hclhigh⟩ := closure_halfSpaces_of_heightIndex_eq_zero K hK hdimE ℓ hℓ hinj hzero r
      hbelow habove
  obtain ⟨hconnlow, hconnhigh⟩ := isPreconnected_halfSpaces_of_heightIndex_eq_zero K hK hdimE ℓ hℓ
      hinj hzero r
  obtain ⟨y, hy, hyr⟩ := hbelow
  obtain ⟨z, hz, hrz⟩ := habove
  have hdiff : K.space \ (K.space ∩ {x | ℓ x = r}) = K.space \ {x | ℓ x = r} := by
    ext x
    simp only [mem_sdiff, mem_inter_iff]
    tauto
  obtain ⟨f, hf, hfJ⟩ := hK.exists_isPLHomeomorphOn_closure_connectedComponentIn_sdiff hJ
    inter_subset_left (show y ∈ K.space \ (K.space ∩ {x | ℓ x = r}) from
      ⟨hy, fun h => hyr.ne h.2⟩)
  obtain ⟨g, hg, hgJ⟩ := hK.exists_isPLHomeomorphOn_closure_connectedComponentIn_sdiff hJ
    inter_subset_left (show z ∈ K.space \ (K.space ∩ {x | ℓ x = r}) from
      ⟨hz, fun h => hrz.ne h.2.symm⟩)
  rw [hdiff, Topology.connectedComponentIn_sdiff_fiber_eq_inter_lt ℓ.continuous.continuousOn
    hconnlow ⟨hy, hyr⟩, hcllow] at hf
  rw [hdiff, Topology.connectedComponentIn_sdiff_fiber_eq_inter_gt ℓ.continuous.continuousOn
    hconnhigh ⟨hz, hrz⟩, hclhigh] at hg
  exact ⟨f, g, hf, hg, hfJ, hgJ⟩

theorem isPLBall_halfSpaces_of_heightIndex_eq_zero
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsPLSphere 2 K.space) (hdimE : Module.finrank ℝ E = 3)
    (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) (hinj : InjOn ℓ K.vertices)
    (hzero : heightIndex K.space ℓ = 0) (r : ℝ)
    (hbelow : ∃ y ∈ K.space, ℓ y < r) (habove : ∃ z ∈ K.space, r < ℓ z) :
    IsPLBall 2 (K.space ∩ {x | ℓ x ≤ r}) ∧ IsPLBall 2 (K.space ∩ {x | r ≤ ℓ x}) := by
  obtain ⟨f, g, hf, hg, -, -⟩ :=
    exists_isPLHomeomorphOn_halfSpaces_of_heightIndex_eq_zero K hK hdimE ℓ hℓ hinj hzero r hbelow
        habove
  exact ⟨⟨f, hf⟩, ⟨g, hg⟩⟩

end DifferentialGeometry.Topology.PiecewiseLinear
