/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PrismCornerChart

open Set Topology
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem IsPLHomeomorphOn.exists_rounded_corner_chart
    {g : (Fin 3 → ℝ) × ℝ → E} {C A : Set E}
    (hg : IsPLHomeomorphOn g (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (0 : ℝ) 1) C)
    (htrace : g '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) = C ∩ A) :
    ∃ U : TopologicalSpace.Opens C, ∃ charts : ChartedSpace (EuclideanHalfSpace 3) U,
      let _ := charts
      IsManifold (𝓡∂ 3) ∞ U ∧
      ∃ d : Diffeomorph (𝓡∂ 3) (𝓡∂ 3) U prismCornerTarget ∞,
        (∀ x : U, x.val.val ∈ A ↔ (d x).val.val 0 = 0 ∧ (d x).val.val 1 ≤ 0) ∧
        (∀ x : U, x ∈ (𝓡∂ 3).boundary U ↔ (d x).val.val 0 = 0) ∧
        ∃ x : U, (d x).val = 0 ∧ x.val.val = g (![0, (1 : ℝ) / 2, 1 / 2], 0) := by
  let P := Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (0 : ℝ) 1
  let e : P ≃ₜ C := hg.homeomorph
  let U : TopologicalSpace.Opens C :=
    ⟨e '' (prismCornerSource : Set P), e.isOpenMap _ prismCornerSource.isOpen⟩
  let j : prismCornerSource ≃ₜ U := e.image (prismCornerSource : Set P)
  let h : U ≃ₜ prismCornerTarget := j.symm.trans prismCornerHomeomorph
  let charts : ChartedSpace (EuclideanHalfSpace 3) U :=
    DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace h
  let _ := charts
  let _ : IsManifold (𝓡∂ 3) ∞ U :=
    DifferentialGeometry.Manifold.Homeomorph.instIsManifoldPullback h
  let d : Diffeomorph (𝓡∂ 3) (𝓡∂ 3) U prismCornerTarget ∞ :=
    DifferentialGeometry.Manifold.Homeomorph.pullbackDiffeomorph h
  have hmem (p : P) : g p.val ∈ A ↔ p.val.1 ∈ stdSimplexBoundary 2 := by
    constructor
    · intro hp
      have him : g p.val ∈ g '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) :=
        htrace.symm ▸ ⟨hg.bijOn.mapsTo p.property, hp⟩
      obtain ⟨q, hq, hqp⟩ := him
      have heq : q = p.val := hg.bijOn.injOn ⟨hq.1.1, hq.2⟩ p.property hqp
      exact heq ▸ hq.1
    · intro hp
      have him : g p.val ∈ g '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) :=
        ⟨p.val, ⟨hp, p.property.2⟩, rfl⟩
      exact (htrace ▸ him).2
  refine ⟨U, charts, inferInstance, d, ?_, ?_, ?_⟩
  · intro x
    have hx := congrArg (fun y : U => y.val.val) (j.apply_symm_apply x)
    change g (j.symm x).val.val = x.val.val at hx
    rw [← hx, hmem]
    exact prismCornerHomeomorph_attaching_iff (j.symm x)
  · intro x
    rw [← d.preimage_boundary (by simp)]
    exact prismCornerTarget_boundary_iff (d x)
  · let z : prismCornerTarget := ⟨0, prismCornerTarget_zero_mem⟩
    refine ⟨j (prismCornerHomeomorph.symm z), ?_, ?_⟩
    · change (prismCornerHomeomorph
        (j.symm (j (prismCornerHomeomorph.symm z)))).val = 0
      simp [z]
    · change g (prismCornerHomeomorph.symm z).val.val = _
      rw [prismCornerHomeomorph_symm_zero]

end DifferentialGeometry.Topology.PiecewiseLinear
