/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PrismAnnulusChart

open Set Metric Topology
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem IsPLHomeomorphOn.exists_rounded_annulus_atlas
    {g : (Fin 3 → ℝ) × ℝ → E} {C A : Set E}
    (hg : IsPLHomeomorphOn g (stdSimplex ℝ (Fin 3) ×ˢ Icc (0 : ℝ) 1) C)
    (htrace : g '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) = C ∩ A) :
    let _ := prismAnnulusChartedSpace
    ∃ U : TopologicalSpace.Opens C,
      C ∩ A ⊆ (fun x : C => x.val) '' (U : Set C) ∧
      ∃ charts : ChartedSpace
        (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanHalfSpace 2)) U,
        let _ := charts
        IsManifold ((𝓡 1).prod (𝓡∂ 2)) ∞ U ∧
        ∃ d : Diffeomorph ((𝓡 1).prod (𝓡∂ 2)) ((𝓡 1).prod (𝓡∂ 2))
            U prismAnnulusSource ∞,
          (∀ x : U, g (d x).val.val = x.val.val) ∧
          (∀ x : U, x.val.val ∈ A ↔ (d x).val.val.1 ∈ stdSimplexBoundary 2) ∧
          (∀ x : U, x ∈ ((𝓡 1).prod (𝓡∂ 2)).boundary U ↔
            (d x).val.val.1 ∈ stdSimplexBoundary 2 ∨
              (d x).val.val.2 = 0 ∨ (d x).val.val.2 = 1) ∧
          ∀ v : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1, ∀ i : Bool,
            d.toHomeomorph.toOpenPartialHomeomorph.trans (prismAnnulusChart v i) ∈
              atlas (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanHalfSpace 2)) U := by
  let _ := prismAnnulusChartedSpace
  let _ : IsManifold ((𝓡 1).prod (𝓡∂ 2)) ∞ prismAnnulusSource := prismAnnulus_isManifold
  let P := stdSimplex ℝ (Fin 3) ×ˢ Icc (0 : ℝ) 1
  let e : P ≃ₜ C := hg.homeomorph
  let U : TopologicalSpace.Opens C :=
    ⟨e '' (prismAnnulusSource : Set P), e.isOpenMap _ prismAnnulusSource.isOpen⟩
  let j : prismAnnulusSource ≃ₜ U := e.image (prismAnnulusSource : Set P)
  let charts : ChartedSpace
      (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanHalfSpace 2)) U :=
    DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace j.symm
  let _ := charts
  let _ : IsManifold ((𝓡 1).prod (𝓡∂ 2)) ∞ U :=
    DifferentialGeometry.Manifold.Homeomorph.instIsManifoldPullback j.symm
  let d : Diffeomorph ((𝓡 1).prod (𝓡∂ 2)) ((𝓡 1).prod (𝓡∂ 2))
      U prismAnnulusSource ∞ :=
    DifferentialGeometry.Manifold.Homeomorph.pullbackDiffeomorph j.symm
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
  have heval (x : U) : g (d x).val.val = x.val.val :=
    congrArg (fun y : U => y.val.val) (j.apply_symm_apply x)
  refine ⟨U, ?_, charts, inferInstance, d, heval, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨q, hq, hqx⟩ := htrace.symm ▸ hx
    refine ⟨⟨x, hx.1⟩, ?_, rfl⟩
    refine ⟨⟨q, hq.1.1, hq.2⟩, mem_prismAnnulusSource_of_boundary _ hq.1, ?_⟩
    exact Subtype.ext hqx
  · intro x
    rw [← heval x]
    exact hmem (d x).val
  · intro x
    rw [← d.preimage_boundary (by simp)]
    exact prismAnnulus_boundary_iff (d x)
  · intro v i
    exact ⟨_, prismAnnulusChart_mem_atlas v i, rfl⟩

end DifferentialGeometry.Topology.PiecewiseLinear
