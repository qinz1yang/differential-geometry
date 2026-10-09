/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Embedding.Diffeomorph
import DifferentialGeometry.Topology.PiecewiseLinear.OneHandleAlignment
import DifferentialGeometry.Topology.PiecewiseLinear.SmoothDiskPairCollar

open Set Topology Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

noncomputable def planarReflectionDiffeomorph :
    Diffeomorph (𝓡 2) (𝓡 2) (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) ∞ where
  toEquiv := planarReflection.toLinearEquiv.toEquiv
  contMDiff_toFun := planarReflection.toContinuousLinearEquiv.contDiff.contMDiff
  contMDiff_invFun := planarReflection.symm.toContinuousLinearEquiv.contDiff.contMDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem isSmoothHandleStage_adjunction_one
    {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    [IsManifold (𝓡∂ 3) ∞ M] [T2Space M] [CompactSpace M]
    (ψ : {z : Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (0 : ℝ) 1 |
      z.val ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({0, 1} : Set ℝ)} → M)
    (hψ : IsClosedEmbedding ψ) (f : Fin 2 → EuclideanSpace ℝ (Fin 2) → M)
    (hf : ∀ j, IsSmoothEmbedding (𝓡 2) (𝓡∂ 3) ∞ (f j))
    (hfbd : ∀ j, range (f j) ⊆ (𝓡∂ 3).boundary M)
    (hdisj : Disjoint (range (f 0)) (range (f 1)))
    (hrange : range ψ = ⋃ j, f j '' Metric.closedBall 0 1) :
    IsSmoothHandleStage
      (AdjunctionSpace (Subtype.val : _ → Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (0 : ℝ) 1) ψ)
      (adjunctionLower ψ '' ((𝓡∂ 3).boundary M \
          ψ '' {z | z.val.val ∈ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) \ stdSimplexBoundary 2) ×ˢ
            ({0, 1} : Set ℝ)}) ∪
        adjunctionCell Subtype.val ψ '' {z | z.val ∈ stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1}) := by
  classical
  obtain ⟨Fb, Ft, hFF, hb, ht⟩ := exists_oneHandle_end_assignment ψ hψ.continuous f
    (fun j => (hf j).contMDiff.continuous) hdisj hrange
  have hFbS : IsSmoothEmbedding (𝓡 2) (𝓡∂ 3) ∞ Fb := by
    rcases hFF with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact hf 0
    · exact hf 1
  have hFtS : IsSmoothEmbedding (𝓡 2) (𝓡∂ 3) ∞ Ft := by
    rcases hFF with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact hf 1
    · exact hf 0
  have hFbbd : range Fb ⊆ (𝓡∂ 3).boundary M := by
    rcases hFF with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact hfbd 0
    · exact hfbd 1
  have hFtbd : range Ft ⊆ (𝓡∂ 3).boundary M := by
    rcases hFF with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact hfbd 1
    · exact hfbd 0
  have hFdisj : Disjoint (range Fb) (range Ft) := by
    rcases hFF with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hdisj
    · exact hdisj.symm
  obtain ⟨L, Ext, hL, hExt, hExtr, hExt1, hExt2, hEb, hEt⟩ :=
    exists_oneHandle_alignment ψ hψ Fb Ft hFbS.isEmbedding hFtS.isEmbedding hb ht
  have hFtL : IsSmoothEmbedding (𝓡 2) (𝓡∂ 3) ∞ (Ft ∘ L) := by
    rcases hL with rfl | rfl
    · exact hFtS
    · exact hFtS.comp_diffeomorph planarReflectionDiffeomorph
  have hrangeL : range (Ft ∘ L) = range Ft := by
    rcases hL with rfl | rfl
    · exact Function.surjective_id.range_comp Ft
    · exact planarReflection.surjective.range_comp Ft
  let Fc : Fin 2 → EuclideanSpace ℝ (Fin 2) → M := ![Fb, Ft ∘ L]
  have hFcS : ∀ j, IsSmoothEmbedding (𝓡 2) (𝓡∂ 3) ∞ (Fc j) := by
    intro j
    fin_cases j
    · exact hFbS
    · exact hFtL
  have hFcbd : ∀ j, range (Fc j) ⊆ (𝓡∂ 3).boundary M := by
    intro j
    fin_cases j
    · exact hFbbd
    · change range (Ft ∘ L) ⊆ _
      rw [hrangeL]
      exact hFtbd
  have hFcdisj : Disjoint (range (Fc 0)) (range (Fc 1)) := by
    change Disjoint (range Fb) (range (Ft ∘ L))
    rw [hrangeL]
    exact hFdisj
  obtain ⟨a, V, θ, Θ, ha, ha2, hV, hθV, hΘO, hΘθ, hθΘ, hΘb, hΘt, hθs, hΘs⟩ :=
    exists_oneHandleCollar_of_isSmoothEmbedding Fc hFcS hFcbd hFcdisj
  have hA : CompactSpace {z : Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (0 : ℝ) 1 |
      z.val ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({0, 1} : Set ℝ)} := hψ.compactSpace
  have hP : CompactSpace (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (0 : ℝ) 1 : Set ((Fin 3 → ℝ) × ℝ)) :=
    isCompact_iff_compactSpace.mp ((Convexity.StdSimplex.isCompact_coordinateSet ℝ (Fin 3)).prod isCompact_Icc)
  have hi : IsClosedEmbedding (Subtype.val : {z : Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (0 : ℝ) 1 |
      z.val ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({0, 1} : Set ℝ)} →
        Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (0 : ℝ) 1) :=
    continuous_subtype_val.isClosedEmbedding Subtype.val_injective
  have hExti : ∀ b, |(Ext b).2| = 1 ↔ b ∈ range (Subtype.val :
      {z : Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (0 : ℝ) 1 |
        z.val ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({0, 1} : Set ℝ)} →
          Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (0 : ℝ) 1) := by
    intro b
    rw [hExt2, Subtype.range_coe]
    exact ⟨fun h => ⟨b.2.1, h⟩, fun h => h.2⟩
  have hΘi : ∀ z : {z : Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (0 : ℝ) 1 |
      z.val ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({0, 1} : Set ℝ)}, Θ (Ext z.val) = ψ z := by
    intro z
    rcases z.2.2 with h | h
    · obtain ⟨h1, h2⟩ := hEb z h
      have he : Ext z.val = ((Ext z.val).1, -1) := Prod.ext rfl h1
      rw [he, hΘb]
      exact h2
    · obtain ⟨h1, h2⟩ := hEt z h
      have he : Ext z.val = ((Ext z.val).1, 1) := Prod.ext rfl h1
      rw [he, hΘt]
      exact h2
  have hstage := isSmoothHandleStage_adjunction_of_oneHandleCollar hi hψ hExt hExtr hExti ha
    ha2 hV hθV hΘO hΘθ hθΘ hΘi hθs hΘs
  have hFr : {b : (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (0 : ℝ) 1 : Set ((Fin 3 → ℝ) × ℝ)) |
      ‖(Ext b).1‖ = 1} = {z | z.val ∈ stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1} := by
    ext b
    change ‖(Ext b).1‖ = 1 ↔ b.val.1 ∈ stdSimplexBoundary 2 ∧ b.val.2 ∈ Icc (0 : ℝ) 1
    rw [hExt1]
    exact ⟨fun h => ⟨h, b.2.2⟩, fun h => h.1⟩
  have hRFr : ∀ z : {z : Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (0 : ℝ) 1 |
      z.val ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({0, 1} : Set ℝ)},
      z ∉ {z : {z : Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (0 : ℝ) 1 |
        z.val ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({0, 1} : Set ℝ)} |
          z.val.val ∈ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) \ stdSimplexBoundary 2) ×ˢ ({0, 1} : Set ℝ)} →
      z.val ∈ {z : (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (0 : ℝ) 1 : Set ((Fin 3 → ℝ) × ℝ)) |
        z.val ∈ stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1} := by
    intro z hz
    refine ⟨?_, z.val.2.2⟩
    by_contra hbd
    exact hz ⟨⟨z.2.1, hbd⟩, z.2.2⟩
  rw [adjunctionLower_boundary_sdiff_union_eq hRFr, ← hFr]
  exact hstage

end DifferentialGeometry.Topology.PiecewiseLinear
