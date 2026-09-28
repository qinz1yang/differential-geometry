/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BallFrontier
import DifferentialGeometry.Topology.PiecewiseLinear.BallGluing
import DifferentialGeometry.Topology.PiecewiseLinear.ExistsAnnularSplitBall
import DifferentialGeometry.Topology.PiecewiseLinear.SphereInclusion
import DifferentialGeometry.Topology.PiecewiseLinear.SphericalDiskComplement

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem sdiff_subset_interior_union_of_inter_eq {V₁ V₂ D : Set E3} (h₁ : IsPLBall 3 V₁)
    (h₂ : IsPLBall 3 V₂) {q : (Fin 3 → ℝ) → E3}
    (hq : IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D) (hD : V₁ ∩ V₂ = D)
    (hD₁ : D ⊆ frontier V₁) (hD₂ : D ⊆ frontier V₂) :
    D \ q '' stdSimplexBoundary 2 ⊆ interior (V₁ ∪ V₂) := by
  have hDball : IsPLBall 2 D := ⟨q, hq⟩
  have hside : ∀ {V W : Set E3}, IsPLBall 3 V → IsClosed W → D ⊆ frontier V → V ∩ W = D →
      ∃ (F : Set E3) (r : (Fin 3 → ℝ) → E3), IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) F ∧
        r '' stdSimplexBoundary 2 = q '' stdSimplexBoundary 2 ∧
        F ∩ D = q '' stdSimplexBoundary 2 ∧ F ⊆ V ∧ F ⊆ frontier (V ∪ W) := by
    intro V W hV hW hDV hVW
    have hS : IsPLSphere 2 (frontier V) := hV.isPLSphere_frontier
    have hVc : IsClosed V := hV.isPolyhedron.isClosed
    obtain ⟨r, hr⟩ := hS.isPLBall_closure_sdiff hDball hDV
    have hmeet : D ∩ closure (frontier V \ D) = q '' stdSimplexBoundary 2 :=
      hS.inter_closure_sdiff_eq_image_stdSimplexBoundary hq hDV
    have hrb : r '' stdSimplexBoundary 2 = closure (frontier V \ D) ∩ D :=
      hS.image_stdSimplexBoundary_complement hDball hDV hr
    have hFV : closure (frontier V \ D) ⊆ V :=
      closure_minimal (sdiff_subset.trans hVc.frontier_subset) hVc
    refine ⟨_, r, hr, by rw [hrb, inter_comm, hmeet], by rw [inter_comm, hmeet], hFV, ?_⟩
    refine closure_minimal (fun x hx => ?_) isClosed_frontier
    have hxV : x ∈ V := hVc.frontier_subset hx.1
    have hxW : x ∉ W := fun hxW => hx.2 (by rw [← hVW]; exact ⟨hxV, hxW⟩)
    refine ⟨subset_closure (Or.inl hxV), fun hxi => hx.1.2 ?_⟩
    refine interior_maximal (t := interior (V ∪ W) ∩ Wᶜ) (fun y hy => ?_)
      (isOpen_interior.inter hW.isOpen_compl) ⟨hxi, hxW⟩
    rcases interior_subset hy.1 with h | h
    · exact h
    · exact absurd h hy.2
  obtain ⟨F₁, r₁, hr₁, hr₁b, hF₁D, hF₁V, hF₁⟩ := hside h₁ h₂.isPolyhedron.isClosed hD₁ hD
  obtain ⟨F₂, r₂, hr₂, hr₂b, hF₂D, hF₂V, hF₂⟩ :=
    hside h₂ h₁.isPolyhedron.isClosed hD₂ (by rw [inter_comm]; exact hD)
  have hF12 : F₁ ∩ F₂ = r₁ '' stdSimplexBoundary 2 := by
    rw [hr₁b]
    apply Subset.antisymm
    · intro x hx
      have hxD : x ∈ D := by
        rw [← hD]
        exact ⟨hF₁V hx.1, hF₂V hx.2⟩
      rw [← hF₁D]
      exact ⟨hx.1, hxD⟩
    · intro x hx
      have h1 : x ∈ F₁ ∩ D := by
        rw [hF₁D]
        exact hx
      have h2 : x ∈ F₂ ∩ D := by
        rw [hF₂D]
        exact hx
      exact ⟨h1.1, h2.1⟩
  have hsph : IsPLSphere 2 (F₁ ∪ F₂) :=
    isPLSphere_union_of_inter_eq_image_stdSimplexBoundary hr₁ hr₂ hF12 (hr₂b.trans hr₁b.symm)
  have hB : IsPLBall 3 (V₁ ∪ V₂) := by
    refine isPLBall_union_of_inter_isPLBall_two h₁ h₂ ?_ ?_ ?_
    · rw [hD]
      exact hDball
    · rw [hD]
      exact hD₁
    · rw [hD]
      exact hD₂
  have hF₂' : F₂ ⊆ frontier (V₁ ∪ V₂) := by
    rw [union_comm]
    exact hF₂
  have hfr : F₁ ∪ F₂ = frontier (V₁ ∪ V₂) :=
    eq_of_subset_of_isPLSphere hsph hB.isPLSphere_frontier (union_subset hF₁ hF₂')
  intro x hx
  have hxV : x ∈ V₁ ∩ V₂ := by
    rw [hD]
    exact hx.1
  rw [← self_sdiff_frontier, ← hfr]
  refine ⟨Or.inl hxV.1, fun hxF => ?_⟩
  rcases hxF with h | h
  · have hxb : x ∈ F₁ ∩ D := ⟨h, hx.1⟩
    rw [hF₁D] at hxb
    exact hx.2 hxb
  · have hxb : x ∈ F₂ ∩ D := ⟨h, hx.1⟩
    rw [hF₂D] at hxb
    exact hx.2 hxb

end DifferentialGeometry.Topology.PiecewiseLinear
