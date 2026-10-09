/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SphericalDiskComplement

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem IsPLSphere.inter_closure_sdiff_disk_of_eventually_eq {S T D : Set E}
    (hS : IsPLSphere 2 S) {q : (Fin 3 → ℝ) → E}
    (hq : IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D) (hDS : D ⊆ S)
    (hlocal : ∀ x ∈ D, ∀ᶠ y in 𝓝 x, y ∈ T ↔ y ∈ S) :
    D ∩ closure (T \ D) = q '' stdSimplexBoundary 2 := by
  have hcl : ∀ x ∈ D, x ∈ closure (T \ D) ↔ x ∈ closure (S \ D) := by
    intro x hx
    obtain ⟨O, hOO, hO, hxO⟩ := _root_.mem_nhds_iff.mp (hlocal x hx)
    constructor
    · intro hxcl
      have hsub : O ∩ (T \ D) ⊆ S \ D := fun y hy => ⟨(hOO hy.1).mp hy.2.1, hy.2.2⟩
      exact closure_mono hsub (hO.inter_closure ⟨hxO, hxcl⟩)
    · intro hxcl
      have hsub : O ∩ (S \ D) ⊆ T \ D := fun y hy => ⟨(hOO hy.1).mpr hy.2.1, hy.2.2⟩
      exact closure_mono hsub (hO.inter_closure ⟨hxO, hxcl⟩)
  have heq : D ∩ closure (T \ D) = D ∩ closure (S \ D) := by
    ext x
    exact ⟨fun hx => ⟨hx.1, (hcl x hx.1).mp hx.2⟩,
      fun hx => ⟨hx.1, (hcl x hx.1).mpr hx.2⟩⟩
  exact heq.trans (hS.inter_closure_sdiff_eq_image_stdSimplexBoundary hq hDS)

theorem IsPLSphere.subset_or_disjoint_disk_of_eventually_eq {S T D Y : Set E}
    (hS : IsPLSphere 2 S) {q : (Fin 3 → ℝ) → E}
    (hq : IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D) (hDS : D ⊆ S)
    (hlocal : ∀ x ∈ D, ∀ᶠ y in 𝓝 x, y ∈ T ↔ y ∈ S)
    (hY : IsPreconnected Y) (hYT : Y ⊆ T) (hYJ : Disjoint Y (q '' stdSimplexBoundary 2)) :
    Y ⊆ D ∨ Disjoint D Y := by
  have hD : IsPLBall 2 D := ⟨q, hq⟩
  have hmeet := hS.inter_closure_sdiff_disk_of_eventually_eq hq hDS hlocal
  have hcover : Y ⊆ D ∪ closure (T \ D) := fun y hy => by
    by_cases hyD : y ∈ D
    · exact Or.inl hyD
    · exact Or.inr (subset_closure ⟨hYT hy, hyD⟩)
  have hdis : Y ∩ (D ∩ closure (T \ D)) = ∅ := by
    rw [hmeet]
    exact hYJ.inter_eq
  rcases isPreconnected_iff_subset_of_disjoint_closed.mp hY D (closure (T \ D))
      hD.isPolyhedron.isClosed isClosed_closure hcover hdis with h | h
  · exact Or.inl h
  · right
    apply Set.disjoint_left.mpr
    intro y hyD hyY
    exact Set.disjoint_left.mp hYJ hyY (hmeet.subset ⟨hyD, h hyY⟩)

end DifferentialGeometry.Topology.PiecewiseLinear
