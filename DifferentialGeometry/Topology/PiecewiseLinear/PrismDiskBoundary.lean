/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PrismSphere
import DifferentialGeometry.Topology.PiecewiseLinear.SphericalDiskComplement

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem IsPLHomeomorphOn.image_stdSimplexBoundary_prism_bottom_union_side
    {D : Set E} {r : (Fin 3 → ℝ) → E} (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D)
    {a b : ℝ} (hab : a < b) {q : (Fin 3 → ℝ) → E × ℝ}
    (hq : IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3))
      (D ×ˢ {a} ∪ (r '' stdSimplexBoundary 2) ×ˢ Icc a b)) :
    q '' stdSimplexBoundary 2 = (r '' stdSimplexBoundary 2) ×ˢ {b} := by
  let J := r '' stdSimplexBoundary 2
  let S := D ×ˢ {a, b} ∪ J ×ˢ Icc a b
  let A := D ×ˢ {a} ∪ J ×ˢ Icc a b
  have hJD : J ⊆ D := (image_mono (fun _ hx => hx.1)).trans hr.image_eq.subset
  have hS : IsPLSphere 2 S := hr.isPLSphere_prism_boundary hab
  have hAS : A ⊆ S := union_subset
    (fun _ hx => Or.inl ⟨hx.1, Or.inl hx.2⟩) subset_union_right
  have hdiff : S \ A = (D \ J) ×ˢ {b} := by
    ext z
    constructor
    · rintro ⟨⟨hzD, hza | hzb⟩ | hzside, hzA⟩
      · exact (hzA (Or.inl ⟨hzD, hza⟩)).elim
      · refine ⟨⟨hzD, fun hzJ => hzA (Or.inr ⟨hzJ, ?_⟩)⟩, hzb⟩
        rw [show z.2 = b from hzb]
        exact ⟨hab.le, le_rfl⟩
      · exact (hzA (Or.inr hzside)).elim
    · rintro ⟨⟨hzD, hzJ⟩, hzb⟩
      refine ⟨Or.inl ⟨hzD, Or.inr hzb⟩, ?_⟩
      rintro (⟨_, hza⟩ | ⟨hzJ', _⟩)
      · exact hab.ne (hza.symm.trans hzb)
      · exact hzJ hzJ'
  have hcl : closure (S \ A) = D ×ˢ {b} := by
    rw [hdiff, closure_prod_eq, hr.closure_sdiff_image_stdSimplexBoundary,
      isClosed_singleton.closure_eq]
  have hmeet : A ∩ (D ×ˢ {b}) = J ×ˢ {b} := by
    ext z
    constructor
    · rintro ⟨hzbase | hzside, hz⟩
      · exact (hab.ne (hzbase.2.symm.trans hz.2)).elim
      · exact ⟨hzside.1, hz.2⟩
    · rintro ⟨hzJ, hzb⟩
      refine ⟨Or.inr ⟨hzJ, ?_⟩, hJD hzJ, hzb⟩
      rw [show z.2 = b from hzb]
      exact ⟨hab.le, le_rfl⟩
  have h := hS.inter_closure_sdiff_eq_image_stdSimplexBoundary hq hAS
  rw [hcl, hmeet] at h
  exact h.symm

end DifferentialGeometry.Topology.PiecewiseLinear
