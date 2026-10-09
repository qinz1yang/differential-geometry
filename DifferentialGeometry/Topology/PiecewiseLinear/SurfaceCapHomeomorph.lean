/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.AnnulusDiskUnion
import DifferentialGeometry.Topology.PiecewiseLinear.BallReplacement

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem exists_isPLHomeomorphOn_cap_replacement {L L' Δ A B G J : Set E3}
    (hL : IsPolyhedron L) (hL' : IsPolyhedron L')
    {r s : (Fin 3 → ℝ) → E3} (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Δ)
    (hrG : r '' stdSimplexBoundary 2 = G) (hAnn : IsPLAnnulusWithEnds A G J)
    (hAL : A ⊆ L) (hAΔ : A ∩ Δ = G) (hLΔ : L ∩ Δ = G)
    (hs : IsPLHomeomorphOn s (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) B)
    (hsJ : s '' stdSimplexBoundary 2 = J) (hBL : B ∩ L = J)
    (heq : L' = (L \ (A \ J)) ∪ B) :
    ∃ f : E3 → E3, IsPLHomeomorphOn f (L ∪ Δ) L' ∧ EqOn f id (L \ (A \ J)) := by
  classical
  let R := L \ (A \ J)
  obtain ⟨q, hq, hqJ, hΔJ⟩ := hAnn.exists_disk_union hr hrG hAΔ
  have hGA : G ⊆ A := hAΔ.symm.subset.trans inter_subset_left
  have hJDA : J ⊆ Δ ∪ A := hqJ ▸
    (image_mono (fun _ hx => hx.1)).trans hq.image_eq.subset
  have hJA : J ⊆ A := fun x hx => (hJDA hx).resolve_left
    (fun hxΔ => disjoint_left.mp hΔJ hxΔ hx)
  have hJL : J ⊆ L := hJA.trans hAL
  have hJR : J ⊆ R := fun x hx => ⟨hJL hx, fun hcut => hcut.2 hx⟩
  have hRinter : L' ∩ L = R := by
    rw [heq]
    refine Subset.antisymm ?_ (fun x hx => ⟨Or.inl hx, hx.1⟩)
    rintro x ⟨hxR | hxB, hxL⟩
    · exact hxR
    · exact ⟨hxL, fun hcut => hcut.2 (hBL.subset ⟨hxB, hxL⟩)⟩
  have hR : IsPolyhedron R := hRinter ▸ hL'.inter hL
  have hRD : R ∩ (Δ ∪ A) = J := by
    refine Subset.antisymm ?_ (fun x hx => ⟨hJR hx, hJDA hx⟩)
    rintro x ⟨hxR, hxΔ | hxA⟩
    · by_contra hxJ
      exact hxR.2 ⟨hGA (hLΔ.subset ⟨hxR.1, hxΔ⟩), hxJ⟩
    · by_contra hxJ
      exact hxR.2 ⟨hxA, hxJ⟩
  have hRB : R ∩ B = J := Subset.antisymm
    (fun x hx => hBL.subset ⟨hx.2, hx.1.1⟩)
    (fun x hx => ⟨hJR hx, (hBL.symm.subset hx).1⟩)
  have hUnion : R ∪ (Δ ∪ A) = L ∪ Δ := by
    refine Subset.antisymm ?_ ?_
    · rintro x (hxR | hxΔ | hxA)
      · exact Or.inl hxR.1
      · exact Or.inr hxΔ
      · exact Or.inl (hAL hxA)
    · rintro x (hxL | hxΔ)
      · by_cases hxA : x ∈ A
        · exact Or.inr (Or.inr hxA)
        · exact Or.inl ⟨hxL, fun hcut => hxA hcut.1⟩
      · exact Or.inr (Or.inl hxΔ)
  obtain ⟨f, hf, hfix⟩ := exists_isPLHomeomorphOn_replace_ball hR hq hs hqJ hsJ hRD hRB
  refine ⟨f, ?_, hfix⟩
  rw [heq, ← hUnion]
  exact hf

end DifferentialGeometry.Topology.PiecewiseLinear
