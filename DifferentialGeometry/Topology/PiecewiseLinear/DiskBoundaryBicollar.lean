/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.DiskBoundaryCollar
import DifferentialGeometry.Topology.PiecewiseLinear.BallReplacement
import DifferentialGeometry.Topology.PiecewiseLinear.PLPath

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_disk_pair_of_boundary_bicollar
    {D J W : Set E} {r : (Fin 3 → ℝ) → E} (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D)
    (hboundary : r '' stdSimplexBoundary 2 = J) {ρ : E × ℝ → E}
    (hρ : IsPLHomeomorphOn ρ (J ×ˢ Icc (-1 : ℝ) 1) W)
    (hfix : ∀ x ∈ J, ρ (x, 0) = x) (hmeet : W ∩ D = J) :
    ∃ q₁ q₂ : (Fin 3 → ℝ) → E,
      IsPLHomeomorphOn q₁ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (D ∪ ρ '' (J ×ˢ Icc (0 : ℝ) 1)) ∧
      IsPLHomeomorphOn q₂ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (D ∪ ρ '' (J ×ˢ Icc (-1 : ℝ) 0)) ∧
      (D ∪ ρ '' (J ×ˢ Icc (0 : ℝ) 1)) ∩ (D ∪ ρ '' (J ×ˢ Icc (-1 : ℝ) 0)) = D ∧
      (D ∪ ρ '' (J ×ˢ Icc (0 : ℝ) 1)) ∪ (D ∪ ρ '' (J ×ˢ Icc (-1 : ℝ) 0)) = D ∪ W ∧
      q₁ '' stdSimplexBoundary 2 = ρ '' (J ×ˢ {(1 : ℝ)}) ∧
      q₂ '' stdSimplexBoundary 2 = ρ '' (J ×ˢ {(-1 : ℝ)}) ∧
      Disjoint D (q₁ '' stdSimplexBoundary 2) ∧ Disjoint D (q₂ '' stdSimplexBoundary 2) := by
  have hJ : IsPolyhedron J := hboundary ▸ hr.isPLSphere_image_stdSimplexBoundary.isPolyhedron
  have hJD : J ⊆ D := hmeet.symm.subset.trans inter_subset_right
  let P := ρ '' (J ×ˢ Icc (0 : ℝ) 1)
  let N := ρ '' (J ×ˢ Icc (-1 : ℝ) 0)
  have hpos : J ×ˢ Icc (0 : ℝ) 1 ⊆ J ×ˢ Icc (-1 : ℝ) 1 :=
    prod_mono Subset.rfl (Icc_subset_Icc (by norm_num) le_rfl)
  have hneg : J ×ˢ Icc (-1 : ℝ) 0 ⊆ J ×ˢ Icc (-1 : ℝ) 1 :=
    prod_mono Subset.rfl (Icc_subset_Icc le_rfl (by norm_num))
  have hP := hρ.restrict (hJ.prod isHPolytope_Icc.isPolyhedron) hpos
  have hN := hρ.restrict (hJ.prod isHPolytope_Icc.isPolyhedron) hneg
  have hPW : P ⊆ W := (image_mono hpos).trans hρ.image_eq.subset
  have hNW : N ⊆ W := (image_mono hneg).trans hρ.image_eq.subset
  have hJP : J ⊆ P := fun x hx => ⟨(x, 0), ⟨hx, le_rfl, zero_le_one⟩, hfix x hx⟩
  have hJN : J ⊆ N := fun x hx => ⟨(x, 0), ⟨hx, by norm_num, le_rfl⟩, hfix x hx⟩
  have hmeet' (V : Set E) (hVW : V ⊆ W) (hJV : J ⊆ V) : V ∩ D = J :=
    Subset.antisymm (fun _ hx => hmeet.subset ⟨hVW hx.1, hx.2⟩)
      (fun _ hx => ⟨hJV hx, hJD hx⟩)
  obtain ⟨q₁, hq₁, hq₁B, hq₁D⟩ := hr.exists_isPLHomeomorphOn_union_collar zero_lt_one
    (by rw [hboundary]; exact hP) (by rw [hboundary]; exact hfix)
    ((hmeet' P hPW hJP).trans hboundary.symm)
  rw [hboundary] at hq₁B
  have hreflect : IsPLHomeomorphOn (fun t : ℝ => -t) (Icc (0 : ℝ) 1) (Icc (-1 : ℝ) 0) := by
    apply isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn isHPolytope_Icc.isPolyhedron
      (isPiecewiseAffineOn_of_affine_of_isHPolytope
        (-LinearMap.id : ℝ →ₗ[ℝ] ℝ).toAffineMap isHPolytope_Icc)
    refine ⟨?_, fun _ _ _ _ h => neg_injective h, ?_⟩
    · intro t ht
      change -1 ≤ -t ∧ -t ≤ 0
      exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
    · intro t ht
      exact ⟨-t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, neg_neg t⟩
  let σ := ρ ∘ Prod.map (id : E → E) (fun t : ℝ => -t)
  have hσ : IsPLHomeomorphOn σ (J ×ˢ Icc (0 : ℝ) 1) N :=
    (hJ.isPLHomeomorphOn_id.prodMap hreflect).trans hN
  have hσ0 : ∀ x ∈ J, σ (x, 0) = x := by
    intro x hx
    simpa [σ] using hfix x hx
  obtain ⟨q₂, hq₂, hq₂B, hq₂D⟩ := hr.exists_isPLHomeomorphOn_union_collar zero_lt_one
    (by rw [hboundary]; exact hσ) (by rw [hboundary]; exact hσ0)
    ((hmeet' N hNW hJN).trans hboundary.symm)
  rw [hboundary] at hq₂B
  have hσtop : σ '' (J ×ˢ {(1 : ℝ)}) = ρ '' (J ×ˢ {(-1 : ℝ)}) := by
    apply Subset.antisymm
    · rintro y ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
      change t = 1 at ht
      subst t
      exact ⟨(x, -1), ⟨hx, rfl⟩, rfl⟩
    · rintro y ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
      change t = -1 at ht
      subst t
      exact ⟨(x, 1), ⟨hx, rfl⟩, rfl⟩
  have hPN : P ∩ N = J := by
    apply Subset.antisymm
    · rintro y ⟨⟨z, hz, hzy⟩, ⟨w, hw, hwy⟩⟩
      have hzw : z = w := hρ.bijOn.injOn (hpos hz) (hneg hw) (hzy.trans hwy.symm)
      have hz0 : z.2 = 0 := le_antisymm (hzw.symm ▸ hw.2.2) hz.2.1
      have heq : ρ z = z.1 := by
        rw [show z = (z.1, 0) from Prod.ext rfl hz0]
        exact hfix z.1 hz.1
      exact (heq.symm.trans hzy) ▸ hz.1
    · exact fun _ hx => ⟨hJP hx, hJN hx⟩
  have hdomains : (J ×ˢ Icc (0 : ℝ) 1) ∪ (J ×ˢ Icc (-1 : ℝ) 0) =
      J ×ˢ Icc (-1 : ℝ) 1 := by
    apply Subset.antisymm (union_subset hpos hneg)
    intro z hz
    by_cases ht : 0 ≤ z.2
    · exact Or.inl ⟨hz.1, ht, hz.2.2⟩
    · exact Or.inr ⟨hz.1, hz.2.1, (lt_of_not_ge ht).le⟩
  have hPNW : P ∪ N = W := by
    change ρ '' (J ×ˢ Icc (0 : ℝ) 1) ∪ ρ '' (J ×ˢ Icc (-1 : ℝ) 0) = W
    rw [← image_union, hdomains, hρ.image_eq]
  refine ⟨q₁, q₂, hq₁, hq₂, ?_, ?_, hq₁B, hq₂B.trans hσtop, hq₁D, hq₂D⟩
  · change (D ∪ P) ∩ (D ∪ N) = D
    rw [← union_inter_distrib_left, hPN, union_eq_left.mpr hJD]
  · change (D ∪ P) ∪ (D ∪ N) = D ∪ W
    rw [union_union_union_comm, union_self, hPNW]

end DifferentialGeometry.Topology.PiecewiseLinear
