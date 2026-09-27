/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.AnnularChainRimCoordinates
import Mathlib.Analysis.Convex.Between

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

private theorem endpoint_mem_of_mem_segments {a b c z : E3}
    (hzab : z ∈ segment ℝ a b) (hzbc : z ∈ segment ℝ b c) (hzb : z ≠ b) :
    a ∈ segment ℝ b c ∨ c ∈ segment ℝ a b := by
  have h₁ : Wbtw ℝ b z a := mem_segment_iff_wbtw.mp (segment_symm ℝ a b ▸ hzab)
  have h₂ : Wbtw ℝ b z c := mem_segment_iff_wbtw.mp hzbc
  have hr := h₁.sameRay_vsub_left.symm.trans h₂.sameRay_vsub_left
    (fun h => False.elim (hzb (vsub_eq_zero_iff_eq.mp h)))
  rcases wbtw_total_of_sameRay_vsub_left hr with h | h
  · exact Or.inl (mem_segment_iff_wbtw.mpr h)
  · exact Or.inr (segment_symm ℝ b a ▸ mem_segment_iff_wbtw.mpr h)

private theorem revolutionOf_inter (X Y : Set E3) :
    revolutionOf X ∩ revolutionOf Y = revolutionOf (X ∩ Y) := by
  ext p
  constructor
  · rintro ⟨⟨q, hqX, hq2, hq0, hq1, hqsq⟩, ⟨q', hq'Y, hq'2, hq'0, hq'1, hq'sq⟩⟩
    have h0 : q 0 = q' 0 := (sq_eq_sq₀ hq0 hq'0).mp (hqsq.trans hq'sq.symm)
    have hqq' : q = q' := by
      refine PiLp.ext fun i => ?_
      fin_cases i
      · exact h0
      · exact hq1.trans hq'1.symm
      · exact hq2.trans hq'2.symm
    exact ⟨q, ⟨hqX, hqq' ▸ hq'Y⟩, hq2, hq0, hq1, hqsq⟩
  · rintro ⟨q, ⟨hqX, hqY⟩, hrest⟩
    exact ⟨⟨q, hqX, hrest⟩, ⟨q, hqY, hrest⟩⟩

variable {φ : E3 → E3} {Pt : ℤ → E3}
  {Dp Dpint J A S T S'' T'' : ℤ → Set E3}
  {Dimg Dbdimg W I : Set E3} {P' : E3}

private theorem tower_segment_subset
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P') (i : ℤ) :
    segment ℝ (Pt i) (Pt (i + 1)) ⊆ Dp i := by
  simpa using ((htw.config i).base.chain.segmentSubset (0 : Fin 3)).trans
    ((htw.config i).base.chain.interiorSubset (0 : Fin 3))

private theorem tower_segments_inter
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P') (i : ℤ) :
    segment ℝ (Pt i) (Pt (i + 1)) ∩ segment ℝ (Pt (i + 1)) (Pt (i + 2)) =
      {Pt (i + 1)} := by
  have hprev : Pt i ∈ Dp (i - 1) := by
    have hh := tower_segment_subset htw (i - 1) (right_mem_segment ℝ _ _)
    simpa using hh
  have hnext : Pt (i + 2) ∈ Dp (i + 2) :=
    tower_segment_subset htw (i + 2) (left_mem_segment ℝ _ _)
  have haprev : Dp (i - 1) ∩ Dp (i + 1) = ∅ := by
    simpa [show i - 1 + 2 = i + 1 by omega] using (htw.config (i - 1)).base.chain.apart
  have hanext : Dp i ∩ Dp (i + 2) = ∅ := by
    simpa using (htw.config i).base.chain.apart
  ext z
  constructor
  · rintro ⟨hz₀, hz₁⟩
    by_contra hz
    have hzne : z ≠ Pt (i + 1) := hz
    rcases endpoint_mem_of_mem_segments hz₀ hz₁ hzne with hp | hp
    · have hh : Pt i ∈ Dp (i - 1) ∩ Dp (i + 1) :=
        ⟨hprev, tower_segment_subset htw (i + 1) (by simpa [add_assoc] using hp)⟩
      rw [haprev] at hh
      exact hh
    · have hh : Pt (i + 2) ∈ Dp i ∩ Dp (i + 2) :=
        ⟨tower_segment_subset htw i hp, hnext⟩
      rw [hanext] at hh
      exact hh
  · rintro rfl
    exact ⟨right_mem_segment ℝ _ _, left_mem_segment ℝ _ _⟩

private theorem tower_annulus_eq
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P') (i : ℤ) :
    A i = revolutionOf (segment ℝ (Pt i) (Pt (i + 1))) := by
  simpa using (htw.config i).base.annulusEq (0 : Fin 3)

private theorem tower_annulus_inter
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P') (i : ℤ) :
    A i ∩ A (i + 1) = J (i + 1) := by
  rw [tower_annulus_eq htw i, tower_annulus_eq htw (i + 1)]
  rw [show i + 1 + 1 = i + 2 by omega, revolutionOf_inter, tower_segments_inter htw i]
  simpa using ((htw.config i).base.circleEq (1 : Fin 4)).symm

theorem IsCanonicalTower.annulus_image_subset
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P') (i : ℤ) :
    φ '' A i ⊆ φ '' S i := by
  apply image_mono
  simpa using ((htw.config i).base.annulusSubset (0 : Fin 3)).trans interior_subset

theorem IsCanonicalTower.annulus_image_disjoint
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P')
    {i j : ℤ} (hij : 2 ≤ |i - j|) : Disjoint (φ '' A i) (φ '' A j) :=
  (htw.apart i j hij).mono (htw.annulus_image_subset i) (htw.annulus_image_subset j)

theorem IsCanonicalTower.annulus_image_inter_next
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P') (i : ℤ) :
    (φ '' A i) ∩ (φ '' A (i + 1)) = φ '' J (i + 1) := by
  rw [← tower_annulus_inter htw i]
  symm
  apply Set.InjOn.image_inter (u := A i ∪ A (i + 1)) ?_ subset_union_left subset_union_right
  have hA₀ : A i ⊆ S i := by
    simpa using ((htw.config i).base.annulusSubset (0 : Fin 3)).trans interior_subset
  have hA₁ : A (i + 1) ⊆ S (i + 1) := by
    simpa using ((htw.config (i + 1)).base.annulusSubset (0 : Fin 3)).trans interior_subset
  have hsub : A i ∪ A (i + 1) ⊆ ⋃ j : Fin 3, S (i + ((j : ℕ) : ℤ)) := by
    rintro x (hx | hx)
    · exact mem_iUnion.mpr ⟨0, by simpa using hA₀ hx⟩
    · exact mem_iUnion.mpr ⟨1, by simpa using hA₁ hx⟩
  intro x hx y hy hxy
  exact congrArg Subtype.val ((htw.config i).isEmbedding.injective
    (a₁ := ⟨x, hsub hx⟩) (a₂ := ⟨y, hsub hy⟩) hxy)

end DifferentialGeometry.Topology.PiecewiseLinear
