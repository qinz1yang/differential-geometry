/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.RadialIndependence
import DifferentialGeometry.Topology.PiecewiseLinear.ConeHalfSpace
import DifferentialGeometry.Topology.PiecewiseLinear.PLPath

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
theorem IsConeBase.le_one_of_mem_coneComplex {p x : E}
    {K : Geometry.SimplicialComplex ℝ E} (hK : IsConeBase p K)
    (hx : x ∈ K.space) {t : ℝ} (ht : 0 < t)
    (hy : p + t • (x - p) ∈ (coneComplex hK).space) : t ≤ 1 := by
  classical
  have hxp : x - p ≠ 0 := sub_ne_zero.mpr (fun h => hK.notMem_space (h ▸ hx))
  rcases (mem_coneComplex_space_iff hK).mp hy with hy | ⟨z, hz, s, hs, hs1, heq⟩
  · have hzero : t • (x - p) = 0 := add_left_cancel (hy.trans (add_zero p).symm)
    exact ((smul_eq_zero.mp hzero).elim ht.ne' hxp).elim
  · have hxz := hK.radial.eq_of_add_smul_eq hx hz ht hs heq
    rw [← hxz] at heq
    have hts : t = s := smul_left_injective ℝ hxp (add_left_cancel heq)
    exact hts.symm ▸ hs1

open Classical in
theorem IsConeBase.isRadiallyInjective_inter_slab_union_fiber {p : E}
    {K : Geometry.SimplicialComplex ℝ E} (hK : IsConeBase p K)
    (ℓ : E →ᵃ[ℝ] ℝ) {b : ℝ} (hpb : ℓ p < b) :
    IsRadiallyInjective p ((K.space ∩ ℓ ⁻¹' Icc (ℓ p) b) ∪
      ((coneComplex hK).space ∩ {x | ℓ x = b})) := by
  classical
  let B := (K.space ∩ ℓ ⁻¹' Icc (ℓ p) b) ∪ ((coneComplex hK).space ∩ {x | ℓ x = b})
  have hcone : B ⊆ (coneComplex hK).space := by
    rintro x (hx | hx)
    · exact space_subset_coneComplex_space hK hx.1
    · exact hx.1
  have hbound : ∀ x ∈ B, ℓ x ≤ b := by
    rintro x (hx | hx)
    · exact hx.2.2
    · exact hx.2.le
  have hpair : ∀ x ∈ B, ∀ y ∈ B, ∀ t : ℝ, 0 < t →
      y = p + t • (x - p) → x ∈ K.space → ℓ y = b → y = x := by
    intro x hx y hy t ht heq hxK hyb
    have ht1 := hK.le_one_of_mem_coneComplex hxK ht (heq ▸ hcone hy)
    have hheight := affineMap_apply_add_smul_sub ℓ p x t
    rw [← heq, hyb] at hheight
    have htone : t = 1 := by nlinarith [hbound x hx]
    simpa only [htone, one_smul, add_sub_cancel] using heq
  intro x hx y hy t ht heq
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact hK.radial x hx.1 y hy.1 t ht heq
  · exact hpair x (Or.inl hx) y (Or.inr hy) t ht heq hx.1 hy.2
  · have hinv : x = p + t⁻¹ • (y - p) := by
      rw [heq, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ ht.ne', one_smul, add_sub_cancel]
    exact (hpair y (Or.inl hy) x (Or.inr hx) t⁻¹ (inv_pos.mpr ht) hinv hy.1 hx.2).symm
  · have hheight := affineMap_apply_add_smul_sub ℓ p x t
    rw [← heq, hx.2, hy.2] at hheight
    have htone : t = 1 := by nlinarith
    simpa only [htone, one_smul, add_sub_cancel] using heq

open Classical in
theorem coneComplex_space_inter_slab {p : E}
    {K L : Geometry.SimplicialComplex ℝ E} (hK : IsConeBase p K) (hL : IsConeBase p L)
    (ℓ : E →ᵃ[ℝ] ℝ) {b : ℝ} (hpb : ℓ p < b)
    (hspace : L.space = (K.space ∩ ℓ ⁻¹' Icc (ℓ p) b) ∪
      ((coneComplex hK).space ∩ {x | ℓ x = b})) :
    (coneComplex hL).space = (coneComplex hK).space ∩ ℓ ⁻¹' Icc (ℓ p) b := by
  classical
  have hbase : L.space ⊆ (coneComplex hK).space ∩ ℓ ⁻¹' Icc (ℓ p) b := by
    intro x hx
    rcases hspace.subset hx with hx | hx
    · exact ⟨space_subset_coneComplex_space hK hx.1, hx.2⟩
    · exact ⟨hx.1, by change ℓ p ≤ ℓ x ∧ ℓ x ≤ b; rw [hx.2]; exact ⟨hpb.le, le_rfl⟩⟩
  have hsegment : ∀ z ∈ (coneComplex hK).space, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      p + t • (z - p) ∈ (coneComplex hK).space := by
    intro z hz t ht ht1
    rcases (mem_coneComplex_space_iff hK).mp hz with rfl | ⟨w, hw, s, hs, hs1, rfl⟩
    · simpa only [sub_self, smul_zero, add_zero] using apex_mem_coneComplex_space hK
    · rcases ht.eq_or_lt with rfl | ht
      · simpa only [zero_smul, add_zero] using apex_mem_coneComplex_space hK
      · rw [add_sub_cancel_left, smul_smul]
        exact (mem_coneComplex_space_iff hK).mpr (Or.inr ⟨w, hw, t * s, mul_pos ht hs,
          (mul_le_mul_of_nonneg_right ht1 hs.le).trans (by simpa using hs1), rfl⟩)
  apply Subset.antisymm
  · intro x hx
    rcases (mem_coneComplex_space_iff hL).mp hx with rfl | ⟨z, hz, t, ht, ht1, rfl⟩
    · exact ⟨apex_mem_coneComplex_space hK, le_rfl, hpb.le⟩
    · have hz' := hbase hz
      refine ⟨hsegment z hz'.1 t ht.le ht1, ?_⟩
      change ℓ p ≤ ℓ (p + t • (z - p)) ∧ ℓ (p + t • (z - p)) ≤ b
      rw [affineMap_apply_add_smul_sub]
      constructor <;> nlinarith [hz'.2.1, hz'.2.2]
  · rintro x ⟨hx, hxab⟩
    rcases (mem_coneComplex_space_iff hK).mp hx with rfl | ⟨z, hz, t, ht, ht1, rfl⟩
    · exact apex_mem_coneComplex_space hL
    · have hxheight : ℓ p ≤ ℓ p + t * (ℓ z - ℓ p) ∧ ℓ p + t * (ℓ z - ℓ p) ≤ b := by
        simpa only [mem_preimage, mem_Icc, affineMap_apply_add_smul_sub] using hxab
      have hpz : ℓ p ≤ ℓ z := by nlinarith [hxheight.1]
      by_cases hzb : ℓ z ≤ b
      · exact (mem_coneComplex_space_iff hL).mpr
          (Or.inr ⟨z, hspace.symm.subset (Or.inl ⟨hz, hpz, hzb⟩), t, ht, ht1, rfl⟩)
      · have hzb' : b < ℓ z := lt_of_not_ge hzb
        have hden : 0 < ℓ z - ℓ p := sub_pos.mpr (hpb.trans hzb')
        let u := (b - ℓ p) / (ℓ z - ℓ p)
        have hu : 0 < u := div_pos (sub_pos.mpr hpb) hden
        have hu1 : u ≤ 1 := (div_le_one hden).mpr (by linarith)
        have humul : u * (ℓ z - ℓ p) = b - ℓ p := div_mul_cancel₀ _ hden.ne'
        have htu : t ≤ u := by nlinarith [hxheight.2]
        let y := p + u • (z - p)
        have hyK : y ∈ (coneComplex hK).space :=
          (mem_coneComplex_space_iff hK).mpr (Or.inr ⟨z, hz, u, hu, hu1, rfl⟩)
        have hyb : ℓ y = b := by
          rw [show y = p + u • (z - p) from rfl, affineMap_apply_add_smul_sub, humul]
          ring
        refine (mem_coneComplex_space_iff hL).mpr
          (Or.inr ⟨y, hspace.symm.subset (Or.inr ⟨hyK, hyb⟩), t / u, div_pos ht hu,
            (div_le_one hu).mpr htu, ?_⟩)
        rw [show y = p + u • (z - p) from rfl, add_sub_cancel_left, smul_smul,
          div_mul_cancel₀ _ hu.ne']

open Classical in
theorem IsConeBase.exists_coneComplex_inter_slab [FiniteDimensional ℝ E] {p : E}
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces] (hK : IsConeBase p K)
    (ℓ : E →ᵃ[ℝ] ℝ) {b : ℝ} (hpb : ℓ p < b) :
    ∃ (L : Geometry.SimplicialComplex ℝ E) (hL : IsConeBase p L), L.faces.Finite ∧
      L.space = (K.space ∩ ℓ ⁻¹' Icc (ℓ p) b) ∪ ((coneComplex hK).space ∩ {x | ℓ x = b}) ∧
      (coneComplex hL).space = (coneComplex hK).space ∩ ℓ ⁻¹' Icc (ℓ p) b := by
  classical
  let _ : Finite (coneComplex hK).faces := (coneComplex_faces_finite hK (Set.toFinite
      K.faces)).to_subtype
  have hfiber : IsPolyhedron ((coneComplex hK).space ∩ {x | ℓ x = b}) := by
    have h : IsPolyhedron ((coneComplex hK).space ∩ ℓ ⁻¹' Icc b b) :=
      (isPolyhedron_space (coneComplex hK)).inter_preimage isHPolytope_Icc.isPolyhedron ℓ
    rwa [show ℓ ⁻¹' Icc b b = {x | ℓ x = b} by ext x; simp [Icc_self, eq_comm]] at h
  have hpoly : IsPolyhedron ((K.space ∩ ℓ ⁻¹' Icc (ℓ p) b) ∪
      ((coneComplex hK).space ∩ {x | ℓ x = b})) :=
    ((isPolyhedron_space K).inter_preimage isHPolytope_Icc.isPolyhedron ℓ).union hfiber
  obtain ⟨L, hLfin, hspace⟩ := hpoly.exists_simplicialComplex
  have hpL : p ∉ L.space := by
    intro hp
    rcases hspace.subset hp with hp | hp
    · exact hK.notMem_space hp.1
    · exact hpb.ne hp.2
  have hL : IsConeBase p L := isConeBase_of_isRadiallyInjective L hpL (by
    rw [hspace]
    exact hK.isRadiallyInjective_inter_slab_union_fiber ℓ hpb)
  exact ⟨L, hL, hLfin, hspace, coneComplex_space_inter_slab hK hL ℓ hpb hspace⟩

end DifferentialGeometry.Topology.PiecewiseLinear
