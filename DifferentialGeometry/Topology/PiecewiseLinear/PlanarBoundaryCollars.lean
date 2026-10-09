/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PrismDisk
import DifferentialGeometry.Topology.PiecewiseLinear.PrismDiskBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryExtension
import Mathlib.Topology.Compactness.Compact

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem IsPLHomeomorphOn.exists_disk_boundary_collar
    {D U : Set E} {r : (Fin 3 → ℝ) → E}
    (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D)
    (hU : U ∈ 𝓝ˢ[D] (r '' stdSimplexBoundary 2)) :
    ∃ (A B : Set E) (ρ : E × ℝ → E),
      IsPolyhedron A ∧ IsPLBall 2 B ∧ A ⊆ U ∧ D = B ∪ A ∧
      IsPLHomeomorphOn ρ ((r '' stdSimplexBoundary 2) ×ˢ Icc (0 : ℝ) 1) A ∧
      (∀ x ∈ r '' stdSimplexBoundary 2, ρ (x, 1) = x) ∧
      A ∩ B = ρ '' ((r '' stdSimplexBoundary 2) ×ˢ ({0} : Set ℝ)) ∧
      A ∈ 𝓝ˢ[D] (r '' stdSimplexBoundary 2) ∧
      MapsTo ρ ((r '' stdSimplexBoundary 2) ×ˢ Ico (0 : ℝ) 1)
        (D \ (r '' stdSimplexBoundary 2)) := by
  classical
  let _ : DecidableEq (Fin 3 → ℝ) := Classical.decEq _
  let Δ : Set (Fin 3 → ℝ) := Convexity.StdSimplex.coordinateSet ℝ (Fin 3)
  let C : Set (Fin 3 → ℝ) := stdSimplexBoundary 2
  let J := r '' C
  have hΔ : IsPLBall 2 Δ := isPLBall_stdSimplex 2
  have hΔid : IsPLHomeomorphOn (id : (Fin 3 → ℝ) → (Fin 3 → ℝ)) Δ Δ :=
    hΔ.isPolyhedron.isPLHomeomorphOn_id
  have hC : IsPLSphere 1 C := by
    simpa only [simplexBoundary_stdVertices_space] using isPLSphere_simplexBoundary_std 1
  have hCΔ : C ⊆ Δ := fun _ hx => hx.1
  have hrC : IsPLHomeomorphOn r C J := hr.restrict hC.isPolyhedron hCΔ
  obtain ⟨K, hKfin, hKspace⟩ := hΔ.isPolyhedron.exists_simplicialComplex
  let _ : Finite K.faces := hKfin.to_subtype
  have hK : IsPLBall 2 K.space := hKspace.symm ▸ hΔ
  have hidK : IsPLHomeomorphOn (id : (Fin 3 → ℝ) → (Fin 3 → ℝ)) Δ K.space := by
    rw [hKspace]
    exact hΔid
  have hKbd : (boundaryComplex 2 K).space = C := by
    have h := boundaryComplex_space_of_isPLHomeomorphOn_stdSimplex K hidK
    simpa only [simplexBoundary_stdVertices_space, image_id] using h
  have hmodel {a b : ℝ} (hab : a < b) :
      IsPLBall 2 (Δ ×ˢ {a} ∪ C ×ˢ Icc a b) := by
    have h := isPLBall_prism_bottom_union_side K hK hab
    rwa [hKspace, hKbd] at h
  let N := Δ ×ˢ {(-2 : ℝ)} ∪ C ×ˢ Icc (-2 : ℝ) 0
  have hN : IsPLBall 2 N := hmodel (by norm_num)
  obtain ⟨q, hq⟩ := id hN
  have hqC : q '' C = C ×ˢ {(0 : ℝ)} := by
    simpa only [image_id] using
      hΔid.image_stdSimplexBoundary_prism_bottom_union_side (by norm_num : (-2 : ℝ) < 0)
        (by simpa only [image_id] using hq)
  have hg : IsPLHomeomorphOn (r ∘ Prod.fst) (q '' stdSimplexBoundary 2)
      (r '' stdSimplexBoundary 2) := by
    rw [show q '' stdSimplexBoundary 2 = C ×ˢ {(0 : ℝ)} from hqC]
    exact (hC.isPolyhedron.isPLHomeomorphOn_fst_prod_const 0).trans hrC
  obtain ⟨G, hG, hGr⟩ := exists_isPLHomeomorphOn_of_stdSimplexBoundary hq hr hg
  have hcenter (x : Fin 3 → ℝ) (hx : x ∈ C) : G (x, 0) = r x := by
    apply hGr
    rw [show q '' stdSimplexBoundary 2 = C ×ˢ {(0 : ℝ)} from hqC]
    exact ⟨hx, rfl⟩
  have hband : C ×ˢ Icc (-2 : ℝ) 0 ⊆ N := subset_union_right
  have hcenterN (x : Fin 3 → ℝ) (hx : x ∈ C) : (x, (0 : ℝ)) ∈ N :=
    hband ⟨hx, by norm_num⟩
  have hcont := hG.isPiecewiseAffineOn.continuousOn.mono hband
  have hmaps : MapsTo G (C ×ˢ Icc (-2 : ℝ) 0) D := hG.bijOn.mapsTo.mono_left hband
  have hpre := hcont.preimage_mem_nhdsSetWithin hU
  rw [show (C ×ˢ Icc (-2 : ℝ) 0) ∩ G ⁻¹' D = C ×ˢ Icc (-2 : ℝ) 0 from
    inter_eq_left.mpr hmaps] at hpre
  have hcore : C ×ˢ {(0 : ℝ)} ⊆ (C ×ˢ Icc (-2 : ℝ) 0) ∩ G ⁻¹' J := by
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    have ht0 : t = 0 := ht
    subst t
    exact ⟨⟨hx, by norm_num⟩, by rw [mem_preimage, hcenter x hx]; exact ⟨x, hx, rfl⟩⟩
  have hpre' : G ⁻¹' U ∈ 𝓝ˢ[C ×ˢ Icc (-2 : ℝ) 0] (C ×ˢ {(0 : ℝ)}) :=
    (nhdsSetWithin_mono_left hcore) hpre
  obtain ⟨V, hV, hCV⟩ := generalized_tube_lemma_right hC.isPolyhedron.isCompact
    (isCompact_singleton (x := (0 : ℝ))) hpre'
  rw [nhdsSetWithin_singleton] at hV
  obtain ⟨O, hO, h0O, hOV⟩ := mem_nhdsWithin.mp hV
  obtain ⟨s, hs, hsO⟩ := Metric.mem_nhds_iff.mp (hO.mem_nhds h0O)
  let ε := min 1 (s / 2)
  have hε : 0 < ε := lt_min zero_lt_one (half_pos hs)
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hεs : ε < s := (min_le_right _ _).trans_lt (by linarith)
  have hsmall : C ×ˢ Icc (-ε) 0 ⊆ N := by
    rintro z ⟨hzC, hzt⟩
    exact hband ⟨hzC, by linarith [hzt.1], hzt.2⟩
  have hsmallU : G '' (C ×ˢ Icc (-ε) 0) ⊆ U := by
    rintro _ ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
    apply hCV ⟨hx, hOV ⟨hsO ?_, ?_⟩⟩
    · rw [Metric.mem_ball, Real.dist_eq, sub_zero]
      apply (abs_le.mpr ⟨ht.1, ht.2.trans hε.le⟩).trans_lt hεs
    · exact ⟨by linarith [ht.1], ht.2⟩
  have hscale : IsPLHomeomorphOn (fun t : ℝ => ε * t - ε) (Icc (0 : ℝ) 1) (Icc (-ε) 0) := by
    refine isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn isHPolytope_Icc.isPolyhedron
      (isPiecewiseAffineOn_of_affine_of_isHPolytope
        (ε • AffineMap.id ℝ ℝ + AffineMap.const ℝ ℝ (-ε)) isHPolytope_Icc) ⟨?_, ?_, ?_⟩
    · intro t ht
      change -ε ≤ ε * t - ε ∧ ε * t - ε ≤ 0
      constructor
      · nlinarith [mul_nonneg hε.le ht.1]
      · nlinarith [mul_le_mul_of_nonneg_left ht.2 hε.le]
    · intro t _ u _ htu
      exact mul_left_cancel₀ hε.ne' (by linarith)
    · intro t ht
      have heq : ε * ((t + ε) / ε) = t + ε := by field_simp
      refine ⟨(t + ε) / ε, ⟨?_, ?_⟩, by linarith⟩
      · exact div_nonneg (by linarith [ht.1]) hε.le
      · apply (div_le_one hε).mpr
        linarith [ht.2]
  let M := Δ ×ˢ {(-2 : ℝ)} ∪ C ×ˢ Icc (-2 : ℝ) (-ε)
  have hM : IsPLBall 2 M := hmodel (by linarith)
  have hMN : M ⊆ N := by
    refine union_subset subset_union_left ?_
    rintro z ⟨hzC, hzt⟩
    exact hband ⟨hzC, hzt.1, hzt.2.trans (neg_nonpos.mpr hε.le)⟩
  let A := G '' (C ×ˢ Icc (-ε) 0)
  let B := G '' M
  let ρ := G ∘ Prod.map (Function.invFunOn r C) (fun t : ℝ => ε * t - ε)
  have hGsmall := hG.restrict (hC.isPolyhedron.prod isHPolytope_Icc.isPolyhedron) hsmall
  have hρ : IsPLHomeomorphOn ρ (J ×ˢ Icc (0 : ℝ) 1) A :=
    (hrC.symm.prodMap hscale).trans hGsmall
  have hA : IsPolyhedron A :=
    (hC.isPolyhedron.prod isHPolytope_Icc.isPolyhedron).image_of_isPiecewiseAffineOn
      hGsmall.isPiecewiseAffineOn hGsmall.bijOn.injOn
  have hB : IsPLBall 2 B := hM.of_isPLHomeomorphOn (hG.restrict hM.isPolyhedron hMN)
  have hcover0 : M ∪ (C ×ˢ Icc (-ε) 0) = N := by
    apply Subset.antisymm (union_subset hMN hsmall)
    rintro z (hzbase | ⟨hzC, hzt⟩)
    · exact Or.inl (Or.inl hzbase)
    · by_cases ht : z.2 ≤ -ε
      · exact Or.inl (Or.inr ⟨hzC, hzt.1, ht⟩)
      · exact Or.inr ⟨hzC, (lt_of_not_ge ht).le, hzt.2⟩
  have hcover : D = B ∪ A := by
    change D = G '' M ∪ G '' (C ×ˢ Icc (-ε) 0)
    rw [← image_union, hcover0, hG.image_eq]
  have hmeet0 : (C ×ˢ Icc (-ε) 0) ∩ M = C ×ˢ {(-ε)} := by
    ext z
    constructor
    · rintro ⟨hz, hbase | hside⟩
      · have ht : z.2 = -2 := hbase.2
        exfalso
        linarith [hz.2.1]
      · exact ⟨hz.1, le_antisymm hside.2.2 hz.2.1⟩
    · rintro ⟨hzC, hzt⟩
      have ht : z.2 = -ε := hzt
      refine ⟨⟨hzC, ?_, ?_⟩, Or.inr ⟨hzC, ?_, ?_⟩⟩ <;> linarith
  have hseam : ρ '' (J ×ˢ ({0} : Set ℝ)) = G '' (C ×ˢ {(-ε)}) := by
    apply Subset.antisymm
    · rintro _ ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
      have ht0 : t = 0 := ht
      subst t
      refine ⟨(Function.invFunOn r C x, -ε), ⟨hrC.bijOn.surjOn.mapsTo_invFunOn hx, rfl⟩, ?_⟩
      simp only [ρ, Function.comp_apply, Prod.map_apply, mul_zero, zero_sub]
    · rintro _ ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
      have htε : t = -ε := ht
      subst t
      refine ⟨(r x, 0), ⟨hrC.bijOn.mapsTo hx, rfl⟩, ?_⟩
      simp only [ρ, Function.comp_apply, Prod.map_apply, mul_zero, zero_sub,
        hrC.bijOn.invOn_invFunOn.1 hx]
  have hmeet : A ∩ B = ρ '' (J ×ˢ ({0} : Set ℝ)) := by
    rw [hseam]
    change G '' (C ×ˢ Icc (-ε) 0) ∩ G '' M = _
    rw [← hG.bijOn.injOn.image_inter hsmall hMN, hmeet0]
  have hfix (x : E) (hx : x ∈ J) : ρ (x, 1) = x := by
    change G (Function.invFunOn r C x, ε * 1 - ε) = x
    rw [mul_one, sub_self, hcenter _ (hrC.bijOn.surjOn.mapsTo_invFunOn hx)]
    exact hrC.bijOn.invOn_invFunOn.2 hx
  have hJB : J ⊆ Bᶜ := by
    intro x hx
    rintro ⟨z, hz, hzx⟩
    obtain ⟨w, hw, rfl⟩ := hrC.bijOn.surjOn hx
    have hzw : z = (w, 0) := hG.bijOn.injOn (hMN hz) (hcenterN w hw)
      (hzx.trans (hcenter w hw).symm)
    rw [hzw] at hz
    rcases hz with hz | hz
    · have ht : (0 : ℝ) = -2 := hz.2
      norm_num at ht
    · exact (not_le_of_gt hε) (neg_nonneg.mp hz.2.2)
  have hnhds : A ∈ 𝓝ˢ[D] J := by
    apply mem_nhdsSetWithin.mpr
    refine ⟨Bᶜ, hB.isPolyhedron.isClosed.isOpen_compl, hJB, ?_⟩
    rintro x ⟨hxB, hxD⟩
    exact (hcover ▸ hxD).resolve_left hxB
  have hpositive : MapsTo ρ (J ×ˢ Ico (0 : ℝ) 1) (D \ J) := by
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    have hxt : (x, t) ∈ J ×ˢ Icc (0 : ℝ) 1 := ⟨hx, ht.1, ht.2.le⟩
    refine ⟨hcover.symm ▸ Or.inr (hρ.bijOn.mapsTo hxt), ?_⟩
    intro hy
    have hxy : (x, t) = (ρ (x, t), 1) := hρ.bijOn.injOn hxt ⟨hy, by norm_num⟩
      (hfix _ hy).symm
    exact ht.2.ne (congrArg Prod.snd hxy)
  exact ⟨A, B, ρ, hA, hB, hsmallU, hcover, hρ, hfix, hmeet, hnhds, hpositive⟩

end DifferentialGeometry.Topology.PiecewiseLinear
