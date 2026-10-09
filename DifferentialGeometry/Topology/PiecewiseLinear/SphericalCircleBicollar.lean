/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SphericalCircleExtension
import DifferentialGeometry.Topology.PiecewiseLinear.PrismSphere
import Mathlib.Topology.Compactness.Compact

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem IsPLSphere.exists_bicollar_of_isPLSphere_one
    {S J U : Set E} (hS : IsPLSphere 2 S) (hJ : IsPLSphere 1 J) (hJS : J ⊆ S)
    (hU : U ∈ 𝓝ˢ[S] J) :
    ∃ (W : Set E) (ρ : E × ℝ → E), IsPolyhedron W ∧ W ⊆ S ∧ W ⊆ U ∧
      W ∈ 𝓝ˢ[S] J ∧ IsPLHomeomorphOn ρ (J ×ˢ Icc (-1 : ℝ) 1) W ∧
      ∀ x ∈ J, ρ (x, 0) = x := by
  classical
  let D : Set (Fin 3 → ℝ) := Convexity.StdSimplex.coordinateSet ℝ (Fin 3)
  let C : Set (Fin 3 → ℝ) := stdSimplexBoundary 2
  let B : Set ((Fin 3 → ℝ) × ℝ) := D ×ˢ {(-2 : ℝ), 2} ∪ C ×ˢ Icc (-2 : ℝ) 2
  obtain ⟨j, hj⟩ := id hJ
  have hC : IsPLSphere 1 C := hJ.of_isPLHomeomorphOn hj.symm
  have hD : IsPLBall 2 D := isPLBall_stdSimplex 2
  have hB : IsPLSphere 2 B := by
    simpa only [image_id] using hD.isPolyhedron.isPLHomeomorphOn_id.isPLSphere_prism_boundary
      (by norm_num : (-2 : ℝ) < 2)
  have hCB : C ×ˢ {(0 : ℝ)} ⊆ B := fun _ hx =>
    Or.inr ⟨hx.1, by rw [show _ = (0 : ℝ) from hx.2]; norm_num⟩
  have hg := (hC.isPolyhedron.isPLHomeomorphOn_fst_prod_const 0).trans hj
  obtain ⟨G, hG, hGj⟩ := exists_isPLHomeomorphOn_eqOn_circle_of_isPLSphere_two hB hS
    (hC.of_isPLHomeomorphOn (hC.isPolyhedron.isPLHomeomorphOn_prod_const 0)) hCB hg hJS
  have hcore (x : Fin 3 → ℝ) (hx : x ∈ C) : G (x, 0) = j x := hGj ⟨hx, rfl⟩
  have hband : C ×ˢ Icc (-2 : ℝ) 2 ⊆ B := subset_union_right
  have hcont := hG.isPiecewiseAffineOn.continuousOn.mono hband
  have hmaps : MapsTo G (C ×ˢ Icc (-2 : ℝ) 2) S := hG.bijOn.mapsTo.mono_left hband
  have hpre := hcont.preimage_mem_nhdsSetWithin hU
  rw [show (C ×ˢ Icc (-2 : ℝ) 2) ∩ G ⁻¹' S = C ×ˢ Icc (-2 : ℝ) 2 from
    inter_eq_left.mpr hmaps] at hpre
  have hcenter : C ×ˢ {(0 : ℝ)} ⊆ (C ×ˢ Icc (-2 : ℝ) 2) ∩ G ⁻¹' J := by
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    change t = 0 at ht
    subst t
    exact ⟨⟨hx, by norm_num⟩, by change G (x, 0) ∈ J; rw [hcore x hx]; exact hj.bijOn.mapsTo hx⟩
  have hpre' : G ⁻¹' U ∈ 𝓝ˢ[C ×ˢ Icc (-2 : ℝ) 2] (C ×ˢ {(0 : ℝ)}) :=
    (nhdsSetWithin_mono_left hcenter) hpre
  obtain ⟨V, hV, hCV⟩ := generalized_tube_lemma_right hC.isPolyhedron.isCompact
    (isCompact_singleton (x := (0 : ℝ))) hpre'
  rw [nhdsSetWithin_singleton,
    nhdsWithin_eq_nhds.mpr (Icc_mem_nhds (by norm_num) (by norm_num))] at hV
  obtain ⟨r, hr, hrV⟩ := Metric.mem_nhds_iff.mp hV
  let ε := min 1 (r / 2)
  have hε : 0 < ε := lt_min zero_lt_one (half_pos hr)
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hεr : ε < r := (min_le_right _ _).trans_lt (by linarith)
  have hsmall : C ×ˢ Icc (-ε) ε ⊆ C ×ˢ Icc (-2 : ℝ) 2 := by
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    exact ⟨hx, by linarith [ht.1], by linarith [ht.2]⟩
  have hsmallU : G '' (C ×ˢ Icc (-ε) ε) ⊆ U := by
    rintro _ ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
    apply hCV ⟨hx, hrV ?_⟩
    rw [Metric.mem_ball, Real.dist_eq, sub_zero]
    exact (abs_le.mpr ht).trans_lt hεr
  have hscale : IsPLHomeomorphOn (fun t : ℝ => ε * t) (Icc (-1) 1) (Icc (-ε) ε) := by
    have hm : StrictMono (fun t : ℝ => ε * t) := fun _ _ h => mul_lt_mul_of_pos_left h hε
    have hc : Continuous (fun t : ℝ => ε * t) := continuous_const.mul continuous_id
    have himage : (fun t : ℝ => ε * t) '' Icc (-1) 1 = Icc (-ε) ε := by
      simpa only [mul_neg, mul_one] using hc.image_Icc_of_strictMono hm (a := -1) (b := 1)
    refine isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn isHPolytope_Icc.isPolyhedron
      (isPiecewiseAffineOn_of_affine_of_isHPolytope (ε • AffineMap.id ℝ ℝ) isHPolytope_Icc) ?_
    exact himage ▸ hm.injective.injOn.bijOn_image
  let W := G '' (C ×ˢ Icc (-ε) ε)
  let ρ := G ∘ Prod.map (Function.invFunOn j C) (fun t : ℝ => ε * t)
  have hGsmall := hG.restrict (hC.isPolyhedron.prod isHPolytope_Icc.isPolyhedron)
    (hsmall.trans hband)
  have hρ : IsPLHomeomorphOn ρ (J ×ˢ Icc (-1 : ℝ) 1) W := (hj.symm.prodMap hscale).trans hGsmall
  let T := G '' (B ∩ (Prod.snd ⁻¹' Ioo (-ε) ε)ᶜ)
  have hTclosed : IsClosed T :=
    (hB.isPolyhedron.isCompact.inter_right
      (isOpen_Ioo.preimage continuous_snd).isClosed_compl).image_of_continuousOn
        (hG.isPiecewiseAffineOn.continuousOn.mono inter_subset_left) |>.isClosed
  have hJT : J ⊆ Tᶜ := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hj.bijOn.surjOn hy
    rintro ⟨z, hz, hzj⟩
    have hz0 := hG.bijOn.injOn hz.1
      (hCB (show (x, (0 : ℝ)) ∈ C ×ˢ {0} from ⟨hx, rfl⟩))
      (hzj.trans (hcore x hx).symm)
    apply hz.2
    rw [hz0]
    exact ⟨neg_neg_of_pos hε, hε⟩
  have hTW : Tᶜ ∩ S ⊆ W := by
    rintro y ⟨hyT, hyS⟩
    obtain ⟨z, hz, rfl⟩ := hG.bijOn.surjOn hyS
    have hzt : z.2 ∈ Ioo (-ε) ε := by
      by_contra hzt
      exact hyT ⟨z, ⟨hz, hzt⟩, rfl⟩
    have hzC : z.1 ∈ C := by
      rcases hz with hz | hz
      · rcases hz.2 with hz2 | hz2
        · have hz2 : z.2 = -2 := hz2
          linarith [hzt.1]
        · have hz2 : z.2 = 2 := hz2
          linarith [hzt.2]
      · exact hz.1
    exact ⟨z, ⟨hzC, hzt.1.le, hzt.2.le⟩, rfl⟩
  refine ⟨W, ρ, (hC.isPolyhedron.prod isHPolytope_Icc.isPolyhedron).image_of_isPiecewiseAffineOn
    hGsmall.isPiecewiseAffineOn hGsmall.bijOn.injOn,
    (image_mono (hsmall.trans hband)).trans hG.image_eq.subset, hsmallU,
    mem_nhdsSetWithin.mpr ⟨Tᶜ, hTclosed.isOpen_compl, hJT, hTW⟩, hρ, ?_⟩
  intro x hx
  change G (Function.invFunOn j C x, ε * 0) = x
  rw [mul_zero, hcore _ (hj.bijOn.surjOn.mapsTo_invFunOn hx)]
  exact hj.bijOn.invOn_invFunOn.2 hx

end DifferentialGeometry.Topology.PiecewiseLinear
