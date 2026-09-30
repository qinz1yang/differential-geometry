/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodRayEmbedding
import DifferentialGeometry.Topology.PiecewiseLinear.FreeFaceArc
import DifferentialGeometry.Topology.PiecewiseLinear.PolyhedralTubeNeighborhoodExists

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem exists_continuousOn_rayCoordinates {Y M : Set E3} (hY : IsCompact Y)
    {Φ : E3 → ℝ → E3} (hΦc : ContinuousOn (fun q : E3 × ℝ => Φ q.1 q.2) (Y ×ˢ Icc 0 1))
    (hM : ∀ b ∈ Y, ∀ t ∈ Icc (0 : ℝ) 1, (Φ b t ∈ M ↔ t < 1))
    (hinj : InjOn (fun q : E3 × ℝ => Φ q.1 q.2) (Y ×ˢ Ico 0 1))
    (hsurj : ∀ z ∈ M, ∃ b ∈ Y, ∃ t ∈ Ico (0 : ℝ) 1, Φ b t = z) :
    ∃ (β : E3 → E3) (τ : E3 → ℝ), ContinuousOn β M ∧ ContinuousOn τ M ∧
      ∀ z ∈ M, β z ∈ Y ∧ τ z ∈ Ico (0 : ℝ) 1 ∧ Φ (β z) (τ z) = z := by
  classical
  have hDc : IsCompact (Y ×ˢ Icc (0 : ℝ) 1) := hY.prod isCompact_Icc
  let _ : CompactSpace ↥(Y ×ˢ Icc (0 : ℝ) 1) := isCompact_iff_compactSpace.mp hDc
  let F : ↥(Y ×ˢ Icc (0 : ℝ) 1) → E3 := fun q => Φ q.1.1 q.1.2
  have hF : Continuous F := hΦc.domRestrict
  let F' := M.restrictPreimage F
  have hbij : Function.Bijective F' := by
    constructor
    · rintro ⟨⟨q, hq⟩, hqM⟩ ⟨⟨q', hq'⟩, hq'M⟩ heq
      have h1 : q.2 < 1 := (hM q.1 hq.1 q.2 hq.2).mp hqM
      have h2 : q'.2 < 1 := (hM q'.1 hq'.1 q'.2 hq'.2).mp hq'M
      have hqq : q = q' := hinj ⟨hq.1, hq.2.1, h1⟩ ⟨hq'.1, hq'.2.1, h2⟩
        (congrArg Subtype.val heq)
      subst hqq
      rfl
    · rintro ⟨z, hz⟩
      obtain ⟨b, hb, t, ht, rfl⟩ := hsurj z hz
      exact ⟨⟨⟨(b, t), hb, ht.1, ht.2.le⟩, (hM b hb t ⟨ht.1, ht.2.le⟩).mpr ht.2⟩, rfl⟩
  have hhom : IsHomeomorph F' := isHomeomorph_iff_continuous_isClosedMap_bijective.mpr
    ⟨hF.restrictPreimage, hF.isClosedMap.restrictPreimage M, hbij⟩
  let ψ := (IsHomeomorph.homeomorph F' hhom).symm
  have hψ : ∀ z : M, F' (ψ z) = z := fun z => (IsHomeomorph.homeomorph F' hhom).apply_symm_apply z
  refine ⟨fun z => if hz : z ∈ M then ((ψ ⟨z, hz⟩).1 : E3 × ℝ).1 else z,
    fun z => if hz : z ∈ M then ((ψ ⟨z, hz⟩).1 : E3 × ℝ).2 else 0, ?_, ?_, ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    have heq : M.domRestrict (fun z => if hz : z ∈ M then ((ψ ⟨z, hz⟩).1 : E3 × ℝ).1 else z) =
        fun z : M => ((ψ z).1 : E3 × ℝ).1 := by
      funext z
      simp only [domRestrict_apply, dite_eq_left z.2]
    rw [heq]
    exact continuous_fst.comp (continuous_subtype_val.comp
      (continuous_subtype_val.comp ψ.continuous))
  · rw [continuousOn_iff_continuous_domRestrict]
    have heq : M.domRestrict (fun z => if hz : z ∈ M then ((ψ ⟨z, hz⟩).1 : E3 × ℝ).2 else 0) =
        fun z : M => ((ψ z).1 : E3 × ℝ).2 := by
      funext z
      simp only [domRestrict_apply, dite_eq_left z.2]
    rw [heq]
    exact continuous_snd.comp (continuous_subtype_val.comp
      (continuous_subtype_val.comp ψ.continuous))
  · intro z hz
    simp only [dite_eq_left hz]
    have hw := (ψ ⟨z, hz⟩).1.2
    have hwM := (ψ ⟨z, hz⟩).2
    have hF'eq := congrArg Subtype.val (hψ ⟨z, hz⟩)
    refine ⟨hw.1, ⟨hw.2.1, ?_⟩, hF'eq⟩
    exact (hM _ hw.1 _ hw.2).mp hwM

theorem IsTube.exists_rayChart {K : Geometry.SimplicialComplex ℝ E3} {N N' : Set E3}
    {C : E3 → Set E3} {D Dbd : Finset E3 → Set E3} {h : E3 → E3}
    (ht : IsTube K N C D Dbd h N') :
    ∃ (Y : Set E3) (Φ : E3 → ℝ → E3), IsCompact Y ∧
      ContinuousOn (fun q : E3 × ℝ => Φ q.1 q.2) (Y ×ˢ Icc 0 1) ∧
      (∀ b ∈ Y, ∀ t ∈ Icc (0 : ℝ) 1, Φ b t ∈ N') ∧
      (∀ b ∈ Y, Φ b 1 ∈ h '' K.space) ∧
      (∀ b ∈ Y, ∀ t ∈ Ico (0 : ℝ) 1, Φ b t ∉ h '' K.space) ∧
      (∀ b ∈ Y, ∀ t ∈ Ioo (0 : ℝ) 1, Φ b t ∈ interior N') ∧
      (∀ b ∈ Y, Φ b 0 ∉ interior N') ∧
      InjOn (fun q : E3 × ℝ => Φ q.1 q.2) (Y ×ˢ Ico 0 1) ∧
      ∃ (β : E3 → E3) (τ : E3 → ℝ), ContinuousOn β (N' \ h '' K.space) ∧
        ContinuousOn τ (N' \ h '' K.space) ∧ ∀ z ∈ N' \ h '' K.space,
          β z ∈ Y ∧ τ z ∈ Ico (0 : ℝ) 1 ∧ Φ (β z) (τ z) = z := by
  classical
  let _ : DecidableEq E3 := fun a b => Classical.propDecidable (a = b)
  have hNc := ht.isCompact
  have hNcl := ht.isClosed
  have hhc := ht.continuousOn
  have hhi := ht.injOn
  have hint := ht.interior_eq_image_interior
  have himg := ht.imageEq
  have hKN : K.space ⊆ interior N := subset_interior_iff_mem_nhdsSet.mpr ht.isNeighborhood
  obtain ⟨A, hAfin, hA, hKA, hC, -⟩ := ht.derivedModel
  let _ : Finite A.faces := hAfin.to_subtype
  have hN : N = (derivedNeighborhood A K).space := by
    rw [ht.unionEq, ← iUnion_graphDualCell_space A K hKA]
    exact iUnion₂_congr hC
  subst hN
  have hNA := derivedNeighborhood_space_subset A K
  have hKint : K.space ⊆ interior A.space := hKN.trans (interior_mono hNA)
  have hNint : (derivedNeighborhood A K).space ⊆ interior A.space :=
    derivedNeighborhood_space_subset_interior (n := 2) finrank_euclideanSpace_fin hA hKA hKint
  have hYN := hNcl.frontier_subset
  have hpc : ContinuousOn (subcomplexBarycentricProjection (barycentricSubdivision A)
      (barycentricSubdivision K)) (derivedNeighborhood A K).space :=
    continuousOn_subcomplexBarycentricProjection_derivedNeighborhood
  have hpK : ∀ b ∈ (derivedNeighborhood A K).space, subcomplexBarycentricProjection
      (barycentricSubdivision A) (barycentricSubdivision K) b ∈ K.space :=
    fun b hb => subcomplexBarycentricProjection_mem_subcomplex hKA hb
  have hRN : ∀ b ∈ frontier (derivedNeighborhood A K).space, ∀ t ∈ Icc (0 : ℝ) 1,
      (1 - t) • b + t • subcomplexBarycentricProjection (barycentricSubdivision A)
        (barycentricSubdivision K) b ∈ (derivedNeighborhood A K).space := by
    intro b hb t ht'
    rcases eq_or_lt_of_le ht'.2 with h1 | h1
    · rw [h1, sub_self, zero_smul, one_smul, zero_add]
      exact interior_subset (hKN (hpK b (hYN hb)))
    rcases eq_or_lt_of_le ht'.1 with h0 | h0
    · rw [← h0, sub_zero, zero_smul, one_smul, add_zero]
      exact hYN hb
    · exact interior_subset
        (smul_add_smul_subcomplexBarycentricProjection_mem_interior hNint hb h0 h1)
  have hRc : ContinuousOn (fun q : E3 × ℝ => (1 - q.2) • q.1 + q.2 •
      subcomplexBarycentricProjection (barycentricSubdivision A) (barycentricSubdivision K) q.1)
      (frontier (derivedNeighborhood A K).space ×ˢ Icc 0 1) := by
    refine ((continuous_const.sub continuous_snd).smul continuous_fst).continuousOn.add
      (continuous_snd.continuousOn.smul ?_)
    exact hpc.comp continuous_fst.continuousOn fun q hq => hYN hq.1
  have hnotK : ∀ b ∈ frontier (derivedNeighborhood A K).space, ∀ t ∈ Ico (0 : ℝ) 1,
      h ((1 - t) • b + t • subcomplexBarycentricProjection (barycentricSubdivision A)
        (barycentricSubdivision K) b) ∉ h '' K.space := by
    rintro b hb t ⟨ht0, ht1⟩ ⟨k, hk, hkeq⟩
    have hmem := hRN b hb t ⟨ht0, ht1.le⟩
    have heq := hhi (interior_subset (hKN hk)) hmem hkeq
    exact smul_add_smul_subcomplexBarycentricProjection_notMem hKA hNint hb ht0 ht1 (heq ▸ hk)
  refine ⟨frontier (derivedNeighborhood A K).space, fun b t => h ((1 - t) • b + t •
    subcomplexBarycentricProjection (barycentricSubdivision A) (barycentricSubdivision K) b),
    hNc.of_isClosed_subset isClosed_frontier hYN, ?_, ?_, ?_, hnotK, ?_, ?_, ?_, ?_⟩
  · exact hhc.comp hRc fun q hq => hRN q.1 hq.1 q.2 hq.2
  · intro b hb t ht'
    rw [himg]
    exact mem_image_of_mem h (hRN b hb t ht')
  · intro b hb
    refine ⟨_, hpK b (hYN hb), ?_⟩
    simp only [sub_self, zero_smul, one_smul, zero_add]
  · intro b hb t ht'
    rw [hint]
    exact mem_image_of_mem h
      (smul_add_smul_subcomplexBarycentricProjection_mem_interior hNint hb ht'.1 ht'.2)
  · intro b hb hbi
    rw [hint] at hbi
    obtain ⟨y, hy, hyeq⟩ := hbi
    have hb' : (1 - (0 : ℝ)) • b + (0 : ℝ) • subcomplexBarycentricProjection
        (barycentricSubdivision A) (barycentricSubdivision K) b = b := by
      rw [sub_zero, zero_smul, one_smul, add_zero]
    have hyeq' : h y = h b := by
      rw [hyeq]
      beta_reduce
      rw [hb']
    have hyb := hhi (interior_subset hy) (hYN hb) hyeq'
    exact hb.2 (hyb ▸ hy)
  · rintro ⟨b, t⟩ ⟨hb, ht0, ht1⟩ ⟨b', t'⟩ ⟨hb', ht0', ht1'⟩ heq
    have h1 := hhi (hRN b hb t ⟨ht0, ht1.le⟩) (hRN b' hb' t' ⟨ht0', ht1'.le⟩) heq
    obtain ⟨hbb, htt⟩ :=
      eq_of_smul_add_smul_subcomplexBarycentricProjection_eq hNint hb hb' ht0 ht1 ht0' ht1' h1
    exact Prod.ext hbb htt
  · refine exists_continuousOn_rayCoordinates (Φ := fun b t => h ((1 - t) • b + t •
      subcomplexBarycentricProjection (barycentricSubdivision A) (barycentricSubdivision K) b))
      (hNc.of_isClosed_subset isClosed_frontier hYN)
      (hhc.comp hRc fun q hq => hRN q.1 hq.1 q.2 hq.2) ?_ ?_ ?_
    · intro b hb t ht'
      beta_reduce
      constructor
      · intro hmem
        by_contra hge
        have ht1 : t = 1 := le_antisymm ht'.2 (not_lt.mp hge)
        subst ht1
        refine hmem.2 ⟨_, hpK b (hYN hb), ?_⟩
        simp only [sub_self, zero_smul, one_smul, zero_add]
      · intro ht1
        refine ⟨?_, hnotK b hb t ⟨ht'.1, ht1⟩⟩
        rw [himg]
        exact mem_image_of_mem h (hRN b hb t ht')
    · rintro ⟨b, t⟩ ⟨hb, ht0, ht1⟩ ⟨b', t'⟩ ⟨hb', ht0', ht1'⟩ heq
      have h1 := hhi (hRN b hb t ⟨ht0, ht1.le⟩) (hRN b' hb' t' ⟨ht0', ht1'.le⟩) heq
      obtain ⟨hbb, htt⟩ :=
        eq_of_smul_add_smul_subcomplexBarycentricProjection_eq hNint hb hb' ht0 ht1 ht0' ht1' h1
      exact Prod.ext hbb htt
    · rintro z ⟨hzN, hzK⟩
      rw [himg] at hzN
      obtain ⟨y, hy, rfl⟩ := hzN
      have hyK : y ∉ K.space := fun hk => hzK (mem_image_of_mem h hk)
      by_cases hyi : y ∈ interior (derivedNeighborhood A K).space
      · obtain ⟨b, hb, t, ht', hbt⟩ :=
          exists_mem_frontier_derivedNeighborhood_of_mem_interior hKA hyi hyK
        exact ⟨b, hb, t, ⟨ht'.1.le, ht'.2⟩, by rw [hbt]⟩
      · refine ⟨y, ⟨subset_closure hy, hyi⟩, 0, ⟨le_rfl, zero_lt_one⟩, ?_⟩
        simp only [sub_zero, zero_smul, one_smul, add_zero]

end DifferentialGeometry.Topology.PiecewiseLinear
