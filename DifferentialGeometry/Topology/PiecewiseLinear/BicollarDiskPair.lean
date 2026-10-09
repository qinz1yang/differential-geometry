/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ClosedStarNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.Prism
import DifferentialGeometry.Topology.PiecewiseLinear.PLHomeomorphTopology
import DifferentialGeometry.Topology.Connected.ClosedCover

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem IsPLHomeomorphOn.exists_isPLBall_neighborhood_pair_sdiff_of_bicollar
    {J W N : Set E} {ρ : E × ℝ → E} (hρ : IsPLHomeomorphOn ρ (J ×ˢ Icc (-1 : ℝ) 1) W)
    (hJ : IsPLSphere 1 J) (hzero : ∀ x ∈ J, ρ (x, 0) = x) {p : E} (hp : p ∈ J)
    (hW : W ∈ 𝓝[N] p) :
    ∃ V : Set E, IsPLBall 2 V ∧ V ⊆ W ∧ V ∈ 𝓝[N] p ∧ IsPLBall 1 (V ∩ J) ∧
      ∃ x ∈ V \ J, ∃ y ∈ V \ J,
        let C := connectedComponentIn (V \ J) x
        let D := connectedComponentIn (V \ J) y
        Disjoint C D ∧ C ∪ D = V \ J ∧ IsPLBall 2 (closure C) ∧ IsPLBall 2 (closure D) ∧
          closure C ∪ closure D = V ∧ closure C ∩ closure D = V ∩ J := by
  classical
  obtain ⟨L, hLfin, hLspace⟩ := hJ.isPolyhedron.exists_simplicialComplex
  let _ : Finite L.faces := hLfin.to_subtype
  have hL : IsPLSphere 1 L.space := hLspace.symm ▸ hJ
  have hLman := hL.isCombinatorialManifold.isCombinatorialManifoldWithBoundary
  obtain ⟨A, hA, hAL, hAnhds⟩ :=
    hLman.exists_isPLBall_subset_of_mem_nhdsWithin (hLspace.symm.subset hp)
      (U := univ) Filter.univ_mem
  have hAJ : A ⊆ J := (hAL.trans inter_subset_left).trans hLspace.subset
  have hAnhdsJ : A ∈ 𝓝[J] p := by rwa [hLspace] at hAnhds
  let P := J ×ˢ Icc (-1 : ℝ) 1
  let V := ρ '' (A ×ˢ Icc (-1 : ℝ) 1)
  let C := ρ '' (A ×ˢ Icc (-1 : ℝ) 0)
  let D := ρ '' (A ×ˢ Icc (0 : ℝ) 1)
  let C' := ρ '' (A ×ˢ Ico (-1 : ℝ) 0)
  let D' := ρ '' (A ×ˢ Ioc (0 : ℝ) 1)
  have hAP : A ×ˢ Icc (-1 : ℝ) 1 ⊆ P := fun _ hz => ⟨hAJ hz.1, hz.2⟩
  have hCP : A ×ˢ Icc (-1 : ℝ) 0 ⊆ P :=
    fun _ hz => ⟨hAJ hz.1, hz.2.1, hz.2.2.trans zero_le_one⟩
  have hDP : A ×ˢ Icc (0 : ℝ) 1 ⊆ P :=
    fun _ hz => ⟨hAJ hz.1, (by norm_num : (-1 : ℝ) ≤ 0).trans hz.2.1, hz.2.2⟩
  have hC'P : A ×ˢ Ico (-1 : ℝ) 0 ⊆ P :=
    fun _ hz => hCP ⟨hz.1, hz.2.1, hz.2.2.le⟩
  have hD'P : A ×ˢ Ioc (0 : ℝ) 1 ⊆ P :=
    fun _ hz => hDP ⟨hz.1, hz.2.1.le, hz.2.2⟩
  have hV : IsPLBall 2 V :=
    (isPLBall_two_prod hA (isPLBall_Icc (by norm_num : (-1 : ℝ) < 1))).of_isPLHomeomorphOn
      (hρ.restrict (hA.isPolyhedron.prod isHPolytope_Icc.isPolyhedron) hAP)
  have hC : IsPLBall 2 C :=
    (isPLBall_two_prod hA (isPLBall_Icc (by norm_num : (-1 : ℝ) < 0))).of_isPLHomeomorphOn
      (hρ.restrict (hA.isPolyhedron.prod isHPolytope_Icc.isPolyhedron) hCP)
  have hD : IsPLBall 2 D :=
    (isPLBall_two_prod hA (isPLBall_Icc (by norm_num : (0 : ℝ) < 1))).of_isPLHomeomorphOn
      (hρ.restrict (hA.isPolyhedron.prod isHPolytope_Icc.isPolyhedron) hDP)
  have hVW : V ⊆ W := (image_mono hAP).trans hρ.image_eq.subset
  have hVnhds : V ∈ 𝓝[N] p := by
    have hpP : (p, (0 : ℝ)) ∈ P := ⟨hp, by norm_num, by norm_num⟩
    have hpW : p ∈ W := (hzero p hp) ▸ hρ.bijOn.mapsTo hpP
    have hinv : Function.invFunOn ρ P p = (p, 0) := by
      have h := hρ.bijOn.invOn_invFunOn.1 hpP
      rwa [hzero p hp] at h
    have hpre : Function.invFunOn ρ P ⁻¹' (A ×ˢ Icc (-1 : ℝ) 1) ∈ 𝓝[W] p := by
      apply (hρ.isPiecewiseAffineOn_invFunOn.continuousOn p hpW).preimage_mem_nhdsWithin'
      rw [hρ.symm.image_eq, hinv]
      exact nhdsWithin_prod hAnhdsJ self_mem_nhdsWithin
    have hrel : V ∈ 𝓝[W] p := by
      apply Filter.mem_of_superset (Filter.inter_mem self_mem_nhdsWithin hpre)
      intro z hz
      exact ⟨Function.invFunOn ρ P z, hz.2, hρ.bijOn.invOn_invFunOn.2 hz.1⟩
    exact nhdsWithin_le_of_mem hW hrel
  have htrace : V ∩ J = A := by
    apply Subset.antisymm
    · rintro z ⟨⟨w, hw, hwz⟩, hzJ⟩
      have heq := hρ.bijOn.injOn (hAP hw) ⟨hzJ, by norm_num, by norm_num⟩
        (hwz.trans (hzero z hzJ).symm)
      rw [heq] at hw
      exact hw.1
    · intro z hz
      exact ⟨⟨(z, 0), ⟨hz, by norm_num, by norm_num⟩, hzero z (hAJ hz)⟩, hAJ hz⟩
  have hcover : C ∪ D = V := by
    apply Subset.antisymm
    · rintro z (⟨w, hw, rfl⟩ | ⟨w, hw, rfl⟩)
      · exact ⟨w, ⟨hw.1, hw.2.1, hw.2.2.trans zero_le_one⟩, rfl⟩
      · exact ⟨w, ⟨hw.1, (by norm_num : (-1 : ℝ) ≤ 0).trans hw.2.1, hw.2.2⟩, rfl⟩
    · rintro z ⟨w, hw, rfl⟩
      rcases le_total w.2 0 with ht | ht
      · exact Or.inl ⟨w, ⟨hw.1, hw.2.1, ht⟩, rfl⟩
      · exact Or.inr ⟨w, ⟨hw.1, ht, hw.2.2⟩, rfl⟩
  have hmeet : C ∩ D = A := by
    apply Subset.antisymm
    · rintro z ⟨⟨w, hw, hwz⟩, ⟨v, hv, hvz⟩⟩
      have heq := hρ.bijOn.injOn (hCP hw) (hDP hv) (hwz.trans hvz.symm)
      have ht := congrArg Prod.snd heq
      have hw0 : w.2 = 0 := by linarith [hw.2.2, hv.2.1]
      have hρw : ρ w = w.1 := by
        rw [show w = (w.1, 0) from Prod.ext rfl hw0, hzero w.1 (hAJ hw.1)]
      exact (hρw.symm.trans hwz) ▸ hw.1
    · intro z hz
      exact ⟨⟨(z, 0), ⟨hz, by norm_num, le_rfl⟩, hzero z (hAJ hz)⟩,
        ⟨(z, 0), ⟨hz, le_rfl, zero_le_one⟩, hzero z (hAJ hz)⟩⟩
  have hnon {z : E × ℝ} (hz : z ∈ P) (ht : z.2 ≠ 0) : ρ z ∉ J := by
    intro hzJ
    have heq := hρ.bijOn.injOn hz ⟨hzJ, by norm_num, by norm_num⟩ (hzero (ρ z) hzJ).symm
    exact ht (congrArg Prod.snd heq)
  have hC' : C' = C \ J := by
    apply Subset.antisymm
    · rintro z ⟨w, hw, rfl⟩
      exact ⟨⟨w, ⟨hw.1, hw.2.1, hw.2.2.le⟩, rfl⟩, hnon (hC'P hw) hw.2.2.ne⟩
    · rintro z ⟨⟨w, hw, rfl⟩, hz⟩
      have ht : w.2 < 0 := lt_of_le_of_ne hw.2.2 (fun ht => by
        apply hz
        rw [show w = (w.1, 0) from Prod.ext rfl ht, hzero w.1 (hAJ hw.1)]
        exact hAJ hw.1)
      exact ⟨w, ⟨hw.1, hw.2.1, ht⟩, rfl⟩
  have hD' : D' = D \ J := by
    apply Subset.antisymm
    · rintro z ⟨w, hw, rfl⟩
      exact ⟨⟨w, ⟨hw.1, hw.2.1.le, hw.2.2⟩, rfl⟩, hnon (hD'P hw) hw.2.1.ne'⟩
    · rintro z ⟨⟨w, hw, rfl⟩, hz⟩
      have ht : 0 < w.2 := lt_of_le_of_ne hw.2.1 (fun ht => by
        apply hz
        rw [show w = (w.1, 0) from Prod.ext rfl ht.symm, hzero w.1 (hAJ hw.1)]
        exact hAJ hw.1)
      exact ⟨w, ⟨hw.1, ht, hw.2.2⟩, rfl⟩
  have hconnC : IsConnected (C \ J) := hC' ▸
    (hA.isConnected.prod (isConnected_Ico (by norm_num : (-1 : ℝ) < 0))).image ρ
      (hρ.isPiecewiseAffineOn.continuousOn.mono hC'P)
  have hconnD : IsConnected (D \ J) := hD' ▸
    (hA.isConnected.prod (isConnected_Ioc (by norm_num : (0 : ℝ) < 1))).image ρ
      (hρ.isPiecewiseAffineOn.continuousOn.mono hD'P)
  have hclC : closure (C \ J) = C := by
    rw [← hC', ← hρ.image_closure (hJ.isPolyhedron.isCompact.prod isCompact_Icc) hC'P,
      closure_prod_eq, hA.isPolyhedron.isClosed.closure_eq,
      closure_Ico (by norm_num : (-1 : ℝ) ≠ 0)]
  have hclD : closure (D \ J) = D := by
    rw [← hD', ← hρ.image_closure (hJ.isPolyhedron.isCompact.prod isCompact_Icc) hD'P,
      closure_prod_eq, hA.isPolyhedron.isClosed.closure_eq,
      closure_Ioc (by norm_num : (0 : ℝ) ≠ 1)]
  have hCJ : C ∩ J = C ∩ D := by
    ext z
    constructor
    · intro hz
      exact ⟨hz.1, (hmeet.symm.subset
        (htrace.subset ⟨hcover.subset (Or.inl hz.1), hz.2⟩)).2⟩
    · intro hz
      exact ⟨hz.1, hAJ (hmeet.subset hz)⟩
  have hdiffC : C \ J = C \ D := by
    ext z
    have hz := Set.ext_iff.mp hCJ z
    simp only [mem_inter_iff] at hz
    simp only [mem_sdiff]
    tauto
  have hdiffD : D \ J = D \ C := by
    have hDJ : D ∩ J = D ∩ C := by
      ext z
      constructor
      · intro hz
        exact ⟨hz.1, (hmeet.symm.subset
          (htrace.subset ⟨hcover.subset (Or.inr hz.1), hz.2⟩)).1⟩
      · intro hz
        exact ⟨hz.1, hAJ (hmeet.subset ⟨hz.2, hz.1⟩)⟩
    ext z
    have hz := Set.ext_iff.mp hDJ z
    simp only [mem_inter_iff] at hz
    simp only [mem_sdiff]
    tauto
  have hdiffV : V \ (V ∩ J) = V \ J := by
    ext z
    simp only [mem_sdiff, mem_inter_iff]
    tauto
  obtain ⟨x, hx⟩ := hconnC.nonempty
  obtain ⟨y, hy⟩ := hconnD.nonempty
  have hccC : connectedComponentIn (V \ J) x = C \ J := by
    have h := Topology.connectedComponentIn_sdiff_inter_eq_sdiff hC.isPolyhedron.isClosed
      hD.isPolyhedron.isClosed (hdiffC ▸ hconnC.isPreconnected) (hdiffC ▸ hx)
    rw [hcover, hmeet, ← htrace, hdiffV, ← hdiffC] at h
    exact h
  have hccD : connectedComponentIn (V \ J) y = D \ J := by
    have h := Topology.connectedComponentIn_sdiff_inter_eq_sdiff hD.isPolyhedron.isClosed
      hC.isPolyhedron.isClosed (hdiffD ▸ hconnD.isPreconnected) (hdiffD ▸ hy)
    rw [union_comm D C, inter_comm D C, hcover, hmeet, ← htrace,
      hdiffV, ← hdiffD] at h
    exact h
  refine ⟨V, hV, hVW, hVnhds, htrace.symm ▸ hA,
    x, ⟨hcover.subset (Or.inl hx.1), hx.2⟩, y, ⟨hcover.subset (Or.inr hy.1), hy.2⟩, ?_⟩
  dsimp only
  rw [hccC, hccD, hclC, hclD]
  refine ⟨disjoint_left.mpr (fun z hzC hzD => hzC.2 (hAJ (hmeet.subset ⟨hzC.1, hzD.1⟩))),
    ?_, hC, hD, hcover, hmeet.trans htrace.symm⟩
  rw [← union_sdiff_distrib, hcover]

end DifferentialGeometry.Topology.PiecewiseLinear
