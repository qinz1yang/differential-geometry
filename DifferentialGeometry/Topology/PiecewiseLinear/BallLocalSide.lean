/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompressionPocket

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem IsPLBall.exists_mem_nhds_of_inter_frontier_subset {V R O : Set E3} (hV : IsPLBall 3 V)
    (hR : IsPLBall 3 R) (hO : IsOpen O) (hRO : O ∩ frontier R ⊆ V)
    (hint : Disjoint (interior R) (interior V)) {y : E3} (hyO : y ∈ O) (hyR : y ∈ R)
    (hyV : y ∈ frontier V) : ∃ U ∈ 𝓝 y, U ∩ frontier V ⊆ R ∧ U \ V ⊆ interior R := by
  have hdim : Module.finrank ℝ E3 = 2 + 1 := by simp
  have hVc : IsClosed V := hV.isPolyhedron.isClosed
  have hRc : IsClosed R := hR.isPolyhedron.isClosed
  have hVreg : closure (interior V) = V := hV.closure_interior_of_finrank hdim
  have hRreg : closure (interior R) = R := hR.closure_interior_of_finrank hdim
  set S := frontier V
  have hSV : S ⊆ V := hVc.frontier_subset
  have : LocallyConnectedSpace S := hV.isPLSphere_frontier.isPolyhedron.locallyConnectedSpace
  obtain ⟨Φ, hΦ, hΦ0⟩ :=
    (isBicollared_iff_exists_isOpenEmbedding S).mp hV.isBicollared_frontier
  set y' : S := ⟨y, hyV⟩
  have hmem : Φ ⁻¹' O ∈ 𝓝 (y', (0 : ℝ)) := by
    apply hΦ.continuous.continuousAt.preimage_mem_nhds
    rw [hΦ0 y']
    exact hO.mem_nhds hyO
  rw [nhds_prod_eq] at hmem
  obtain ⟨u, hu, v, hv, huv⟩ := Filter.mem_prod_iff.mp hmem
  obtain ⟨δ, hδ, hδv⟩ := Metric.mem_nhds_iff.mp hv
  obtain ⟨N, ⟨hNo, hyN, hNc⟩, hNu⟩ :=
    (LocallyConnectedSpace.open_connected_basis y').mem_iff.mp hu
  have hoff : ∀ (n : S) (t : ℝ), Φ (n, t) ∈ S → t = 0 := by
    intro n t h
    have h2 : Φ (n, t) = Φ (⟨Φ (n, t), h⟩, 0) := (hΦ0 ⟨Φ (n, t), h⟩).symm
    exact congrArg Prod.snd (hΦ.injective h2)
  have hbox : ∀ n ∈ N, ∀ t : ℝ, t ∈ Ioo (-δ) δ → Φ (n, t) ∈ O := by
    intro n hn t ht
    refine huv ⟨hNu hn, hδv ?_⟩
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
    exact ht
  set Ap := Φ '' (N ×ˢ Ioo 0 δ)
  set Am := Φ '' (N ×ˢ Ioo (-δ) 0)
  set Nb := Φ '' (N ×ˢ Ioo (-δ) δ)
  have hNb : IsOpen Nb := hΦ.isOpenMap _ (hNo.prod isOpen_Ioo)
  have hyNb : y ∈ Nb := ⟨(y', 0), ⟨hyN, neg_lt_zero.mpr hδ, hδ⟩, hΦ0 y'⟩
  have hsplit : Nb ⊆ Ap ∪ Am ∪ S := by
    rintro _ ⟨⟨n, t⟩, ⟨hn, ht⟩, rfl⟩
    rcases lt_trichotomy t 0 with h | rfl | h
    · exact Or.inl (Or.inr ⟨(n, t), ⟨hn, ht.1, h⟩, rfl⟩)
    · refine Or.inr ?_
      rw [hΦ0 n]
      exact n.2
    · exact Or.inl (Or.inl ⟨(n, t), ⟨hn, h, ht.2⟩, rfl⟩)
  have hApO : Ap ⊆ O := by
    rintro _ ⟨⟨n, t⟩, ⟨hn, ht⟩, rfl⟩
    exact hbox n hn t ⟨by linarith [ht.1], ht.2⟩
  have hAmO : Am ⊆ O := by
    rintro _ ⟨⟨n, t⟩, ⟨hn, ht⟩, rfl⟩
    exact hbox n hn t ⟨ht.1, by linarith [ht.2]⟩
  have hApc : IsPreconnected Ap :=
    (hNc.isPreconnected.prod isPreconnected_Ioo).image _ hΦ.continuous.continuousOn
  have hAmc : IsPreconnected Am :=
    (hNc.isPreconnected.prod isPreconnected_Ioo).image _ hΦ.continuous.continuousOn
  have hApS : Disjoint Ap S := by
    refine Set.disjoint_left.mpr ?_
    rintro _ ⟨⟨n, t⟩, ⟨-, ht⟩, rfl⟩ hfr
    exact (ne_of_gt ht.1) (hoff n t hfr)
  have hAmS : Disjoint Am S := by
    refine Set.disjoint_left.mpr ?_
    rintro _ ⟨⟨n, t⟩, ⟨-, ht⟩, rfl⟩ hfr
    exact (ne_of_lt ht.2) (hoff n t hfr)
  have hclAp : Nb ∩ S ⊆ closure Ap := by
    rintro _ ⟨⟨⟨n, t⟩, ⟨hn, -⟩, rfl⟩, hS⟩
    have ht0 := hoff n t hS
    subst ht0
    have htend : Filter.Tendsto (fun s : ℝ => Φ (n, s)) (𝓝[>] 0) (𝓝 (Φ (n, 0))) :=
      ((hΦ.continuous.comp (Continuous.prodMk_right n)).tendsto 0).mono_left
        nhdsWithin_le_nhds
    refine mem_closure_of_tendsto htend ?_
    filter_upwards [Ioo_mem_nhdsGT hδ] with s hs
    exact ⟨(n, s), ⟨hn, hs⟩, rfl⟩
  have hclAm : Nb ∩ S ⊆ closure Am := by
    rintro _ ⟨⟨⟨n, t⟩, ⟨hn, -⟩, rfl⟩, hS⟩
    have ht0 := hoff n t hS
    subst ht0
    have htend : Filter.Tendsto (fun s : ℝ => Φ (n, s)) (𝓝[<] 0) (𝓝 (Φ (n, 0))) :=
      ((hΦ.continuous.comp (Continuous.prodMk_right n)).tendsto 0).mono_left
        nhdsWithin_le_nhds
    refine mem_closure_of_tendsto htend ?_
    filter_upwards [Ioo_mem_nhdsLT (neg_lt_zero.mpr hδ)] with s hs
    exact ⟨(n, s), ⟨hn, hs⟩, rfl⟩
  have hintR : ∀ z ∈ interior R, z ∉ V := by
    intro z hz hzV
    have hzc : z ∈ closure (interior V) := by
      rw [hVreg]
      exact hzV
    obtain ⟨w, hwR, hwV⟩ := mem_closure_iff.mp hzc (interior R) isOpen_interior hz
    exact Set.disjoint_left.mp hint hwR hwV
  have key : ∀ A B : Set E3, A ⊆ Vᶜ → B ⊆ V → IsPreconnected A → A ⊆ O →
      Nb ⊆ A ∪ B ∪ S → Nb ∩ S ⊆ closure A →
      ∃ U ∈ 𝓝 y, U ∩ frontier V ⊆ R ∧ U \ V ⊆ interior R := by
    intro A B hAV hBV hAc hAO hNbAB hclA
    have hAR : Disjoint A (frontier R) := by
      refine Set.disjoint_left.mpr fun z hzA hzR => hAV hzA ?_
      exact hRO ⟨hAO hzA, hzR⟩
    have hAint : A ⊆ interior R := by
      rcases subset_interior_or_subset_compl_of_disjoint_frontier hRc hAc hAR with h | h
      · exact h
      · have hyc : y ∈ closure (interior R) := by
          rw [hRreg]
          exact hyR
        obtain ⟨z, hzNb, hzi⟩ := mem_closure_iff.mp hyc Nb hNb hyNb
        exfalso
        rcases hNbAB hzNb with (hz | hz) | hz
        · exact h hz (interior_subset hzi)
        · exact hintR z hzi (hBV hz)
        · exact hintR z hzi (hSV hz)
    refine ⟨Nb, hNb.mem_nhds hyNb, fun z hz => ?_, fun z hz => ?_⟩
    · have hzA := hclA hz
      rw [← hRreg]
      exact closure_mono hAint hzA
    · rcases hNbAB hz.1 with (h | h) | h
      · exact hAint h
      · exact absurd (hBV h) hz.2
      · exact absurd (hSV h) hz.2
  have hnotboth : ¬ (Ap ⊆ interior V ∧ Am ⊆ interior V) := by
    rintro ⟨h1, h2⟩
    have hsub : Nb ⊆ V := by
      intro z hz
      rcases hsplit hz with (h | h) | h
      · exact interior_subset (h1 h)
      · exact interior_subset (h2 h)
      · exact hSV h
    exact hyV.2 (mem_interior.mpr ⟨Nb, hsub, hNb, hyNb⟩)
  have hnotnone : ¬ (Ap ⊆ Vᶜ ∧ Am ⊆ Vᶜ) := by
    rintro ⟨h1, h2⟩
    have hyc : y ∈ closure (interior V) := by
      rw [hVreg]
      exact hVc.frontier_subset hyV
    obtain ⟨z, hzNb, hzi⟩ := mem_closure_iff.mp hyc Nb hNb hyNb
    rcases hsplit hzNb with (h | h) | h
    · exact h1 h (interior_subset hzi)
    · exact h2 h (interior_subset hzi)
    · exact h.2 hzi
  rcases subset_interior_or_subset_compl_of_disjoint_frontier hVc hApc hApS with hAp | hAp <;>
    rcases subset_interior_or_subset_compl_of_disjoint_frontier hVc hAmc hAmS with hAm | hAm
  · exact absurd ⟨hAp, hAm⟩ hnotboth
  · refine key Am Ap hAm (hAp.trans interior_subset) hAmc hAmO ?_ hclAm
    intro z hz
    rcases hsplit hz with (h | h) | h
    · exact Or.inl (Or.inr h)
    · exact Or.inl (Or.inl h)
    · exact Or.inr h
  · exact key Ap Am hAp (hAm.trans interior_subset) hApc hApO hsplit hclAp
  · exact absurd ⟨hAp, hAm⟩ hnotnone

end DifferentialGeometry.Topology.PiecewiseLinear
