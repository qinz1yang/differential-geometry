/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.BicollaredComplement
import DifferentialGeometry.Topology.SimplicialComplex.GeometricConnectivity
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheoremDiskVocabulary
import DifferentialGeometry.Topology.PiecewiseLinear.Section33CollarPush
import DifferentialGeometry.Topology.PiecewiseLinear.Section33LoopTheoremInjective
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceSideLoops

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem section33_fundamentalGroup_map_bijective_of_isTube
    {K : Geometry.SimplicialComplex ℝ E3} {N N' : Set E3} {C : E3 → Set E3}
    {D Dbd Ec Eint Ebd : Finset E3 → Set E3} {h : E3 → E3}
    {XK : Geometry.SimplicialComplex ℝ E3} (h264 : Moise264Orientable)
    (ht : IsTube K N C D Dbd h N')
    (h2 : IsPolyhedralTubeNeighborhood K h N' Ec Eint Ebd XK)
    (hXc : IsConnected (frontier XK.space))
    (hnoLTD : ∀ Δ : Set E3, ¬ IsLoopTheoremDisk (h '' K.space) N' (frontier XK.space) Δ) :
    ∀ hsub : frontier XK.space ⊆ N' \ h '' K.space, ∀ x : frontier XK.space,
      Function.Bijective (FundamentalGroup.map
        (⟨Set.inclusion hsub, continuous_inclusion hsub⟩ :
          C(frontier XK.space, ↥(N' \ h '' K.space))) x) := by
  intro hsub x
  classical
  let _ : Finite XK.faces := h2.facesFinite.to_subtype
  have hXcl : IsClosed XK.space := (isPolyhedron_space XK).isClosed
  let BX := @boundaryComplex _ _ _ (Classical.decEq _) (2 + 1) XK
  have hFr : frontier XK.space = BX.space := frontier_space_eq_boundaryComplex_space h2.isManifold
  let _ : Finite BX.faces := ((Set.toFinite XK.faces).subset fun _ hs => hs.1).to_subtype
  have hBman : IsCombinatorialManifold 2 BX :=
    isCombinatorialManifold_boundaryComplex XK h2.isManifold
  have hSc : IsCompact (frontier XK.space) :=
    (isPolyhedron_space XK).isCompact.of_isClosed_subset isClosed_frontier hXcl.frontier_subset
  have hlpc : LocallyPathConnectedSpace (frontier XK.space) := by
    rw [hFr]
    exact SimplicialComplex.locallyPathConnectedSpace_geometricSpace BX
  have hpc : PathConnectedSpace (frontier XK.space) := by
    have := isConnected_iff_connectedSpace.mp hXc
    exact PathConnectedSpace.of_locallyPathConnectedSpace
  have hKint : h '' K.space ⊆ interior XK.space :=
    subset_interior_iff_mem_nhdsSet.mpr h2.isNeighborhood
  have hSW : frontier XK.space ⊆ interior N' \ h '' K.space := fun y hy =>
    ⟨h2.subsetInterior (hXcl.frontier_subset hy),
      fun hyK => disjoint_interior_frontier.notMem_of_mem_left (hKint hyK) hy⟩
  have hWo : IsOpen (interior N' \ h '' K.space) :=
    isOpen_interior.sdiff ht.isCompact_image_space.isClosed
  have hWM : interior N' \ h '' K.space ⊆ N' \ h '' K.space := fun z hz =>
    ⟨interior_subset hz.1, hz.2⟩
  have hdisj : Disjoint (interior XK.space) XK.spaceᶜ :=
    disjoint_compl_right.mono_left interior_subset
  have hWS : (interior N' \ h '' K.space) \ frontier XK.space ⊆
      interior XK.space ∪ XK.spaceᶜ := fun z hz => by
    rw [← compl_frontier_eq_interior_union_compl hXcl]
    exact hz.2
  have hWS' : (interior N' \ h '' K.space) \ frontier XK.space ⊆
      XK.spaceᶜ ∪ interior XK.space := fun z hz => Or.symm (hWS hz)
  obtain ⟨Y, Φ, hYc, hΦc, -, hΦK, hΦnK, hΦint, hΦ0, hinj, β, τ, hβc, hτc, hinv⟩ :=
    ht.exists_rayChart
  have hτpos : ∀ z ∈ interior N' \ h '' K.space, 0 < τ z := by
    intro z hz
    obtain ⟨hβ, hτ, heq⟩ := hinv z (hWM hz)
    rcases eq_or_lt_of_le hτ.1 with h0 | h0
    · exfalso
      have h1 : Φ (β z) 0 = z := by
        rw [h0]
        exact heq
      apply hΦ0 _ hβ
      rw [h1]
      exact hz.1
    · exact h0
  have hinvW : ∀ z ∈ interior N' \ h '' K.space,
      β z ∈ Y ∧ τ z ∈ Ioo (0 : ℝ) 1 ∧ Φ (β z) (τ z) = z := fun z hz =>
    ⟨(hinv z (hWM hz)).1, ⟨hτpos z hz, (hinv z (hWM hz)).2.1.2⟩, (hinv z (hWM hz)).2.2⟩
  have hΦW : ∀ b ∈ Y, ∀ t ∈ Ioo (0 : ℝ) 1, Φ b t ∈ interior N' \ h '' K.space :=
    fun b hb t htt => ⟨hΦint b hb t htt, hΦnK b hb t ⟨htt.1.le, htt.2⟩⟩
  have hτeq : ∀ z ∈ interior N' \ h '' K.space, ∀ b ∈ Y, ∀ t ∈ Ico (0 : ℝ) 1,
      Φ b t = z → τ z = t := by
    intro z hz b hb t htt hΦz
    have hq := hinj
      (show (β z, τ z) ∈ Y ×ˢ Ico (0 : ℝ) 1 from ⟨(hinv z (hWM hz)).1, (hinv z (hWM hz)).2.1⟩)
      (show (b, t) ∈ Y ×ˢ Ico (0 : ℝ) 1 from ⟨hb, htt⟩) ((hinv z (hWM hz)).2.2.trans hΦz.symm)
    exact congrArg Prod.snd hq
  have hslice : ∀ b ∈ Y, ContinuousOn (fun t : ℝ => Φ b t) (Icc 0 1) := fun b hb =>
    hΦc.comp (continuousOn_const.prodMk continuousOn_id) fun t htt => ⟨hb, htt⟩
  have hxW := hinvW x (hSW x.2)
  have hxmem : (β x, τ x) ∈ Y ×ˢ Icc (0 : ℝ) 1 := ⟨hxW.1, hxW.2.1.1.le, hxW.2.1.2.le⟩
  have hYI : IsCompact (Y ×ˢ Icc (0 : ℝ) 1) := hYc.prod isCompact_Icc
  have hZin : IsCompact ((Y ×ˢ Icc (0 : ℝ) 1) ∩ (fun q : E3 × ℝ => Φ q.1 q.2) ⁻¹' XK.space) :=
    hYI.of_isClosed_subset (hΦc.preimage_isClosed_of_isClosed hYI.isClosed hXcl)
      inter_subset_left
  have hxZ : (β x, τ x) ∈ (Y ×ˢ Icc (0 : ℝ) 1) ∩ (fun q : E3 × ℝ => Φ q.1 q.2) ⁻¹' XK.space := by
    refine ⟨hxmem, ?_⟩
    change Φ (β x) (τ x) ∈ XK.space
    rw [hxW.2.2]
    exact hXcl.frontier_subset x.2
  obtain ⟨q₀, hq₀, hmin⟩ := hZin.exists_isMinOn ⟨_, hxZ⟩ continuous_snd.continuousOn
  have hq₀le : ∀ q ∈ (Y ×ˢ Icc (0 : ℝ) 1) ∩ (fun q : E3 × ℝ => Φ q.1 q.2) ⁻¹' XK.space,
      q₀.2 ≤ q.2 := fun q hq => isMinOn_iff.mp hmin q hq
  have he0 : 0 < q₀.2 := by
    rcases eq_or_lt_of_le hq₀.1.2.1 with h0 | h0
    · exfalso
      have hmemX : Φ q₀.1 q₀.2 ∈ XK.space := hq₀.2
      rw [← h0] at hmemX
      exact hΦ0 _ hq₀.1.1 (h2.subsetInterior hmemX)
    · exact h0
  have he1 : q₀.2 < 1 := (hq₀le _ hxZ).trans_lt hxW.2.1.2
  have hlevin : ∀ b ∈ Y, Φ b q₀.2 ∉ interior XK.space := by
    intro b hb hbint
    have hev : (fun t : ℝ => Φ b t) ⁻¹' interior XK.space ∈ 𝓝[Icc (0 : ℝ) 1] q₀.2 :=
      hslice b hb q₀.2 ⟨he0.le, he1.le⟩ (isOpen_interior.mem_nhds hbint)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.mp hev
    have hlt := max_lt (show q₀.2 - ε / 2 < q₀.2 by linarith) (show q₀.2 / 2 < q₀.2 by linarith)
    have htI : max (q₀.2 - ε / 2) (q₀.2 / 2) ∈ Icc (0 : ℝ) 1 :=
      ⟨le_max_of_le_right (by linarith), max_le (by linarith) (by linarith)⟩
    have htb : max (q₀.2 - ε / 2) (q₀.2 / 2) ∈ Metric.ball q₀.2 ε := by
      rw [Metric.mem_ball, Real.dist_eq, abs_sub_lt_iff]
      constructor
      · linarith
      · linarith [le_max_left (q₀.2 - ε / 2) (q₀.2 / 2)]
    have hle := hq₀le (b, max (q₀.2 - ε / 2) (q₀.2 / 2))
      ⟨⟨hb, htI⟩, interior_subset (s := XK.space) (hball ⟨htb, htI⟩)⟩
    exact absurd hle (not_le.mpr hlt)
  have hP₀ : Φ q₀.1 q₀.2 ∈ frontier XK.space := by
    rw [hXcl.frontier_eq]
    exact ⟨hq₀.2, hlevin q₀.1 hq₀.1.1⟩
  have hτP₀ : τ (Φ q₀.1 q₀.2) = q₀.2 := hτeq _ (hSW hP₀) q₀.1 hq₀.1.1 q₀.2 ⟨he0.le, he1⟩ rfl
  have hZout : IsCompact
      ((Y ×ˢ Icc (0 : ℝ) 1) ∩ (fun q : E3 × ℝ => Φ q.1 q.2) ⁻¹' (interior XK.space)ᶜ) :=
    hYI.of_isClosed_subset
      (hΦc.preimage_isClosed_of_isClosed hYI.isClosed isOpen_interior.isClosed_compl)
      inter_subset_left
  have hxZ₂ : (β x, τ x) ∈
      (Y ×ˢ Icc (0 : ℝ) 1) ∩ (fun q : E3 × ℝ => Φ q.1 q.2) ⁻¹' (interior XK.space)ᶜ := by
    refine ⟨hxmem, ?_⟩
    change Φ (β x) (τ x) ∈ (interior XK.space)ᶜ
    rw [hxW.2.2]
    exact fun hxi => disjoint_interior_frontier.notMem_of_mem_left hxi x.2
  obtain ⟨q₂, hq₂, hmax⟩ := hZout.exists_isMaxOn ⟨_, hxZ₂⟩ continuous_snd.continuousOn
  have hq₂ge : ∀ q ∈ (Y ×ˢ Icc (0 : ℝ) 1) ∩ (fun q : E3 × ℝ => Φ q.1 q.2) ⁻¹'
      (interior XK.space)ᶜ, q.2 ≤ q₂.2 := fun q hq => isMaxOn_iff.mp hmax q hq
  have he2pos : 0 < q₂.2 := hxW.2.1.1.trans_le (hq₂ge _ hxZ₂)
  have he21 : q₂.2 < 1 := by
    rcases eq_or_lt_of_le hq₂.1.2.2 with h1 | h1
    · exfalso
      have hmem : Φ q₂.1 q₂.2 ∈ (interior XK.space)ᶜ := hq₂.2
      rw [h1] at hmem
      exact hmem (hKint (hΦK _ hq₂.1.1))
    · exact h1
  have hlevout : ∀ b ∈ Y, Φ b q₂.2 ∈ XK.space := by
    intro b hb
    by_contra hbX
    have hev : (fun t : ℝ => Φ b t) ⁻¹' XK.spaceᶜ ∈ 𝓝[Icc (0 : ℝ) 1] q₂.2 :=
      hslice b hb q₂.2 ⟨he2pos.le, he21.le⟩ (hXcl.isOpen_compl.mem_nhds hbX)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.mp hev
    have hlt := lt_min (show q₂.2 < q₂.2 + ε / 2 by linarith)
      (show q₂.2 < (q₂.2 + 1) / 2 by linarith)
    have htI : min (q₂.2 + ε / 2) ((q₂.2 + 1) / 2) ∈ Icc (0 : ℝ) 1 :=
      ⟨le_min (by linarith) (by linarith), min_le_of_right_le (by linarith)⟩
    have htb : min (q₂.2 + ε / 2) ((q₂.2 + 1) / 2) ∈ Metric.ball q₂.2 ε := by
      rw [Metric.mem_ball, Real.dist_eq, abs_sub_lt_iff]
      constructor
      · linarith [min_le_left (q₂.2 + ε / 2) ((q₂.2 + 1) / 2)]
      · linarith
    have hle := hq₂ge (b, min (q₂.2 + ε / 2) ((q₂.2 + 1) / 2))
      ⟨⟨hb, htI⟩, fun hint => hball ⟨htb, htI⟩ (interior_subset (s := XK.space) hint)⟩
    exact absurd hle (not_le.mpr hlt)
  have hP₂ : Φ q₂.1 q₂.2 ∈ frontier XK.space := by
    rw [hXcl.frontier_eq]
    exact ⟨hlevout q₂.1 hq₂.1.1, hq₂.2⟩
  have hτP₂ : τ (Φ q₂.1 q₂.2) = q₂.2 :=
    hτeq _ (hSW hP₂) q₂.1 hq₂.1.1 q₂.2 ⟨he2pos.le, he21⟩ rfl
  have hlev₁ : ∀ b ∈ Y, Φ b (τ (Φ q₀.1 q₀.2)) ∈ XK.spaceᶜ ∪ frontier XK.space := by
    intro b hb
    rw [hτP₀]
    by_cases hbX : Φ b q₀.2 ∈ XK.space
    · right
      rw [hXcl.frontier_eq]
      exact ⟨hbX, hlevin b hb⟩
    · exact Or.inl hbX
  have hlev₂ : ∀ b ∈ Y, Φ b (τ (Φ q₂.1 q₂.2)) ∈ interior XK.space ∪ frontier XK.space := by
    intro b hb
    rw [hτP₂]
    by_cases hbi : Φ b q₂.2 ∈ interior XK.space
    · exact Or.inl hbi
    · right
      rw [hXcl.frontier_eq]
      exact ⟨hlevout b hb, hbi⟩
  let ιSW : C(frontier XK.space, ↥(interior N' \ h '' K.space)) :=
    ⟨Set.inclusion hSW, continuous_inclusion hSW⟩
  have h₁ : ∀ (a b : frontier XK.space) (p : Path (Set.inclusion hSW a) (Set.inclusion hSW b)),
      (∀ s, (p s : E3) ∈ interior XK.space ∪ frontier XK.space) →
        ∃ σ : Path a b, p.Homotopic (σ.map (continuous_inclusion hSW)) := by
    intro a b p hp
    exact exists_path_homotopic_map_of_loops ιSW
      (R := {w | (w : E3) ∈ interior XK.space ∪ frontier XK.space})
      (by
        rintro _ ⟨y, rfl⟩
        exact Or.inr y.2)
      ⟨Φ q₀.1 q₀.2, hP₀⟩
      (fun γ hγ => exists_surface_loop_homotopic_of_level hWo hSc hSW isOpen_interior
        hXcl.isOpen_compl hdisj hWS hΦc hΦW (hβc.mono hWM) (hτc.mono hWM) hinvW
        ⟨Φ q₀.1 q₀.2, hP₀⟩ hlev₁ γ hγ) p hp
  have h₂ : ∀ (a b : frontier XK.space) (p : Path (Set.inclusion hSW a) (Set.inclusion hSW b)),
      (∀ s, (p s : E3) ∈ XK.spaceᶜ ∪ frontier XK.space) →
        ∃ σ : Path a b, p.Homotopic (σ.map (continuous_inclusion hSW)) := by
    intro a b p hp
    exact exists_path_homotopic_map_of_loops ιSW
      (R := {w | (w : E3) ∈ XK.spaceᶜ ∪ frontier XK.space})
      (by
        rintro _ ⟨y, rfl⟩
        exact Or.inr y.2)
      ⟨Φ q₂.1 q₂.2, hP₂⟩
      (fun γ hγ => exists_surface_loop_homotopic_of_level hWo hSc hSW hXcl.isOpen_compl
        isOpen_interior hdisj.symm hWS' hΦc hΦW (hβc.mono hWM) (hτc.mono hWM) hinvW
        ⟨Φ q₂.1 q₂.2, hP₂⟩ hlev₂ γ hγ) p hp
  have hsurjSW : Function.Surjective (FundamentalGroup.map ιSW x) := by
    intro g
    obtain ⟨γ, hγ⟩ := Path.Homotopic.Quotient.mk_surjective (FundamentalGroup.toPath g)
    obtain ⟨σ, hσ⟩ := exists_surface_path_homotopic_of_sides hWo hSc hSW isOpen_interior
      hXcl.isOpen_compl hdisj hWS h₁ h₂ (a := x) (b := x) γ
    refine ⟨FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk σ), ?_⟩
    refine Eq.trans ?_ hγ
    exact (Path.Homotopic.Quotient.eq.mpr hσ).symm
  have hinjSW : Function.Injective (FundamentalGroup.map ιSW x) :=
    injective_fundamentalGroup_map_of_moise264Orientable h264 finrank_euclideanSpace_fin hBman
      (hFr ▸ hXc) hFr.symm hWo hSW (fun Δ r hr hΔ hmeet hb => by
        by_contra hnn
        exact hnoLTD Δ ⟨r, hr, hΔ, hmeet, hb, hnn⟩) x
  let ιWM : C(↥(interior N' \ h '' K.space), ↥(N' \ h '' K.space)) :=
    ⟨Set.inclusion hWM, continuous_inclusion hWM⟩
  have hWMbij := ht.bijective_fundamentalGroup_map_interior_sdiff hWM (ιSW x)
  have hcomp : ∀ g, FundamentalGroup.map (⟨Set.inclusion hsub, continuous_inclusion hsub⟩ :
      C(frontier XK.space, ↥(N' \ h '' K.space))) x g =
      FundamentalGroup.map ιWM (ιSW x) (FundamentalGroup.map ιSW x g) := by
    intro g
    obtain ⟨γ, hγ⟩ := Path.Homotopic.Quotient.mk_surjective (FundamentalGroup.toPath g)
    rw [show g = FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ) from hγ.symm]
    rfl
  refine ⟨fun g₁ g₂ hg => hinjSW (hWMbij.1 ?_), fun g => ?_⟩
  · rw [← hcomp, ← hcomp]
    exact hg
  · obtain ⟨g', rfl⟩ := hWMbij.2 g
    obtain ⟨g'', rfl⟩ := hsurjSW g'
    exact ⟨g'', hcomp g''⟩

end DifferentialGeometry.Topology.PiecewiseLinear
