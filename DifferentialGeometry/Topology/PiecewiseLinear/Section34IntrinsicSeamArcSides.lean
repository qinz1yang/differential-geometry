/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CrossingCellSeam
import DifferentialGeometry.Topology.PiecewiseLinear.CurveCrossingArcCharts
import DifferentialGeometry.Topology.PiecewiseLinear.OutermostCircleCrosscut
import DifferentialGeometry.Topology.PiecewiseLinear.Section34FaceBallUpdate
import DifferentialGeometry.Topology.PiecewiseLinear.Section34VertexFrontier

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace E3 M₁]
  [MetricSpace M₂] [ChartedSpace E3 M₂]
  {U : Set M₁} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁} {f₁ : M₁ → M₂}

omit [FiniteDimensional ℝ Ea] in
theorem Section34CutFrame.not_model_arc_interior_on_split_disk_boundary
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hf₁ : IsPLHomeomorphInto 3 f₁ (section34CutNeighborhood src))
    (w : Section34VertexIndex 𝒦 𝒦') (e : Section34EdgeIndex 𝒦 𝒦')
    {P A : Set E3} {u : E3 → M₂} {J : Set M₂} {α : ℝ → E3}
    (hu : IsPLHomeomorphInto 3 u P) (hα : IsPLHomeomorphOn α (Icc 0 1) A)
    (hAP : A ⊆ P) (hAJ : A ⊆ u ⁻¹' J)
    (hAV : A ⊆ u ⁻¹' section34VertexBallImage src f₁ w) {x : E3}
    (hxγ : u x ∈ section34SplitDiskImage srcBd f₁ e)
    {c : OpenPartialHomeomorph M₂ E3} (hxc : u x ∈ c.source)
    (hc : HasPLCurveCrossingOnAt
      (c '' (frontier (⋃ v, section34VertexBallImage src f₁ v) ∩ c.source))
      (c '' (J ∩ c.source))
      (c '' (section34SplitDiskImage srcBd f₁ e ∩ c.source)) (c (u x))) :
    x ∉ A \ {α 0, α 1} := by
  intro hx
  have hxE := (hcut.isPLCellOn_splitDiskImage hf₁ e).boundary_subset hxγ
  have hwe := hcut.subset_of_mem_splitDiskImage hf₁.injOn hxE (hAV hx.1)
  obtain ⟨v, hends, heq⟩ : ∃ v : Section34VertexIndex 𝒦 𝒦',
      (e.1 : Set Ea) = (w.1 : Set Ea) ∪ (v.1 : Set Ea) ∧
      section34SplitDiskImage src f₁ e = section34VertexBallImage src f₁ w ∩
        section34VertexBallImage src f₁ v := by
    obtain ⟨a, b, -, heab, heq⟩ := hcut.splitDiskImage_eq_inter hf₁.injOn e
    rcases eq_or_eq_of_section34VertexIndex_subset e heab hwe with rfl | rfl
    · exact ⟨b, heab, heq⟩
    · exact ⟨a, heab.trans (union_comm _ _), heq.trans (inter_comm _ _)⟩
  have hlocal := hcut.frontier_eventually_eq_vertex_pair hf₁ w v
    (mem_iUnion.mpr ⟨w, hAV hx.1⟩) (by
      intro z hzw hzv hxz
      rcases eq_or_eq_of_section34VertexIndex_subset e hends
        (hcut.subset_of_mem_splitDiskImage hf₁.injOn hxE hxz) with hz | hz
      · exact hzw hz
      · exact hzv hz)
  have hparam : (u ∘ α) '' Icc 0 1 = u '' A := by
    calc
      (u ∘ α) '' Icc 0 1 = u '' (α '' Icc 0 1) := (image_image u α _).symm
      _ = u '' A := by rw [hα.image_eq]
  have hximage : u x ∈ u '' A \ {u (α 0), u (α 1)} := by
    refine ⟨⟨x, hx.1, rfl⟩, ?_⟩
    rintro (h0 | h1)
    · exact hx.2 (Or.inl (hu.injOn (hAP hx.1)
        (hAP (hα.bijOn.mapsTo (by norm_num))) h0))
    · exact hx.2 (Or.inr (hu.injOn (hAP hx.1)
        (hAP (hα.bijOn.mapsTo (by norm_num))) h1))
  have hlocalA := hc.swap.eventually_mem_arc_iff_in_chart c hxc
    ((hu.continuousOn.mono hAP).comp hα.isPiecewiseAffineOn.continuousOn hα.bijOn.mapsTo)
    ((hu.injOn.mono hAP).comp hα.bijOn.injOn hα.bijOn.mapsTo)
    hparam (image_subset_iff.mpr hAJ) hximage
  have hpush {F G : Set M₂} (hFG : ∀ᶠ y in 𝓝 (u x), y ∈ F ↔ y ∈ G) :
      ∀ᶠ y in 𝓝 (c (u x)), y ∈ c '' (F ∩ c.source) ↔
        y ∈ c '' (G ∩ c.source) := by
    obtain ⟨O, hOO, hO, hxO⟩ := _root_.mem_nhds_iff.mp hFG
    have hOeq : F ∩ O = G ∩ O := by
      ext y
      exact and_congr_left fun hy => hOO hy
    exact eventually_mem_image_inter_source_iff hO hOeq hxO hxc
  have hc' := hc.congr (hpush hlocal)
    (hpush (by filter_upwards [hlocalA] with y hy using hy.symm))
    (Filter.Eventually.of_forall fun _ => Iff.rfl)
  have hD := hcut.isPLCellOn_splitDiskImage hf₁ e
  rw [heq] at hD
  exact hc'.not_subset_of_cell_seam_in_chart (hcut.isPLCellOn_vertexBallImage hf₁ w)
    (hcut.isPLCellOn_vertexBallImage hf₁ v) hD c hxc (image_subset_iff.mpr hAV)

omit [FiniteDimensional ℝ Ea] in
theorem Section34CutFrame.ne_initial_points_of_model_arcs_in_vertex_ball
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hf₁ : IsPLHomeomorphInto 3 f₁ (section34CutNeighborhood src))
    (w : Section34VertexIndex 𝒦 𝒦') (e : Section34EdgeIndex 𝒦 𝒦')
    {P A B : Set E3} {u : E3 → M₂} {J : Set M₂} {α β : ℝ → E3}
    (hu : IsPLHomeomorphInto 3 u P)
    (hα : IsPLHomeomorphOn α (Icc 0 1) A) (hβ : IsPLHomeomorphOn β (Icc 0 1) B)
    (hAP : A ⊆ P) (hBP : B ⊆ P) (hAJ : A ⊆ u ⁻¹' J) (hBJ : B ⊆ u ⁻¹' J)
    (hAV : A ⊆ u ⁻¹' section34VertexBallImage src f₁ w)
    (hBV : B ⊆ u ⁻¹' section34VertexBallImage src f₁ w)
    (hAB : A ∩ B ⊆ {α 0, α 1})
    (hxγ : u (α 0) ∈ section34SplitDiskImage srcBd f₁ e)
    {c : OpenPartialHomeomorph M₂ E3} (hxc : u (α 0) ∈ c.source)
    (hc : HasPLCurveCrossingOnAt
      (c '' (frontier (⋃ v, section34VertexBallImage src f₁ v) ∩ c.source))
      (c '' (J ∩ c.source))
      (c '' (section34SplitDiskImage srcBd f₁ e ∩ c.source)) (c (u (α 0)))) :
    α 0 ≠ β 0 := by
  intro hp
  have ha : IsPLHomeomorphOn (fun t => α ((1 / 2 : ℝ) * t)) (Icc 0 1) (α '' Icc 0 (1 / 2)) := by
    simpa only [sub_zero, add_zero] using isPLHomeomorphOn_comp_mul_add_Icc hα
      (a := 0) (b := 1 / 2) le_rfl (by norm_num) (by norm_num)
  have hb : IsPLHomeomorphOn (fun t => β ((1 / 2 : ℝ) * t)) (Icc 0 1) (β '' Icc 0 (1 / 2)) := by
    simpa only [sub_zero, add_zero] using isPLHomeomorphOn_comp_mul_add_Icc hβ
      (a := 0) (b := 1 / 2) le_rfl (by norm_num) (by norm_num)
  have hasub : α '' Icc 0 (1 / 2) ⊆ A :=
    (image_mono (Icc_subset_Icc le_rfl (by norm_num))).trans hα.image_eq.subset
  have hbsub : β '' Icc 0 (1 / 2) ⊆ B :=
    (image_mono (Icc_subset_Icc le_rfl (by norm_num))).trans hβ.image_eq.subset
  have hinter : α '' Icc 0 (1 / 2) ∩ β '' Icc 0 (1 / 2) = {α 0} := by
    apply Subset.antisymm
    · rintro x ⟨hxA, hxB⟩
      rcases hAB ⟨hasub hxA, hbsub hxB⟩ with h0 | h1
      · exact h0
      · obtain ⟨t, ht, htx⟩ := hxA
        have ht1 : t = 1 := hα.bijOn.injOn ⟨ht.1, ht.2.trans (by norm_num)⟩
          (by norm_num) (htx.trans h1)
        norm_num [ht1] at ht
    · rintro x rfl
      exact ⟨⟨0, by norm_num, rfl⟩, ⟨0, by norm_num, hp.symm⟩⟩
  obtain ⟨γ, hγ, _, hγmid, _⟩ := exists_isPLHomeomorphOn_Icc_concat
    (isPLHomeomorphOn_comp_one_sub ha) hb (by simpa only [mul_zero, sub_self] using hp.symm)
    (by simpa only [sub_self, mul_zero] using hinter)
  have hmid : γ (1 / 2) = α 0 := by simpa only [sub_self, mul_zero] using hγmid
  have hxC : α 0 ∈ (α '' Icc 0 (1 / 2) ∪ β '' Icc 0 (1 / 2)) \ {γ 0, γ 1} := by
    refine ⟨hmid ▸ hγ.bijOn.mapsTo (by norm_num), ?_⟩
    rintro (h0 | h1)
    · have hm0 := hγ.bijOn.injOn (by norm_num : (1 / 2 : ℝ) ∈ Icc 0 1)
        (by norm_num) (hmid.trans h0)
      norm_num at hm0
    · have hm1 := hγ.bijOn.injOn (by norm_num : (1 / 2 : ℝ) ∈ Icc 0 1)
        (by norm_num) (hmid.trans h1)
      norm_num at hm1
  exact hcut.not_model_arc_interior_on_split_disk_boundary hf₁ w e hu hγ
    (union_subset (hasub.trans hAP) (hbsub.trans hBP))
    (union_subset (hasub.trans hAJ) (hbsub.trans hBJ))
    (union_subset (hasub.trans hAV) (hbsub.trans hBV)) hxγ hxc hc hxC

end DifferentialGeometry.Topology.PiecewiseLinear
