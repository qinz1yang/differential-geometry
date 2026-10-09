/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Connected.FinitePartition
import DifferentialGeometry.Topology.PiecewiseLinear.PLModelCircleCrosscut
import DifferentialGeometry.Topology.PiecewiseLinear.Section34IntrinsicSeamArcSides
import DifferentialGeometry.Topology.PiecewiseLinear.Section34IntrinsicCompressionOperations
import DifferentialGeometry.Topology.PiecewiseLinear.Section34ReturnDiskBoundary

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace E3 M₁]
  [MetricSpace M₂] [ChartedSpace E3 M₂]
  {U W : Set M₁} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁} {f₁ h : M₁ → M₂}
  {η : M₁ → ℝ} {H : Finset Ea → Set M₂} {cr : Section34VertexIndex 𝒦 𝒦' → Finset Ea}
  {fbl fblBd : Section34SimplexIndex 𝒦 3 → Set M₂}

theorem exists_section34_model_trace_crosscut_in_return_disk
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hgraph : Section34GraphFrame U W h η H 𝒦 𝒦' src cr f₁)
    (hinv : Section34FaceBallInvariants 𝒦 𝒦' h H (section34VertexBallImage src f₁)
      (section34SplitDiskImage srcBd f₁) fbl fblBd)
    (hnc : ∀ t, ¬ Section34Compression 𝒦 𝒦' (section34VertexBallImage srcBd f₁)
      (section34SplitDiskImage src f₁) fbl fblBd t)
    (s : Section34SimplexIndex 𝒦 3) (w : Section34VertexIndex 𝒦 𝒦')
    (e : Section34EdgeIndex 𝒦 𝒦') {P B R D : Set E3} {u : E3 → M₂}
    {β : ℝ → E3} {q : (Fin 3 → ℝ) → E3}
    (hu : IsPLHomeomorphInto 3 u P) (hβ : IsPLHomeomorphOn β (Icc 0 1) B)
    (hBF : B ⊆ u ⁻¹' fblBd s) (hR : R ⊆ u ⁻¹' section34SplitDiskImage srcBd f₁ e)
    (hBR : B ∩ R = {β 0, β 1})
    (hq : IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D)
    (hqB : q '' stdSimplexBoundary 2 = B ∪ R) (hDP : D ⊆ P)
    (hDloc : D ⊆ u ⁻¹' (section34VertexBallImage srcBd f₁ w ∩
      frontier (⋃ v, section34VertexBallImage src f₁ v)))
    (hother : ∀ d : Section34EdgeIndex 𝒦 𝒦', d ≠ e →
      Disjoint D (u ⁻¹' section34SplitDiskImage src f₁ d))
    (hdirty : ((D \ (B ∪ R)) ∩ ⋃ t : Section34SimplexIndex 𝒦 3,
      u ⁻¹' fblBd t).Nonempty) :
    ∃ (t : Section34SimplexIndex 𝒦 3) (A : Set E3) (α : ℝ → E3),
      IsPLHomeomorphOn α (Icc 0 1) A ∧ A ⊆ u ⁻¹' fblBd t ∧ A ⊆ D ∧
      A ∩ (B ∪ R) = {α 0, α 1} ∧ ({α 0, α 1} : Set E3) ⊆ R \ {β 0, β 1} := by
  classical
  have hf₁ := hgraph.2.2.1
  have hV := hcut.isPLCellOn_vertexBallImage hf₁ w
  have hDpoly : IsPolyhedron D := (IsPLBall.isPolyhedron ⟨q, hq⟩)
  have hboundaryD : B ∪ R ⊆ D := by
    rw [← hqB, ← hq.image_eq]
    exact image_mono fun x hx => hx.1
  have hBD : B ⊆ D := subset_union_left.trans hboundaryD
  have hRD : R ⊆ D := subset_union_right.trans hboundaryD
  have hBP : B ⊆ P := hBD.trans hDP
  have hRP : R ⊆ P := hRD.trans hDP
  have hBN : B ⊆ u ⁻¹' frontier (⋃ v, section34VertexBallImage src f₁ v) :=
    fun x hx => (hDloc (hBD hx)).2
  obtain ⟨x, hxD, hxF⟩ := hdirty
  obtain ⟨t, hxt⟩ := mem_iUnion.mp hxF
  obtain ⟨Q, v, hQ, hv, himageQ, hfrontQ⟩ :=
    exists_section34FaceTorus_intrinsic_model hcut hgraph t
  obtain ⟨ι, hι, F, hF, -, hmodeltrace, hactual, hdis, htrace, -⟩ :=
    exists_finite_section34Trace_model_circles hcut hf₁ hinv t hQ hv himageQ hfrontQ
  let _ := hι
  have hFQ : ∀ i, F i ⊆ Q := fun i y hy => hQ.isPolyhedron.isClosed.frontier_subset
    ((hmodeltrace.symm.subset (mem_iUnion.mpr ⟨i, hy⟩)).1)
  have hFT : ∀ i, v '' F i ⊆ fblBd t ∩
      frontier (⋃ z, section34VertexBallImage src f₁ z) :=
    fun i y hy => htrace.symm.subset (mem_iUnion.mpr ⟨i, hy⟩)
  obtain ⟨j, hxj⟩ := mem_iUnion.mp (htrace.subset ⟨hxt, (hDloc hxD.1).2⟩)
  have hjno : ¬ v '' F j ⊆ u '' D := by
    intro hjD
    exact hinv.not_circle_subset_vertexBall_of_no_compression hcut hgraph hnc t w
      (hactual j) (hFT j)
      (hjD.trans (image_subset_iff.mpr fun y hy => hV.boundary_subset (hDloc hy).1))
  have hrel : Disjoint (v '' F j) (u '' B) ∨ u '' B ⊆ v '' F j := by
    by_cases hts : t = s
    · have hBU : u '' B ⊆ ⋃ i, v '' F i := by
        rintro y ⟨z, hz, rfl⟩
        exact htrace.subset ⟨hts.symm ▸ hBF hz, hBN hz⟩
      have hpair : (range (fun i => v '' F i)).PairwiseDisjoint id := by
        rintro _ ⟨i, rfl⟩ _ ⟨k, rfl⟩ hik
        exact hdis (fun heq => hik (congrArg (fun i => v '' F i) heq))
      have hBconn : IsConnected B :=
        ((isPLBall_Icc (by norm_num : (0 : ℝ) < 1)).of_isPLHomeomorphOn hβ).isConnected
      have hBc : IsConnected (u '' B) := hBconn.image u (hu.continuousOn.mono hBP)
      obtain ⟨G, ⟨hGF, hBG⟩, -⟩ :=
        existsUnique_subset_of_isConnected_of_finite_closed_partition hBc
          (finite_range (fun i => v '' F i))
          (by rintro _ ⟨i, rfl⟩; exact (hactual i).isCompact.isClosed) hpair
          (by simpa only [sUnion_range] using hBU)
      obtain ⟨i, rfl⟩ := hGF
      by_cases hji : j = i
      · exact Or.inr (hji.symm ▸ hBG)
      · exact Or.inl ((hdis hji).mono_right hBG)
    · refine Or.inl (disjoint_left.mpr ?_)
      rintro y hyF ⟨z, hz, rfl⟩
      exact (hFT j hyF).2.2 (hinv.2.2.2.1 t s hts
        ⟨(hinv.1 t).boundary_subset (hFT j hyF).1,
          (hinv.1 s).boundary_subset (hBF hz)⟩)
  have hfinite : (v '' F j ∩ u '' R).Finite :=
    (hinv.2.2.2.2.2.2.2.1 t).subset (by
      rintro y ⟨hyF, z, hz, rfl⟩
      exact ⟨(hFT j hyF).1, mem_iUnion.mpr ⟨e, hR hz⟩⟩)
  have hcell : IsPLCellOn 2 (u '' D) (u '' (B ∪ R)) :=
    ⟨D, q, u, hq, hu.mono_of_polyhedron hDpoly hDP, rfl, by rw [hqB]⟩
  have hβ0 : β 0 ∈ B := hβ.bijOn.mapsTo (by norm_num)
  have hβ0R : β 0 ∈ R := (hBR.symm.subset (by simp : β 0 ∈ {β 0, β 1})).2
  have hwe : w.1 ⊆ e.1 := hcut.subset_of_mem_splitDiskImage hf₁.injOn
    ((hcut.isPLCellOn_splitDiskImage hf₁ e).boundary_subset (hR hβ0R))
    (hV.boundary_subset (hDloc (hBD hβ0)).1)
  have hboundary : u '' D ∩ closure
      (frontier (⋃ z, section34VertexBallImage src f₁ z) \ u '' D) = u '' (B ∪ R) :=
    hcut.inter_closure_frontier_sdiff_return_disk hf₁ w e hwe hcell
      (image_subset_iff.mpr hDloc) (fun d hd => disjoint_left.mpr (by
        rintro y ⟨z, hz, rfl⟩ hy
        exact disjoint_left.mp (hother d hd) hz hy))
  have hxnot : u x ∉ u '' (B ∪ R) := by
    rintro ⟨z, hz, hzx⟩
    exact hxD.2 (hu.injOn (hboundaryD.trans hDP hz) (hDP hxD.1) hzx ▸ hz)
  obtain ⟨A, α, hα, hAF, hAD, hAL, hαR⟩ :=
    exists_model_circle_crosscut_ending_on_boundary_arc hu
      (hv.mono_of_polyhedron (hF j).isPolyhedron (hFQ j)) (hF j)
      (fun y hy => (hFT j hy).2) hDpoly hDP hboundary hβ hBP hRP hBR hrel hfinite
      hjno ⟨u x, hxj, ⟨x, hxD.1, rfl⟩, hxnot⟩
  have hAP : A ⊆ P := hAD.trans hDP
  have hcorner : ∀ γ : ℝ → E3, IsPLHomeomorphOn γ (Icc 0 1) A →
      ({γ 0, γ 1} : Set E3) = {α 0, α 1} → γ 0 ∉ ({β 0, β 1} : Set E3) := by
    intro γ hγ hγends hp
    have hpA : γ 0 ∈ A := hγ.bijOn.mapsTo (by norm_num)
    have hpF : u (γ 0) ∈ v '' F j := hAF ⟨γ 0, hpA, rfl⟩
    have hpB : γ 0 ∈ B := (pair_subset (hβ.bijOn.mapsTo (by norm_num))
      (hβ.bijOn.mapsTo (by norm_num))) hp
    have hBFj : u '' B ⊆ v '' F j := hrel.resolve_left fun hd =>
      disjoint_left.mp hd hpF ⟨γ 0, hpB, rfl⟩
    have hpγ := hR (hαR (hγends.subset (by simp : γ 0 ∈ {γ 0, γ 1})))
    obtain ⟨c, -, hpc, hc⟩ := hinv.2.2.2.2.2.1 t e (u (γ 0))
      ⟨(hFT j hpF).1, hpγ⟩
    have hAB : A ∩ B ⊆ {γ 0, γ 1} :=
      fun y hy => hγends.symm.subset (hAL.subset ⟨hy.1, Or.inl hy.2⟩)
    have hAJ : A ⊆ u ⁻¹' (fblBd t ∩
        frontier (⋃ z, section34VertexBallImage src f₁ z)) :=
      fun y hy => hFT j (hAF ⟨y, hy, rfl⟩)
    have hBJ : B ⊆ u ⁻¹' (fblBd t ∩
        frontier (⋃ z, section34VertexBallImage src f₁ z)) :=
      fun y hy => hFT j (hBFj ⟨y, hy, rfl⟩)
    have hAV : A ⊆ u ⁻¹' section34VertexBallImage src f₁ w :=
      fun y hy => hV.boundary_subset (hDloc (hAD hy)).1
    have hBV : B ⊆ u ⁻¹' section34VertexBallImage src f₁ w :=
      fun y hy => hV.boundary_subset (hDloc (hBD hy)).1
    rcases hp with hp0 | hp1
    · exact hcut.ne_initial_points_of_model_arcs_in_vertex_ball hf₁ w e hu hγ hβ
        hAP hBP hAJ hBJ hAV hBV hAB hpγ hpc hc hp0
    · exact hcut.ne_initial_points_of_model_arcs_in_vertex_ball hf₁ w e hu hγ
        (isPLHomeomorphOn_comp_one_sub hβ) hAP hBP hAJ hBJ hAV hBV hAB hpγ hpc hc
        (by simpa only [sub_zero, mem_singleton_iff] using hp1)
  have h0 := hcorner α hα rfl
  have h1 : α 1 ∉ ({β 0, β 1} : Set E3) := by
    have hr := hcorner (fun t => α (1 - t)) (isPLHomeomorphOn_comp_one_sub hα)
      (by simp only [sub_zero, sub_self, pair_comm])
    simpa only [sub_zero] using hr
  exact ⟨t, A, α, hα, (fun y hy => (hFT j (hAF ⟨y, hy, rfl⟩)).1), hAD, hAL,
    pair_subset ⟨hαR (by simp), h0⟩ ⟨hαR (by simp), h1⟩⟩

end DifferentialGeometry.Topology.PiecewiseLinear
