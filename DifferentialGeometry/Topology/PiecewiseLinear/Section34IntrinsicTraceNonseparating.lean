/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CirclePartition
import DifferentialGeometry.Topology.PiecewiseLinear.Section34IntrinsicCompressionOperations
import DifferentialGeometry.Topology.PiecewiseLinear.Section34IntrinsicReturnOperations
import DifferentialGeometry.Topology.PiecewiseLinear.Section34IntrinsicSeparatingReturn
import DifferentialGeometry.Topology.PiecewiseLinear.Section34IntrinsicTraceCarrying

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

theorem exists_section34BigonSlide_of_separating_model_trace
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hgraph : Section34GraphFrame U W h η H 𝒦 𝒦' src cr f₁)
    (hinv : Section34FaceBallInvariants 𝒦 𝒦' h H (section34VertexBallImage src f₁)
      (section34SplitDiskImage srcBd f₁) fbl fblBd)
    (hnc : ∀ t, ¬ Section34Compression 𝒦 𝒦' (section34VertexBallImage srcBd f₁)
      (section34SplitDiskImage src f₁) fbl fblBd t)
    (s : Section34SimplexIndex 𝒦 3) {P J : Set E3} {u : E3 → M₂}
    (hP : IsCombinatorialSolidTorus P) (hu : IsPLHomeomorphInto 3 u P)
    (hUP : u '' P = section34FaceTorus (section34VertexBallImage src f₁) s)
    (hfront : u '' frontier P =
      frontier (section34FaceTorus (section34VertexBallImage src f₁) s))
    (hJ : IsPLSphere 1 J) (hJfr : J ⊆ frontier P) (hJF : J ⊆ u ⁻¹' fblBd s)
    (hsep : ¬ IsPreconnected (frontier P \ J)) :
    ∃ t : Section34SimplexIndex 𝒦 3,
      Section34BigonSlide 𝒦 𝒦' (section34VertexBallImage src f₁)
        (section34VertexBallImage srcBd f₁) (section34SplitDiskImage src f₁)
        (section34SplitDiskImage srcBd f₁) fblBd t := by
  have hf₁ := hgraph.2.2.1
  have hJP : J ⊆ P := hJfr.trans hP.isPolyhedron.isClosed.frontier_subset
  have hactual : u '' J ⊆ fblBd s ∩ frontier (⋃ v, section34VertexBallImage src f₁ v) := by
    rintro _ ⟨x, hx, rfl⟩
    apply (section34Trace_eq_inter_frontier_faceTorus hcut hf₁ hinv s).symm.subset
    exact ⟨hJF hx, hfront.subset ⟨x, hJfr hx, rfl⟩⟩
  obtain ⟨Δ, q, hq, hΔP, hJq⟩ :=
    hP.isPLTorus_frontier.exists_isPLHomeomorphOn_disk_of_not_isPreconnected_sdiff hJ hJfr hsep
  rcases exists_section34_vertex_circle_or_return_arc_of_model_disk hcut hgraph hinv
      s hP hu hUP hfront hJ hJF hq hJq.symm hΔP with hvertex | hreturn
  · obtain ⟨w, -, hJV⟩ := hvertex
    have hJactual : IsPolyhedralSphere (n := 3) 1 (u '' J) :=
      hJ.isPolyhedralSphere_image_of_maximalAtlas_cover hu hJP (by
        intro y hy
        obtain ⟨c, hc, hyc, -⟩ := hinv.2.2.2.2.1 s y (hactual hy)
        exact ⟨c, hc, hyc⟩)
    exact (hinv.not_circle_subset_vertexBall_of_no_compression hcut hgraph hnc
      s w hJactual hactual hJV).elim
  · obtain ⟨w, e, B, β, hws, hβ, hBJ, hBS, hends, hmeet⟩ := hreturn
    have hVP : section34VertexBallImage src f₁ w ⊆ u '' P := by
      rw [hUP]
      exact fun x hx => mem_section34FaceTorus_iff.mpr ⟨w, hws, hx⟩
    exact exists_section34BigonSlide_of_returning_model_trace_arc hcut hgraph hinv hnc
      s w e hu hVP hβ (hBJ.trans hJP) (hBJ.trans hJF) hBS
      (fun x hx => (hactual ⟨x, hBJ hx, rfl⟩).2) hends hmeet

theorem Section34FaceBallInvariants.model_trace_circle_nonseparating_of_no_operation
    (hinv : Section34FaceBallInvariants 𝒦 𝒦' h H (section34VertexBallImage src f₁)
      (section34SplitDiskImage srcBd f₁) fbl fblBd)
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hgraph : Section34GraphFrame U W h η H 𝒦 𝒦' src cr f₁)
    (hnc : ∀ t, ¬ Section34Compression 𝒦 𝒦' (section34VertexBallImage srcBd f₁)
      (section34SplitDiskImage src f₁) fbl fblBd t)
    (hnb : ∀ t, ¬ Section34BigonSlide 𝒦 𝒦' (section34VertexBallImage src f₁)
      (section34VertexBallImage srcBd f₁) (section34SplitDiskImage src f₁)
      (section34SplitDiskImage srcBd f₁) fblBd t)
    (s : Section34SimplexIndex 𝒦 3) {P J : Set E3} {u : E3 → M₂}
    (hP : IsCombinatorialSolidTorus P) (hu : IsPLHomeomorphInto 3 u P)
    (hUP : u '' P = section34FaceTorus (section34VertexBallImage src f₁) s)
    (hfront : u '' frontier P =
      frontier (section34FaceTorus (section34VertexBallImage src f₁) s))
    (hJ : IsPLSphere 1 J) (hJfr : J ⊆ frontier P) (hJF : J ⊆ u ⁻¹' fblBd s) :
    IsPreconnected (frontier P \ J) := by
  by_contra hsep
  obtain ⟨t, ht⟩ := exists_section34BigonSlide_of_separating_model_trace hcut hgraph hinv
    hnc s hP hu hUP hfront hJ hJfr hJF hsep
  exact hnb t ht

theorem Section34FaceBallInvariants.model_trace_circle_carriesFirstHomologyOnto_of_no_operation
    (hinv : Section34FaceBallInvariants 𝒦 𝒦' h H (section34VertexBallImage src f₁)
      (section34SplitDiskImage srcBd f₁) fbl fblBd)
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hgraph : Section34GraphFrame U W h η H 𝒦 𝒦' src cr f₁)
    (hnc : ∀ t, ¬ Section34Compression 𝒦 𝒦' (section34VertexBallImage srcBd f₁)
      (section34SplitDiskImage src f₁) fbl fblBd t)
    (hnb : ∀ t, ¬ Section34BigonSlide 𝒦 𝒦' (section34VertexBallImage src f₁)
      (section34VertexBallImage srcBd f₁) (section34SplitDiskImage src f₁)
      (section34SplitDiskImage srcBd f₁) fblBd t)
    (s : Section34SimplexIndex 𝒦 3) {P J : Set E3} {u : E3 → M₂}
    (hP : IsCombinatorialSolidTorus P) (hu : IsPLHomeomorphInto 3 u P)
    (hUP : u '' P = section34FaceTorus (section34VertexBallImage src f₁) s)
    (hfront : u '' frontier P =
      frontier (section34FaceTorus (section34VertexBallImage src f₁) s))
    (hJ : IsPLSphere 1 J) (hJfr : J ⊆ frontier P) (hJF : J ⊆ u ⁻¹' fblBd s) :
    CarriesFirstHomologyOnto (u '' J)
      (section34FaceTorus (section34VertexBallImage src f₁) s) := by
  have hnonsep := hinv.model_trace_circle_nonseparating_of_no_operation hcut hgraph
    hnc hnb s hP hu hUP hfront hJ hJfr hJF
  obtain ⟨n, F, -, hF, hdis, hmodel, -, -, -, -, -, k, hknonsep, hkcarry⟩ :=
    exists_positive_finite_section34Trace_model_circles hcut hgraph.2.2.1 hinv
      s hP hu hUP hfront
  have hJU : J ⊆ ⋃ i, F i := fun x hx => hmodel.subset ⟨hJfr hx, hJF hx⟩
  have hpair : (range F).PairwiseDisjoint id := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hne
    exact hdis (fun hij => hne (congrArg F hij))
  have hmem : J ∈ range F :=
    (setOf_isPLSphere_one_subset_sUnion_eq (finite_range F)
      (by rintro _ ⟨i, rfl⟩; exact hF i) hpair).subset
        ⟨hJ, by simpa only [sUnion_range] using hJU⟩
  obtain ⟨i, rfl⟩ := hmem
  by_cases hik : i = k
  · simpa only [hik] using hkcarry
  have hFfr : ∀ j, F j ⊆ frontier P := fun j x hx =>
    (hmodel.symm.subset (mem_iUnion.mpr ⟨j, hx⟩)).1
  have hfrP : frontier P ⊆ P := hP.isPolyhedron.isClosed.frontier_subset
  exact hP.isPLTorus_frontier.carriesFirstHomologyOnto_image_of_disjoint
    (hF k) (hFfr k) (hF i) (hFfr i) (hdis hik) hknonsep hnonsep
    (hu.continuousOn.mono hfrP) (hu.injOn.mono hfrP)
    ((image_mono hfrP).trans hUP.subset) hkcarry

end DifferentialGeometry.Topology.PiecewiseLinear
