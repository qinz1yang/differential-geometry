/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CurveCrossingGeneralPosition
import DifferentialGeometry.Topology.PiecewiseLinear.PolyhedralSphereInclusion
import DifferentialGeometry.Topology.PiecewiseLinear.Section34IntrinsicTraceCircles

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem eventually_polyhedral_trace_eq_circle
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E3 M]
    {ι : Type*} [Finite ι] {F : ι → Set M}
    (hF : ∀ i, IsPolyhedralSphere (n := 3) 1 (F i))
    (hdis : Pairwise fun i j => Disjoint (F i) (F j))
    {J : Set M} (hJ : IsPolyhedralSphere (n := 3) 1 J)
    (hJU : J ⊆ ⋃ i, F i) {x : M} (hx : x ∈ J) :
    ∀ᶠ y in 𝓝 x, y ∈ ⋃ i, F i ↔ y ∈ J := by
  have hpair : (range F).PairwiseDisjoint id := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hne
    exact hdis (fun hij => hne (congrArg F hij))
  have hmem : J ∈ range F :=
    (setOf_isPolyhedralSphere_one_subset_sUnion_eq (finite_range F)
      (by rintro _ ⟨i, rfl⟩; exact hF i) hpair).subset
        ⟨hJ, by simpa only [sUnion_range] using hJU⟩
  obtain ⟨k, hk⟩ := hmem
  let O := (⋃ i ∈ {i | i ≠ k}, F i)ᶜ
  have hO : IsOpen O :=
    ((Set.toFinite _).isClosed_biUnion fun i _ => (hF i).isCompact.isClosed).isOpen_compl
  have hxO : x ∈ O := by
    intro hbad
    obtain ⟨i, hik, hxi⟩ := mem_iUnion₂.mp hbad
    exact disjoint_left.mp (hdis hik) hxi (hk.symm ▸ hx)
  filter_upwards [hO.mem_nhds hxO] with y hyO
  constructor
  · intro hy
    obtain ⟨i, hyi⟩ := mem_iUnion.mp hy
    by_cases hik : i = k
    · exact hk ▸ hik ▸ hyi
    · exact (hyO (mem_iUnion₂.mpr ⟨i, hik, hyi⟩)).elim
  · intro hy
    exact mem_iUnion.mpr ⟨k, hk.symm ▸ hy⟩

theorem OpenPartialHomeomorph.eventually_mem_image_inter_source_of_eventually
    {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    (c : OpenPartialHomeomorph M N) {A B : Set M} {x : M} (hxc : x ∈ c.source)
    (hlocal : ∀ᶠ y in 𝓝 x, y ∈ A ↔ y ∈ B) :
    ∀ᶠ z in 𝓝 (c x), z ∈ c '' (A ∩ c.source) ↔ z ∈ c '' (B ∩ c.source) := by
  have htarget : c x ∈ c.target := c.map_source hxc
  have hloc := (c.continuousAt_symm htarget).tendsto.eventually
    (show ∀ᶠ y in 𝓝 (c.symm (c x)), y ∈ A ↔ y ∈ B from by rwa [c.left_inv hxc])
  filter_upwards [hloc, c.open_target.mem_nhds htarget] with z hz hzt
  have hmem (Q : Set M) : z ∈ c '' (Q ∩ c.source) ↔ c.symm z ∈ Q := by
    constructor
    · rintro ⟨y, hy, hyz⟩
      rw [← hyz, c.left_inv hy.2]
      exact hy.1
    · intro hy
      exact ⟨c.symm z, ⟨hy, c.map_target hzt⟩, c.right_inv hzt⟩
  exact (hmem A).trans (hz.trans (hmem B).symm)

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace E3 M₁]
  [MetricSpace M₂] [ChartedSpace E3 M₂]
  {U W : Set M₁} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁} {f₁ h : M₁ → M₂}
  {η : M₁ → ℝ} {H : Finset Ea → Set M₂} {cr : Section34VertexIndex 𝒦 𝒦' → Finset Ea}
  {fbl fblBd : Section34SimplexIndex 𝒦 3 → Set M₂}

theorem Section34FaceBallInvariants.curve_crossing_trace_circle_in_chart
    (hinv : Section34FaceBallInvariants 𝒦 𝒦' h H (section34VertexBallImage src f₁)
      (section34SplitDiskImage srcBd f₁) fbl fblBd)
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hgraph : Section34GraphFrame U W h η H 𝒦 𝒦' src cr f₁)
    (s : Section34SimplexIndex 𝒦 3) {J : Set M₂}
    (hJ : IsPolyhedralSphere (n := 3) 1 J)
    (hJT : J ⊆ fblBd s ∩ frontier (⋃ w, section34VertexBallImage src f₁ w))
    (e : Section34EdgeIndex 𝒦 𝒦') {x : M₂}
    (hx : x ∈ J ∩ section34SplitDiskImage srcBd f₁ e) :
    ∃ c ∈ (plGroupoid 3).maximalAtlas M₂, x ∈ c.source ∧
      HasPLCurveCrossingOnAt
        (c '' (frontier (⋃ w, section34VertexBallImage src f₁ w) ∩ c.source))
        (c '' (J ∩ c.source)) (c '' (section34SplitDiskImage srcBd f₁ e ∩ c.source)) (c x) := by
  obtain ⟨ι, hι, F, hF, hdis, htrace, -⟩ :=
    exists_finite_section34Trace_circles_of_crossings hcut hgraph hinv s
  have : Finite ι := hι
  have hloc := eventually_polyhedral_trace_eq_circle hF hdis hJ (hJT.trans htrace.subset) hx.1
  rw [← htrace] at hloc
  obtain ⟨-, -, -, -, -, hc, -⟩ := id hinv
  obtain ⟨c, hc, hxc, hcross⟩ := hc s e x ⟨(hJT hx.1).1, hx.2⟩
  refine ⟨c, hc, hxc, hcross.congr (Filter.Eventually.of_forall fun _ => Iff.rfl) ?_
    (Filter.Eventually.of_forall fun _ => Iff.rfl)⟩
  exact OpenPartialHomeomorph.eventually_mem_image_inter_source_of_eventually c hxc hloc

theorem Section34FaceBallInvariants.curve_crossing_face_torus_in_chart
    (hinv : Section34FaceBallInvariants 𝒦 𝒦' h H (section34VertexBallImage src f₁)
      (section34SplitDiskImage srcBd f₁) fbl fblBd)
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hgraph : Section34GraphFrame U W h η H 𝒦 𝒦' src cr f₁)
    (s : Section34SimplexIndex 𝒦 3) {J : Set M₂}
    (hJ : IsPolyhedralSphere (n := 3) 1 J)
    (hJT : J ⊆ fblBd s ∩ frontier (⋃ w, section34VertexBallImage src f₁ w))
    (e : Section34EdgeIndex 𝒦 𝒦') {x : M₂}
    (hx : x ∈ J ∩ section34SplitDiskImage srcBd f₁ e) :
    ∃ c ∈ (plGroupoid 3).maximalAtlas M₂, x ∈ c.source ∧
      HasPLCurveCrossingOnAt
        (c '' (frontier (section34FaceTorus (section34VertexBallImage src f₁) s) ∩ c.source))
        (c '' (J ∩ c.source)) (c '' (section34SplitDiskImage srcBd f₁ e ∩ c.source)) (c x) := by
  obtain ⟨c, hc, hxc, hcross⟩ :=
    hinv.curve_crossing_trace_circle_in_chart hcut hgraph s hJ hJT e hx
  have hT := section34Trace_subset_faceTorus hcut hgraph.2.2.1 hinv s (hJT hx.1)
  have hN : x ∈ ⋃ w, section34VertexBallImage src f₁ w := by
    obtain ⟨w, -, hxw⟩ := mem_section34FaceTorus_iff.mp hT
    exact mem_iUnion.mpr ⟨w, hxw⟩
  have hlocal := eventually_mem_frontier_vertexUnion_iff_faceTorus hcut hgraph.2.2.1 hinv s
    ⟨(hinv.1 s).boundary_subset (hJT hx.1).1, hN⟩
  exact ⟨c, hc, hxc, hcross.congr
    (OpenPartialHomeomorph.eventually_mem_image_inter_source_of_eventually c hxc hlocal)
    (Filter.Eventually.of_forall fun _ => Iff.rfl)
    (Filter.Eventually.of_forall fun _ => Iff.rfl)⟩

end DifferentialGeometry.Topology.PiecewiseLinear
