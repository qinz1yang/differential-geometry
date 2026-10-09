/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34IntrinsicTraceLocalization
import DifferentialGeometry.Topology.PiecewiseLinear.Section34IntrinsicTraceCrossing
import DifferentialGeometry.Topology.PiecewiseLinear.Section34IntrinsicTraceLongitude
import DifferentialGeometry.Topology.PiecewiseLinear.Section34MouthConnectivity
import DifferentialGeometry.Topology.PiecewiseLinear.Section34VertexFrontier
import DifferentialGeometry.Topology.PiecewiseLinear.TorusMeridianReturnCharts

open Set Topology
open scoped ContinuousMap

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

theorem exists_intrinsic_returning_arc_of_excess_meridian_crossings
    (hinv : Section34FaceBallInvariants 𝒦 𝒦' h H (section34VertexBallImage src f₁)
      (section34SplitDiskImage srcBd f₁) fbl fblBd)
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hgraph : Section34GraphFrame U W h η H 𝒦 𝒦' src cr f₁)
    (s : Section34SimplexIndex 𝒦 3) {P J : Set E3} {u : E3 → M₂}
    (hP : IsCombinatorialSolidTorus P) (hu : IsPLHomeomorphInto 3 u P)
    (hUP : u '' P = section34FaceTorus (section34VertexBallImage src f₁) s)
    (hJ : IsPLSphere 1 J) (hJΘ : J ⊆ frontier P)
    (hJu : IsPolyhedralSphere (n := 3) 1 (u '' J))
    (hJT : u '' J ⊆ fblBd s ∩ frontier (⋃ v, section34VertexBallImage src f₁ v))
    (hcarry : CarriesFirstHomologyOnto (u '' J)
      (section34FaceTorus (section34VertexBallImage src f₁) s))
    (hmore : ∃ e : Section34EdgeIndex 𝒦 𝒦', Section34Incident e.1 s.1 ∧
      ((u '' J) ∩ section34SplitDiskImage srcBd f₁ e).Nontrivial) :
    ∃ (w : Section34VertexIndex 𝒦 𝒦') (e : Section34EdgeIndex 𝒦 𝒦')
      (B : Set E3) (α : ℝ → E3),
      Section34Incident w.1 s.1 ∧ Section34Incident e.1 s.1 ∧
      IsPLHomeomorphOn α (Icc 0 1) B ∧ B ⊆ J ∧
      B ⊆ u ⁻¹' section34VertexBallImage srcBd f₁ w ∧
      ({α 0, α 1} : Set E3) ⊆ u ⁻¹' section34SplitDiskImage srcBd f₁ e ∧
      B ∩ u ⁻¹' (⋃ d, section34SplitDiskImage src f₁ d) = {α 0, α 1} := by
  classical
  have hf₁ := hgraph.2.2.1
  let I := {e : Section34EdgeIndex 𝒦 𝒦' // Section34Incident e.1 s.1}
  have hIfin : ({e : Section34EdgeIndex 𝒦 𝒦' | Section34Incident e.1 s.1}).Finite :=
    finite_setOf_section34Incident_graphIndex hcut.2.1 (graphSkeletonSpace 𝒦) 2 s.2.1
  let _ : Finite I := hIfin.to_subtype
  have hΘP : frontier P ⊆ P := hP.isPolyhedron.isClosed.frontier_subset
  have hJP : J ⊆ P := hJΘ.trans hΘP
  have hfront : u '' frontier P =
      frontier (section34FaceTorus (section34VertexBallImage src f₁) s) := by
    rw [hu.image_frontier_of_isCompact hP.isPolyhedron.isCompact, hUP]
  obtain ⟨M, Q, f, hf, p, _, _, _, hQ, _, hmarked, honto, -⟩ :=
    exists_primitive_intrinsic_marked_meridian_coordinates hcut hf₁ s hP hu hUP
      hJ hJΘ hcarry
  let φ := (Homeomorph.Set.prod M Q).symm.trans hf.homeomorph
  let g := Function.invFunOn u P
  have hleft : LeftInvOn g u P := hu.injOn.leftInvOn_invFunOn
  have hfiber (i : I) : range (fun m : M => (φ (m, p i) : E3)) =
      g '' section34SplitDiskImage srcBd f₁ i.1 := by
    rw [hmarked i]
    ext x
    constructor
    · rintro ⟨m, rfl⟩
      exact ⟨((m : E3), (p i : E3)), ⟨m.property, rfl⟩, rfl⟩
    · rintro ⟨⟨m, q⟩, ⟨hm, hq⟩, rfl⟩
      have hq' : q = (p i : E3) := mem_singleton_iff.mp hq
      subst q
      exact ⟨⟨m, hm⟩, rfl⟩
  have hrimP (i : I) : section34SplitDiskImage srcBd f₁ i.1 ⊆ u '' P := by
    rw [hUP]
    exact (hcut.isPLCellOn_splitDiskImage hf₁ i.1).boundary_subset.trans
      (hcut.splitDiskImage_subset_faceTorus hf₁ s i.1 i.2)
  have himage (i : I) : u '' range (fun m : M => (φ (m, p i) : E3)) =
      section34SplitDiskImage srcBd f₁ i.1 := by
    rw [hfiber]
    apply Subset.antisymm
    · rintro _ ⟨z, ⟨y, hy, rfl⟩, rfl⟩
      rwa [hu.injOn.bijOn_image.invOn_invFunOn.2 (hrimP i hy)]
    · intro y hy
      exact ⟨g y, ⟨y, hy, rfl⟩, hu.injOn.bijOn_image.invOn_invFunOn.2 (hrimP i hy)⟩
  have hcross : ∀ i : I, ∀ x ∈ (u '' J) ∩
      (u '' range (fun m : M => (φ (m, p i) : E3))),
      ∃ c : OpenPartialHomeomorph M₂ E3, x ∈ c.source ∧
        HasPLCurveCrossingOnAt (c '' ((u '' frontier P) ∩ c.source))
          (c '' ((u '' J) ∩ c.source))
          (c '' ((u '' range (fun m : M => (φ (m, p i) : E3))) ∩ c.source)) (c x) := by
    intro i x hx
    rw [himage i] at hx ⊢
    rw [hfront]
    obtain ⟨c, -, hxc, hc⟩ :=
      hinv.curve_crossing_face_torus_in_chart hcut hgraph s hJu hJT i.1 hx
    exact ⟨c, hxc, hc⟩
  have hmore' : ∃ i : I,
      (J ∩ range (fun m : M => (φ (m, p i) : E3))).Nontrivial := by
    obtain ⟨e, he, a, ha, b, hb, hab⟩ := hmore
    obtain ⟨x, hx, rfl⟩ := ha.1
    obtain ⟨y, hy, rfl⟩ := hb.1
    refine ⟨⟨e, he⟩, x, ⟨hx, ?_⟩, y, ⟨hy, ?_⟩, fun hxy => hab (congrArg u hxy)⟩
    · rw [hfiber]
      exact ⟨u x, ha.2, hleft (hJP hx)⟩
    · rw [hfiber]
      exact ⟨u y, hb.2, hleft (hJP hy)⟩
  obtain ⟨i, B, α, hα, hBJ, hends, hmeet⟩ :=
    exists_returning_arc_of_primitive_longitude_in_charts hJ hQ
      hP.isPLTorus_frontier.1 hu hΘP φ hJΘ p hcross honto hmore'
  have hends' : ({α 0, α 1} : Set E3) ⊆
      u ⁻¹' section34SplitDiskImage srcBd f₁ i.1 := by
    intro x hx
    exact (himage i).subset (mem_image_of_mem u (hends hx))
  have hBtrace : B ⊆ u ⁻¹' (fblBd s ∩ frontier (⋃ v, section34VertexBallImage src f₁ v)) :=
    fun x hx => hJT (mem_image_of_mem u (hBJ hx))
  have hBE : B ∩ u ⁻¹' (⋃ d, section34SplitDiskImage src f₁ d) = {α 0, α 1} := by
    apply Subset.antisymm
    · rintro x ⟨hxB, hxE⟩
      obtain ⟨d, hxd⟩ := mem_iUnion.mp hxE
      have hinc : Section34Incident d.1 s.1 := by
        by_contra hd
        exact disjoint_left.mp (hinv.disjoint_splitDiskImage_of_not_incident hcut hf₁ s d hd)
          ((hinv.1 s).boundary_subset (hBtrace hxB).1) hxd
      have hbd : u x ∈ section34SplitDiskImage srcBd f₁ d := by
        by_contra hx
        exact (hBtrace hxB).2.2
          (hcut.splitDiskImage_sdiff_subset_interior_vertexBallImages hf₁ d ⟨hxd, hx⟩)
      apply hmeet.subset
      refine ⟨hxB, mem_iUnion.mpr ⟨⟨d, hinc⟩, ?_⟩⟩
      rw [hfiber]
      exact ⟨u x, hbd, hleft (hJP (hBJ hxB))⟩
    · intro x hx
      exact ⟨(pair_subset (hα.bijOn.mapsTo (by norm_num))
        (hα.bijOn.mapsTo (by norm_num))) hx,
        mem_iUnion.mpr ⟨i.1, (hcut.isPLCellOn_splitDiskImage hf₁ i.1).boundary_subset
          (hends' hx)⟩⟩
  obtain ⟨w, hwinc, hw⟩ := hcut.exists_vertex_boundary_of_model_arc_avoiding_split_disks
    hf₁ s hu hUP hα (hBJ.trans hJP) (fun x hx => (hBtrace hx).2) (by
      intro d
      apply disjoint_left.mpr
      rintro x ⟨hxB, hxends⟩ hxd
      exact hxends (hBE.subset ⟨hxB, mem_iUnion.mpr ⟨d, hxd⟩⟩))
  exact ⟨w, i.1, B, α, hwinc, i.2, hα, hBJ, hw, hends', hBE⟩

end DifferentialGeometry.Topology.PiecewiseLinear
