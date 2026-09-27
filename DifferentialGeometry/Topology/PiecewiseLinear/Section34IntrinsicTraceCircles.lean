/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ModelLineCharts
import DifferentialGeometry.Topology.PiecewiseLinear.PLModelIntersection
import DifferentialGeometry.Topology.PiecewiseLinear.PolyhedralSphereImage
import DifferentialGeometry.Topology.PiecewiseLinear.RegularFrontierLineChart
import DifferentialGeometry.Topology.PiecewiseLinear.Section34FaceTorusFrontier
import DifferentialGeometry.Topology.PiecewiseLinear.Section34IntrinsicFaceTorusModel

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

omit [FiniteDimensional ℝ Ea] in
theorem exists_finite_section34Trace_model_circles
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hf₁ : IsPLHomeomorphInto 3 f₁ (section34CutNeighborhood src))
    (hinv : Section34FaceBallInvariants 𝒦 𝒦' h H (section34VertexBallImage src f₁)
      (section34SplitDiskImage srcBd f₁) fbl fblBd)
    (s : Section34SimplexIndex 𝒦 3) {P : Set E3} {u : E3 → M₂}
    (hP : IsCombinatorialSolidTorus P) (hu : IsPLHomeomorphInto 3 u P)
    (himage : u '' P = section34FaceTorus (section34VertexBallImage src f₁) s)
    (hfront : u '' frontier P =
      frontier (section34FaceTorus (section34VertexBallImage src f₁) s)) :
    ∃ (ι : Type) (_ : Finite ι) (J : ι → Set E3),
      (∀ i, IsPLSphere 1 (J i)) ∧ (Pairwise fun i j => Disjoint (J i) (J j)) ∧
      frontier P ∩ u ⁻¹' fblBd s = ⋃ i, J i ∧
      (∀ i, IsPolyhedralSphere (n := 3) 1 (u '' J i)) ∧
      (Pairwise fun i j => Disjoint (u '' J i) (u '' J j)) ∧
      fblBd s ∩ frontier (⋃ w, section34VertexBallImage src f₁ w) = ⋃ i, u '' J i ∧
      fblBd s ∩ frontier
        (section34FaceTorus (section34VertexBallImage src f₁) s) = ⋃ i, u '' J i := by
  let S := frontier P ∩ u ⁻¹' fblBd s
  let T := section34FaceTorus (section34VertexBallImage src f₁) s
  let N := ⋃ w, section34VertexBallImage src f₁ w
  have hSP : S ⊆ P := inter_subset_left.trans hP.isPolyhedron.isClosed.frontier_subset
  have hS : IsPolyhedron S := (hinv.1 s).isPolyhedron_inter_preimage_boundary hu
    hP.isPolyhedron.frontier hP.isPolyhedron.isClosed.frontier_subset
  have hTc : IsClosed T := by
    change IsClosed (section34FaceTorus (section34VertexBallImage src f₁) s)
    rw [← himage]
    exact (hP.isPolyhedron.isCompact.image_of_continuousOn hu.continuousOn).isClosed
  have hTN : T ⊆ N := by
    intro z hz
    obtain ⟨w, -, hzw⟩ := mem_section34FaceTorus_iff.mp hz
    exact mem_iUnion.mpr ⟨w, hzw⟩
  have hSN : u '' S = fblBd s ∩ frontier N := by
    change u '' (frontier P ∩ u ⁻¹' fblBd s) = _
    rw [image_inter_preimage, hfront, inter_comm]
    exact (section34Trace_eq_inter_frontier_faceTorus hcut hf₁ hinv s).symm
  have hST : u '' S = fblBd s ∩ frontier T := by
    change u '' (frontier P ∩ u ⁻¹' fblBd s) = _
    rw [image_inter_preimage, hfront, inter_comm]
  have hcharts : ∀ y ∈ u '' S, ∃ e : OpenPartialHomeomorph M₂ (ℝ × ℝ × ℝ),
      y ∈ e.source ∧ e y = 0 ∧ ∀ z ∈ e.source, z ∈ u '' S ↔ (e z).2 = 0 := by
    intro y hy
    have hyN : y ∈ fblBd s ∩ frontier N := hSN ▸ hy
    have hyT : y ∈ fblBd s ∩ frontier T := hST ▸ hy
    obtain ⟨c, -, hyc, hcross⟩ := hinv.2.2.2.2.1 s y hyN
    have hyFT : y ∈ fbl s ∩ N :=
      ⟨(hinv.1 s).boundary_subset hyT.1, hTN (hTc.frontier_subset hyT.2)⟩
    have hlocal := eventually_mem_frontier_vertexUnion_iff_faceTorus hcut hf₁ hinv s hyFT
    have himg (A : Set M₂) : c.IsImage A (c '' (A ∩ c.source)) := by
      intro z hz
      constructor
      · rintro ⟨w, ⟨hwA, hwc⟩, hwz⟩
        exact c.injOn hwc hz hwz ▸ hwA
      · intro hzA
        exact ⟨z, ⟨hzA, hz⟩, rfl⟩
    have hcrossT : HasPLCrossingAt (c '' (frontier (fbl s) ∩ c.source))
        (c '' (frontier T ∩ c.source)) (c y) := by
      rw [← (hinv.1 s).boundary_eq_frontier]
      refine hcross.congr (Filter.Eventually.of_forall fun _ => Iff.rfl) ?_
      have htend := (c.continuousAt_symm (c.map_source hyc)).tendsto
      have hevent : ∀ᶠ z in 𝓝 (c y), c.symm z ∈ frontier N ↔
          c.symm z ∈ frontier T := by
        exact htend.eventually (show ∀ᶠ z in 𝓝 (c.symm (c y)),
          z ∈ frontier N ↔ z ∈ frontier T from by rwa [c.left_inv hyc])
      filter_upwards [c.open_target.mem_nhds (c.map_source hyc), hevent] with z hzt hz
      exact ((himg (frontier N)).symm_apply_mem_iff hzt).symm.trans
        (hz.trans ((himg (frontier T)).symm_apply_mem_iff hzt))
    have hyregT : y ∈ closure (interior T) := by
      obtain ⟨w, hws, hyw⟩ := mem_section34FaceTorus_iff.mp (hTc.frontier_subset hyT.2)
      have hVT : section34VertexBallImage src f₁ w ⊆ T := fun z hz =>
        mem_section34FaceTorus_iff.mpr ⟨w, hws, hz⟩
      exact closure_mono (interior_mono hVT)
        ((hcut.isPLCellOn_vertexBallImage hf₁ w).subset_closure_interior hyw)
    obtain ⟨e, hye, hey, hline⟩ :=
      HasPLCrossingAt.exists_lineChart_of_regular_frontiers_of_chart hyc hcrossT
        (hinv.1 s).isCompact.isClosed hTc
        ((hinv.1 s).subset_closure_interior ((hinv.1 s).boundary_subset hyT.1)) hyregT
    refine ⟨e, hye, hey, fun z hz => ?_⟩
    rw [hST, mem_inter_iff, (hinv.1 s).boundary_eq_frontier,
      (hline z hz).1, (hline z hz).2]
    exact ⟨fun h => Prod.ext h.2 h.1, fun h =>
      ⟨congrArg Prod.snd h, congrArg Prod.fst h⟩⟩
  obtain ⟨ι, hι, J, hJ, hdis, hcover⟩ :=
    hu.exists_model_circles_of_image_lineCharts hS hSP hcharts
  have hJS : ∀ i, J i ⊆ S := fun i => hcover.symm ▸ subset_iUnion J i
  have hJP : ∀ i, J i ⊆ P := fun i => (hJS i).trans hSP
  have hactual : ∀ i, IsPolyhedralSphere (n := 3) 1 (u '' J i) := by
    intro i
    apply (hJ i).isPolyhedralSphere_image_of_maximalAtlas_cover hu (hJP i)
    intro y hy
    have hyN : y ∈ fblBd s ∩ frontier N := hSN ▸ image_mono (hJS i) hy
    obtain ⟨c, hc, hyc, -⟩ := hinv.2.2.2.2.1 s y hyN
    exact ⟨c, hc, hyc⟩
  have hactualdis : Pairwise fun i j => Disjoint (u '' J i) (u '' J j) := by
    intro i j hij
    apply disjoint_left.mpr
    rintro y ⟨x, hxi, hxy⟩ ⟨z, hzj, hzy⟩
    have hxz : x = z := hu.injOn (hJP i hxi) (hJP j hzj) (hxy.trans hzy.symm)
    exact disjoint_left.mp (hdis hij) hxi (hxz.symm ▸ hzj)
  have himagecover : u '' S = ⋃ i, u '' J i := by rw [hcover, image_iUnion]
  exact ⟨ι, hι, J, hJ, hdis, hcover, hactual, hactualdis,
    hSN.symm.trans himagecover, hST.symm.trans himagecover⟩

theorem exists_finite_section34Trace_circles_of_crossings
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hgraph : Section34GraphFrame U W h η H 𝒦 𝒦' src cr f₁)
    (hinv : Section34FaceBallInvariants 𝒦 𝒦' h H (section34VertexBallImage src f₁)
      (section34SplitDiskImage srcBd f₁) fbl fblBd) (s : Section34SimplexIndex 𝒦 3) :
    ∃ (ι : Type) (_ : Finite ι) (J : ι → Set M₂),
      (∀ i, IsPolyhedralSphere (n := 3) 1 (J i)) ∧
      (Pairwise fun i j => Disjoint (J i) (J j)) ∧
      fblBd s ∩ frontier (⋃ w, section34VertexBallImage src f₁ w) = ⋃ i, J i ∧
      fblBd s ∩ frontier
        (section34FaceTorus (section34VertexBallImage src f₁) s) = ⋃ i, J i := by
  obtain ⟨P, u, hP, hu, himage, hfront⟩ :=
    exists_section34FaceTorus_intrinsic_model hcut hgraph s
  obtain ⟨ι, hι, J, -, -, -, hJ, hdis, hN, hT⟩ :=
    exists_finite_section34Trace_model_circles hcut hgraph.2.2.1 hinv s hP hu himage hfront
  exact ⟨ι, hι, fun i => u '' J i, hJ, hdis, hN, hT⟩

end DifferentialGeometry.Topology.PiecewiseLinear
