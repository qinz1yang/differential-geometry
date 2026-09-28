/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ModelCurveCrossingDiskInterior
import DifferentialGeometry.Topology.PiecewiseLinear.OutermostCircleCrosscutTopology
import DifferentialGeometry.Topology.PiecewiseLinear.Section34IntrinsicMeridianSystem
import DifferentialGeometry.Topology.PiecewiseLinear.Section34IntrinsicTraceCrossing
import DifferentialGeometry.Topology.PiecewiseLinear.Section34IntrinsicTraceLocalization
import DifferentialGeometry.Topology.PiecewiseLinear.Section34MouthConnectivity

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

open Classical in
theorem exists_section34_vertex_circle_or_return_arc_of_model_disk
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hgraph : Section34GraphFrame U W h η H 𝒦 𝒦' src cr f₁)
    (hinv : Section34FaceBallInvariants 𝒦 𝒦' h H (section34VertexBallImage src f₁)
      (section34SplitDiskImage srcBd f₁) fbl fblBd)
    (s : Section34SimplexIndex 𝒦 3) {P J Δ : Set E3} {u : E3 → M₂}
    (hP : IsCombinatorialSolidTorus P) (hu : IsPLHomeomorphInto 3 u P)
    (hUP : u '' P = section34FaceTorus (section34VertexBallImage src f₁) s)
    (hfront : u '' frontier P =
      frontier (section34FaceTorus (section34VertexBallImage src f₁) s))
    (hJ : IsPLSphere 1 J) (hJF : J ⊆ u ⁻¹' fblBd s)
    {q : (Fin 3 → ℝ) → E3} (hq : IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Δ)
    (hqJ : q '' stdSimplexBoundary 2 = J) (hΔP : Δ ⊆ frontier P) :
    (∃ w : Section34VertexIndex 𝒦 𝒦', Section34Incident w.1 s.1 ∧
      u '' J ⊆ section34VertexBallImage src f₁ w) ∨
    ∃ (w : Section34VertexIndex 𝒦 𝒦') (e : Section34EdgeIndex 𝒦 𝒦')
      (B : Set E3) (β : ℝ → E3), Section34Incident w.1 s.1 ∧
      IsPLHomeomorphOn β (Icc 0 1) B ∧ B ⊆ J ∧
      B ⊆ u ⁻¹' section34VertexBallImage srcBd f₁ w ∧
      ({β 0, β 1} : Set E3) ⊆ u ⁻¹' section34SplitDiskImage srcBd f₁ e ∧
      B ∩ u ⁻¹' (⋃ d, section34SplitDiskImage src f₁ d) = {β 0, β 1} := by
  have hf₁ := hgraph.2.2.1
  have hfrP : frontier P ⊆ P := hP.isPolyhedron.isClosed.frontier_subset
  have hJΔ : J ⊆ Δ := by
    rw [← hqJ, ← hq.image_eq]
    exact image_mono fun x hx => hx.1
  have hJfr : J ⊆ frontier P := hJΔ.trans hΔP
  have hJP : J ⊆ P := hJfr.trans hfrP
  have hactual : u '' J ⊆ fblBd s ∩ frontier (⋃ v, section34VertexBallImage src f₁ v) := by
    rintro _ ⟨x, hx, rfl⟩
    apply (section34Trace_eq_inter_frontier_faceTorus hcut hf₁ hinv s).symm.subset
    exact ⟨hJF hx, hfront.subset ⟨x, hJfr hx, rfl⟩⟩
  have hJactual : IsPolyhedralSphere (n := 3) 1 (u '' J) :=
    hJ.isPolyhedralSphere_image_of_maximalAtlas_cover hu hJP (by
      intro y hy
      obtain ⟨c, hc, hyc, -⟩ := hinv.2.2.2.2.1 s y (hactual hy)
      exact ⟨c, hc, hyc⟩)
  let g := Function.invFunOn u P
  have hleft : LeftInvOn g u P := hu.injOn.leftInvOn_invFunOn
  have hright : RightInvOn g u (u '' P) := hu.injOn.bijOn_image.invOn_invFunOn.2
  let I := {e : Section34EdgeIndex 𝒦 𝒦' // Section34Incident e.1 s.1}
  let G : I → Set E3 := fun e => g '' section34SplitDiskImage srcBd f₁ e.1
  have hmer := fun e : I => hcut.intrinsic_splitDisk_meridian hf₁ s hu hUP e.1 e.2
  have hG : ∀ i, IsPLSphere 1 (G i) := by
    intro i
    obtain ⟨r, hr, hrG⟩ := (hmer i).1
    rw [show G i = r '' stdSimplexBoundary 2 from hrG]
    exact hr.isPLSphere_image_stdSimplexBoundary
  have hGfr : ∀ i, G i ⊆ frontier P :=
    fun i x hx => (((hmer i).2.2.1).symm.subset hx).1
  have hGP : ∀ i, G i ⊆ P := fun i => (hGfr i).trans hfrP
  have hEUP (i : I) : section34SplitDiskImage srcBd f₁ i.1 ⊆ u '' P := by
    rw [hUP]
    exact (hcut.isPLCellOn_splitDiskImage hf₁ i.1).boundary_subset.trans
      (hcut.splitDiskImage_subset_faceTorus hf₁ s i.1 i.2)
  have hGimage : ∀ i, u '' G i = section34SplitDiskImage srcBd f₁ i.1 := by
    intro i
    change u '' (g '' section34SplitDiskImage srcBd f₁ i.1) = _
    rw [image_image]
    calc
      (u ∘ g) '' section34SplitDiskImage srcBd f₁ i.1 =
          id '' section34SplitDiskImage srcBd f₁ i.1 :=
        image_congr fun y hy => hright (hEUP i hy)
      _ = _ := image_id _
  have hinc : ∀ x ∈ J, ∀ e : Section34EdgeIndex 𝒦 𝒦',
      u x ∈ section34SplitDiskImage src f₁ e → Section34Incident e.1 s.1 := by
    intro x hx e hxe
    by_contra he
    exact disjoint_left.mp (hinv.disjoint_splitDiskImage_of_not_incident hcut hf₁ s e he)
      ((hinv.1 s).boundary_subset (hJF hx)) hxe
  have hγ : ∀ x ∈ J, ∀ e : Section34EdgeIndex 𝒦 𝒦',
      (he : Section34Incident e.1 s.1) → u x ∈ section34SplitDiskImage src f₁ e →
      x ∈ G ⟨e, he⟩ := by
    intro x hx e he hxe
    exact ((hmer ⟨e, he⟩).2.2.1).subset
      ⟨hJfr hx, u x, hxe, hleft (hJP hx)⟩
  by_cases hmeet : (J ∩ ⋃ i, G i).Nonempty
  · right
    have hno : ∀ i, ¬ G i ⊆ Δ := by
      intro i hi
      obtain ⟨D, r, hr, hDΔ, hrG⟩ := hq.exists_disk_subset_of_circle_subset (hG i) hi
      exact (hmer i).2.2.2.2.2 ⟨D, r, hr, hDΔ.trans hΔP, hrG.symm⟩
    have hGdis : Pairwise fun i j => Disjoint (G i) (G j) := by
      intro i j hij
      apply disjoint_left.mpr
      intro x hxi hxj
      have hne : i.1 ≠ j.1 := fun heq => hij (Subtype.ext heq)
      exact disjoint_left.mp (hcut.disjoint_splitDiskImage hf₁.injOn hne)
        ((hcut.isPLCellOn_splitDiskImage hf₁ i.1).boundary_subset
          ((hGimage i).subset ⟨x, hxi, rfl⟩))
        ((hcut.isPLCellOn_splitDiskImage hf₁ j.1).boundary_subset
          ((hGimage j).subset ⟨x, hxj, rfl⟩))
    have hfinite := hinv.2.2.2.2.2.2.2.1 s
    have hfin : (J ∩ ⋃ i, G i).Finite := by
      apply Set.Finite.of_finite_image (f := u) (hfinite.subset ?_)
        (hu.injOn.mono (inter_subset_left.trans hJP))
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨i, hxi⟩ := mem_iUnion.mp hx.2
      exact ⟨hJF hx.1, mem_iUnion.mpr ⟨i.1, (hGimage i).subset ⟨x, hxi, rfl⟩⟩⟩
    obtain ⟨L, hLfin, hL, -, hLfr⟩ := hP.isPLTorus_frontier.exists_combinatorial_triangulation
    let _ : Finite L.faces := hLfin.to_subtype
    have hacc : ∀ i, ∀ x ∈ J ∩ G i, ∀ (D : Set E3) (r : (Fin 3 → ℝ) → E3),
        IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D → D ⊆ L.space →
        (∀ᶠ y in 𝓝 x, y ∈ r '' stdSimplexBoundary 2 ↔ y ∈ J) →
        x ∈ closure (G i ∩ (D \ r '' stdSimplexBoundary 2)) := by
      intro i x hx D r hr hDL hlocal
      obtain ⟨c, -, hxc, hc⟩ := hinv.curve_crossing_face_torus_in_chart hcut hgraph s
        hJactual hactual i.1 ⟨⟨x, hx.1, rfl⟩, (hGimage i).subset ⟨x, hx.2, rfl⟩⟩
      have hc' : HasPLCurveCrossingOnAt (c '' ((u '' frontier P) ∩ c.source))
          (c '' ((u '' G i) ∩ c.source)) (c '' ((u '' J) ∩ c.source)) (c (u x)) := by
        rw [hfront, hGimage]
        exact hc.swap
      exact HasPLCurveCrossingOnAt.mem_closure_inter_model_diskInterior_in_chart hu
        hP.isPolyhedron.isCompact hfrP (hGP i) hJP (hJP hx.1) c hxc hc' hr
          (hDL.trans hLfr.subset) hlocal
    obtain ⟨i, B, β, hβ, hBJ, hends, hBG⟩ :=
      exists_boundary_arc_avoiding_disjoint_circles_of_disk_accumulation L hL hq hqJ
        (hΔP.trans hLfr.symm.subset) hJ hG
        (fun i => (hGfr i).trans hLfr.symm.subset) hGdis hfin hno hacc hmeet
    have hBE : B ∩ u ⁻¹' (⋃ e, section34SplitDiskImage src f₁ e) = {β 0, β 1} := by
      apply Subset.antisymm
      · rintro x ⟨hxB, hxE⟩
        obtain ⟨e, hxe⟩ := mem_iUnion.mp hxE
        exact hBG.subset ⟨hxB, mem_iUnion.mpr
          ⟨⟨e, hinc x (hBJ hxB) e hxe⟩, hγ x (hBJ hxB) e (hinc x (hBJ hxB) e hxe) hxe⟩⟩
      · intro x hx
        exact ⟨(pair_subset (hβ.bijOn.mapsTo (by norm_num))
          (hβ.bijOn.mapsTo (by norm_num))) hx,
          mem_iUnion.mpr ⟨i.1, (hcut.isPLCellOn_splitDiskImage hf₁ i.1).boundary_subset
            ((hGimage i).subset ⟨x, hends hx, rfl⟩)⟩⟩
    obtain ⟨w, hws, hw⟩ := hcut.exists_vertex_boundary_of_model_arc_avoiding_split_disks
      hf₁ s hu hUP hβ (hBJ.trans hJP)
      (fun x hx => (hactual ⟨x, hBJ hx, rfl⟩).2) (by
        intro e
        apply disjoint_left.mpr
        rintro x ⟨hxB, hxends⟩ hxe
        exact hxends (hBE.subset ⟨hxB, mem_iUnion.mpr ⟨e, hxe⟩⟩))
    exact ⟨w, i.1, B, β, hws, hβ, hBJ, hw,
      fun x hx => (hGimage i).subset ⟨x, hends hx, rfl⟩, hBE⟩
  · left
    have hJE : ∀ e : Section34EdgeIndex 𝒦 𝒦',
        Disjoint (u '' J) (section34SplitDiskImage src f₁ e) := by
      intro e
      apply disjoint_left.mpr
      rintro _ ⟨x, hx, rfl⟩ hxe
      exact hmeet ⟨x, hx, mem_iUnion.mpr
        ⟨⟨e, hinc x hx e hxe⟩, hγ x hx e (hinc x hx e hxe) hxe⟩⟩
    exact hcut.exists_vertex_ball_of_connected_subset_faceTorus hf₁ s hJactual.isConnected
      ((image_mono hJP).trans hUP.subset) hJE

end DifferentialGeometry.Topology.PiecewiseLinear
