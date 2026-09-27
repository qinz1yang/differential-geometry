/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34IntrinsicPolygonFilling
import DifferentialGeometry.Topology.PiecewiseLinear.Section34IntrinsicVertexTrace
import DifferentialGeometry.Topology.PiecewiseLinear.Section34IntrinsicVertexCompression

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

theorem exists_section34_compression_of_vertex_circle_avoiding_split_disks
    (hinv : Section34FaceBallInvariants 𝒦 𝒦' h H (section34VertexBallImage src f₁)
      (section34SplitDiskImage srcBd f₁) fbl fblBd)
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hgraph : Section34GraphFrame U W h η H 𝒦 𝒦' src cr f₁)
    (s : Section34SimplexIndex 𝒦 3) (w : Section34VertexIndex 𝒦 𝒦')
    {J : Set M₂} (hJ : IsPolyhedralSphere (n := 3) 1 J)
    (hJP : J ⊆ fblBd s) (hJV : J ⊆ section34VertexBallImage src f₁ w)
    (hJN : J ⊆ frontier (⋃ v, section34VertexBallImage src f₁ v))
    (hJE : ∀ e : Section34EdgeIndex 𝒦 𝒦', Disjoint J (section34SplitDiskImage src f₁ e)) :
    ∃ t : Section34SimplexIndex 𝒦 3,
      Section34Compression 𝒦 𝒦' (section34VertexBallImage srcBd f₁)
        (section34SplitDiskImage src f₁) fbl fblBd t := by
  apply exists_section34_compression_of_vertex_trace_circle hinv hcut hgraph.2.2.1
    (fun t => ?_) s w hJ hJP hJV hJN hJE
  · intro t hwt hJF hJγ
    exact exists_section34_vertex_disk_of_disjoint_face_trace hinv hcut hgraph t w hwt
      hJ hJV hJN hJF hJγ
  · obtain ⟨ι, hι, F, hF, hdis, hN, -⟩ :=
      exists_finite_section34Trace_circles_of_crossings hcut hgraph hinv t
    exact ⟨ι, hι, F, hF, hdis, hN⟩

theorem exists_section34_compression_of_vertex_contained_trace
    (hinv : Section34FaceBallInvariants 𝒦 𝒦' h H (section34VertexBallImage src f₁)
      (section34SplitDiskImage srcBd f₁) fbl fblBd)
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hgraph : Section34GraphFrame U W h η H 𝒦 𝒦' src cr f₁)
    (s : Section34SimplexIndex 𝒦 3) (w : Section34VertexIndex 𝒦 𝒦')
    {J : Set M₂} (hJ : IsPolyhedralSphere (n := 3) 1 J)
    (hJT : J ⊆ fblBd s ∩ frontier (⋃ v, section34VertexBallImage src f₁ v))
    (hJV : J ⊆ section34VertexBallImage src f₁ w) :
    ∃ t : Section34SimplexIndex 𝒦 3,
      Section34Compression 𝒦 𝒦' (section34VertexBallImage srcBd f₁)
        (section34SplitDiskImage src f₁) fbl fblBd t := by
  exact exists_section34_compression_of_vertex_circle_avoiding_split_disks hinv hcut hgraph
    s w hJ (fun x hx => (hJT hx).1) hJV (fun x hx => (hJT hx).2)
      (hinv.disjoint_splitDiskImage_of_circle_subset_vertexBall hcut hgraph s w hJ
        (fun x hx => (hJT hx).1) hJV (fun x hx => (hJT hx).2))

theorem Section34FaceBallInvariants.not_circle_subset_vertexBall_of_no_compression
    (hinv : Section34FaceBallInvariants 𝒦 𝒦' h H (section34VertexBallImage src f₁)
      (section34SplitDiskImage srcBd f₁) fbl fblBd)
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hgraph : Section34GraphFrame U W h η H 𝒦 𝒦' src cr f₁)
    (hnc : ∀ t, ¬ Section34Compression 𝒦 𝒦' (section34VertexBallImage srcBd f₁)
      (section34SplitDiskImage src f₁) fbl fblBd t)
    (s : Section34SimplexIndex 𝒦 3) (w : Section34VertexIndex 𝒦 𝒦')
    {J : Set M₂} (hJ : IsPolyhedralSphere (n := 3) 1 J)
    (hJT : J ⊆ fblBd s ∩ frontier (⋃ v, section34VertexBallImage src f₁ v)) :
    ¬ J ⊆ section34VertexBallImage src f₁ w := by
  intro hJV
  obtain ⟨t, ht⟩ :=
    exists_section34_compression_of_vertex_contained_trace hinv hcut hgraph s w hJ hJT hJV
  exact hnc t ht

end DifferentialGeometry.Topology.PiecewiseLinear
