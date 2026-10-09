/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34IntrinsicMeridianSystem
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceDiskSeparation

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace E3 M₁]
  [MetricSpace M₂] [ChartedSpace E3 M₂]
  {U : Set M₁} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁} {f₁ : M₁ → M₂}

theorem Section34CutFrame.intrinsic_disk_subset_vertexBall_of_boundary_subset
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hf₁ : IsPLHomeomorphInto 3 f₁ (section34CutNeighborhood src))
    (s : Section34SimplexIndex 𝒦 3) (w : Section34VertexIndex 𝒦 𝒦')
    (hw : Section34Incident w.1 s.1) {P : Set E3} {u : E3 → M₂}
    (hP : IsCombinatorialSolidTorus P) (hu : IsPLHomeomorphInto 3 u P)
    (hUP : u '' P = section34FaceTorus (section34VertexBallImage src f₁) s)
    {D : Set E3} {q : (Fin 3 → ℝ) → E3}
    (hq : IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D) (hDP : D ⊆ frontier P)
    (hJV : q '' stdSimplexBoundary 2 ⊆
      Function.invFunOn u P '' section34VertexBallImage src f₁ w)
    (hJdis : ∀ e : Section34EdgeIndex 𝒦 𝒦', Section34Incident e.1 s.1 →
      Disjoint (q '' stdSimplexBoundary 2)
        (Function.invFunOn u P '' section34SplitDiskImage srcBd f₁ e)) :
    D ⊆ Function.invFunOn u P '' section34VertexBallImage srcBd f₁ w ∧
      ∀ e : Section34EdgeIndex 𝒦 𝒦', Section34Incident e.1 s.1 →
        Disjoint D (Function.invFunOn u P '' section34SplitDiskImage src f₁ e) := by
  classical
  let g := Function.invFunOn u P
  have hDE : ∀ e : Section34EdgeIndex 𝒦 𝒦', Section34Incident e.1 s.1 →
      Disjoint D (g '' section34SplitDiskImage src f₁ e) := by
    intro e he
    obtain ⟨⟨r, hr, hrb⟩, -, hmeet, -, -, hess⟩ :=
      hcut.intrinsic_splitDisk_meridian hf₁ s hu hUP e he
    have hG : IsPLSphere 1 (g '' section34SplitDiskImage srcBd f₁ e) := by
      rw [hrb]
      exact hr.isPLSphere_image_stdSimplexBoundary
    have hGΘ : g '' section34SplitDiskImage srcBd f₁ e ⊆ frontier P :=
      fun x hx => (hmeet.symm.subset hx).1
    have hdis := hP.isPLTorus_frontier.disjoint_disk_of_essential_circle
      hq hDP hG hGΘ (hJdis e he).symm hess
    exact disjoint_left.mpr fun x hxD hxE =>
      disjoint_left.mp hdis hxD (hmeet.subset ⟨hDP hxD, hxE⟩)
  obtain ⟨n, v, -, hv, hB, hnext, -, hfar, -, hcover⟩ :=
    exists_cycle_order_intrinsic_face_vertex_balls hcut hf₁ s hu hUP
  let B := fun i => g '' section34VertexBallImage src f₁ (v i)
  obtain ⟨i₀, hi₀⟩ := (hv w).mp hw
  let O := ⋃ j ∈ {j : Fin (n + 3) | j ≠ i₀}, B j
  have hO : IsClosed O := (Set.toFinite _).isClosed_biUnion fun j _ =>
    (hB j).isPolyhedron.isClosed
  have hDcover : D ⊆ B i₀ ∪ O := by
    intro x hx
    have hxP := hP.isPolyhedron.isClosed.frontier_subset (hDP hx)
    rw [← hcover] at hxP
    obtain ⟨j, hxj⟩ := mem_iUnion.mp hxP
    by_cases hji : j = i₀
    · exact Or.inl (hji ▸ hxj)
    · exact Or.inr (mem_iUnion₂.mpr ⟨j, hji, hxj⟩)
  have hinter : D ∩ (B i₀ ∩ O) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    rintro x ⟨hxD, hx₀, hxO⟩
    obtain ⟨j, hji, hxj⟩ := mem_iUnion₂.mp hxO
    have hadj : (SimpleGraph.cycleGraph (n + 3)).Adj i₀ j := by
      by_contra hnot
      exact disjoint_left.mp (hfar i₀ j hji.symm hnot) hx₀ hxj
    obtain ⟨e, he, heq⟩ := hnext i₀ j hadj
    exact disjoint_left.mp (hDE e he) hxD (heq.symm.subset ⟨hx₀, hxj⟩)
  have hDV : D ⊆ g '' section34VertexBallImage src f₁ w := by
    have hD : IsPLBall 2 D := ⟨q, hq⟩
    rcases isPreconnected_iff_subset_of_disjoint_closed.mp hD.isConnected.isPreconnected
        (B i₀) O (hB i₀).isPolyhedron.isClosed hO hDcover hinter with hd | hd
    · simpa only [B, hi₀] using hd
    · obtain ⟨x, hx⟩ := hq.isPLSphere_image_stdSimplexBoundary.nonempty
      have hxD : x ∈ D := by
        obtain ⟨a, ha, rfl⟩ := hx
        exact hq.bijOn.mapsTo ha.1
      have hxV : x ∈ B i₀ := by simpa only [B, hi₀] using hJV hx
      exact (notMem_empty x (hinter ▸ ⟨hxD, hxV, hd hxD⟩)).elim
  have hVT : section34VertexBallImage src f₁ w ⊆ u '' P := by
    rw [hUP]
    exact fun x hx => mem_iUnion₂.mpr ⟨⟨(s, w), hw⟩, rfl, hx⟩
  obtain ⟨r, hr, hrb⟩ :=
    (hcut.isPLCellOn_vertexBallImage hf₁ w).exists_isPLHomeomorphOn_invFunOn hu hVT
  have hVP : g '' section34VertexBallImage src f₁ w ⊆ P := by
    rintro x ⟨y, hy, rfl⟩
    exact hu.injOn.bijOn_image.surjOn.mapsTo_invFunOn (hVT hy)
  refine ⟨?_, hDE⟩
  rw [hrb, hr.image_stdSimplexBoundary]
  exact fun x hx => ⟨subset_closure (hDV hx),
    fun hi => (hDP hx).2 (interior_mono hVP hi)⟩

end DifferentialGeometry.Topology.PiecewiseLinear
