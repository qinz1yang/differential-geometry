/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PolyhedralTubeNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodRayEmbedding
import DifferentialGeometry.Topology.PiecewiseLinear.HandlePieceEulerChar
import DifferentialGeometry.Topology.PiecewiseLinear.PolyhedralTubeNeighborhoodExists
import DifferentialGeometry.Topology.PiecewiseLinear.Section33TubeFrame
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheoremDiskVocabulary
import DifferentialGeometry.Topology.PiecewiseLinear.PolyhedralTubeSinglePolygonTraces
import DifferentialGeometry.Topology.PiecewiseLinear.PolyhedralTubeHandlePieces
import DifferentialGeometry.Topology.PiecewiseLinear.DiskMeetsGraph
import DifferentialGeometry.Topology.PiecewiseLinear.NoHandleLoopTheoremDisk
import DifferentialGeometry.Topology.PiecewiseLinear.NotLoopTheoremDisk
import DifferentialGeometry.Topology.PiecewiseLinear.Section33BoundaryMatch
import DifferentialGeometry.Topology.PiecewiseLinear.Section33Extension
import DifferentialGeometry.Topology.PiecewiseLinear.Section33FundamentalGroupBijective

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

section Vocabulary

end Vocabulary

section Leaves

variable {K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))}
  {N N' : Set (EuclideanSpace ℝ (Fin 3))}
  {C Cpp : EuclideanSpace ℝ (Fin 3) → Set (EuclideanSpace ℝ (Fin 3))}
  {D Dbd Ec Eint Ebd : Finset (EuclideanSpace ℝ (Fin 3)) → Set (EuclideanSpace ℝ (Fin 3))}
  {h : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
  {XK : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))}
  {AK : EuclideanSpace ℝ (Fin 3) → Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))}

end Leaves

section Assembly

variable {K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))}
  {N N' : Set (EuclideanSpace ℝ (Fin 3))}
  {C : EuclideanSpace ℝ (Fin 3) → Set (EuclideanSpace ℝ (Fin 3))}
  {D Dbd : Finset (EuclideanSpace ℝ (Fin 3)) → Set (EuclideanSpace ℝ (Fin 3))}
  {h : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}

theorem exists_section33HandleFrame (h323 : Moise323) (ht : IsTube K N C D Dbd h N') {ε : ℝ}
    (hsmall : ∀ v ∈ K.vertices, ∀ x ∈ C v, ∀ y ∈ C v, dist (h x) (h y) < ε / 4) :
    ∃ (Ec Eint Ebd : Finset (EuclideanSpace ℝ (Fin 3)) → Set (EuclideanSpace ℝ (Fin 3)))
      (Cpp : EuclideanSpace ℝ (Fin 3) → Set (EuclideanSpace ℝ (Fin 3))),
      IsHandleDecompositionOfTube K N C D Dbd h N' Ec Eint Ebd Cpp ∧
      ∀ v ∈ K.vertices, ∀ x ∈ Cpp v, ∀ y ∈ Cpp v, dist x y < ε / 4 := by
  have hcont : ContinuousOn h N :=
    continuousOn_iff_continuous_domRestrict.mpr ht.isEmbedding.continuous
  have key : ∀ v : EuclideanSpace ℝ (Fin 3), ∃ V : Set (EuclideanSpace ℝ (Fin 3)),
      v ∈ K.vertices → V ∈ nhdsSet (h '' C v) ∧ ∀ x ∈ V, ∀ y ∈ V, dist x y < ε / 4 := by
    intro v
    by_cases hv : v ∈ K.vertices
    · have hCN : C v ⊆ N := by
        rw [ht.unionEq]
        exact subset_biUnion_of_mem (u := C) hv
      have hvC : v ∈ C v := by
        have hmem : v ∈ C v ∩ K.vertices := by
          rw [ht.dualVertex hv]
          exact mem_singleton v
        exact hmem.1
      have hSc : IsCompact (h '' C v) :=
        (ht.dualBall v hv).isPolyhedron.isCompact.image_of_continuousOn (hcont.mono hCN)
      have hne : (h '' C v).Nonempty := ⟨h v, mem_image_of_mem h hvC⟩
      obtain ⟨p, hp, hmax⟩ := (hSc.prod hSc).exists_isMaxOn (hne.prod hne)
        (continuous_dist.continuousOn (s := (h '' C v) ×ˢ (h '' C v)))
      obtain ⟨x₀, hx₀, hpx⟩ := (mem_prod.mp hp).1
      obtain ⟨y₀, hy₀, hpy⟩ := (mem_prod.mp hp).2
      have hm : dist p.1 p.2 < ε / 4 := by
        rw [← hpx, ← hpy]
        exact hsmall v hv x₀ hx₀ y₀ hy₀
      have hrpos : 0 < (ε / 4 - dist p.1 p.2) / 3 := by linarith
      refine ⟨Metric.thickening ((ε / 4 - dist p.1 p.2) / 3) (h '' C v), fun _ => ⟨?_, ?_⟩⟩
      · exact Metric.isOpen_thickening.mem_nhdsSet.mpr (Metric.self_subset_thickening hrpos _)
      · intro x hx y hy
        obtain ⟨s, hs, hxs⟩ := Metric.mem_thickening_iff.mp hx
        obtain ⟨s', hs', hys⟩ := Metric.mem_thickening_iff.mp hy
        have hss' : dist s s' ≤ dist p.1 p.2 :=
          isMaxOn_iff.mp hmax (s, s') (mk_mem_prod hs hs')
        have h4 := dist_triangle4 x s s' y
        rw [dist_comm s' y] at h4
        linarith
    · exact ⟨univ, fun hv' => absurd hv' hv⟩
  choose V hV using key
  obtain ⟨Ec, Eint, Ebd, Cpp, hd, hsub⟩ :=
    h323 K N C D Dbd h N' ht V fun v hv => (hV v hv).1
  exact ⟨Ec, Eint, Ebd, Cpp, hd,
    fun v hv x hx y hy => (hV v hv).2 x (hsub v hv hx) y (hsub v hv hy)⟩

open Classical in
theorem moise331_of_moise323_of_moise324_of_moise264Orientable (h323 : Moise323) (h324 : Moise324)
    (h264 : Moise264Orientable) : Moise331 := by
  intro L hfin hdim hedge hconn hend U hU hLU h hh ε hε
  obtain ⟨T, L', C, D, Dbd, hTfin, hsub, hLT, hT, hDN, hNU, hend', ht, -, hCsmall⟩ :=
    exists_section33TubeFrame L hdim hedge hend hU hLU hh hε
  obtain ⟨Ec, Eint, Ebd, Cpp, hd, hCppSmall⟩ := exists_section33HandleFrame h323 ht hCsmall
  have hconn' : IsConnected L'.space := by
    rw [hsub.space_eq]
    exact hconn
  obtain ⟨XK₀, h2₀⟩ := exists_isPolyhedralTubeNeighborhood hd
  obtain ⟨XK₁, h2₁, h34₁⟩ := exists_hasSinglePolygonTraces hd h2₀
  obtain ⟨XK₂, AK₂, h2₂, h34₂, h56₂⟩ := exists_hasConnectedHandlePieces hd hconn' h2₁ h34₁
  obtain ⟨XK, AK, h2, h34, h56, h7⟩ := exists_hasNoHandleLoopTheoremDisk hd h2₂ h34₂ h56₂
  have h8 : ∀ v₁ ∈ L'.vertices, ∀ e₁ ∈ L'.faces, e₁.card = 2 →
      ∀ (Δ : Set (EuclideanSpace ℝ (Fin 3))) (r : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)),
        IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Δ →
        Δ ⊆ Cpp v₁ ∩ interior (h '' (derivedNeighborhood T L').space) →
        Δ ∩ Ec e₁ = r '' stdSimplexBoundary 2 →
        (∃ DJ DJint : Set (EuclideanSpace ℝ (Fin 3)),
          IsTopologicalCellWithInterior 2 DJ DJint ∧ DJ ⊆ Ec e₁ ∧
            DJ \ DJint = r '' stdSimplexBoundary 2 ∧ h (e₁.centroid ℝ id) ∈ DJint) →
        (∀ e ∈ L'.faces, e.card = 2 → e ≠ e₁ → Disjoint Δ (Ec e)) →
        (Δ ∩ h '' L'.space).Nonempty :=
    fun _ hv₁ _ he₁ hcard _ _ hr hΔ hbd hcenter hmiss =>
      section33_disk_meets_graph h324 hd hend' hv₁ he₁ hcard hr hΔ hbd hcenter hmiss
  have h9 := section33_not_isLoopTheoremDisk hd h2 h34 h7 h8
  have h10 := section33_fundamentalGroup_map_bijective_of_isTube h264 ht h2 h56.2.1 h9
  have h12 := section33_faceEulerChar_handlePiece hd h2 h34 h56 h10
  obtain ⟨g, hg, hgA, hgD⟩ := exists_section33BoundaryMatch hd hconn' h2 h34 h56 h12
  obtain ⟨f, hf, hfN, -, hfv, hfsmall⟩ :=
    exists_section33Extension h324 hd h2 h34 h56 hg hgA hgD hCppSmall
  refine ⟨T, L', hTfin, hsub, hLT, hT, ?_, hDN, ?_, hNU, f, hf, ?_, ?_⟩
  · rw [← hsub.space_eq]
    exact Filter.mem_of_superset ht.isNeighborhood (derivedNeighborhood_space_subset T L')
  · rw [← hsub.space_eq]
    exact ht.isNeighborhood
  · rw [← hsub.space_eq]
    exact hfN
  · intro x hx
    have hx' : x ∈ ⋃ v ∈ L'.vertices, C v := by
      rw [← ht.unionEq]
      exact hx
    obtain ⟨v, hv, hxv⟩ := mem_iUnion₂.mp hx'
    have hvC : v ∈ C v := by
      have hmem : v ∈ C v ∩ L'.vertices := by
        rw [ht.dualVertex hv]
        exact mem_singleton v
      exact hmem.1
    obtain ⟨y, hy, hfy⟩ := hfv v hv
    calc dist (f x) (h x) ≤ dist (f x) (f y) + dist (f y) (h x) := dist_triangle _ _ _
      _ = dist (f x) (f y) + dist (h v) (h x) := by rw [hfy]
      _ < ε / 4 + ε / 4 := add_lt_add (hfsmall v hv x hxv y hy) (hCsmall v hv v hvC x hxv)
      _ < ε := by linarith

end Assembly

end DifferentialGeometry.Topology.PiecewiseLinear
