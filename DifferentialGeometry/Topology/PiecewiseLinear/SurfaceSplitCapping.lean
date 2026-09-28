/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceSplitEuler
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceSplitNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.BallReplacement
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryGluing
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldDisjointUnion

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

namespace SurfaceSplitAlongPolygon

open Classical in
theorem exists_surface_split_and_cap_of_disk_pair
    (source split : Geometry.SimplicialComplex ℝ E)
    [Finite split.faces]
    (h : SurfaceSplitAlongPolygon source split)
    (hsplit : IsCombinatorialManifoldWithBoundary 2 split)
    {D₀ D₁ : Set E} {q₀ q₁ : (Fin 3 → ℝ) → E}
    (hq₀ : IsPLHomeomorphOn q₀ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D₀)
    (hq₁ : IsPLHomeomorphOn q₁ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D₁)
    (hdis : Disjoint D₀ D₁)
    (hmeet₀ : split.space ∩ D₀ = q₀ '' stdSimplexBoundary 2)
    (hmeet₁ : split.space ∩ D₁ = q₁ '' stdSimplexBoundary 2)
    (hboundary : (boundaryComplex 2 split).space =
      q₀ '' stdSimplexBoundary 2 ∪ q₁ '' stdSimplexBoundary 2) :
    ∃ (split' result : Geometry.SimplicialComplex ℝ E)
      (hsplit'fin : split'.faces.Finite) (hresultfin : result.faces.Finite),
      letI := hsplit'fin.to_subtype
      letI := hresultfin.to_subtype
      IsSubdivision split' split ∧
      IsCombinatorialManifold 2 result ∧
      result.space = split.space ∪ D₀ ∪ D₁ ∧
      Nonempty (SurfaceSplitAndCap source split' result) := by
  have hD₀ : IsPLBall 2 D₀ := ⟨q₀, hq₀⟩
  have hD₁ : IsPLBall 2 D₁ := ⟨q₁, hq₁⟩
  obtain ⟨C₀, hC₀fin, hC₀space⟩ := hD₀.isPolyhedron.exists_simplicialComplex
  obtain ⟨C₁, hC₁fin, hC₁space⟩ := hD₁.isPolyhedron.exists_simplicialComplex
  let _ : Finite C₀.faces := hC₀fin.to_subtype
  let _ : Finite C₁.faces := hC₁fin.to_subtype
  obtain ⟨T, hTfin, hTspace, hTsplit, hTC₀, hTC₁⟩ :=
    exists_simplicialComplex_space_union_three split C₀ C₁
  let _ : Finite T.faces := hTfin.to_subtype
  let split' := restrict T split.space
  let cap₀ := restrict T C₀.space
  let cap₁ := restrict T C₁.space
  have hsplit'fin : split'.faces.Finite := restrict_faces_finite T split.space
  have hcap₀fin : cap₀.faces.Finite := restrict_faces_finite T C₀.space
  have hcap₁fin : cap₁.faces.Finite := restrict_faces_finite T C₁.space
  let _ : Finite split'.faces := hsplit'fin.to_subtype
  let _ : Finite cap₀.faces := hcap₀fin.to_subtype
  let _ : Finite cap₁.faces := hcap₁fin.to_subtype
  have hsplit'space : split'.space = split.space := hTsplit.space_eq
  have hcap₀space : cap₀.space = D₀ := hTC₀.space_eq.trans hC₀space
  have hcap₁space : cap₁.space = D₁ := hTC₁.space_eq.trans hC₁space
  have hcompat₀ : ∀ s ∈ split'.faces, ∀ t ∈ cap₀.faces,
      convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E) ⊆
        convexHull ℝ ((s : Set E) ∩ (t : Set E)) := by
    intro s hs t ht
    exact T.inter_subset_convexHull hs.1 ht.1
  let U := unionComplex split' cap₀ hcompat₀
  let _ : Finite U.faces := finite_unionComplex_faces split' cap₀ hcompat₀
  have hcompat₁ : ∀ s ∈ U.faces, ∀ t ∈ cap₁.faces,
      convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E) ⊆
        convexHull ℝ ((s : Set E) ∩ (t : Set E)) := by
    intro s hs t ht
    rcases hs with hs | hs
    · exact T.inter_subset_convexHull hs.1 ht.1
    · exact T.inter_subset_convexHull hs.1 ht.1
  let result := unionComplex U cap₁ hcompat₁
  have hresultfin : result.faces.Finite := finite_unionComplex_faces U cap₁ hcompat₁
  let _ : Finite result.faces := hresultfin.to_subtype
  have hresultspace : result.space = split.space ∪ D₀ ∪ D₁ := by
    rw [unionComplex_space, unionComplex_space, hsplit'space, hcap₀space, hcap₁space]
  have hsplit'man : IsCombinatorialManifoldWithBoundary 2 split' :=
    hsplit.of_isSubdivision hTsplit
  have hboundary' : (boundaryComplex 2 split').space =
      q₀ '' stdSimplexBoundary 2 ∪ q₁ '' stdSimplexBoundary 2 := by
    rw [boundaryComplex_space_of_isSubdivision split split' hsplit hTsplit, hboundary]
  have hcapdis : Disjoint cap₀.faces cap₁.faces := by
    apply disjoint_left.mpr
    intro s hs₀ hs₁
    obtain ⟨v, hv⟩ := cap₀.nonempty_of_mem_faces hs₀
    exact Set.disjoint_left.mp hdis
      (hcap₀space.subset (cap₀.subset_space hs₀ hv))
      (hcap₁space.subset (cap₁.subset_space hs₁ hv))
  have hcapSpaceDis : Disjoint cap₀.space cap₁.space := by
    rwa [hcap₀space, hcap₁space]
  have hcapCompat : ∀ s ∈ cap₀.faces, ∀ t ∈ cap₁.faces,
      convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E) ⊆
        convexHull ℝ ((s : Set E) ∩ (t : Set E)) := by
    intro s hs t ht
    exact T.inter_subset_convexHull hs.1 ht.1
  let caps := unionComplex cap₀ cap₁ hcapCompat
  let _ : Finite caps.faces := finite_unionComplex_faces cap₀ cap₁ hcapCompat
  have hcap₀man : IsCombinatorialManifoldWithBoundary 2 cap₀ :=
    (hcap₀space.symm ▸ hD₀).isCombinatorialManifoldWithBoundary
  have hcap₁man : IsCombinatorialManifoldWithBoundary 2 cap₁ :=
    (hcap₁space.symm ▸ hD₁).isCombinatorialManifoldWithBoundary
  have hcapsman : IsCombinatorialManifoldWithBoundary 2 caps :=
    IsCombinatorialManifoldWithBoundary.unionComplex_of_disjoint
      cap₀ cap₁ hcapCompat hcap₀man hcap₁man hcapSpaceDis
  have hcap₀boundary :
      (boundaryComplex 2 cap₀).space = q₀ '' stdSimplexBoundary 2 := by
    rw [boundaryComplex_space_of_isPLHomeomorphOn_stdSimplex cap₀
      (hcap₀space.symm ▸ hq₀), simplexBoundary_stdVertices_space]
  have hcap₁boundary :
      (boundaryComplex 2 cap₁).space = q₁ '' stdSimplexBoundary 2 := by
    rw [boundaryComplex_space_of_isPLHomeomorphOn_stdSimplex cap₁
      (hcap₁space.symm ▸ hq₁), simplexBoundary_stdVertices_space]
  have hcapsBoundary : (boundaryComplex 2 caps).space =
      q₀ '' stdSimplexBoundary 2 ∪ q₁ '' stdSimplexBoundary 2 := by
    rw [boundaryComplex_space_unionComplex_of_disjoint
      2 cap₀ cap₁ hcapCompat hcapSpaceDis, hcap₀boundary, hcap₁boundary]
  have hsplitCapsCompat : ∀ s ∈ split'.faces, ∀ t ∈ caps.faces,
      convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E) ⊆
        convexHull ℝ ((s : Set E) ∩ (t : Set E)) := by
    intro s hs t ht
    rcases ht with ht | ht
    · exact T.inter_subset_convexHull hs.1 ht.1
    · exact T.inter_subset_convexHull hs.1 ht.1
  have hsplitCapsMeet : split'.space ∩ caps.space = (boundaryComplex 2 split').space := by
    rw [unionComplex_space, inter_union_distrib_left, hsplit'space,
      hcap₀space, hcap₁space, hmeet₀, hmeet₁, hboundary']
  have hcapsMeet : split'.space ∩ caps.space = (boundaryComplex 2 caps).space := by
    rw [unionComplex_space, inter_union_distrib_left, hsplit'space,
      hcap₀space, hcap₁space, hmeet₀, hmeet₁, hcapsBoundary]
  let closed := unionComplex split' caps hsplitCapsCompat
  let _ : Finite closed.faces := finite_unionComplex_faces split' caps hsplitCapsCompat
  have hclosedman : IsCombinatorialManifold 2 closed :=
    isCombinatorialManifold_unionComplex split' caps hsplitCapsCompat
      hsplit'man hcapsman hsplitCapsMeet hcapsMeet
  have hclosedspace : closed.space = split.space ∪ D₀ ∪ D₁ := by
    rw [unionComplex_space, unionComplex_space, hsplit'space,
      hcap₀space, hcap₁space, union_assoc]
  have hresultman : IsCombinatorialManifold 2 result := by
    apply hclosedman.of_isPLHomeomorphOn (f := (id : E → E))
    rw [hclosedspace, hresultspace]
    exact (((isPolyhedron_space split).union hD₀.isPolyhedron).union
      hD₁.isPolyhedron).isPLHomeomorphOn_id
  have hcapBoundary₀space :
      (intersectionComplex split' cap₀).space = q₀ '' stdSimplexBoundary 2 := by
    rw [intersectionComplex_space split' cap₀ hcompat₀,
      hsplit'space, hcap₀space, hmeet₀]
  have hcapBoundary₁space :
      (intersectionComplex split' cap₁).space = q₁ '' stdSimplexBoundary 2 := by
    have hcompat : ∀ s ∈ split'.faces, ∀ t ∈ cap₁.faces,
        convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E) ⊆
          convexHull ℝ ((s : Set E) ∩ (t : Set E)) := by
      intro s hs t ht
      exact T.inter_subset_convexHull hs.1 ht.1
    rw [intersectionComplex_space split' cap₁ hcompat,
      hsplit'space, hcap₁space, hmeet₁]
  have hsplitData : SurfaceSplitAlongPolygon source split' := by
    refine { h with splitHomeomorph := ?_ }
    obtain ⟨f, hf⟩ := h.splitHomeomorph
    exact ⟨f, by rwa [hsplit'space]⟩
  have hcapData : SurfaceSplitAndCap source split' result := by
    refine
      { toSurfaceSplitAlongPolygon := hsplitData
        cap₀ := cap₀
        cap₁ := cap₁
        capBoundary₀ := intersectionComplex split' cap₀
        capBoundary₁ := intersectionComplex split' cap₁
        cap₀_faces_finite := hcap₀fin
        cap₁_faces_finite := hcap₁fin
        capBoundary₀_faces_finite := intersectionComplex_faces_finite split' cap₀ hsplit'fin
        capBoundary₁_faces_finite := intersectionComplex_faces_finite split' cap₁ hsplit'fin
        result_faces := rfl
        split_inter_cap₀_faces := rfl
        split_inter_cap₁_faces := rfl
        cap_faces_disjoint := hcapdis
        cap₀_isPLBall := hcap₀space.symm ▸ hD₀
        cap₁_isPLBall := hcap₁space.symm ▸ hD₁
        capBoundary₀_isPLSphere :=
          hcapBoundary₀space.symm ▸ hq₀.isPLSphere_image_stdSimplexBoundary
        capBoundary₁_isPLSphere :=
          hcapBoundary₁space.symm ▸ hq₁.isPLSphere_image_stdSimplexBoundary }
  exact ⟨split', result, hsplit'fin, hresultfin, hTsplit, hresultman,
    hresultspace, ⟨hcapData⟩⟩

end SurfaceSplitAlongPolygon

end DifferentialGeometry.Topology.PiecewiseLinear
