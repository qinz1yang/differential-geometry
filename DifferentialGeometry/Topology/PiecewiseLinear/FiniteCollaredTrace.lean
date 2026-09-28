/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceCircleCollar
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceInnermostDisk

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

structure HasFiniteCollaredTrace (L T : Set E3) : Prop where
  isPolyhedron : IsPolyhedron L
  finiteTrace : (traceCircles L T).Finite
  traceCover : L ∩ T = ⋃ G ∈ traceCircles L T, G
  circleCollar : ∀ G ∈ traceCircles L T, HasPLCircleCollar L G

theorem HasFiniteCollaredTrace.exists_innermost_disk_neighborhood {L T O : Set E3}
    (h : HasFiniteCollaredTrace L T) (hT : IsPLTorus T)
    (hO : IsOpen O) (hTO : T ⊆ O)
    (hnull : ∃ G ∈ traceCircles L T, boundsDiskIn G T) :
    ∃ (G Δ Ω : Set E3) (r : (Fin 3 → ℝ) → E3),
      G ∈ traceCircles L T ∧ IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Δ ∧
      Δ ⊆ T ∧ r '' stdSimplexBoundary 2 = G ∧ IsOpen Ω ∧ Δ ⊆ Ω ∧ Ω ⊆ O ∧
      Δ ∩ L = G ∧ Ω ∩ L ∩ T ⊆ G ∧
      ∀ J ∈ traceCircles L T, J ≠ G → Disjoint Ω J := by
  classical
  let _ : Finite (traceCircles L T) := h.finiteTrace.to_subtype
  have hseed : ∃ (G : traceCircles L T) (Δ : Set E3) (r : (Fin 3 → ℝ) → E3),
      IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Δ ∧ Δ ⊆ T ∧
        r '' stdSimplexBoundary 2 = (G : Set E3) := by
    obtain ⟨G, hG, Δ, r, hr, hΔT, hGr⟩ := hnull
    exact ⟨⟨G, hG⟩, Δ, r, hr, hΔT, hGr.symm⟩
  obtain ⟨G, Δ, r, hr, hΔT, hrG, hdis⟩ := hT.exists_innermost_disk
    (fun G : traceCircles L T => traceCircles_isPLSphere G.property)
    (fun G => (traceCircles_subset G.property).trans inter_subset_right)
    (fun G J hne => pairwiseDisjoint_traceCircles L T G.property J.property
      (fun heq => hne (Subtype.ext heq))) hseed
  have hGΔ : (G : Set E3) ⊆ Δ := hrG ▸
    (image_mono (fun _ hx => hx.1)).trans hr.image_eq.subset
  have hdis' : ∀ J ∈ traceCircles L T, J ≠ (G : Set E3) → Disjoint Δ J := by
    intro J hJ hJG
    exact hdis ⟨J, hJ⟩ (fun heq => hJG (congrArg Subtype.val heq))
  let F := ⋃ J ∈ traceCircles L T \ {(G : Set E3)}, J
  have hF : IsClosed F := (h.finiteTrace.sdiff).isClosed_biUnion fun J hJ =>
    (traceCircles_isPLSphere hJ.1).isPolyhedron.isClosed
  let Ω := O \ F
  have hΔΩ : Δ ⊆ Ω := by
    intro x hxΔ
    refine ⟨hTO (hΔT hxΔ), ?_⟩
    intro hxF
    obtain ⟨J, hJ, hxJ⟩ := mem_iUnion₂.mp hxF
    exact disjoint_left.mp (hdis' J hJ.1 hJ.2) hxΔ hxJ
  have hisolated : Ω ∩ L ∩ T ⊆ (G : Set E3) := by
    rintro x ⟨⟨hxΩ, hxL⟩, hxT⟩
    obtain ⟨J, hJ, hxJ⟩ := mem_iUnion₂.mp (h.traceCover.subset ⟨hxL, hxT⟩)
    by_cases hJG : J = (G : Set E3)
    · exact hJG ▸ hxJ
    · exact (hxΩ.2 (mem_iUnion₂.mpr ⟨J, ⟨hJ, hJG⟩, hxJ⟩)).elim
  refine ⟨G, Δ, Ω, r, G.property, hr, hΔT, hrG, hO.sdiff hF, hΔΩ,
    sdiff_subset, ?_, hisolated, ?_⟩
  · exact Subset.antisymm (fun x hx => hisolated ⟨⟨hΔΩ hx.1, hx.2⟩, hΔT hx.1⟩)
      (fun x hx => ⟨hGΔ hx, (traceCircles_subset G.property hx).1⟩)
  · intro J hJ hJG
    exact disjoint_left.mpr fun x hx hxJ =>
      hx.2 (mem_iUnion₂.mpr ⟨J, ⟨hJ, hJG⟩, hxJ⟩)

end DifferentialGeometry.Topology.PiecewiseLinear
