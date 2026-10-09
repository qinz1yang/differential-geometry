/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Connected.RelativeBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellPullback
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellBoundaryComplement

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E3 M]

theorem IsPLCellOn.inter_closure_boundary_sdiff_eq_boundary
    {V S D J : Set M} (hV : IsPLCellOn 3 V S) (hD : IsPLCellOn 2 D J) (hDS : D ⊆ S) :
    D ∩ closure (S \ D) = J := by
  obtain ⟨P, p, u, hp, hu, hVP, hSP⟩ := hV
  have hP : IsPLBall 3 P := ⟨p, hp⟩
  have hfrP : frontier P ⊆ P := hP.isPolyhedron.isClosed.frontier_subset
  rw [IsPLHomeomorphOn.image_stdSimplexBoundary (n := 2) hp] at hSP
  let g := Function.invFunOn u P
  have hleft : LeftInvOn g u P := hu.injOn.leftInvOn_invFunOn
  have hDP : D ⊆ u '' P := by
    rw [← hVP]
    exact hDS.trans (by rw [hSP, hVP]; exact image_mono hfrP)
  obtain ⟨q, hq, hqJ⟩ := hD.exists_isPLHomeomorphOn_invFunOn hu hDP
  have hright : ∀ y ∈ u '' P, u (g y) = y :=
    fun y hy => hu.injOn.bijOn_image.invOn_invFunOn.2 hy
  have hDimage : u '' (g '' D) = D := by
    rw [image_image]
    calc
      (u ∘ g) '' D = id '' D := image_congr fun y hy => hright y (hDP hy)
      _ = D := image_id _
  have hJimage : u '' (g '' J) = J := by
    rw [image_image]
    calc
      (u ∘ g) '' J = id '' J :=
        image_congr fun y hy => hright y (hDP (hD.boundary_subset hy))
      _ = J := image_id _
  have hDfr : g '' D ⊆ frontier P := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨z, hz, hzy⟩ := hSP.subset (hDS hy)
    rw [← hzy, hleft (hfrP hz)]
    exact hz
  have hsource := hP.isPLSphere_frontier.inter_closure_sdiff_eq_image_stdSimplexBoundary
    hq hDfr
  have hclosure : closure (frontier P \ g '' D) ⊆ frontier P :=
    closure_minimal sdiff_subset isClosed_frontier
  have hclosed : IsClosed (u '' closure (frontier P \ g '' D)) :=
    ((hP.isPolyhedron.isCompact.of_isClosed_subset isClosed_closure
      (hclosure.trans hfrP)).image_of_continuousOn
        (hu.continuousOn.mono (hclosure.trans hfrP))).isClosed
  have hcl : closure (u '' (frontier P \ g '' D)) =
      u '' closure (frontier P \ g '' D) :=
    subset_antisymm (closure_minimal (image_mono subset_closure) hclosed)
      (ContinuousOn.image_closure (hu.continuousOn.mono (hclosure.trans hfrP)))
  have hdiff : u '' (frontier P \ g '' D) = S \ D := by
    rw [(hu.injOn.mono hfrP).image_sdiff_subset hDfr, ← hSP, hDimage]
  have hinter : u '' ((g '' D) ∩ closure (frontier P \ g '' D)) =
      (u '' (g '' D)) ∩ (u '' closure (frontier P \ g '' D)) :=
    image_inter_on fun x hx y hy hxy => hu.injOn (hclosure.trans hfrP hx)
      (hDfr.trans hfrP hy) hxy
  calc
    D ∩ closure (S \ D) = (u '' (g '' D)) ∩
        (u '' closure (frontier P \ g '' D)) := by rw [hDimage, ← hcl, hdiff]
    _ = u '' ((g '' D) ∩ closure (frontier P \ g '' D)) := hinter.symm
    _ = J := by rw [hsource, ← hqJ, hJimage]

theorem IsPLCellOn.inter_closure_sdiff_of_eventually_eq
    {V S T D J : Set M} (hV : IsPLCellOn 3 V S) (hD : IsPLCellOn 2 D J) (hDS : D ⊆ S)
    (hlocal : ∀ x ∈ D, ∀ᶠ y in 𝓝 x, y ∈ T ↔ y ∈ S) :
    D ∩ closure (T \ D) = J := by
  have hcl : ∀ x ∈ D, x ∈ closure (T \ D) ↔ x ∈ closure (S \ D) := by
    intro x hx
    obtain ⟨O, hOO, hO, hxO⟩ := _root_.mem_nhds_iff.mp (hlocal x hx)
    constructor
    · intro hxcl
      have hsub : O ∩ (T \ D) ⊆ S \ D := fun y hy => ⟨(hOO hy.1).mp hy.2.1, hy.2.2⟩
      exact closure_mono hsub (hO.inter_closure ⟨hxO, hxcl⟩)
    · intro hxcl
      have hsub : O ∩ (S \ D) ⊆ T \ D := fun y hy => ⟨(hOO hy.1).mpr hy.2.1, hy.2.2⟩
      exact closure_mono hsub (hO.inter_closure ⟨hxO, hxcl⟩)
  have heq : D ∩ closure (T \ D) = D ∩ closure (S \ D) := by
    ext x
    exact ⟨fun hx => ⟨hx.1, (hcl x hx.1).mp hx.2⟩,
      fun hx => ⟨hx.1, (hcl x hx.1).mpr hx.2⟩⟩
  exact heq.trans (hV.inter_closure_boundary_sdiff_eq_boundary hD hDS)

theorem IsPLCellOn.subset_or_disjoint_disk_of_eventually_eq
    {V S T D J Y : Set M} (hV : IsPLCellOn 3 V S) (hD : IsPLCellOn 2 D J) (hDS : D ⊆ S)
    (hlocal : ∀ x ∈ D, ∀ᶠ y in 𝓝 x, y ∈ T ↔ y ∈ S)
    (hY : IsPreconnected Y) (hYT : Y ⊆ T) (hYJ : Disjoint Y J) :
    Y ⊆ D ∨ Disjoint D Y :=
  DifferentialGeometry.Topology.IsPreconnected.subset_or_disjoint_of_disjoint_relativeBoundary
    hY hYT hD.isCompact.isClosed
    ((hV.inter_closure_sdiff_of_eventually_eq hD hDS hlocal).symm ▸ hYJ)

end DifferentialGeometry.Topology.PiecewiseLinear
