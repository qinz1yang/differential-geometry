/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.TorusSurfaceCollars
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceSeamDeletion

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def HasPLCircleCollar (L G : Set E) : Prop :=
  IsPLSphere 1 G ∧ ∀ U : Set E, IsOpen U → G ⊆ U →
    ∃ (W : Set E) (ρ : E × ℝ → E),
      IsPLHomeomorphOn ρ (G ×ˢ Icc (0 : ℝ) 1) W ∧
      (∀ x ∈ G, ρ (x, 0) = x) ∧ W ⊆ L ∩ U ∧ W ∈ 𝓝ˢ[L] G

theorem HasPLCircleCollar.subset {L G : Set E} (h : HasPLCircleCollar L G) : G ⊆ L := by
  obtain ⟨W, ρ, hρ, hρ0, hW, -⟩ := h.2 univ isOpen_univ (subset_univ _)
  intro x hx
  exact (hW (hρ0 x hx ▸ hρ.bijOn.mapsTo ⟨hx, by norm_num⟩)).1

theorem HasPLCircleCollar.of_locally_eq {L L' G U : Set E}
    (h : HasPLCircleCollar L G) (hU : IsOpen U) (hGU : G ⊆ U)
    (heq : L' ∩ U = L ∩ U) : HasPLCircleCollar L' G := by
  refine ⟨h.1, ?_⟩
  intro V hV hGV
  obtain ⟨W, ρ, hρ, hρ0, hW, hnear⟩ := h.2 (V ∩ U) (hV.inter hU)
    (fun x hx => ⟨hGV hx, hGU hx⟩)
  refine ⟨W, ρ, hρ, hρ0, ?_, ?_⟩
  · intro x hx
    have hWx := hW hx
    exact ⟨(heq.symm.subset ⟨hWx.1, hWx.2.2⟩).1, hWx.2.1⟩
  · obtain ⟨O, hO, hGO, hOW⟩ := mem_nhdsSetWithin.mp hnear
    refine mem_nhdsSetWithin.mpr ⟨O ∩ U, hO.inter hU,
      fun x hx => ⟨hGO hx, hGU hx⟩, ?_⟩
    rintro x ⟨hxO, hxL'⟩
    exact hOW ⟨hxO.1, (heq.subset ⟨hxL', hxO.2⟩).1⟩

theorem HasPLCircleCollar.of_sdiff_eq {L L' G C : Set E}
    (h : HasPLCircleCollar L G) (hC : IsClosed C) (hGC : Disjoint G C)
    (heq : L' \ C = L \ C) : HasPLCircleCollar L' G := by
  exact h.of_locally_eq hC.isOpen_compl
    (fun x hx => disjoint_left.mp hGC hx) (by simpa only [sdiff_eq] using heq)

end General

theorem IsPLTorus.hasPLCircleCollar_sdiff_interior {T X G : Set E3}
    (hT : IsPLTorus T) (hX : IsClosed X) (hreg : X ⊆ closure (interior X))
    (hfin : (traceCircles T (frontier X)).Finite)
    (hcover : T ∩ frontier X = ⋃ J ∈ traceCircles T (frontier X), J)
    (hG : G ∈ traceCircles T (frontier X))
    (hcross : ∀ x ∈ G, HasPLCrossingAt T (frontier X) x) :
    HasPLCircleCollar (T \ interior X) G := by
  classical
  have hGs := traceCircles_isPLSphere hG
  have hGT := (traceCircles_subset hG).trans inter_subset_left
  have hGX := (traceCircles_subset hG).trans inter_subset_right
  refine ⟨hGs, ?_⟩
  intro U hU hGU
  let R := ⋃ J ∈ traceCircles T (frontier X) \ {G}, J
  have hRc : IsClosed R := (hfin.sdiff).isClosed_biUnion fun J hJ =>
    (traceCircles_isPLSphere hJ.1).isPolyhedron.isClosed
  have hGR : Disjoint G R := by
    refine disjoint_iUnion_right.mpr fun J => disjoint_iUnion_right.mpr fun hJ => ?_
    exact pairwiseDisjoint_traceCircles T (frontier X) hG hJ.1 (Ne.symm hJ.2)
  have hGU' : G ⊆ U \ R := fun x hx => ⟨hGU hx, disjoint_left.mp hGR hx⟩
  have hisolated : (U \ R) ∩ T ∩ frontier X ⊆ G := by
    rintro x ⟨⟨hxU, hxT⟩, hxX⟩
    obtain ⟨J, hJ, hxJ⟩ := mem_iUnion₂.mp (hcover.subset ⟨hxT, hxX⟩)
    by_cases hJG : J = G
    · exact hJG ▸ hxJ
    · exact (hxU.2 (mem_iUnion₂.mpr ⟨J, ⟨hJ, hJG⟩, hxJ⟩)).elim
  obtain ⟨x, hxG⟩ := hGs.nonempty
  obtain ⟨W, ρ, hρ, hρ0, hW, hnear, -⟩ :=
    hT.exists_exterior_collar_of_crossing hGs hGT hGX hX (hU.sdiff hRc) hGU'
      hisolated hxG (hcross x hxG) (hreg (hX.frontier_subset (hGX hxG)))
  exact ⟨W, ρ, hρ, hρ0, fun y hy => ⟨(hW hy).1, (hW hy).2.1⟩, hnear⟩

end DifferentialGeometry.Topology.PiecewiseLinear
