/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ComponentCollaredTrace
import DifferentialGeometry.Topology.PiecewiseLinear.DiskAttachmentComponentEuler
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalSurfaceSplit

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem HasPLCircleCollar.of_connected_component
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] {G : Set E}
    (h : HasPLCircleCollar K.space G) (c : ConnectedComponents K.space)
    (hG : G ⊆ (connectedComponentComplex K c).space) :
    HasPLCircleCollar (connectedComponentComplex K c).space G := by
  have hsub : (connectedComponentComplex K c).space ⊆ K.space :=
    (subset_iUnion (fun d => (connectedComponentComplex K d).space) c).trans
      (iUnion_connectedComponentComplex_space K).subset
  apply h.of_locally_eq (isPolyhedron_sdiff_connectedComponentComplex K c).isClosed.isOpen_compl
    (fun x hx hxR => hxR.2 (hG hx))
  ext x
  constructor
  · exact fun hx => ⟨hsub hx.1, hx.2⟩
  · rintro ⟨hxK, hxR⟩
    refine ⟨?_, hxR⟩
    by_contra hxc
    exact hxR ⟨hxK, hxc⟩

end General

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem mem_traceCircles_iff_subset {L P T G : Set E3}
    (hG : G ∈ traceCircles L T) (hPL : P ⊆ L) : G ∈ traceCircles P T ↔ G ⊆ P := by
  constructor
  · exact fun h => (traceCircles_subset h).trans inter_subset_left
  · intro hGP
    obtain ⟨x, hx, hEq, hSphere⟩ := hG
    have hxG : x ∈ G := hEq.symm ▸ mem_connectedComponentIn hx
    have hGT : G ⊆ T := by
      rw [hEq]
      exact (connectedComponentIn_subset _ _).trans inter_subset_right
    refine ⟨x, ⟨hGP hxG, hx.2⟩, ?_, hSphere⟩
    apply Subset.antisymm
    · exact hSphere.isConnected.isPreconnected.subset_connectedComponentIn hxG
        (fun y hy => ⟨hGP hy, hGT hy⟩)
    · rw [hEq]
      exact connectedComponentIn_mono x (fun y hy => ⟨hPL hy.1, hy.2⟩)

open Classical in
theorem IsCircleCapping.exists_component_capping
    (K Q : Geometry.SimplicialComplex ℝ E3) [Finite K.faces] [Finite Q.faces] {T B : Set E3}
    (hcap : IsCircleCapping K.space Q.space T B) :
    letI (c : ConnectedComponents K.space) : Finite (connectedComponentComplex K c).faces :=
      (connectedComponentComplex_faces_finite K c).to_subtype
    letI (c : ConnectedComponents Q.space) : Finite (connectedComponentComplex Q c).faces :=
      (connectedComponentComplex_faces_finite Q c).to_subtype
    ∃ (c₀ : ConnectedComponents K.space) (e : ConnectedComponents K.space ≃
        ConnectedComponents Q.space),
      IsCircleCapping (connectedComponentComplex K c₀).space
        (connectedComponentComplex Q (e c₀)).space T (B ∩ (connectedComponentComplex K c₀).space) ∧
      (∀ c, c ≠ c₀ → ∃ f : E3 → E3, IsPLHomeomorphOn f
        (connectedComponentComplex K c).space (connectedComponentComplex Q (e c)).space ∧
          EqOn f id (B ∩ (connectedComponentComplex K c).space)) ∧
      eulerChar (connectedComponentComplex Q (e c₀)) =
        eulerChar (connectedComponentComplex K c₀) + 1 ∧
      ∀ c, c ≠ c₀ → eulerChar (connectedComponentComplex Q (e c)) =
        eulerChar (connectedComponentComplex K c) := by
  obtain ⟨D, r, f, hr, hDT, hmeet, hG, hcollar, hf, hfix⟩ := hcap
  obtain ⟨c₀, e, hattach, hcomp, hχ, hχrest⟩ :=
    IsPLHomeomorphOn.exists_component_eulerChar_of_disk_attachment K Q hr hmeet hf
  let _ (c : ConnectedComponents K.space) : Finite (connectedComponentComplex K c).faces :=
    (connectedComponentComplex_faces_finite K c).to_subtype
  let _ (c : ConnectedComponents Q.space) : Finite (connectedComponentComplex Q c).faces :=
    (connectedComponentComplex_faces_finite Q c).to_subtype
  have hsub : (connectedComponentComplex K c₀).space ⊆ K.space :=
    (subset_iUnion (fun c => (connectedComponentComplex K c).space) c₀).trans
      (iUnion_connectedComponentComplex_space K).subset
  have hGsub := hmeet.symm.subset.trans hattach
  refine ⟨c₀, e, ?_, ?_, hχ, hχrest⟩
  · refine ⟨D, r, f, hr, hDT, ?_, (mem_traceCircles_iff_subset hG hsub).mpr hGsub,
      hcollar.of_connected_component K c₀ hGsub, ?_, ?_⟩
    · exact Subset.antisymm (fun x hx => hmeet.subset ⟨hsub hx.1, hx.2⟩)
        (fun x hx => ⟨hGsub hx, (hmeet.symm.subset hx).2⟩)
    · simpa only [↓reduceIte] using hcomp c₀
    · apply hfix.mono
      intro x hx
      exact ⟨hx.1.1, hx.2⟩
  · intro c hc
    refine ⟨f, by simpa only [ite_eq_right hc, union_empty] using hcomp c, ?_⟩
    apply hfix.mono
    intro x hx
    exact ⟨hx.1, fun hxG =>
      disjoint_left.mp (pairwise_disjoint_connectedComponentComplex_space K hc) hx.2 (hGsub hxG)⟩

end DifferentialGeometry.Topology.PiecewiseLinear
