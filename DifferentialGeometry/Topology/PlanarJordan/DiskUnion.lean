/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PlanarJordan.ClosedInterior
import DifferentialGeometry.Topology.PlanarJordan.CompactRegion
import DifferentialGeometry.Topology.PlanarJordan.RegionRecognition
import DifferentialGeometry.Topology.PlanarJordan.AmbientExtension
import DifferentialGeometry.Topology.ClosedBallImage

open Set Topology Metric Schoenflies

namespace DifferentialGeometry.Topology.PlanarJordan

theorem isJordanCurve_frontier_of_homeomorphClosedBall {C : Set Plane}
    (φ : C ≃ₜ closedBall (0 : Plane) 1) :
    IsJordanCurve (frontier C) := by
  have _ : CompactSpace (Metric.sphere (0 : Plane) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere (0 : Plane) 1)
  have hemb : Topology.IsEmbedding
      (fun s : Metric.sphere (0 : Plane) 1 =>
        closedBallParam φ ⟨s.1, sphere_subset_closedBall s.2⟩) := by
    have hcont : Continuous
        (fun s : Metric.sphere (0 : Plane) 1 =>
          closedBallParam φ ⟨s.1, sphere_subset_closedBall s.2⟩) :=
      (continuous_closedBallParam φ).comp (continuous_subtype_val.subtype_mk _)
    have hinj : Function.Injective
        (fun s : Metric.sphere (0 : Plane) 1 =>
          closedBallParam φ ⟨s.1, sphere_subset_closedBall s.2⟩) := by
      intro s₁ s₂ h
      have hval := injective_closedBallParam φ h
      have hval' : (s₁ : Plane) = (s₂ : Plane) :=
        congrArg (fun x : closedBall (0 : Plane) 1 => (x : Plane)) hval
      exact Subtype.ext hval'
    exact (hcont.isClosedEmbedding hinj).isEmbedding
  have hrange : range (fun s : Metric.sphere (0 : Plane) 1 =>
      closedBallParam φ ⟨s.1, sphere_subset_closedBall s.2⟩) = frontier C := by
    rw [frontier_eq_image_sphere_of_homeomorphClosedBall φ]
    ext y
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨⟨s.1, sphere_subset_closedBall s.2⟩, s.2, rfl⟩
    · rintro ⟨b, hb, rfl⟩
      exact ⟨⟨b.1, hb⟩, rfl⟩
  rw [← hrange]
  exact isJordanCurve_range_of_isEmbedding_circle hemb

theorem interior_eq_inside_frontier_of_homeomorphClosedBall {C : Set Plane}
    (φ : C ≃ₜ closedBall (0 : Plane) 1) :
    interior C = inside (frontier C) := by
  have hC : IsCompact C := isCompact_of_homeomorphClosedBall φ
  have hJ : IsJordanCurve (frontier C) := isJordanCurve_frontier_of_homeomorphClosedBall φ
  have hne : (interior C).Nonempty := by
    rw [interior_eq_image_of_homeomorphClosedBall φ]
    refine ⟨closedBallParam φ ⟨0, by simp⟩, ⟨⟨0, by simp⟩, by simp, rfl⟩⟩
  exact interior_eq_inside_frontier_of_isCompact hC hJ hne

theorem closure_inside_frontier_eq_of_homeomorphClosedBall {C : Set Plane}
    (φ : C ≃ₜ closedBall (0 : Plane) 1) :
    closure (inside (frontier C)) = C := by
  have hC : IsCompact C := isCompact_of_homeomorphClosedBall φ
  have hJ : IsJordanCurve (frontier C) := isJordanCurve_frontier_of_homeomorphClosedBall φ
  have hne : (interior C).Nonempty := by
    rw [interior_eq_image_of_homeomorphClosedBall φ]
    refine ⟨closedBallParam φ ⟨0, by simp⟩, ⟨⟨0, by simp⟩, by simp, rfl⟩⟩
  exact closure_inside_frontier_eq_of_isCompact hC hJ hne

theorem isTopologicalCell_union_of_subset {A B : Set Plane}
    (hB : Nonempty (↥B ≃ₜ closedBall (0 : Plane) 1)) (hAB : A ⊆ B) :
    Nonempty (↥(A ∪ B) ≃ₜ closedBall (0 : Plane) 1) := by
  have heq : (A ∪ B : Set Plane) = B := union_eq_self_of_subset_left hAB
  rw [heq]
  exact hB

theorem isTopologicalCell_union_of_subset_right {A B : Set Plane}
    (hA : Nonempty (↥A ≃ₜ closedBall (0 : Plane) 1)) (hBA : B ⊆ A) :
    Nonempty (↥(A ∪ B) ≃ₜ closedBall (0 : Plane) 1) := by
  have heq : (A ∪ B : Set Plane) = A := union_eq_self_of_subset_right hBA
  rw [heq]
  exact hA

theorem subset_of_inter_subset_interior {A B : Set Plane}
    (hA : IsClosed A) (hBconn : IsConnected B) (hne : (A ∩ B).Nonempty)
    (hsub : A ∩ B ⊆ interior A) : B ⊆ A := by
  have hdisj : Disjoint B (frontier A) := by
    refine disjoint_left.mpr fun x hxB hxfr => ?_
    have hxA : x ∈ A := hA.closure_subset (frontier_subset_closure hxfr)
    have hxint : x ∈ interior A := hsub ⟨hxA, hxB⟩
    exact (hA.frontier_eq ▸ hxfr).2 hxint
  have hcover : B ⊆ interior A ∪ Aᶜ := by
    intro x hx
    by_cases hxA : x ∈ A
    · by_cases hxint : x ∈ interior A
      · exact Or.inl hxint
      · exfalso
        have hxfr : x ∈ frontier A := ⟨subset_closure hxA, hxint⟩
        exact disjoint_left.mp hdisj hx hxfr
    · exact Or.inr hxA
  obtain ⟨p, hpA, hpB⟩ := hne
  have hpint : p ∈ interior A := hsub ⟨hpA, hpB⟩
  have hsub_int := hBconn.isPreconnected.subset_left_of_subset_union
    isOpen_interior hA.isOpen_compl
    (disjoint_compl_right.mono_left interior_subset)
    hcover ⟨p, hpB, hpint⟩
  exact hsub_int.trans interior_subset

end DifferentialGeometry.Topology.PlanarJordan
