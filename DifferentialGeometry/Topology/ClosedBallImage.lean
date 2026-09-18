/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.OpenEmbeddingFrontier
import DifferentialGeometry.Topology.BicollaredComplement
import Mathlib.Analysis.Normed.Module.Connected

/-!
# Images of closed balls under homeomorphisms
-/

open Set Metric

namespace DifferentialGeometry.Topology

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

noncomputable def closedBallParam {C : Set E} (φ : C ≃ₜ closedBall (0 : E) 1) :
    closedBall (0 : E) 1 → E := fun b => (φ.symm b : E)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem continuous_closedBallParam {C : Set E} (φ : C ≃ₜ closedBall (0 : E) 1) :
    Continuous (closedBallParam φ) :=
  continuous_subtype_val.comp φ.symm.continuous

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem injective_closedBallParam {C : Set E} (φ : C ≃ₜ closedBall (0 : E) 1) :
    Function.Injective (closedBallParam φ) := fun _ _ hab =>
  φ.symm.injective (Subtype.ext hab)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem range_closedBallParam {C : Set E} (φ : C ≃ₜ closedBall (0 : E) 1) :
    range (closedBallParam φ) = C := by
  ext y
  constructor
  · rintro ⟨b, rfl⟩
    exact (φ.symm b).2
  · intro hy
    exact ⟨φ ⟨y, hy⟩, congrArg Subtype.val (φ.symm_apply_apply ⟨y, hy⟩)⟩

theorem isCompact_of_homeomorphClosedBall {C : Set E} (φ : C ≃ₜ closedBall (0 : E) 1) :
    IsCompact C := by
  have hB : CompactSpace (closedBall (0 : E) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall 0 1)
  have _ : CompactSpace C := φ.symm.compactSpace
  exact isCompact_iff_compactSpace.mpr inferInstance

theorem interior_eq_image_of_homeomorphClosedBall {C : Set E}
    (φ : C ≃ₜ closedBall (0 : E) 1) :
    interior C =
      closedBallParam φ '' ((Subtype.val : closedBall (0 : E) 1 → E) ⁻¹' ball 0 1) := by
  have h := interior_range_eq_image_preimage_interior (isCompact_closedBall (0 : E) 1)
    (closedBallParam φ) (continuous_closedBallParam φ) (injective_closedBallParam φ)
  rw [range_closedBallParam φ, interior_closedBall (0 : E) one_ne_zero] at h
  exact h

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem univ_sdiff_preimage_ball :
    (univ : Set (closedBall (0 : E) 1)) \
        ((Subtype.val : closedBall (0 : E) 1 → E) ⁻¹' ball 0 1) =
      (Subtype.val : closedBall (0 : E) 1 → E) ⁻¹' sphere 0 1 := by
  ext b
  have hb : dist (b : E) 0 ≤ 1 := by simpa only [mem_closedBall] using b.2
  simp only [Set.mem_sdiff, mem_univ, true_and, mem_preimage, mem_ball, mem_sphere, not_lt]
  constructor
  · intro h
    exact le_antisymm hb h
  · intro h
    exact h.ge

theorem frontier_eq_image_sphere_of_homeomorphClosedBall {C : Set E}
    (φ : C ≃ₜ closedBall (0 : E) 1) :
    frontier C =
      closedBallParam φ '' ((Subtype.val : closedBall (0 : E) 1 → E) ⁻¹' sphere 0 1) := by
  have hC : IsCompact C := isCompact_of_homeomorphClosedBall φ
  rw [hC.isClosed.frontier_eq, interior_eq_image_of_homeomorphClosedBall φ,
    ← univ_sdiff_preimage_ball (E := E),
    Set.image_sdiff (injective_closedBallParam φ), image_univ, range_closedBallParam φ]

theorem isConnected_frontier_of_homeomorphClosedBall (hrank : 1 < Module.rank ℝ E)
    {C : Set E} (φ : C ≃ₜ closedBall (0 : E) 1) : IsConnected (frontier C) := by
  have hsp : IsConnected (sphere (0 : E) 1) := isConnected_sphere hrank 0 zero_le_one
  have _ : ConnectedSpace (sphere (0 : E) 1) := isConnected_iff_connectedSpace.mp hsp
  have hcont : Continuous
      (fun s : sphere (0 : E) 1 =>
        closedBallParam φ ⟨s.1, sphere_subset_closedBall s.2⟩) :=
    (continuous_closedBallParam φ).comp (continuous_subtype_val.subtype_mk _)
  have himg :
      closedBallParam φ '' ((Subtype.val : closedBall (0 : E) 1 → E) ⁻¹' sphere 0 1) =
        range (fun s : sphere (0 : E) 1 =>
          closedBallParam φ ⟨s.1, sphere_subset_closedBall s.2⟩) := by
    ext y
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact ⟨⟨b.1, hb⟩, rfl⟩
    · rintro ⟨s, rfl⟩
      exact ⟨⟨s.1, sphere_subset_closedBall s.2⟩, s.2, rfl⟩
  rw [frontier_eq_image_sphere_of_homeomorphClosedBall φ, himg]
  exact isConnected_range hcont

theorem interior_nonempty_of_homeomorphClosedBall {C : Set E}
    (φ : C ≃ₜ closedBall (0 : E) 1) : (interior C).Nonempty := by
  rw [interior_eq_image_of_homeomorphClosedBall φ]
  exact ⟨closedBallParam φ ⟨0, by simp⟩, ⟨0, by simp⟩, by simp, rfl⟩

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem compl_nonempty_of_isCompact [NoncompactSpace E] {C : Set E} (hC : IsCompact C) :
    Cᶜ.Nonempty := by
  refine Set.nonempty_compl.mpr ?_
  intro hCuniv
  rw [hCuniv] at hC
  exact (not_compactSpace_iff.mpr (inferInstance : NoncompactSpace E))
    (isCompact_univ_iff.mp hC)

theorem isCompact_frontier_of_homeomorphClosedBall {C : Set E}
    (φ : C ≃ₜ closedBall (0 : E) 1) : IsCompact (frontier C) :=
  (isCompact_of_homeomorphClosedBall φ).of_isClosed_subset isClosed_frontier
    (isCompact_of_homeomorphClosedBall φ).isClosed.frontier_subset

theorem isConnected_compl_of_homeomorphClosedBall_of_isBicollared [NoncompactSpace E]
    (hrank : 1 < Module.rank ℝ E) {C : Set E} (φ : C ≃ₜ closedBall (0 : E) 1)
    (hbi : IsBicollared (frontier C)) : IsConnected Cᶜ :=
  isConnected_compl_of_isBicollared_frontier
    (isCompact_of_homeomorphClosedBall φ).isClosed
    (isCompact_frontier_of_homeomorphClosedBall φ)
    (isConnected_frontier_of_homeomorphClosedBall hrank φ)
    (interior_nonempty_of_homeomorphClosedBall φ)
    (compl_nonempty_of_isCompact (isCompact_of_homeomorphClosedBall φ)) hbi

end DifferentialGeometry.Topology
