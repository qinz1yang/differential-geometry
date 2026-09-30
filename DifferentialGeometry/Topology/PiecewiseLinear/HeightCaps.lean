/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.HeightHalfDisk
import DifferentialGeometry.Topology.PiecewiseLinear.PlanarSpanningDisk
import DifferentialGeometry.Topology.PiecewiseLinear.BallReplacement

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_isPLSphere_pair_of_heightIndex_eq_zero
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsPLSphere 2 K.space) (hdimE : Module.finrank ℝ E = 3)
    (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) (hinj : InjOn ℓ K.vertices)
    (hzero : heightIndex K.space ℓ = 0) (r : ℝ)
    (hbelow : ∃ y ∈ K.space, ℓ y < r) (habove : ∃ z ∈ K.space, r < ℓ z)
    {W : Set E} (hW : IsOpen W) (hWconv : Convex ℝ W) (hKW : K.space ⊆ W) :
    ∃ (D : Set E) (g : (Fin 3 → ℝ) → E),
      IsPLHomeomorphOn g (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D ∧
      g '' stdSimplexBoundary 2 = K.space ∩ {x | ℓ x = r} ∧
      D ⊆ W ∩ {x | ℓ x = r} ∧ K.space ∩ D = g '' stdSimplexBoundary 2 ∧
      IsPLSphere 2 ((K.space ∩ {x | ℓ x ≤ r}) ∪ D) ∧
      IsPLSphere 2 ((K.space ∩ {x | r ≤ ℓ x}) ∪ D) ∧
      ((K.space ∩ {x | ℓ x ≤ r}) ∪ D) ∩ ((K.space ∩ {x | r ≤ ℓ x}) ∪ D) = D ∧
      (((K.space ∩ {x | ℓ x ≤ r}) ∪ D) ∪ ((K.space ∩ {x | r ≤ ℓ x}) ∪ D)) \
        (D \ (g '' stdSimplexBoundary 2)) = K.space := by
  let A := K.space ∩ {x | ℓ x ≤ r}
  let B := K.space ∩ {x | r ≤ ℓ x}
  let J := K.space ∩ {x | ℓ x = r}
  have hlinear : ℓ.toLinearMap ≠ 0 := by
    intro h
    apply hℓ
    ext x
    exact congrArg (fun a : E →ₗ[ℝ] ℝ => a x) h
  obtain ⟨f, h, hf, hh, hfJ, hhJ⟩ :=
    exists_isPLHomeomorphOn_halfSpaces_of_heightIndex_eq_zero K hK hdimE ℓ hℓ hinj hzero r hbelow
        habove
  have hJ := isPLSphere_one_fiber_of_heightIndex_eq_zero K hK hdimE ℓ hℓ hinj hzero r hbelow habove
  obtain ⟨D, g, hg, hgJ, hDW⟩ := hJ.exists_isPLHomeomorphOn_disk_of_subset_fiber hdimE
    ℓ.toLinearMap hlinear inter_subset_right hW hWconv (inter_subset_left.trans hKW)
  change g '' stdSimplexBoundary 2 = J at hgJ
  have hJD : J ⊆ D := by
    rw [← hgJ]
    rintro _ ⟨x, hx, rfl⟩
    exact hg.bijOn.mapsTo hx.1
  have hSD : K.space ∩ D = J := by
    ext x
    constructor
    · intro hx
      exact ⟨hx.1, (hDW hx.2).2⟩
    · intro hx
      exact ⟨hx.1, hJD hx⟩
  have hunion : A ∪ B = K.space := by
    apply Subset.antisymm (union_subset inter_subset_left inter_subset_left)
    intro x hx
    exact (le_total (ℓ x) r).elim (fun h => Or.inl ⟨hx, h⟩) (fun h => Or.inr ⟨hx, h⟩)
  have hinter : A ∩ B = J := by
    ext x
    constructor
    · rintro ⟨hxA, hxB⟩
      exact ⟨hxA.1, le_antisymm hxA.2 hxB.2⟩
    · intro hx
      exact ⟨⟨hx.1, (show ℓ x = r from hx.2).le⟩, hx.1, (show ℓ x = r from hx.2).ge⟩
  have hAD : A ∩ D = J := by
    apply Subset.antisymm (fun _ hx => hSD.subset ⟨hx.1.1, hx.2⟩)
    exact fun _ hx => ⟨⟨hx.1, (show ℓ _ = r from hx.2).le⟩, hJD hx⟩
  have hBD : B ∩ D = J := by
    apply Subset.antisymm (fun _ hx => hSD.subset ⟨hx.1.1, hx.2⟩)
    exact fun _ hx => ⟨⟨hx.1, (show ℓ _ = r from hx.2).ge⟩, hJD hx⟩
  obtain ⟨F, hF, -⟩ := exists_isPLHomeomorphOn_replace_ball
    (show IsPLBall 2 A from ⟨f, hf⟩).isPolyhedron hh hg hhJ hgJ hinter hAD
  obtain ⟨G, hG, -⟩ := exists_isPLHomeomorphOn_replace_ball
    (show IsPLBall 2 B from ⟨h, hh⟩).isPolyhedron hf hg hfJ hgJ
    ((inter_comm B A).trans hinter) hBD
  have hFA : IsPLSphere 2 (A ∪ D) := (hunion.symm ▸ hK).of_isPLHomeomorphOn hF
  have hGB : IsPLSphere 2 (B ∪ D) :=
    (((union_comm B A).trans hunion).symm ▸ hK).of_isPLHomeomorphOn hG
  refine ⟨D, g, hg, hgJ, hDW, hSD.trans hgJ.symm, hFA, hGB, ?_, ?_⟩
  · change (A ∪ D) ∩ (B ∪ D) = D
    rw [← inter_union_distrib_right, hinter, union_eq_right.mpr hJD]
  · change ((A ∪ D) ∪ (B ∪ D)) \ (D \ (g '' stdSimplexBoundary 2)) = K.space
    rw [hgJ]
    have hcover : (A ∪ D) ∪ (B ∪ D) = K.space ∪ D := by
      rw [← hunion]
      ext x
      simp only [mem_union]
      tauto
    rw [hcover]
    ext x
    constructor
    · rintro ⟨hxS | hxD, hnot⟩
      · exact hxS
      · exact (show x ∈ J by by_contra hxJ; exact hnot ⟨hxD, hxJ⟩).1
    · intro hxS
      exact ⟨Or.inl hxS, fun hx => hx.2 (hSD.subset ⟨hxS, hx.1⟩)⟩

end DifferentialGeometry.Topology.PiecewiseLinear
