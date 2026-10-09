/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PlanarBoundaryCollars
import DifferentialGeometry.Topology.PiecewiseLinear.SphericalDiskComplement

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem IsPLSphere.exists_isPLBall_neighborhood {S D U : Set E}
    (hS : IsPLSphere 2 S) (hD : IsPLBall 2 D) (hDS : D ⊆ S) (hU : U ∈ 𝓝ˢ[S] D) :
    ∃ D' : Set E, IsPLBall 2 D' ∧ D' ⊆ S ∩ U ∧ D' ∈ 𝓝ˢ[S] D := by
  obtain ⟨O, hO, hDO, hOU⟩ := mem_nhdsSetWithin.mp hU
  let C := closure (S \ D)
  have hC : IsPLBall 2 C := hS.isPLBall_closure_sdiff hD hDS
  have hCS : C ⊆ S := closure_minimal sdiff_subset hS.isPolyhedron.isClosed
  obtain ⟨q, hq⟩ := id hC
  have hJ : q '' stdSimplexBoundary 2 = C ∩ D :=
    hS.image_stdSimplexBoundary_complement hD hDS hq
  have hOq : O ∈ 𝓝ˢ[C] (q '' stdSimplexBoundary 2) := by
    apply mem_nhdsSetWithin.mpr
    exact ⟨O, hO, fun x hx => hDO ((hJ ▸ hx).2), inter_subset_left⟩
  obtain ⟨A, B, ρ, hA, hB, hAO, hCAB, hρ, hρfix, hAB, -, -⟩ :=
    hq.exists_disk_boundary_collar hOq
  have hBC : B ⊆ C := fun x hx => hCAB.symm ▸ Or.inl hx
  have hBS : B ⊆ S := hBC.trans hCS
  have hJB : ∀ x ∈ q '' stdSimplexBoundary 2, x ∉ B := by
    intro x hxJ hxB
    have hxA : x ∈ A := by
      rw [← hρfix x hxJ]
      exact hρ.bijOn.mapsTo ⟨hxJ, by norm_num⟩
    obtain ⟨⟨y, t⟩, ⟨hy, ht⟩, hyx⟩ := hAB.subset ⟨hxA, hxB⟩
    have ht0 : t = 0 := ht
    have heq : (y, t) = (x, (1 : ℝ)) := hρ.bijOn.injOn
      ⟨hy, by rw [ht0]; norm_num⟩ ⟨hxJ, by norm_num⟩
      (hyx.trans (hρfix x hxJ).symm)
    have ht1 : t = 1 := congrArg Prod.snd heq
    linarith
  have hDB : ∀ x ∈ D, x ∉ B := by
    intro x hxD hxB
    exact hJB x (hJ.symm ▸ ⟨hBC hxB, hxD⟩) hxB
  have hcover : closure (S \ B) ⊆ D ∪ A := by
    apply closure_minimal _ (hD.isPolyhedron.isClosed.union hA.isClosed)
    intro x hx
    by_cases hxD : x ∈ D
    · exact Or.inl hxD
    · have hxC : x ∈ C := subset_closure ⟨hx.1, hxD⟩
      exact Or.inr ((hCAB ▸ hxC).resolve_left hx.2)
  have hsubS : closure (S \ B) ⊆ S :=
    closure_minimal sdiff_subset hS.isPolyhedron.isClosed
  refine ⟨closure (S \ B), hS.isPLBall_closure_sdiff hB hBS, ?_, ?_⟩
  · intro x hx
    have hxO : x ∈ O := (hcover hx).elim (hDO ·) (hAO ·)
    exact ⟨hsubS hx, hOU ⟨hxO, hsubS hx⟩⟩
  · apply mem_nhdsSetWithin.mpr
    refine ⟨Bᶜ, hB.isPolyhedron.isClosed.isOpen_compl, hDB, ?_⟩
    rintro x ⟨hxB, hxS⟩
    exact subset_closure ⟨hxS, hxB⟩

end DifferentialGeometry.Topology.PiecewiseLinear
