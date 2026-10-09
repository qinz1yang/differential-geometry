/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PLImage

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

def HasPushPropertyAt (C D : Set (EuclideanSpace ℝ (Fin 3))) : Prop :=
  IsPLBall 3 C ∧ IsPLBall 2 D ∧ D ⊆ frontier C ∧
    ∀ f : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3),
      IsPLHomeomorphOn f (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D →
      ∀ N : Set (EuclideanSpace ℝ (Fin 3)), IsPolyhedron N →
        C \ (f '' stdSimplexBoundary 2) ⊆ interior N →
        ∃ h : EuclideanSpace ℝ (Fin 3) ≃ₜ EuclideanSpace ℝ (Fin 3),
          IsPLHomeomorphOn h univ univ ∧ h '' D = closure (frontier C \ D) ∧ EqOn h id Nᶜ

def HasPushProperty (C : Set (EuclideanSpace ℝ (Fin 3))) : Prop :=
  IsPLBall 3 C ∧ ∀ D : Set (EuclideanSpace ℝ (Fin 3)),
    IsPLBall 2 D → D ⊆ frontier C → HasPushPropertyAt C D

theorem HasPushPropertyAt.image {C D : Set (EuclideanSpace ℝ (Fin 3))}
    (hCD : HasPushPropertyAt C D)
    {e : EuclideanSpace ℝ (Fin 3) ≃ₜ EuclideanSpace ℝ (Fin 3)}
    (he : IsPLHomeomorphOn e univ univ) : HasPushPropertyAt (e '' C) (e '' D) := by
  obtain ⟨hC, hD, hDC, hpush⟩ := hCD
  have heC := he.restrict hC.isPolyhedron (subset_univ C)
  have heD := he.restrict hD.isPolyhedron (subset_univ D)
  have hC' := hC.of_isPLHomeomorphOn heC
  have hD' := hD.of_isPLHomeomorphOn heD
  refine ⟨hC', hD', ?_, ?_⟩
  · rw [← e.image_frontier]
    exact image_mono hDC
  intro f hf N hN hCN
  have hback := he.homeomorph_symm.restrict hD'.isPolyhedron (subset_univ _)
  rw [e.image_symm, e.injective.preimage_image] at hback
  have hg := hf.trans hback
  have hN' : IsPolyhedron (e ⁻¹' N) := by
    simpa only [univ_inter] using he.isPolyhedron_preimage hN (subset_univ N)
  have hCN' : C \ ((e.symm ∘ f) '' stdSimplexBoundary 2) ⊆ interior (e ⁻¹' N) := by
    rw [← e.preimage_interior]
    intro x hx
    apply hCN
    refine ⟨⟨x, hx.1, rfl⟩, ?_⟩
    rintro ⟨z, hz, hzx⟩
    apply hx.2
    refine ⟨z, hz, ?_⟩
    change e.symm (f z) = x
    rw [hzx, e.symm_apply_apply]
  obtain ⟨k, hk, hkD, hkfix⟩ := hpush (e.symm ∘ f) hg (e ⁻¹' N) hN' hCN'
  let H := e.symm.trans (k.trans e)
  refine ⟨H, (he.homeomorph_symm.trans hk).trans he, ?_, ?_⟩
  · calc
      H '' (e '' D) = e '' (k '' D) := by
        rw [image_image, image_image]
        congr 1
        funext x
        simp [H]
      _ = e '' closure (frontier C \ D) := congrArg (Set.image e) hkD
      _ = closure (frontier (e '' C) \ (e '' D)) := by
        rw [e.image_closure, Set.image_sdiff e.injective, e.image_frontier]
  · intro y hy
    have hpre : e.symm y ∈ (e ⁻¹' N)ᶜ := by
      simpa only [mem_compl_iff, mem_preimage, e.apply_symm_apply] using hy
    change e (k (e.symm y)) = y
    rw [hkfix hpre]
    exact e.apply_symm_apply y

theorem HasPushProperty.image {C : Set (EuclideanSpace ℝ (Fin 3))}
    (hC : HasPushProperty C)
    {e : EuclideanSpace ℝ (Fin 3) ≃ₜ EuclideanSpace ℝ (Fin 3)}
    (he : IsPLHomeomorphOn e univ univ) : HasPushProperty (e '' C) := by
  refine ⟨hC.1.of_isPLHomeomorphOn (he.restrict hC.1.isPolyhedron (subset_univ C)), ?_⟩
  intro D hD hDC
  have hD' := hD.of_isPLHomeomorphOn
    (he.homeomorph_symm.restrict hD.isPolyhedron (subset_univ D))
  have hboundary : e.symm '' frontier (e '' C) = frontier C := by
    rw [e.symm.image_frontier, e.image_symm, e.injective.preimage_image]
  have hD'C : e.symm '' D ⊆ frontier C := (image_mono hDC).trans hboundary.le
  have h := (hC.2 (e.symm '' D) hD' hD'C).image he
  have heD : e '' (e.symm '' D) = D := by
    rw [e.image_eq_preimage_symm, e.symm.injective.preimage_image]
  rwa [heD] at h

theorem hasPushProperty_image_iff {C : Set (EuclideanSpace ℝ (Fin 3))}
    {e : EuclideanSpace ℝ (Fin 3) ≃ₜ EuclideanSpace ℝ (Fin 3)}
    (he : IsPLHomeomorphOn e univ univ) : HasPushProperty (e '' C) ↔ HasPushProperty C := by
  constructor
  · intro h
    have h' := h.image he.homeomorph_symm
    rwa [e.image_symm, e.injective.preimage_image] at h'
  · exact fun h => h.image he

end DifferentialGeometry.Topology.PiecewiseLinear
