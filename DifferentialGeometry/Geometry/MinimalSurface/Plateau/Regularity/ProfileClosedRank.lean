/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Regularity.ProfileBoundaryRank
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Regularity.ProfileInteriorRank

noncomputable section

open Set Metric Manifold Bundle TopologicalSpace
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Geometry.Metric.BarrierProfile
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry

/-- The supplied smooth extension of the completed-profile Morrey disk is an
immersion on the whole closed disk, as is its composition with the inclusion
into the original target. The same extension provides ambient smoothness. -/
theorem closed_disk_immersion_of_completed_profile
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    (hd3 : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (a : ℝ) (ha : 0 < a)
    (ρ : M → ℝ) (hρ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ ρ)
    (hbase : ∀ x : M, 0 < ρ x → ρ x < a →
      ∀ v : TangentSpace 𝓘(ℝ, E) x, 0 ≤ hessFun g ρ x v v)
    (hcontact : ∀ x : M, ρ x = 0 → ∀ v : TangentSpace 𝓘(ℝ, E) x,
      v ≠ 0 → 0 < hessFun g ρ x v v) :
    let U : Opens M := ⟨{x | ρ x < a}, isOpen_lt hρ.continuous continuous_const⟩
    let δ : M → ℝ := fun x => cutoff a (ρ x)
    let hδ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ δ :=
      (cutoff_smooth a).contMDiff.comp hρ
    let hU : ∀ x : M, x ∈ U ↔ 0 < δ x :=
      fun x => (cutoff_pos_iff ha (ρ x)).symm
    let G := canonicalPositiveDomainMetric g hδ U hU
    let ι : C(U, M) := ⟨Subtype.val, continuous_subtype_val⟩
    ∀ (γU : freeLoop U) (q : C(closedDisk, U)),
      IsSmoothEmbeddedLoop (E := E) γU → IsMorreyDisk G γU q →
      (∀ θ : loopCircle, ρ (γU θ : M) = 0) →
      ∀ (Q : ℂ → U), SmoothDiskExtension (E := E) q Q →
        SmoothDiskExtension (E := E) (ι.comp q) (Subtype.val ∘ Q) ∧
        ∀ z ∈ closedBall (0 : ℂ) 1,
          Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) Q z) ∧
          Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (Subtype.val ∘ Q) z) := by
  intro U δ hδ hU G ι γU q hγ hq hγzero Q hQ
  obtain ⟨hAmbient, hBoundary⟩ :=
    boundary_immersion_of_profile_metric g a ha ρ hρ hbase hcontact
      γU q hγ hq hγzero Q hQ
  have hInterior := interior_immersion_of_completed_profile
    hd3 g a ha ρ hρ hbase hcontact γU q hγ hq hγzero Q hQ
  refine ⟨hAmbient, ?_⟩
  intro z hz
  have hRank : Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) Q z) := by
    rcases lt_or_eq_of_le (Metric.mem_closedBall.mp hz) with hlt | heq
    · exact hInterior z (Metric.mem_ball.mpr hlt)
    · have h := hBoundary z (Metric.mem_sphere.mpr heq)
      rw [DifferentialGeometry.Topology.mfderiv_subtypeVal_comp
        (I := 𝓘(ℝ, ℂ)) (J := 𝓘(ℝ, E)) U Q z] at h
      exact h
  refine ⟨hRank, ?_⟩
  rw [DifferentialGeometry.Topology.mfderiv_subtypeVal_comp
    (I := 𝓘(ℝ, ℂ)) (J := 𝓘(ℝ, E)) U Q z]
  exact hRank

end DifferentialGeometry.Geometry
