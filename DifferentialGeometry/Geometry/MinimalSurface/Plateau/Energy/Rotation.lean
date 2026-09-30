import DifferentialGeometry.Analysis.Calculus.Manifold.LinearEquiv
import DifferentialGeometry.Analysis.Integration.PlaneRotation
import DifferentialGeometry.Analysis.Complex.BoundaryLens.Rotation
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.Lipschitz

noncomputable section

open Manifold Set Filter MeasureTheory
open scoped Manifold ContDiff NNReal ENNReal Topology



namespace DifferentialGeometry.Topology

open DifferentialGeometry.Geometry (diskExtension diskExtension_coe)

def rotatedDiskMap {M : Type*} [TopologicalSpace M]
    (u : C(closedDisk, M)) (ζ : Circle) : C(closedDisk, M) :=
  u.comp ⟨fun z => ⟨rotation ζ z, by
    simpa only [Metric.mem_closedBall, dist_zero_right, LinearIsometryEquiv.norm_map]
      using z.property⟩,
    ((rotation ζ).continuous.comp continuous_subtype_val).subtype_mk _⟩

@[simp]
theorem rotatedDiskMap_apply {M : Type*} [TopologicalSpace M]
    (u : C(closedDisk, M)) (ζ : Circle) (z : closedDisk) :
    rotatedDiskMap u ζ z = u ⟨rotation ζ z, by
      simpa only [Metric.mem_closedBall, dist_zero_right, LinearIsometryEquiv.norm_map]
        using z.property⟩ := rfl

theorem diskExtension_rotatedDiskMap_eq {M : Type*} [TopologicalSpace M]
    (u : C(closedDisk, M)) (ζ : Circle) {z : ℂ} (hz : z ∈ Metric.closedBall 0 1) :
    diskExtension (rotatedDiskMap u ζ) z = diskExtension u (rotation ζ z) := by
  rw [diskExtension_coe _ ⟨z, hz⟩, rotatedDiskMap_apply,
    diskExtension_coe u ⟨rotation ζ z, by
      simpa only [Metric.mem_closedBall, dist_zero_right, LinearIsometryEquiv.norm_map]
        using hz⟩]

theorem rotatedDiskMap_diskBoundary {M : Type*} [TopologicalSpace M]
    (u : C(closedDisk, M)) (d t : ℝ) :
    rotatedDiskMap u (Circle.exp (2 * Real.pi * d)) (diskBoundary (t : loopCircle)) =
      u (diskBoundary ((d + t : ℝ) : loopCircle)) := by
  apply congrArg u
  apply Subtype.ext
  change rotation (Circle.exp (2 * Real.pi * d)) (diskBoundary (t : loopCircle) : ℂ) =
    (diskBoundary ((d + t : ℝ) : loopCircle) : ℂ)
  simp only [diskBoundary_coe, rotation_apply, Circle.coe_exp]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem rotatedDiskMap_trace_lift {M : Type*} [TopologicalSpace M]
    (u : C(closedDisk, M)) (γ : freeLoop M) (ψ : ℝ → ℝ)
    (htrace : ∀ t : ℝ, u (diskBoundary (t : loopCircle)) = γ (ψ t : loopCircle))
    (d t : ℝ) :
    rotatedDiskMap u (Circle.exp (2 * Real.pi * d)) (diskBoundary (t : loopCircle)) =
      γ (ψ (d + t) : loopCircle) := by
  rw [rotatedDiskMap_diskBoundary, htrace]

end DifferentialGeometry.Topology

namespace DifferentialGeometry.Geometry

open DifferentialGeometry.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

theorem riemannian_lipschitz_rotatedDiskMap
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {u : C(closedDisk, M)} {K : ℝ≥0}
    (hu : ∀ x y, riemannianEDistOf g (u x) (u y) ≤ (K : ℝ≥0∞) * edist x y)
    (ζ : Circle) (x y : closedDisk) :
    riemannianEDistOf g (rotatedDiskMap u ζ x) (rotatedDiskMap u ζ y) ≤
      (K : ℝ≥0∞) * edist x y := by
  have h := hu ⟨rotation ζ x, by
      simpa only [Metric.mem_closedBall, dist_zero_right, LinearIsometryEquiv.norm_map]
        using x.property⟩ ⟨rotation ζ y, by
      simpa only [Metric.mem_closedBall, dist_zero_right, LinearIsometryEquiv.norm_map]
        using y.property⟩
  change riemannianEDistOf g (rotatedDiskMap u ζ x) (rotatedDiskMap u ζ y) ≤
    (K : ℝ≥0∞) * edist (rotation ζ (x : ℂ)) (rotation ζ (y : ℂ)) at h
  change riemannianEDistOf g (rotatedDiskMap u ζ x) (rotatedDiskMap u ζ y) ≤
    (K : ℝ≥0∞) * edist (x : ℂ) (y : ℂ)
  simpa only [(rotation ζ).isometry.edist_eq] using h

theorem diskMapEnergyDensity_comp_rotation
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (u : ℂ → M) (ζ : Circle) (z : ℂ) :
    diskMapEnergyDensity g (u ∘ rotation ζ) z = diskMapEnergyDensity g u (rotation ζ z) := by
  have hd := (rotation ζ).toContinuousLinearEquiv.comp_right_mfderiv (I := 𝓘(ℝ, E)) u z
  have hd' : (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (u ∘ rotation ζ) z : ℂ →L[ℝ] E) =
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) u (rotation ζ z) : ℂ →L[ℝ] E).comp
        (rotation ζ).toContinuousLinearMap := hd
  unfold diskMapEnergyDensity diskMapPartial
  change ((g.inner (u (rotation ζ z)) : E →L[ℝ] E →L[ℝ] ℝ)
      ((mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (u ∘ rotation ζ) z : ℂ →L[ℝ] E) (1 : ℂ))
      ((mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (u ∘ rotation ζ) z : ℂ →L[ℝ] E) (1 : ℂ)) +
    (g.inner (u (rotation ζ z)) : E →L[ℝ] E →L[ℝ] ℝ)
      ((mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (u ∘ rotation ζ) z : ℂ →L[ℝ] E) Complex.I)
      ((mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (u ∘ rotation ζ) z : ℂ →L[ℝ] E) Complex.I)) / 2 = _
  rw [hd']
  change ((g.inner (u (rotation ζ z)) : E →L[ℝ] E →L[ℝ] ℝ)
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) u (rotation ζ z) (rotation ζ 1))
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) u (rotation ζ z) (rotation ζ 1)) +
    (g.inner (u (rotation ζ z)) : E →L[ℝ] E →L[ℝ] ℝ)
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) u (rotation ζ z) (rotation ζ Complex.I))
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) u (rotation ζ z) (rotation ζ Complex.I))) / 2 = _
  exact congrArg (fun t : ℝ => t / 2)
    (Analysis.quadratic_sum_comp_rotation
      (g.inner (u (rotation ζ z)) : E →L[ℝ] E →L[ℝ] ℝ)
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) u (rotation ζ z) : ℂ →L[ℝ] E) ζ)

theorem integral_diskMapEnergyDensity_comp_rotation_preimage
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (u : ℂ → M) (ζ : Circle) (s : Set ℂ) :
    (∫ z in rotation ζ ⁻¹' s, diskMapEnergyDensity g (u ∘ rotation ζ) z) =
      ∫ z in s, diskMapEnergyDensity g u z := by
  simp_rw [diskMapEnergyDensity_comp_rotation]
  exact (rotation ζ).measurePreserving.setIntegral_preimage_emb
    (rotation ζ).toMeasurableEquiv.measurableEmbedding (diskMapEnergyDensity g u) s

theorem integral_diskMapEnergyDensity_rotatedDiskMap_preimage
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (u : C(closedDisk, M)) (ζ : Circle)
    {s : Set ℂ} (hs : s ⊆ Metric.closedBall (0 : ℂ) 1) :
    (∫ z in rotation ζ ⁻¹' s, diskMapEnergyDensity g (diskExtension (rotatedDiskMap u ζ)) z) =
      ∫ z in s, diskMapEnergyDensity g (diskExtension u) z := by
  have hsub : rotation ζ ⁻¹' s ⊆ Metric.closedBall (0 : ℂ) 1 := by
    intro z hz
    have h := hs hz
    simpa only [Metric.mem_closedBall, dist_zero_right, LinearIsometryEquiv.norm_map] using h
  rw [← integral_diskMapEnergyDensity_comp_rotation_preimage g (diskExtension u) ζ s]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub ae_disk_interior] with z hz
  have heq : diskExtension (rotatedDiskMap u ζ) =ᶠ[𝓝 z] diskExtension u ∘ rotation ζ := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hz] with w hw
    exact diskExtension_rotatedDiskMap_eq u ζ (Metric.ball_subset_closedBall hw)
  unfold diskMapEnergyDensity diskMapPartial
  rw [heq.mfderiv_eq, heq.eq_of_nhds]
  rfl

theorem integral_diskMapEnergyDensity_rotatedDiskMap
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (u : C(closedDisk, M)) (ζ : Circle) :
    (∫ z in Metric.closedBall (0 : ℂ) 1,
      diskMapEnergyDensity g (diskExtension (rotatedDiskMap u ζ)) z) =
      ∫ z in Metric.closedBall (0 : ℂ) 1, diskMapEnergyDensity g (diskExtension u) z := by
  have hs : rotation ζ ⁻¹' Metric.closedBall (0 : ℂ) 1 = Metric.closedBall (0 : ℂ) 1 := by
    ext z
    simp only [mem_preimage, Metric.mem_closedBall, dist_zero_right, LinearIsometryEquiv.norm_map]
  simpa only [hs] using
    integral_diskMapEnergyDensity_rotatedDiskMap_preimage g u ζ (s := Metric.closedBall 0 1)
      (subset_refl _)

theorem integral_diskMapEnergyDensity_rotatedDiskMap_boundaryLens
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (u : C(closedDisk, M)) (ζ : Circle) (a : ℝ) :
    (∫ z in Analysis.boundaryLens a,
      diskMapEnergyDensity g (diskExtension (rotatedDiskMap u ζ)) z) =
      ∫ z in Metric.closedBall (rotation ζ (-1)) a ∩ Metric.closedBall (0 : ℂ) 1,
        diskMapEnergyDensity g (diskExtension u) z := by
  simpa only [Analysis.preimage_rotated_boundaryLens] using
    integral_diskMapEnergyDensity_rotatedDiskMap_preimage g u ζ
      (s := Metric.closedBall (rotation ζ (-1)) a ∩ Metric.closedBall (0 : ℂ) 1)
      inter_subset_right

end DifferentialGeometry.Geometry

end
