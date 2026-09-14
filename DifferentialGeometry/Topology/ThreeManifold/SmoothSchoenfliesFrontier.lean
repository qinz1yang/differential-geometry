import DifferentialGeometry.Topology.SphereSeparation.SmoothSchoenfliesBallFilling
import DifferentialGeometry.Topology.ThreeManifold.schoenflies

open scoped ContDiff Manifold

namespace DifferentialGeometry.Topology.ThreeManifold

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)
local notation "S²" => Metric.sphere (0 : ℝ³) 1

theorem exists_ambient_diffeomorph_image_sphere_of_smoothSchoenfliesThree
    (h : SphereSeparation.smoothSchoenfliesThree) (e : S² → ℝ³)
    (he : Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e) :
    ∃ Φ : ℝ³ ≃ₘ[ℝ] ℝ³, Φ '' S² = Set.range e :=
  (SphereSeparation.smoothSchoenfliesThree_iff_exists_ambient_diffeomorph.mp h) e he

theorem exists_ambient_diffeomorph_image_sphere_of_smoothSchoenfliesBallFilling
    (h : SphereSeparation.smoothSchoenfliesBallFilling) (e : S² → ℝ³)
    (he : Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e) :
    ∃ Φ : ℝ³ ≃ₘ[ℝ] ℝ³, Φ '' S² = Set.range e :=
  exists_ambient_diffeomorph_image_sphere_of_smoothSchoenfliesThree
    (SphereSeparation.smoothSchoenfliesThree_iff_smoothSchoenfliesBallFilling.mpr h) e he

theorem smoothSchoenfliesThree_of_exists_ambient_diffeomorph_image_sphere
    (h : ∀ (e : S² → ℝ³),
      Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e →
        ∃ Φ : ℝ³ ≃ₘ[ℝ] ℝ³, Φ '' S² = Set.range e) :
    SphereSeparation.smoothSchoenfliesThree :=
  SphereSeparation.smoothSchoenfliesThree_iff_exists_ambient_diffeomorph.mpr h

theorem exists_ambient_diffeomorph_image_sphere_of_range_eq_sphere
    (e : S² → ℝ³) {c : ℝ³} {r : ℝ} (hr : 0 < r)
    (hrange : Set.range e = Metric.sphere c r) :
    ∃ Φ : ℝ³ ≃ₘ[ℝ] ℝ³, Φ '' S² = Set.range e := by
  obtain ⟨Φ, hΦ⟩ := exists_diffeomorph_image_sphere c hr
  exact ⟨Φ, by rw [hrange, hΦ]⟩

theorem exists_continuous_no_ambient_diffeomorph_image_sphere :
    ∃ e : S² → ℝ³,
      Continuous e ∧ ¬ ∃ Φ : ℝ³ ≃ₘ[ℝ] ℝ³, Φ '' S² = Set.range e := by
  refine ⟨fun _ => 0, continuous_const, ?_⟩
  rintro ⟨Φ, hΦ⟩
  rw [Set.range_const] at hΦ
  obtain ⟨u, hu⟩ := (NormedSpace.sphere_nonempty (x := (0 : ℝ³)) (r := (1 : ℝ))).mpr
    zero_le_one
  have hnu : (-u : ℝ³) ∈ S² := by
    simpa [Metric.mem_sphere, dist_eq_norm] using hu
  have hzu : Φ u = 0 := by
    have : Φ u ∈ ({0} : Set ℝ³) := by rw [← hΦ]; exact ⟨u, hu, rfl⟩
    simpa using this
  have hnzu : Φ (-u) = 0 := by
    have : Φ (-u) ∈ ({0} : Set ℝ³) := by rw [← hΦ]; exact ⟨-u, hnu, rfl⟩
    simpa using this
  have huu : u = -u := Φ.injective (hzu.trans hnzu.symm)
  have hnorm : ‖u‖ = 1 := by
    simpa [Metric.mem_sphere, dist_eq_norm] using hu
  have hsum : u + u = 0 :=
    (congrArg (fun v : ℝ³ => u + v) huu).trans (add_neg_cancel u)
  have htwo : (2 : ℝ) • u = 0 := by rw [two_smul]; exact hsum
  have hzero : ‖(2 : ℝ) • u‖ = 0 := by rw [htwo, norm_zero]
  rw [norm_smul, hnorm, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2),
    mul_one] at hzero
  norm_num at hzero

end DifferentialGeometry.Topology.ThreeManifold
