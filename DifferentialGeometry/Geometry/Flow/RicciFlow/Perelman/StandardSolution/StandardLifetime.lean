import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardCylinderScalarConvergence
import DifferentialGeometry.Geometry.Curvature.Bounds.ScalarNorm
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.VolumeCollapse
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardBlowupVolume
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardLifetimeBounds

noncomputable section
open Set Filter
open scoped Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow

theorem one_le_uniformStandardLifetime : 1 ≤ uniformStandardLifetime := by
  by_contra hnot
  have hlt : uniformStandardLifetime < 1 := lt_of_not_ge hnot
  have hfinite : uniformStandardLifetime ≠ ⊤ := ne_top_of_lt hlt
  let T := uniformStandardLifetime.toReal
  have hT : 0 < T := ENNReal.toReal_pos uniformStandardLifetime_pos.ne' hfinite
  have hLife : uniformStandardLifetime = ENNReal.ofReal T := (ENNReal.ofReal_toReal hfinite).symm
  have hT1 : T < 1 := by
    rw [hLife] at hlt
    exact ENNReal.ofReal_lt_one.mp hlt
  obtain ⟨S, t, x, R, D, v, _, hD, hv, hmem, hdom, htime, hscalar, hvolume⟩ :=
    exists_standard_family_scalar_blowup_sequence_with_positive_ball_volume hT hT1 hLife
  have hcollapse := standard_fixed_radius_volume_tendsto_zero_of_time_tendsto
    (fun n => (S n).val) x t hdom hT hT1
    (htime.mono_right nhdsWithin_le_nhds) hscalar hD
  have hle : ENNReal.ofReal v ≤ 0 := ge_of_tendsto hcollapse (hvolume.mono fun _ hn => hn.2)
  exact (not_le_of_gt (ENNReal.ofReal_pos.mpr hv)) hle

theorem uniformStandardLifetime_eq_one : uniformStandardLifetime = 1 :=
  le_antisymm uniformStandardLifetime_le_one one_le_uniformStandardLifetime

theorem StandardSolution.one_le_lifetime (S : StandardSolution) : 1 ≤ S.val.lifetime := by
  rw [← uniformStandardLifetime_eq_one]
  exact uniformStandardLifetime_le_lifetime S


theorem StandardSolution.lifetime_le_one (S : StandardSolution) : S.val.lifetime ≤ 1 := by
  by_contra hnot
  have hSlife : (1 : ℝ≥0∞) < S.val.lifetime := lt_of_not_ge hnot
  obtain ⟨K, hK, hcurv⟩ := S.val.curvature_bound 1 zero_le_one (by simpa using hSlife)
  let τ : ℝ := 1 - 1 / (9 * K + 2)
  have hden : 0 < 9 * K + 2 := by positivity
  have hinv : 0 < 1 / (9 * K + 2) := by positivity
  have hinv1 : 1 / (9 * K + 2) < 1 := (div_lt_one hden).mpr (by linarith)
  have hτ : 0 < τ := by dsimp only [τ]; linarith
  have hτ1 : τ < 1 := by dsimp only [τ]; linarith
  have hτLife : ENNReal.ofReal τ < uniformStandardLifetime := by
    rw [uniformStandardLifetime_eq_one]
    exact ENNReal.ofReal_lt_one.mpr hτ1
  let x : ℕ → EuclideanSpace ℝ (Fin 3) := fun n => EuclideanSpace.single 0 (n : ℝ)
  have hescape : Tendsto (fun n =>
      (DifferentialGeometry.riemannianEDistOf (S.val.metric 0) 0 (x n)).toReal) atTop atTop := by
    have heq : (fun n => (DifferentialGeometry.riemannianEDistOf (S.val.metric 0) 0 (x n)).toReal) =
        fun n : ℕ => (n : ℝ) := by
      funext n
      rw [S.val.initial, StandardCap.distance_zero]
      simp only [x, EuclideanSpace.single, PiLp.norm_single, Real.norm_eq_abs]
      exact abs_of_nonneg (Nat.cast_nonneg n)
    rw [heq]
    exact tendsto_natCast_atTop_atTop
  obtain ⟨ψ, _, hconv⟩ := exists_standard_scalar_cylinder_subsequence hτ hτ1 hτLife
    (fun _ => S) x hescape
  have hbound : ∀ n : ℕ,
      Geometry.Curvature.metricScalarAt (S.val.metric τ) (x (ψ n)) ≤ 9 * K := by
    intro n
    have hh := Geometry.Curvature.scalar_abs_le_rm (S.val.metric τ) (x (ψ n))
    change |Geometry.Curvature.metricScalarAt (S.val.metric τ) (x (ψ n))| ≤
      (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) : ℝ) ^ 2 * _ at hh
    norm_num only [finrank_euclideanSpace, Fintype.card_fin, Nat.cast_ofNat] at hh
    exact (le_abs_self _).trans (hh.trans
      (mul_le_mul_of_nonneg_left (hcurv τ ⟨hτ.le, hτ1.le⟩ (x (ψ n))) (by norm_num)))
  have hle : (1 - τ)⁻¹ ≤ 9 * K := le_of_tendsto hconv (Eventually.of_forall hbound)
  have heq : (1 - τ)⁻¹ = 9 * K + 2 := by
    dsimp only [τ]
    rw [sub_sub_cancel, one_div, inv_inv]
  rw [heq] at hle
  linarith

theorem StandardSolution.lifetime_eq_one (S : StandardSolution) : S.val.lifetime = 1 :=
  le_antisymm S.lifetime_le_one S.one_le_lifetime

end DifferentialGeometry.PDE.RicciFlow
