import DifferentialGeometry.Geometry.Comparison.Volume.Bishop.LocalBallRatio
import DifferentialGeometry.Geometry.Comparison.BonnetMyers.RicciPointwise
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventData

set_option autoImplicit false

noncomputable section

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private local instance : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp⟩

theorem exists_riemannianVolumeMeasure_ball_ge_of_rm_le :
    ∃ c : ℝ, 0 < c ∧ ∀ {P : OrientedThreeStage.{u}} (g : P.Metric) (p : P.Carrier) {r R : ℝ},
      0 < r → r ≤ R →
      (∀ x ∈ riemannianBallOf g p R, R ^ 4 * normSq0S g x 4 (metricRm04At g x) ≤ 1) →
      ENNReal.ofReal (c * (r / R) ^ 3) *
          riemannianVolumeMeasure ThreeModel P.Carrier g (riemannianBallOf g p R) ≤
        riemannianVolumeMeasure ThreeModel P.Carrier g (riemannianBallOf g p r) := by
  refine ⟨Real.exp (-6) / 8, by positivity, ?_⟩
  intro P g p r R hr hrR hRm
  have hR : 0 < R := hr.trans_le hrR
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp
  have hRic : ∀ y ∈ riemannianBallOf g p R, ∀ v : TangentSpace ThreeModel y,
      -(((Module.finrank ℝ ThreeSpace - 1 : ℕ) : ℝ) * (3 / R) ^ 2) * g.inner y v v ≤
        ricciTensor (I := ThreeModel) g y v v := by
    intro y hy v
    have hN4 : normSq0S g y 4 (metricRm04At g y) ≤ ((R ^ 2)⁻¹) ^ 2 := by
      rw [inv_pow, ← pow_mul, ← one_div, le_div_iff₀ (by positivity)]
      rw [show (2 * 2 : ℕ) = 4 by norm_num, mul_comm]
      exact hRm y hy
    have hsq : Real.sqrt (normSq0S g y 4 (metricRm04At g y)) ≤ (R ^ 2)⁻¹ :=
      (Real.sqrt_le_sqrt hN4).trans_eq (Real.sqrt_sq (by positivity))
    have hlow := Geometry.Riemannian.BonnetMyers.ricciLowerAt_of_rm (I := ThreeModel) g hsq v
    have hinner : 0 ≤ g.inner y v v := by
      rcases eq_or_ne v 0 with hv | hv
      · subst v
        simp
      · exact (g.pos y v hv).le
    rw [hdim] at hlow ⊢
    have hcoef : -(((3 - 1 : ℕ) : ℝ) * (3 / R) ^ 2) ≤ -(((3 : ℕ) : ℝ) ^ 2 * (R ^ 2)⁻¹) := by
      rw [div_pow]
      field_simp
      norm_num
    exact (mul_le_mul_of_nonneg_right hcoef hinner).trans hlow
  have hmain := Geometry.Riemannian.VolumeComparison.riemannianBallOf_volume_ratio_ge_of_ricci_lower
    g (RiemannianMetricComplete.of_compact g) p (q := 3 / R) (by positivity) hr hrR hRic
  have hc : Real.exp (-(3 / R * ((Module.finrank ℝ ThreeSpace - 1 : ℕ) : ℝ) * R)) *
      (r / (2 * R)) ^ Module.finrank ℝ ThreeSpace = Real.exp (-6) / 8 * (r / R) ^ 3 := by
    rw [hdim]
    have h6 : 3 / R * ((3 - 1 : ℕ) : ℝ) * R = 6 := by
      field_simp
      norm_num
    rw [h6]
    field_simp
    ring
  rwa [hc] at hmain

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
