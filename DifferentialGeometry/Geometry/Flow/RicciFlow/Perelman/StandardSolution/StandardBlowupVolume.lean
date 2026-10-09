import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardDistanceComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardExteriorVolume
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardUniformCurvatureBlowup

noncomputable section
open Set Filter Manifold MeasureTheory DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

theorem standard_uniform_high_scalar_ball_volume_lower
    {T : ℝ} (hT : 0 < T) (hT1 : T < 1)
    (hTLife : ENNReal.ofReal T ≤ uniformStandardLifetime) :
    ∃ R Q D v : ℝ, 0 < R ∧ 0 < Q ∧ 0 < D ∧ 0 < v ∧
      ∀ (S : StandardSolution) (t : ℝ) (x : E3), t ∈ Ico 0 T →
        Q < metricScalarAt (S.val.metric t) x →
        ‖x‖ < R ∧ ENNReal.ofReal v ≤
          riemannianVolumeMeasure (𝓡 3) E3 (S.val.metric t)
            (riemannianBallOf (S.val.metric t) x D) := by
  obtain ⟨R, Q, hR, hQ, hexterior⟩ := standard_uniform_exterior_scalar_bound hT hT1 hTLife
  obtain ⟨p, v, hv, hvolume⟩ := exists_standard_uniform_fixed_ball_volume_lower hT hT1 hTLife
  let D := R + ‖p‖ + 1
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨R, Q, D, v, hR, hQ, hD, hv, ?_⟩
  intro S t x ht hscalar
  have hx : ‖x‖ < R := by
    by_contra h
    exact hscalar.not_ge (hexterior S t ht x (le_of_not_gt h))
  have htdom : t ∈ S.val.domain := by
    exact (mem_lifetimeInterval_carrier S.val.lifetime S.val.lifetime_pos t).mpr
      ⟨ht.1, ((ENNReal.ofReal_lt_ofReal_iff hT).mpr ht.2).trans_le
        (hTLife.trans (uniformStandardLifetime_le_lifetime S))⟩
  refine ⟨hx, (hvolume S t ht).trans ?_⟩
  exact measure_mono (S.val.euclidean_ball_subset_riemannianBallOf htdom p x hx.le)

theorem exists_standard_family_scalar_blowup_sequence_with_positive_ball_volume
    {T : ℝ} (hT : 0 < T) (hT1 : T < 1)
    (hLifetime : uniformStandardLifetime = ENNReal.ofReal T) :
    ∃ (S : ℕ → StandardSolution) (t : ℕ → ℝ) (x : ℕ → E3) (R D v : ℝ),
      0 < R ∧ 0 < D ∧ 0 < v ∧ (∀ n, t n ∈ Ioo 0 T) ∧
      (∀ n, t n ∈ (S n).val.domain) ∧ Tendsto t atTop (𝓝[<] T) ∧
      Tendsto (fun n => metricScalarAt ((S n).val.metric (t n)) (x n)) atTop atTop ∧
      ∀ᶠ n in atTop, ‖x n‖ < R ∧ ENNReal.ofReal v ≤
        riemannianVolumeMeasure (𝓡 3) E3 ((S n).val.metric (t n))
          (riemannianBallOf ((S n).val.metric (t n)) (x n) D) := by
  obtain ⟨S, t, x, hmem, hdomain, htime, hscalar⟩ :=
    standard_family_scalar_blowup_sequence hT hT1 hLifetime
  obtain ⟨R, Q, D, v, hR, _, hD, hv, hvolume⟩ :=
    standard_uniform_high_scalar_ball_volume_lower hT hT1 hLifetime.symm.le
  refine ⟨S, t, x, R, D, v, hR, hD, hv, hmem, hdomain, htime, hscalar, ?_⟩
  filter_upwards [hscalar.eventually (eventually_gt_atTop Q)] with n hn
  exact hvolume (S n) (t n) (x n) ⟨(hmem n).1.le, (hmem n).2⟩ hn

end DifferentialGeometry.PDE.RicciFlow
