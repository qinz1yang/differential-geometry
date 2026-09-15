import DifferentialGeometry.Analysis.Schauder.Cutoff.Parabolic.Ball

noncomputable section

open Set
open scoped ContDiff

namespace DifferentialGeometry.Analysis.Schauder

variable {V : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

theorem parabolicBallCutoff_contDiff
    (a t₀ t₁ b : ℝ) (ha : a < t₀) (ht : t₀ ≤ t₁) (hb : t₁ < b)
    (center : V) {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R) :
    ContDiff ℝ ∞ (fun p : ℝ × V ↦
      parabolicBallCutoff a t₀ t₁ b ha ht hb center hr hrR p.1 p.2) := by
  change ContDiff ℝ ∞ (fun p : ℝ × V ↦
    ballCutoff (intervalCutoffCenter t₀ t₁)
      (intervalCutoffInnerRadius t₀ t₁) (intervalCutoffOuterRadius a t₀ t₁ b) p.1 *
        ballCutoff center r R p.2)
  exact ((ballCutoff_contDiff _ _ _).comp contDiff_fst).mul
    ((ballCutoff_contDiff _ _ _).comp contDiff_snd)

theorem parabolicBallCutoff_tsupport_subset_closedBall_prod
    (a t₀ t₁ b : ℝ) (ha : a < t₀) (ht : t₀ ≤ t₁) (hb : t₁ < b)
    (center : V) {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R) :
    tsupport (fun p : ℝ × V ↦
      parabolicBallCutoff a t₀ t₁ b ha ht hb center hr hrR p.1 p.2) ⊆
        Metric.closedBall (intervalCutoffCenter t₀ t₁)
          (intervalCutoffOuterRadius a t₀ t₁ b) ×ˢ Metric.closedBall center R := by
  apply closure_minimal _ (Metric.isClosed_closedBall.prod Metric.isClosed_closedBall)
  intro p hp
  change ballCutoff (intervalCutoffCenter t₀ t₁)
      (intervalCutoffInnerRadius t₀ t₁) (intervalCutoffOuterRadius a t₀ t₁ b) p.1 *
        ballCutoff center r R p.2 ≠ 0 at hp
  obtain ⟨hleft, hright⟩ := mul_ne_zero_iff.mp hp
  exact ⟨Metric.ball_subset_closedBall
      (ballCutoff_support_subset_ball (intervalCutoffInnerRadius_nonneg ht)
        (intervalCutoffInnerRadius_lt_outerRadius ha hb) hleft),
    Metric.ball_subset_closedBall (ballCutoff_support_subset_ball hr hrR hright)⟩

theorem parabolicBallCutoff_hasCompactSupport
    (a t₀ t₁ b : ℝ) (ha : a < t₀) (ht : t₀ ≤ t₁) (hb : t₁ < b)
    (center : V) {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R) :
    HasCompactSupport (fun p : ℝ × V ↦
      parabolicBallCutoff a t₀ t₁ b ha ht hb center hr hrR p.1 p.2) := by
  exact ((isCompact_closedBall (intervalCutoffCenter t₀ t₁)
      (intervalCutoffOuterRadius a t₀ t₁ b)).prod
      (isCompact_closedBall center R)).of_isClosed_subset (isClosed_tsupport _)
    (parabolicBallCutoff_tsupport_subset_closedBall_prod a t₀ t₁ b ha ht hb center hr hrR)

theorem parabolicBallCutoff_tsupport_subset_Ioo_prod_ball
    (a t₀ t₁ b : ℝ) (ha : a < t₀) (ht : t₀ ≤ t₁) (hb : t₁ < b)
    (center : V) {r R S : ℝ} (hr : 0 ≤ r) (hrR : r < R) (hRS : R < S) :
    tsupport (fun p : ℝ × V ↦
      parabolicBallCutoff a t₀ t₁ b ha ht hb center hr hrR p.1 p.2) ⊆
        Ioo a b ×ˢ Metric.ball center S := by
  exact (parabolicBallCutoff_tsupport_subset_closedBall_prod
      a t₀ t₁ b ha ht hb center hr hrR).trans
    (Set.prod_mono (intervalCutoff_closedBall_subset_Ioo ha hb)
      (Metric.closedBall_subset_ball hRS))

end DifferentialGeometry.Analysis.Schauder
