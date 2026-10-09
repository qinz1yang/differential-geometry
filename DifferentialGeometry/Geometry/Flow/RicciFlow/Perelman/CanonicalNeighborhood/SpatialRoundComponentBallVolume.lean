import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialRoundComponentVolume
import DifferentialGeometry.Geometry.Comparison.Volume.Bishop.LocalBallRatio
import DifferentialGeometry.Geometry.Comparison.BonnetMyers.RicciPointwise
import DifferentialGeometry.Geometry.Curvature.Bounds.ScalarNorm
import DifferentialGeometry.Geometry.Metric.ConnectedComponentDistance
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventData

set_option autoImplicit false
noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private local instance : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp⟩

theorem sqrt_scalarAt_mul_le_three_of_rm_le {M : Type u} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M] [T2Space M] (g : SmoothRiemannianMetric I3 M)
    (x : M)
    {r : ℝ} (hcurv : r ^ 4 * normSq0S g x 4 (metricRm04At g x) ≤ 1) :
    Real.sqrt (metricScalarAt g x) * r ≤ 3 := by
  rcases lt_or_ge r 0 with hr | hr
  · nlinarith [Real.sqrt_nonneg (metricScalarAt g x)]
  set N := normSq0S g x 4 (metricRm04At g x) with hNdef
  have hN : 0 ≤ N := normSq0S_nonneg _ _ _ _
  have hscalar : metricScalarAt g x ≤ 9 * Real.sqrt N := by
    have hh := (le_abs_self (metricScalarAt g x)).trans (scalar_abs_le_rm g x)
    change metricScalarAt g x ≤ (Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * _ at hh
    norm_num [ThreeSpace] at hh
    exact hh
  have hsN : Real.sqrt N * r ^ 2 ≤ 1 := by
    have hsq : (r ^ 2 * Real.sqrt N) ^ 2 ≤ 1 := by
      rw [mul_pow, ← pow_mul, Real.sq_sqrt hN]
      exact hcurv
    have hnn : 0 ≤ r ^ 2 * Real.sqrt N := by positivity
    nlinarith
  rcases le_or_gt (metricScalarAt g x) 0 with hQ | hQ
  · rw [Real.sqrt_eq_zero'.mpr hQ, zero_mul]
    norm_num
  have hQr : (Real.sqrt (metricScalarAt g x) * r) ^ 2 ≤ 3 ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hQ.le]
    nlinarith [sq_nonneg r]
  exact abs_le_of_sq_le_sq' hQr (by norm_num) |>.2

theorem exists_ball_volume_of_spatialRoundComponent (C1 C2 : ℝ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ {P : OrientedThreeStage.{u}} {g : P.Metric} {x : P.Carrier} {eps : ℝ}
      (W : SpatialCanonicalWitness g eps C1 C2 x), W.domain.carrier = connectedComponent x →
      SpatialRoundComponent g eps x W.domain.carrier →
      SimplyConnectedSpace (connectedComponent x) → ∀ r : ℝ, 0 < r →
      r ^ 4 * normSq0S g x 4 (metricRm04At g x) ≤ 1 →
      ENNReal.ofReal (κ * r ^ 3) ≤
        riemannianVolumeMeasure I3 P.Carrier g (riemannianBallOf g x r) := by
  set A := max C1 1 with hAdef
  set B := max C2 1 with hBdef
  have hA : 1 ≤ A := le_max_right _ _
  have hB : 1 ≤ B := le_max_right _ _
  refine ⟨Real.exp (-(18 * A * Real.sqrt B)) * (4 * Real.sqrt 3 * Real.pi) / (216 * A ^ 3),
    by positivity, ?_⟩
  intro P g x eps W whole D hsc r hr hcurv
  set Q := metricScalarAt g x with hQdef
  have hQ : 0 < Q := W.Q_pos
  have hsQ : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
  have hsQsq : Real.sqrt Q ^ 2 = Q := Real.sq_sqrt hQ.le
  set L := 3 * A / Real.sqrt Q with hLdef
  have hL : 0 < L := by positivity
  have hrL : r ≤ L := by
    have h3 := sqrt_scalarAt_mul_le_three_of_rm_le g x hcurv
    rw [hLdef, le_div_iff₀ hsQ]
    nlinarith
  have hball : riemannianBallOf g x L ⊆ W.domain.carrier := by
    rw [whole]
    exact DifferentialGeometry.Geometry.Metric.edistOf_ball_subset_connCompOpen
      (I := I3) g x L
  have hdomain : W.domain.carrier ⊆ riemannianBallOf g x L := by
    refine W.inside_ball.trans (riemannianBallOf_mono g x ?_)
    have hrad : W.radius ≤ A / Real.sqrt Q :=
      W.radius_upper.trans (div_le_div_of_nonneg_right (le_max_left _ _) hsQ.le)
    have hApos : 0 ≤ A / Real.sqrt Q := by positivity
    rw [hLdef, mul_div_assoc]
    linarith
  set q := 3 * Real.sqrt (B * Q) with hqdef
  have hq : 0 ≤ q := by positivity
  have hRic : ∀ y ∈ riemannianBallOf g x L, ∀ v : TangentSpace I3 y,
      -(((Module.finrank ℝ ThreeSpace - 1 : ℕ) : ℝ) * q ^ 2) * g.inner y v v ≤
        ricciTensor (I := I3) g y v v := by
    intro y hy v
    have hrm : Real.sqrt (normSq0S g y 4 (metricRm04At g y)) ≤ B * Q :=
      (W.rm_bound y (hball hy)).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) hQ.le)
    have hlow := Geometry.Riemannian.BonnetMyers.ricciLowerAt_of_rm (I := I3) g hrm v
    have hinner : 0 ≤ g.inner y v v := by
      rcases eq_or_ne v 0 with hv | hv
      · subst v
        simp
      · exact (g.pos y v hv).le
    have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp
    rw [hdim] at hlow ⊢
    have hq2 : q ^ 2 = 9 * (B * Q) := by
      rw [hqdef, mul_pow, Real.sq_sqrt (by positivity)]
      norm_num
    have hcoef : -(((3 - 1 : ℕ) : ℝ) * q ^ 2) ≤ -(((3 : ℕ) : ℝ) ^ 2 * (B * Q)) := by
      rw [hq2]
      norm_num
      nlinarith [mul_pos (zero_lt_one.trans_le hB) hQ]
    exact (mul_le_mul_of_nonneg_right hcoef hinner).trans hlow
  have hmain :=
    Geometry.Riemannian.VolumeComparison.riemannianBallOf_volume_ratio_ge_of_ricci_lower g
      (RiemannianMetricComplete.of_compact g) x hq hr hrL hRic
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp
  rw [hdim] at hmain
  have hU : ENNReal.ofReal (4 * Real.sqrt 3 * Real.pi / (Q * Real.sqrt Q)) ≤
      riemannianVolumeMeasure I3 P.Carrier g (riemannianBallOf g x L) := by
    rw [← whole] at hsc
    exact (D.volume_lower_of_simplyConnected).trans (measure_mono hdomain)
  have hexp : q * ((3 - 1 : ℕ) : ℝ) * L = 18 * A * Real.sqrt B := by
    rw [hqdef, hLdef, Real.sqrt_mul (by positivity)]
    field_simp
    norm_num
  rw [hexp] at hmain
  have hcoef : Real.exp (-(18 * A * Real.sqrt B)) * (4 * Real.sqrt 3 * Real.pi) /
        (216 * A ^ 3) * r ^ 3 =
      Real.exp (-(18 * A * Real.sqrt B)) * (r / (2 * L)) ^ 3 *
        (4 * Real.sqrt 3 * Real.pi / (Q * Real.sqrt Q)) := by
    rw [hLdef]
    have hQ3 : Q * Real.sqrt Q = Real.sqrt Q ^ 3 := by rw [pow_succ, hsQsq]
    rw [hQ3]
    field_simp
    ring
  rw [hcoef, ENNReal.ofReal_mul (by positivity)]
  exact (mul_le_mul' le_rfl hU).trans hmain

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
