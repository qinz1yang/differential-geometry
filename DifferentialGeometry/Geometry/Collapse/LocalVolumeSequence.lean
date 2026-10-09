import DifferentialGeometry.Geometry.Collapse.LocalVolumeCube
import DifferentialGeometry.Geometry.Metric.Approximation.RiemannianExtraction
import DifferentialGeometry.Geometry.Metric.Approximation.LimitVolumeLowerBound

set_option autoImplicit false

noncomputable section

open Set Metric Filter Bundle Manifold
open scoped Manifold ContDiff Topology ENNReal
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Geometry.Comparison.Toponogov GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

universe u v

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {Z : ℕ → Type u} [∀ n, MetricSpace (Z n)] [∀ n, CompleteSpace (Z n)]
  [∀ n, ChartedSpace H (Z n)] [∀ n, IsManifold I ∞ (Z n)]
  [∀ n, T2Space (TangentBundle I (Z n))] [∀ n, SigmaCompactSpace (Z n)]
  {X : Type v} [MetricSpace X] {p : ∀ n, Z n} {x : X}

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

/-- The LC15 binding on the original convergent sequence, without extracting another limit. -/
theorem eventually_volume_ball_two_lower_of_growing_sectional_bound
    (g : ∀ n, SmoothRiemannianMetric I (Z n))
    (hmetric : ∀ n a b, riemannianEDistOf (g n) a b = ENNReal.ofReal (dist a b))
    (hdim : Module.finrank ℝ E = 3) {κ ρ : ℕ → ℝ}
    (hκ : ∀ n, 0 ≤ κ n) (hκzero : Tendsto κ atTop (𝓝 0))
    (hρ : Tendsto ρ atTop atTop)
    (hsec : ∀ n, ∀ y ∈ ball (p n) (ρ n), SectionalBoundedBelowAt (g n) y (-κ n))
    (hconv : PointedGHConverges p x) (hdimlo : 2 < dimH (univ : Set X)) :
    ∃ v : ℝ, 0 < v ∧ ∀ᶠ n in atTop, ENNReal.ofReal v ≤ ballVolume (g n) (p n) 2 := by
  have hcompκ : ∀ R : ℝ, 0 < R →
      ∀ᶠ n in atTop, fourPointComparison (κ n) (ball (p n) R) := by
    intro R _
    filter_upwards [hρ.eventually (eventually_gt_atTop (8 * R))] with n hn
    exact fourPointComparison_of_sectional_lower_bound_on_eight_ball (g n) (hmetric n)
      (p n) (hκ n) (fun y hy => hsec n y (ball_subset_ball hn.le hy))
  have hcomp : ∀ R : ℝ, 0 < R →
      ∀ᶠ n in atTop, fourPointComparison 1 (ball (p n) R) := by
    intro R _
    filter_upwards [hρ.eventually (eventually_gt_atTop (8 * R)),
      hκzero.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with n hn hkn
    exact fourPointComparison_of_sectional_lower_bound_on_eight_ball (g n) (hmetric n)
      (p n) (by norm_num) (fun y hy =>
        (hsec n y (ball_subset_ball hn.le hy)).mono (by linarith))
  have hcompX := hconv.fourPointComparison_zero_of_eventual_comparison hκ hκzero hcompκ
  let B : ℝ → ℝ := fun R => 16 * Real.sqrt 3 * Real.sinh (2 * R)
  have hB : ∀ R : ℝ, 0 < R → 0 ≤ B R := by
    intro R hR
    dsimp [B]
    positivity
  have hcover : ∀ R : ℝ, 0 < R → ∀ η : ℝ, 0 < η → η ≤ 1 →
      ∀ᶠ n in atTop, ∃ S : Finset (Z n), S.card ≤ (1 + Nat.ceil (B R / η)) ^ 3 ∧
        (∀ y ∈ S, dist y (p n) ≤ R) ∧
        ∀ y : Z n, dist y (p n) ≤ R → ∃ z ∈ S, dist y z ≤ η := by
    intro R hR η hη _
    filter_upwards [eventual_internal_nets_of_growing_sectional_lower_bound
      g hmetric p hκzero hρ hsec hR hη] with n hn
    obtain ⟨S, hcard, hS, hnet⟩ := hn
    refine ⟨S, ?_, fun y hy => hS hy, fun y hy => ?_⟩
    · norm_num [hdim, B] at hcard ⊢
      exact hcard
    · obtain ⟨z, hz, hyz⟩ := hnet y hy
      exact ⟨z, hz, hyz.le⟩
  have hdimhi := hconv.dimH_le_of_ceil_covering 3 B hB hcover
  have hcurves := fun n (a b : Z n) (η : ℝ) (hη : 0 < η) =>
    exists_arbitrarily_short_riemannian_curve (g n) (hmetric n) a b hη
  let : ∀ n, MeasurableSpace (Z n) := fun n => borel (Z n)
  let : ∀ n, BorelSpace (Z n) := fun n => ⟨rfl⟩
  obtain ⟨v, hv, htail⟩ := hconv.eventually_normalizedHausdorffMeasure_ball_lower_bound
    hcurves hcomp hcompX hdimlo hdimhi
  refine ⟨v, hv, ?_⟩
  filter_upwards [htail] with n hn
  let : RiemannianBundle (fun y : Z n => TangentSpace I y) := ⟨(g n).toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun y : Z n => TangentSpace I y) :=
    ⟨⟨(g n).inner, (g n).contMDiff.continuous, fun y a b => rfl⟩⟩
  let : IsRiemannianManifold I (Z n) := ⟨fun a b => by
    change edist a b = riemannianEDistOf (g n) a b
    rw [edist_dist, hmetric]⟩
  have hEnorm : IsMetricNorm (I := I) (g n) := isMetricNorm_of_riemannianBundle (g n)
  rw [normalizedHausdorffMeasure_three_apply_eq_riemannianVolumeMeasure_apply
    (g n) hEnorm hdim (ball (p n) 2)] at hn
  simpa only [ballVolume, riemannianBallOf_eq_ball_of_isMetricNorm
    (g n) hEnorm (p n) 2] using hn

end DifferentialGeometry.Geometry.Collapse
