import DifferentialGeometry.Geometry.Metric.Convergence.Scalar
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.MetricRicciDifference


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff

private theorem pinching_from_three_error_bounds
    {R c B delta q hq r ric : ℝ}
    (hR : 0 ≤ R) (hc : 0 ≤ c) (hc1 : c ≤ 1) (hB : 0 ≤ B)
    (hd0 : 0 ≤ delta) (hd1 : delta ≤ 1) (hq0 : 0 ≤ q) (hhq : 0 ≤ hq)
    (hsmall : (1296 + 3 * R + 4 * B) * delta ≤ (1 / 3 - c) * R)
    (hric : (R / 3) * q - 1296 * delta * q ≤ ric)
    (hr : r ≤ R + B * delta) (hm : hq ≤ (1 + 3 * delta) * q) :
    c * r * hq ≤ ric := by
  have hprod : (R + B * delta) * (1 + 3 * delta) ≤
      R + (3 * R + 4 * B) * delta := by
    nlinarith [mul_nonneg (mul_nonneg hB hd0) (sub_nonneg.mpr hd1)]
  have hrest : 0 ≤ (3 * R + 4 * B) * delta := by positivity
  have hcRest : c * ((3 * R + 4 * B) * delta) ≤ (3 * R + 4 * B) * delta :=
    mul_le_of_le_one_left hrest hc1
  have hcoef : c * (R + B * delta) * (1 + 3 * delta) ≤
      c * R + (3 * R + 4 * B) * delta := by
    nlinarith [mul_le_mul_of_nonneg_left hprod hc]
  have hfinal : c * R + (3 * R + 4 * B) * delta ≤ R / 3 - 1296 * delta := by
    nlinarith [hsmall]
  calc
    c * r * hq = (c * hq) * r := by ring
    _ ≤ (c * hq) * (R + B * delta) :=
      mul_le_mul_of_nonneg_left hr (mul_nonneg hc hhq)
    _ = (c * (R + B * delta)) * hq := by ring
    _ ≤ (c * (R + B * delta)) * ((1 + 3 * delta) * q) :=
      mul_le_mul_of_nonneg_left hm (by positivity)
    _ = (c * (R + B * delta) * (1 + 3 * delta)) * q := by ring
    _ ≤ (c * R + (3 * R + 4 * B) * delta) * q :=
      mul_le_mul_of_nonneg_right hcoef hq0
    _ ≤ (R / 3 - 1296 * delta) * q := mul_le_mul_of_nonneg_right hfinal hq0
    _ = (R / 3) * q - 1296 * delta * q := by ring
    _ ≤ ric := hric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [BoundarylessManifold I M]


theorem metric_ricci_pinching_of_relative_two_jets
    (g h : SmoothRiemannianMetric I M) (hdim : Module.finrank ℝ E = 3)
    (x : M) {R c delta : ℝ} (hR : 0 < R) (hc : 0 ≤ c) (hcUpper : c < 1 / 3)
    (hscalar : metricScalarAt g x = R)
    (hEin : ∀ v : TangentSpace I x, ricciTensor g x v v = (R / 3) * g.inner x v v)
    (hd0 : 0 ≤ delta) (hd1 : delta ≤ 1 / 6)
    (hsmall : (1296 + 3 * R + 4 * (9 * (864 + 2 * (R / 3)))) * delta ≤
      (1 / 3 - c) * R)
    (hjet : ∀ a : ℕ, a ≤ 2 → metricDerivNorm a h g g x ≤ delta) :
    ∀ v : TangentSpace I x,
      c * metricScalarAt h x * h.inner x v v ≤ ricciTensor h x v v := by
  have hdimSmall : (Module.finrank ℝ E : ℝ) * delta ≤ 1 / 2 := by
    rw [hdim]
    norm_num
    linarith
  have hdOne : delta ≤ 1 := by linarith
  have hKb : ∀ v : TangentSpace I x,
      |ricciTensor g x v v| ≤ (R / 3) * g.inner x v v := by
    intro v
    rw [hEin v, abs_of_nonneg]
    exact mul_nonneg (div_nonneg hR.le (by norm_num))
      (DifferentialGeometry.metric_inner_self_nonneg g x v)
  have hs := metricScalar_difference_le_relative_two_jets g h x hd0 hdOne hdimSmall hjet hKb
  rw [hdim, hscalar] at hs
  norm_num only [Nat.cast_ofNat, Nat.reducePow] at hs
  intro v
  have hq := DifferentialGeometry.metric_inner_self_nonneg g x v
  have hhq := DifferentialGeometry.metric_inner_self_nonneg h x v
  have hr := metricRicci_difference_le_relative_two_jets g h x hd0 hdOne hdimSmall hjet v
  rw [hdim, hEin v] at hr
  norm_num only [Nat.cast_ofNat] at hr
  have hm0 := metricQuadFormDiff_le_metricDerivNorm h g g x v
  change |h.inner x v v - g.inner x v v| ≤
    (Module.finrank ℝ E : ℝ) * metricDerivNorm 0 h g g x * g.inner x v v at hm0
  rw [hdim] at hm0
  norm_num only [Nat.cast_ofNat] at hm0
  have hm1 : (3 : ℝ) * metricDerivNorm 0 h g g x * g.inner x v v ≤
      3 * delta * g.inner x v v :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hjet 0 (by norm_num)) (by norm_num)) hq
  apply pinching_from_three_error_bounds hR.le hc (by linarith : c ≤ 1)
    (by positivity : 0 ≤ 9 * (864 + 2 * (R / 3))) hd0 hdOne hq hhq hsmall
  · have hrlo := (abs_le.mp hr).1
    nlinarith
  · have hsup := (abs_le.mp hs).2
    nlinarith
  · have hupper := (abs_le.mp (hm0.trans hm1)).2
    nlinarith


theorem metric_ricci_pinching_eventually_of_round_convergence [CompactSpace M]
    (gSeq : ℕ → SmoothRiemannianMetric I M) (g : SmoothRiemannianMetric I M)
    (hdim : Module.finrank ℝ E = 3) {R : ℝ} (hR : 0 < R)
    (hscalar : ∀ x : M, metricScalarAt g x = R)
    (hEin : ∀ x : M, ∀ v : TangentSpace I x,
      ricciTensor g x v v = (R / 3) * g.inner x v v)
    (hconv : MetricCInfConvergenceOnCompacts gSeq g g)
    {c : ℝ} (hc : 0 ≤ c) (hcUpper : c < 1 / 3) :
    ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k → ∀ x : M,
      0 < metricScalarAt (gSeq k) x ∧ ∀ v : TangentSpace I x,
        c * metricScalarAt (gSeq k) x * (gSeq k).inner x v v ≤
          ricciTensor (gSeq k) x v v := by
  let B : ℝ := 9 * (864 + 2 * (R / 3))
  let C : ℝ := 1296 + 3 * R + 4 * B
  let delta : ℝ := min (1 / 6)
    (min (((1 / 3 - c) * R) / (C + 1)) (R / (2 * (B + 1))))
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hd0 : 0 < delta := by dsimp [delta]; positivity
  have hd1 : delta ≤ 1 / 6 := min_le_left _ _
  have hdC : C * delta ≤ (1 / 3 - c) * R := by
    have h := (le_div_iff₀ (by positivity : 0 < C + 1)).mp
      ((min_le_right _ _).trans (min_le_left _ _): delta ≤ ((1 / 3 - c) * R) / (C + 1))
    nlinarith [hd0]
  have hdB : B * delta < R / 2 := by
    have h := (le_div_iff₀ (by positivity : 0 < 2 * (B + 1))).mp
      ((min_le_right _ _).trans (min_le_right _ _): delta ≤ R / (2 * (B + 1)))
    nlinarith [hd0]
  obtain ⟨k0, hk0⟩ := hconv univ isCompact_univ 2 delta hd0
  refine ⟨k0, fun k hk x => ?_⟩
  have hjet (a : ℕ) (ha : a ≤ 2) : metricDerivNorm a (gSeq k) g g x ≤ delta :=
    (derivNorm_le_sup isCompact_univ ha (gSeq k) g g (mem_univ x)).trans (hk0 k hk).le
  refine ⟨?_, metric_ricci_pinching_of_relative_two_jets g (gSeq k) hdim x hR hc hcUpper
    (hscalar x) (hEin x) hd0.le hd1 hdC hjet⟩
  have hKb : ∀ v : TangentSpace I x, |ricciTensor g x v v| ≤ (R / 3) * g.inner x v v := by
    intro v
    rw [hEin x v, abs_of_nonneg]
    exact mul_nonneg (div_nonneg hR.le (by norm_num))
      (DifferentialGeometry.metric_inner_self_nonneg g x v)
  have hsmall : (Module.finrank ℝ E : ℝ) * delta ≤ 1 / 2 := by rw [hdim]; norm_num; linarith
  have hs := metricScalar_difference_le_relative_two_jets g (gSeq k) x hd0.le
    (by linarith : delta ≤ 1) hsmall hjet hKb
  rw [hdim, hscalar x] at hs
  have hs' : |metricScalarAt (gSeq k) x - R| ≤ B * delta := by
    norm_num at hs
    simpa only [B] using hs
  have hlow := (abs_le.mp hs').1
  linarith

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
