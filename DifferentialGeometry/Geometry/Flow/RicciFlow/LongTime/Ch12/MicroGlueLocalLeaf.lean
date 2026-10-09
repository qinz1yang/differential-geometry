import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BoundedCurvatureAtDistanceLimit
import DifferentialGeometry.Geometry.Measure.BallComparison

/-!
# CH12-O3, group 1a: the volume leaf of the KL70.2 kernel with a LOCAL terminal volume test

In the kernel `ST/BoundedCurvatureAtDistanceBoundedThreshold.lean:900` the noncollapsing hypothesis
`TerminalNoncollapsedBefore κ ρ t` is only consumed by the two volume leaves
(`BoundedCurvatureAtDistanceLimit.lean:32`, `BoundedCurvatureAtDistanceCone.lean:108`).  Their output
is a lower volume bound, at the terminal time, of normalized balls centred in a normalized ball about
the blow-up centre `x n`.

Here that output is produced from a *terminal-time, spatially local* hypothesis:
`vol B(z, b) ≥ κ b³` for every `z` with `d(x n, z) < σ n` and every `b ≤ σ n`, where
`σ n · √Q n → ∞`.  No earlier time and no global noncollapsing are used.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace GC.LongTime.Ch12

universe u

/-- One-index form: a local terminal volume test at physical scale `σ` gives the normalized volume
lower bound at every centre of the normalized closed ball of radius `r`, at normalized radius `a`,
as soon as `r < σ √Q` and `a ≤ σ √Q`. -/
theorem scaled_ball_volume_of_local_O3 {M : Type*} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric ThreeModel M) (x y : M) {Q σ κ r a : ℝ} (hQ : 0 < Q)
    (ha : 0 < a) (hrσ : r < σ * Real.sqrt Q) (haσ : a ≤ σ * Real.sqrt Q)
    (hy : y ∈ riemannianClosedBallOf (scaleMetric Q hQ g) x r)
    (hloc : ∀ z : M, riemannianEDistOf g x z < ENNReal.ofReal σ → ∀ b : ℝ, 0 < b → b ≤ σ →
      ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
        riemannianVolumeMeasure ThreeModel M g (riemannianBallOf g z b)) :
    ENNReal.ofReal (κ * a ^ 3) ≤
      riemannianVolumeMeasure ThreeModel M (scaleMetric Q hQ g)
        (riemannianBallOf (scaleMetric Q hQ g) y a) := by
  have hsq : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
  -- the physical distance from `x` to `y`
  have hyd : riemannianEDistOf g x y < ENNReal.ofReal σ := by
    have hy' : riemannianEDistOf (scaleMetric Q hQ g) x y ≤ ENNReal.ofReal r := hy
    rw [DifferentialGeometry.edistOf_scale] at hy'
    have hr0 : r / Real.sqrt Q < σ := (div_lt_iff₀ hsq).mpr hrσ
    have hle : riemannianEDistOf g x y ≤ ENNReal.ofReal (r / Real.sqrt Q) := by
      have hmul : ENNReal.ofReal (Real.sqrt Q) * riemannianEDistOf g x y ≤
          ENNReal.ofReal (Real.sqrt Q) * ENNReal.ofReal (r / Real.sqrt Q) := by
        rw [← ENNReal.ofReal_mul hsq.le, mul_div_cancel₀ _ hsq.ne']
        exact hy'
      exact (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.mpr hsq).ne'
        ENNReal.ofReal_ne_top).mp hmul
    exact hle.trans_lt ((ENNReal.ofReal_lt_ofReal_iff
      (pos_of_mul_pos_left (lt_of_lt_of_le ha haσ) hsq.le)).mpr hr0)
  have hb : 0 < a / Real.sqrt Q := div_pos ha hsq
  have hbσ : a / Real.sqrt Q ≤ σ := (div_le_iff₀ hsq).mpr haσ
  have hv := hloc y hyd (a / Real.sqrt Q) hb hbσ
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  have hscaled :=
    (DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_ball_ge_scaleMetric_iff
      g Q hQ y (a / Real.sqrt Q) (ENNReal.ofReal κ)).mpr (by simpa only [hdim] using hv)
  have hscale : Real.sqrt Q * (a / Real.sqrt Q) = a := mul_div_cancel₀ _ hsq.ne'
  rw [hscale, hdim] at hscaled
  rcases le_or_gt κ 0 with hκ | hκ
  · rw [ENNReal.ofReal_of_nonpos (mul_nonpos_of_nonpos_of_nonneg hκ (by positivity))]
    exact bot_le
  · simpa only [ENNReal.ofReal_mul hκ.le, ENNReal.ofReal_pow ha.le] using hscaled

/-- Sequence form, in exactly the shape of the `hvol` input of
`ObservedHistory.exists_terminal_pointed_convergence_of_buffered_backward_traces`
(`TracedTerminalCompactness.lean:170`), without its `R < rho` restriction. -/
theorem normalized_inner_ball_volume_local_O3 {M : ℕ → Type u} [∀ n, TopologicalSpace (M n)]
    [∀ n, ChartedSpace ThreeSpace (M n)] [∀ n, IsManifold ThreeModel ∞ (M n)]
    [∀ n, T2Space (M n)] [∀ n, SigmaCompactSpace (M n)]
    (g : ∀ n, SmoothRiemannianMetric ThreeModel (M n)) (x : ∀ n, M n) (Q : ℕ → ℝ)
    (hQ : ∀ n, 1 ≤ Q n) {κ : ℝ} (hκ : 0 < κ) (σ : ℕ → ℝ)
    (hσ : Tendsto (fun n => σ n * Real.sqrt (Q n)) atTop atTop)
    (hloc : ∀ᶠ n in atTop, ∀ z : M n, riemannianEDistOf (g n) (x n) z < ENNReal.ofReal (σ n) →
      ∀ b : ℝ, 0 < b → b ≤ σ n →
        ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
          riemannianVolumeMeasure ThreeModel (M n) (g n) (riemannianBallOf (g n) z b)) :
    ∀ r R : ℝ, 0 < r → r < R → ∀ J : ℝ, 0 ≤ J →
      ∃ a κ' : ℝ, 0 < a ∧ 0 < κ' ∧ r + a ≤ R ∧ a ^ 4 * J ^ 2 ≤ 1 ∧
      ∀ᶠ n in atTop, ∀ y ∈ riemannianClosedBallOf
        (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (g n)) (x n) r,
        ENNReal.ofReal (κ' * a ^ 3) ≤ riemannianVolumeMeasure ThreeModel (M n)
          (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (g n))
          (riemannianBallOf (scaleMetric (Q n) (zero_lt_one.trans_le (hQ n)) (g n)) y a) := by
  intro r R hr hrR J hJ
  let a := min (R - r) (min 1 (1 / (J + 1)))
  have ha : 0 < a := lt_min (sub_pos.mpr hrR) (lt_min one_pos (by positivity))
  have haR : a ≤ R - r := min_le_left _ _
  have ha1 : a ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have haJ' : a ≤ 1 / (J + 1) := (min_le_right _ _).trans (min_le_right _ _)
  have haJ : a * (J + 1) ≤ 1 := (le_div_iff₀ (by positivity)).mp haJ'
  have hasmall : a ^ 4 * J ^ 2 ≤ 1 := by
    have h1 : a ^ 2 ≤ a := by nlinarith
    have h2 : a ^ 2 * J ≤ 1 :=
      (mul_le_mul_of_nonneg_right h1 hJ).trans (by nlinarith)
    have hh := pow_le_pow_left₀ (mul_nonneg (sq_nonneg a) hJ) h2 2
    nlinarith only [hh]
  refine ⟨a, κ, ha, hκ, by linarith, hasmall, ?_⟩
  filter_upwards [hσ.eventually_gt_atTop R, hloc] with n hn hlocn y hy
  exact scaled_ball_volume_of_local_O3 (g n) (x n) y (zero_lt_one.trans_le (hQ n)) ha
    (hrR.trans hn) (by linarith) hy hlocn

end GC.LongTime.Ch12
