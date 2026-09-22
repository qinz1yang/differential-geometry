import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Positivity

set_option autoImplicit false
open Set Filter
open scoped Topology

theorem Isometry.isCompact_closedBall_of_punctured_closedBall
    {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y} (hf : Isometry f)
    {p : Y} {r : ℝ} (hcompact : IsCompact (Metric.closedBall p r))
    (hcover : Metric.closedBall p r ⊆ insert p (range f))
    {x : X} {R : ℝ} (hR : R < dist (f x) p) (hbuffer : dist (f x) p + R ≤ r) :
    IsCompact (Metric.closedBall x R) := by
  have hsub : Metric.closedBall (f x) R ⊆ Metric.closedBall p r := by
    intro y hy
    have htriangle := dist_triangle y (f x) p
    change dist y (f x) ≤ R at hy
    change dist y p ≤ r
    linarith only [htriangle, hy, hbuffer]
  have hK := hcompact.of_isClosed_subset Metric.isClosed_closedBall hsub
  have hrange : Metric.closedBall (f x) R ⊆ range f := by
    intro y hy
    rcases hcover (hsub hy) with h | h
    · rw [h] at hy
      have hdist : dist (f x) p ≤ R := by simpa only [Metric.mem_closedBall, dist_comm] using hy
      exact False.elim (hR.not_ge hdist)
    · exact h
  have hpre : f ⁻¹' Metric.closedBall (f x) R = Metric.closedBall x R := by
    ext y
    simp only [mem_preimage, Metric.mem_closedBall, hf.dist_eq]
  rw [← hpre]
  exact (hf.isEmbedding.isInducing.isCompact_preimage_iff hrange).mpr hK

theorem Isometry.eventually_isCompact_scaled_closedBall
    {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y} (hf : Isometry f)
    {q : Y} {r : ℝ} (hr : 0 < r) (hcompact : IsCompact (Metric.closedBall q r))
    (hcover : Metric.closedBall q r ⊆ insert q (range f))
    {x : ℕ → X} (hx : Tendsto (fun n => f (x n)) atTop (𝓝 q))
    {Q : ℕ → ℝ} {a : ℝ} (ha : 0 < a)
    (hquant : ∀ᶠ n in atTop, (2 * a) ^ 2 < Q n * dist (f (x n)) q ^ 2) :
    ∀ᶠ n in atTop, 0 < Q n ∧
      IsCompact (Metric.closedBall (x n) (a / Real.sqrt (Q n))) ∧
      ∀ y ∈ Metric.closedBall (x n) (a / Real.sqrt (Q n)),
        dist (f (x n)) q / 2 < dist (f y) q ∧
          dist (f y) q < 3 * dist (f (x n)) q / 2 := by
  have hd : Tendsto (fun n => dist (f (x n)) q) atTop (𝓝 (0 : ℝ)) :=
    tendsto_iff_dist_tendsto_zero.mp hx
  filter_upwards [hquant, hd.eventually (eventually_lt_nhds (half_pos hr))] with n hn hnear
  have hQ : 0 < Q n := by
    by_contra hQ
    have hh := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hQ) (sq_nonneg (dist (f (x n)) q))
    nlinarith only [hn, hh, sq_nonneg (2 * a)]
  have hsqrt : 0 < Real.sqrt (Q n) := Real.sqrt_pos.mpr hQ
  have hroot : 2 * a < Real.sqrt (Q n) * dist (f (x n)) q := by
    apply (sq_lt_sq₀ (by positivity) (mul_nonneg hsqrt.le dist_nonneg)).mp
    simpa only [mul_pow, Real.sq_sqrt hQ.le] using hn
  have hsmall : a / Real.sqrt (Q n) < dist (f (x n)) q / 2 := by
    apply (div_lt_iff₀ hsqrt).mpr
    nlinarith only [hroot]
  have hdistpos : 0 < dist (f (x n)) q := by
    have hh : 0 ≤ a / Real.sqrt (Q n) := by positivity
    linarith only [hh, hsmall]
  refine ⟨hQ, hf.isCompact_closedBall_of_punctured_closedBall hcompact hcover
    (hsmall.trans (half_lt_self hdistpos)) (by linarith only [hsmall, hnear, hr]), ?_⟩
  intro y hy
  have hxy : dist (f y) (f (x n)) ≤ a / Real.sqrt (Q n) := by
    rw [hf.dist_eq]
    exact hy
  have htri₁ := dist_triangle (f (x n)) (f y) q
  have htri₂ := dist_triangle (f y) (f (x n)) q
  rw [dist_comm (f (x n)) (f y)] at htri₁
  constructor <;> linarith only [htri₁, htri₂, hxy, hsmall]
