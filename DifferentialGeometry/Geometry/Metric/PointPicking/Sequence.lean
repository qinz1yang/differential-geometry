import DifferentialGeometry.Geometry.Metric.RiemannianPointPicking

noncomputable section
open Filter Set
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.SmoothRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

theorem exists_point_selection_of_tendsto_atTop_on_compact_balls
    {M : ℕ → Type*} [∀ n, TopologicalSpace (M n)] [∀ n, ChartedSpace H (M n)]
    [∀ n, IsManifold I ∞ (M n)] [∀ n, RegularSpace (M n)] [∀ n, PreconnectedSpace (M n)]
    (g : ∀ n, SmoothRiemannianMetric I (M n)) (p y : ∀ n, M n)
    (f : ∀ n, M n → ℝ) {D : ℝ} (hD : 0 ≤ D)
    (hcompact : ∀ n, IsCompact (riemannianClosedBallOf (g n) (p n) (D + 1)))
    (hcont : ∀ n, ContinuousOn (f n) (riemannianClosedBallOf (g n) (p n) (D + 1)))
    (hy : ∀ n, riemannianEDistOf (g n) (p n) (y n) ≤ ENNReal.ofReal D)
    (hfy : ∀ n, 0 < f n (y n))
    (hlim : Tendsto (fun n => f n (y n)) atTop atTop) :
    ∃ (x : ∀ n, M n) (r : ℕ → ℝ),
      (∀ n, 0 < r n ∧ r n < D + 1 ∧
        (riemannianEDistOf (g n) (p n) (x n)).toReal < D + 1 ∧ 0 < f n (x n)) ∧
      Tendsto (fun n => f n (x n)) atTop atTop ∧
      Tendsto (fun n => f n (x n) * r n ^ 2) atTop atTop ∧
      (∀ n, r n = (D + 1-(riemannianEDistOf (g n) (p n) (x n)).toReal)/4) ∧
      (∀ n, f n (y n)/16 ≤ f n (x n) * r n ^ 2) ∧
      (∀ n, IsCompact (riemannianClosedBallOf (g n) (x n) (r n))) ∧
      ∀ n z, (riemannianEDistOf (g n) (x n) z).toReal ≤ r n →
        (riemannianEDistOf (g n) (p n) z).toReal < D + 1 ∧
          f n z ≤ (16/9 : ℝ) * f n (x n) := by
  classical
  have hyD (n : ℕ) : (riemannianEDistOf (g n) (p n) (y n)).toReal ≤ D :=
    ENNReal.toReal_le_of_le_ofReal hD (hy n)
  have hselect := fun n => (g n).exists_weighted_point_selection (eta := 1/4)
    (hcompact n) (hcont n) (lt_of_le_of_lt (hyD n) (by linarith)) (hfy n) (by norm_num)
  choose x hx hfx hweight hcontrol using hselect
  let r := fun n => (D + 1-(riemannianEDistOf (g n) (p n) (x n)).toReal)/4
  have hr (n : ℕ) : 0 < r n := by dsimp only [r]; linarith [hx n]
  have hrD (n : ℕ) : r n < D + 1 := by
    dsimp only [r]
    linarith [ENNReal.toReal_nonneg (a := riemannianEDistOf (g n) (p n) (x n))]
  have hweighted (n : ℕ) : f n (y n)/16 ≤ f n (x n)*r n^2 := by
    have hmargin : 1 ≤ D + 1-(riemannianEDistOf (g n) (p n) (y n)).toReal := by linarith [hyD n]
    have hsquare : 1 ≤ (D + 1-(riemannianEDistOf (g n) (p n) (y n)).toReal)^2 := by nlinarith
    have hh := mul_le_mul_of_nonneg_left hsquare (hfy n).le
    dsimp only [r]
    nlinarith [hweight n]
  have hprod : Tendsto (fun n => f n (x n)*r n^2) atTop atTop :=
    tendsto_atTop_mono hweighted (hlim.atTop_div_const (by norm_num : (0 : ℝ) < 16))
  have hvalue : Tendsto (fun n => f n (x n)) atTop atTop := by
    apply Tendsto.atTop_of_const_mul₀ (sq_pos_of_pos (by linarith : 0 < D + 1))
    apply tendsto_atTop_mono (fun n => ?_) hprod
    have hh := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (hr n).le (hrD n).le 2) (hfx n).le
    simpa only [mul_comm] using hh
  refine ⟨x,r,(fun n => ⟨hr n,hrD n,hx n,hfx n⟩),hvalue,hprod,fun _ => rfl,hweighted,?_,?_⟩
  · intro n
    let _ : PseudoMetricSpace (M n) := (g n).toPseudoMetricSpace
    have hball : riemannianClosedBallOf (g n) (x n) (r n) = Metric.closedBall (x n) (r n) := by
      ext z
      rw [Metric.mem_closedBall,dist_comm]
      exact (ENNReal.le_ofReal_iff_toReal_le (riemannianEDistOf_ne_top (g n) (x n) z) (hr n).le)
    apply (hcompact n).of_isClosed_subset
    · rw [hball]
      exact Metric.isClosed_closedBall
    · intro z hz
      have hzd : (riemannianEDistOf (g n) (x n) z).toReal ≤ r n :=
        ENNReal.toReal_le_of_le_ofReal (hr n).le hz
      have hh := hcontrol n z (by simpa only [r,div_eq_mul_inv,mul_comm,one_mul] using hzd)
      exact (ENNReal.le_ofReal_iff_toReal_le (riemannianEDistOf_ne_top (g n) (p n) z) (by linarith)).mpr hh.1.le
  · intro n z hz
    have hh := hcontrol n z (by simpa only [r,div_eq_mul_inv,mul_comm,one_mul] using hz)
    refine ⟨hh.1,?_⟩
    norm_num at hh
    exact hh.2

end DifferentialGeometry.SmoothRiemannianMetric
