import DifferentialGeometry.Geometry.Comparison.Volume.Bishop.LocalBallRatio
import DifferentialGeometry.Geometry.Comparison.RadialHessianLowerBound

set_option autoImplicit false

/-!
# CX-SPINE G11：局部 Ricci 控制下的相邻球与有限球链体积

直接复用 public riemannianBallOf_volume_ratio_ge_of_ricci_lower。
每一步只使用目标中心的 2r 球；系数 exp(-2*q*(n-1)*r)/4^n 在几何数据前固定。
不要求整个流形 connected，也不扩大到全局 2S+r+2 曲率域。
-/

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

/-- 相邻中心的 r 球体积比较只需目标中心 2r 球内的 Ricci 下界。 -/
theorem ball_volume_lower_of_nearby_center_CXSP
    (g : SmoothRiemannianMetric I M) (hg : RiemannianMetricComplete g)
    (x y : M) {q r : ℝ} (hq : 0 ≤ q) (hr : 0 < r)
    (hxy : riemannianEDistOf g x y ≤ ENNReal.ofReal r)
    (hRic : ∀ z ∈ riemannianBallOf g y (2 * r), ∀ w : TangentSpace I z,
      -(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * q ^ 2) * g.inner z w w ≤
        ricciTensor g z w w) :
    ENNReal.ofReal (Real.exp (-2 * q * ((Module.finrank ℝ E - 1 : ℕ) : ℝ) * r) /
      4 ^ Module.finrank ℝ E) * riemannianVolumeMeasure I M g (riemannianBallOf g x r) ≤
      riemannianVolumeMeasure I M g (riemannianBallOf g y r) := by
  let _ : T2Space (TangentBundle I M) :=
    DifferentialGeometry.FiberBundle.t2Space_totalSpace (F := E) (E := TangentSpace I)
  have hsub : riemannianBallOf g x r ⊆ riemannianBallOf g y (2 * r) := by
    intro z hz
    change riemannianEDistOf g y z < ENNReal.ofReal (2 * r)
    calc
      _ ≤ riemannianEDistOf g y x + riemannianEDistOf g x z :=
        riemannianEDistOf_triangle g y x z
      _ < ENNReal.ofReal r + ENNReal.ofReal r := by
        rw [riemannianEDistOf_comm g y x]
        exact ENNReal.add_lt_add_of_le_of_lt
          (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hxy) hxy hz
      _ = ENNReal.ofReal (2 * r) := by
        rw [← ENNReal.ofReal_add hr.le hr.le]
        congr 1
        ring
  have hbase := riemannianBallOf_volume_ratio_ge_of_ricci_lower g hg y hq hr
    (by linarith : r ≤ 2 * r) hRic
  have hratio : r / (2 * (2 * r)) = (1 / 4 : ℝ) := by field_simp; ring
  have hexp : -(q * ((Module.finrank ℝ E - 1 : ℕ) : ℝ) * (2 * r)) =
      -2 * q * ((Module.finrank ℝ E - 1 : ℕ) : ℝ) * r := by ring
  rw [hratio, hexp, div_pow, one_pow] at hbase
  have hcoef : Real.exp (-2 * q * ((Module.finrank ℝ E - 1 : ℕ) : ℝ) * r) *
      (1 / 4 ^ Module.finrank ℝ E) =
      Real.exp (-2 * q * ((Module.finrank ℝ E - 1 : ℕ) : ℝ) * r) /
        4 ^ Module.finrank ℝ E := by ring
  rw [hcoef] at hbase
  exact (mul_le_mul' le_rfl (measure_mono hsub)).trans hbase

/-- 有限球链逐步传播体积；每步保持相同局部曲率预算与测试半径。 -/
theorem ball_volume_lower_of_chain_CXSP
    (g : SmoothRiemannianMetric I M) (hg : RiemannianMetricComplete g)
    (points : ℕ → M) (N : ℕ) {q r : ℝ} (hq : 0 ≤ q) (hr : 0 < r)
    (hstep : ∀ k < N, riemannianEDistOf g (points k) (points (k + 1)) ≤ ENNReal.ofReal r)
    (hRic : ∀ k < N, ∀ z ∈ riemannianBallOf g (points (k + 1)) (2 * r),
      ∀ w : TangentSpace I z,
      -(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * q ^ 2) * g.inner z w w ≤
        ricciTensor g z w w) :
    ENNReal.ofReal ((Real.exp (-2 * q * ((Module.finrank ℝ E - 1 : ℕ) : ℝ) * r) /
      4 ^ Module.finrank ℝ E) ^ N) *
      riemannianVolumeMeasure I M g (riemannianBallOf g (points 0) r) ≤
        riemannianVolumeMeasure I M g (riemannianBallOf g (points N) r) := by
  let c := Real.exp (-2 * q * ((Module.finrank ℝ E - 1 : ℕ) : ℝ) * r) /
    4 ^ Module.finrank ℝ E
  have hc : 0 < c := by dsimp [c]; positivity
  have hmain : ∀ k ≤ N,
      ENNReal.ofReal (c ^ k) *
        riemannianVolumeMeasure I M g (riemannianBallOf g (points 0) r) ≤
          riemannianVolumeMeasure I M g (riemannianBallOf g (points k) r) := by
    intro k
    induction k with
    | zero => intro hk; simp only [pow_zero, ENNReal.ofReal_one, one_mul, le_refl]
    | succ k ih =>
      intro hk
      have hkn : k < N := Nat.lt_of_succ_le hk
      have hnext := ball_volume_lower_of_nearby_center_CXSP g hg (points k)
        (points (k + 1)) hq hr (hstep k hkn) (hRic k hkn)
      calc
        _ = ENNReal.ofReal c * (ENNReal.ofReal (c ^ k) *
            riemannianVolumeMeasure I M g (riemannianBallOf g (points 0) r)) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hc.le, pow_succ']
        _ ≤ ENNReal.ofReal c *
            riemannianVolumeMeasure I M g (riemannianBallOf g (points k) r) :=
          mul_le_mul' le_rfl (ih hkn.le)
        _ ≤ _ := hnext
  exact hmain N le_rfl

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
