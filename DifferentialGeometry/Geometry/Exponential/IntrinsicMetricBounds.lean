import DifferentialGeometry.Geometry.Comparison.Volume.Intrinsic.Gronwall
import DifferentialGeometry.Geometry.Exponential.Intrinsic.Framed.Jacobi

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open DifferentialGeometry
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open scoped ContDiff Manifold Topology ENNReal

namespace DifferentialGeometry.Geometry.Riemannian

def intrinsicNormalMetricRadius (n : ℕ) (K : ℝ) : ℝ :=
  Real.sqrt ((1 / (4 * (Real.exp 1 + 1))) / (Real.sqrt n * K + 1))

theorem intrinsicNormalMetricRadius_pos (n : ℕ) (K : ℝ) (hK : 0 ≤ K) :
    0 < intrinsicNormalMetricRadius n K := by
  unfold intrinsicNormalMetricRadius
  exact Real.sqrt_pos.mpr (div_pos (by positivity) (by positivity))

variable {E H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem intrFrameMetric_bound_of_rm04
    [PseudoEMetricSpace M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (K : ℝ) (hK : 0 ≤ K)
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (hRm : ∀ x : M,
      Real.sqrt (normSq0S (I := I) g x 4 (metricRm04At (I := I) g x)) ≤ K)
    (p : M) {z : E}
    (hz : z ∈ Metric.ball (0 : E)
      (intrinsicNormalMetricRadius (Module.finrank ℝ E) K)) (v : E) :
    (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ intrinsicFrameMetric (I := I) g hEnorm p z v v ∧
      intrinsicFrameMetric (I := I) g hEnorm p z v v ≤ 2 * ‖v‖ ^ 2 := by
  let C : ℝ := Real.sqrt (Module.finrank ℝ E) * K
  let κ : ℝ := 1 / (4 * (Real.exp 1 + 1))
  have hC : 0 ≤ C := mul_nonneg (Real.sqrt_nonneg _) hK
  have hκ : 0 < κ := by dsimp only [κ]; positivity
  have hC1 : 0 < C + 1 := by linarith
  have hexp : 0 < Real.exp 1 + 1 := by positivity
  have hκeval : κ * (Real.exp 1 + 1) = 1 / 4 := by
    dsimp only [κ]
    field_simp [hexp.ne']
  have hκ1 : κ ≤ 1 := by
    dsimp only [κ]
    apply (div_le_iff₀ (show 0 < 4 * (Real.exp 1 + 1) by positivity)).2
    nlinarith [Real.exp_pos (1 : ℝ)]
  have hr : 0 < intrinsicNormalMetricRadius (Module.finrank ℝ E) K :=
    intrinsicNormalMetricRadius_pos _ _ hK
  have hzNorm : ‖z‖ < intrinsicNormalMetricRadius (Module.finrank ℝ E) K := by
    simpa only [Metric.mem_ball, dist_zero_right] using hz
  have hradSq : intrinsicNormalMetricRadius (Module.finrank ℝ E) K ^ 2 =
      κ / (C + 1) := by
    exact Real.sq_sqrt (div_pos hκ hC1).le
  have hsq : ‖z‖ ^ 2 ≤ κ / (C + 1) := by
    rw [← hradSq]
    exact (sq_le_sq₀ (norm_nonneg z) hr.le).2 hzNorm.le
  let u : TangentSpace I p := normalFrame (I := I) g p z
  let w : TangentSpace I p := normalFrame (I := I) g p v
  let k : ℝ := Real.sqrt (Module.finrank ℝ E) * K * g.inner p u u
  have hkEq : k = C * ‖z‖ ^ 2 := by
    dsimp only [k, C, u]
    rw [normalFrame_normSq]
  have hk0 : 0 ≤ k := by rw [hkEq]; positivity
  have hkκ : k ≤ κ := by
    rw [hkEq]
    calc
      C * ‖z‖ ^ 2 ≤ C * (κ / (C + 1)) := mul_le_mul_of_nonneg_left hsq hC
      _ ≤ (C + 1) * (κ / (C + 1)) :=
        mul_le_mul_of_nonneg_right (by linarith) (div_pos hκ hC1).le
      _ = κ := by field_simp [hC1.ne']
  have hk1 : k ≤ 1 := hkκ.trans hκ1
  have herr : gronwallBound 0 (max k 1) k 1 ≤ 1 / 4 := by
    rw [max_eq_right hk1]
    simp only [gronwallBound, one_ne_zero, if_false, zero_mul, zero_add,
      div_one, one_mul]
    calc
      k * (Real.exp 1 - 1) ≤ k * (Real.exp 1 + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) hk0
      _ ≤ κ * (Real.exp 1 + 1) := mul_le_mul_of_nonneg_right hkκ hexp.le
      _ = 1 / 4 := hκeval
  have hscale : gronwallBound 0 (max k 1) (k * ‖v‖) 1 =
      ‖v‖ * gronwallBound 0 (max k 1) k 1 := by
    rw [max_eq_right hk1]
    simp only [gronwallBound, one_ne_zero, if_false, zero_mul, zero_add,
      div_one, one_mul]
    ring
  have herror : gronwallBound 0 (max k 1) (k * ‖v‖) 1 ≤ (1 / 4 : ℝ) * ‖v‖ := by
    rw [hscale]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left herr (norm_nonneg v)
  have hRmRay : IntrinsicRm04Bound (I := I) g hEnorm p u K :=
    fun t _ ↦ hRm (intrinsicGeodesic (I := I) g hEnorm p u t)
  have hODE := intrinsicJacobi_ode (I := I) g hEnorm p u w hK hRmRay
  obtain ⟨hupper, hlower⟩ := intrinsicJacobi_bounds (I := I) g hEnorm p u w
    hk0 zero_lt_one (by simpa only [k, Fintype.card_fin] using hODE)
  have hu1 := hupper 1 (by norm_num)
  have hl1 := hlower 1 (by norm_num)
  have hw : Real.sqrt (g.inner p w w) = ‖v‖ := by
    exact normalFrame_sqrt (I := I) g p v
  simp only [one_mul, hw] at hu1 hl1
  let q : M := intrinsicGeodesic (I := I) g hEnorm p u 1
  let J : TangentSpace I q := intrinsicJacobi (I := I) g hEnorm p u w 1
  have hsqrtU : Real.sqrt (g.inner q J J) ≤ (5 / 4 : ℝ) * ‖v‖ := by
    change Real.sqrt (g.inner q J J) ≤ _ at hu1
    linarith
  have hsqrtL : (3 / 4 : ℝ) * ‖v‖ ≤ Real.sqrt (g.inner q J J) := by
    change _ ≤ Real.sqrt (g.inner q J J) at hl1
    linarith
  have hnonneg : 0 ≤ g.inner q J J := by
    rcases eq_or_ne J 0 with hJ | hJ
    · simp [hJ]
    · exact (g.pos q J hJ).le
  have hLsq := (sq_le_sq₀
    (show 0 ≤ (3 / 4 : ℝ) * ‖v‖ by positivity) (Real.sqrt_nonneg _)).2 hsqrtL
  have hUsq := (sq_le_sq₀ (Real.sqrt_nonneg _)
    (show 0 ≤ (5 / 4 : ℝ) * ‖v‖ by positivity)).2 hsqrtU
  rw [Real.sq_sqrt hnonneg] at hLsq hUsq
  have heq : intrinsicFrameMetric (I := I) g hEnorm p z v v = g.inner q J J := by
    rw [intrinsic_metric_jacobi (I := I) g hEnorm p z v v]
    dsimp only [q, J, u, w, intrinsicFramedExp, expMapIntrinsic]
    rw [intrinsicFrameCLM_apply]
    rfl
  rw [heq]
  constructor <;> nlinarith [sq_nonneg ‖v‖]

end DifferentialGeometry.Geometry.Riemannian

end
