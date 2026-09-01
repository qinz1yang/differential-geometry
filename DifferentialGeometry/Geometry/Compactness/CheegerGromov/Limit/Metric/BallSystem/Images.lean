import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.MetricBallImage
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Limit.Metric.BallSystem.Basic

open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff
open Set Topology TopologicalSpace

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : ℕ → Type u} [∀ j, MetricSpace (M j)] [∀ j, ChartedSpace H (M j)]
  [∀ j, IsManifold I ∞ (M j)] [∀ j, SigmaCompactSpace (M j)] [∀ j, T2Space (M j)]

section ApproxData

open Bundle

variable [∀ j, RiemannianBundle (fun x : M j => TangentSpace I x)]
variable [∀ j, IsRiemannianManifold I (M j)]
variable [NeZero (Module.finrank ℝ E)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [I.Boundaryless] [NeZero (Module.finrank ℝ E)] in
omit [∀ (j : ℕ), SigmaCompactSpace (M j)] in
theorem chain_image_open
    (b : ∀ j, M j)
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    (hbase : ∀ j, (Ψ j : M j → M (j + 1)) (b j) = b (j + 1))
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    (hnorm : ∀ j (x : M j) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((g j).inner x v v)))
    {j a : ℕ} (ha : 1 ≤ a)
    (D : PartialDiffeomorphMetricApproximation (I := I)
      (Metric.closedBall (b j) ((2 : ℝ) ^ j)) (1 / 2) 0
      (chainComp (I := I) (Mf := M) Ψ j a) (g j) (g (j + a))) :
    (chainComp (I := I) (Mf := M) Ψ j a : M j → M (j + a)) ''
        Metric.ball (b j) ((2 : ℝ) ^ j) ⊆
      Metric.ball (b (j + a)) ((2 : ℝ) ^ (j + a)) := by
  have hr : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
  have hsqrt : Real.sqrt (1 + (1 / 2 : ℝ)) < 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 + 1 / 2)]
  have hpow : (2 : ℝ) ≤ (2 : ℝ) ^ a := by
    simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) ha
  have hR : Real.sqrt (1 + (1 / 2 : ℝ)) * (2 : ℝ) ^ j < (2 : ℝ) ^ (j + a) := by
    rw [pow_add]
    calc
      Real.sqrt (1 + (1 / 2 : ℝ)) * (2 : ℝ) ^ j < 2 * (2 : ℝ) ^ j :=
        mul_lt_mul_of_pos_right hsqrt hr
      _ ≤ (2 : ℝ) ^ j * (2 : ℝ) ^ a := by
        rw [mul_comm 2]
        exact mul_le_mul_of_nonneg_left hpow hr.le
  have hdata : MapMetricApproximationOn (I := I)
      (Metric.closedEBall (b j) (ENNReal.ofReal ((2 : ℝ) ^ j))) (1 / 2) 0
      (chainComp (I := I) (Mf := M) Ψ j a : M j → M (j + a)) (g j) (g (j + a)) := by
    rw [Metric.closedEBall_ofReal hr.le]
    exact D.forward
  have hsource : Metric.closedEBall (b j) (ENNReal.ofReal ((2 : ℝ) ^ j)) ⊆
      (chainComp (I := I) (Mf := M) Ψ j a).source := by
    rw [Metric.closedEBall_ofReal hr.le]
    exact D.source_sub
  have himg := data_image_metric_ball (I := I)
    (chainComp (I := I) (Mf := M) Ψ j a) (hnorm j) (hnorm (j + a))
    hr le_rfl (by norm_num : (0 : ℝ) ≤ 1 / 2) hR hdata hsource
  intro y hy
  have hyball := himg hy
  rw [chainComp_base (I := I) (Mf := M) Ψ b hbase j a] at hyball
  exact hyball

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [I.Boundaryless] [NeZero (Module.finrank ℝ E)]
    [∀ j, SigmaCompactSpace (M j)] in
theorem chain_image_ball
    (b : ∀ j, M j)
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    (hbase : ∀ j, (Ψ j : M j → M (j + 1)) (b j) = b (j + 1))
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    (hnorm : ∀ j (x : M j) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((g j).inner x v v)))
    {j a : ℕ} (ha : 1 ≤ a)
    (D : PartialDiffeomorphMetricApproximation (I := I)
      (Metric.closedBall (b j) ((2 : ℝ) ^ j)) (1 / 2) 0
      (chainComp (I := I) (Mf := M) Ψ j a) (g j) (g (j + a))) :
    (chainComp (I := I) (Mf := M) Ψ j a : M j → M (j + a)) ''
        Metric.ball (b j) ((2 : ℝ) ^ j) ⊆
      Metric.closedBall (b (j + a)) ((2 : ℝ) ^ (j + a)) :=
  (chain_image_open (I := I) b Ψ hbase g hnorm ha D).trans Metric.ball_subset_closedBall

omit [I.Boundaryless] [∀ j, IsRiemannianManifold I (M j)]
  [∀ j, RiemannianBundle (fun x : M j => TangentSpace I x)]
  [NeZero (Module.finrank ℝ E)] in
omit [∀ (j : ℕ), SigmaCompactSpace (M j)] in
theorem tailBall_source
    (b : ∀ j, M j)
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    (j₀ n : ℕ)
    (D0 : ∀ k, PartialDiffeomorphMetricApproximation (I := I)
      (Metric.closedBall (b (j₀ + n)) ((2 : ℝ) ^ (j₀ + n))) (1 / 2) 0
      (chainComp (I := I) (Mf := M) Ψ (j₀ + n) k)
      (g (j₀ + n)) (g ((j₀ + n) + k))) :
    ∀ k, (tailBallOpen b j₀ n : Set (M (j₀ + n))) ⊆
      (chainComp (I := I) (Mf := M) Ψ (j₀ + n) k).source := by
  have hpow : (2 : ℝ) ^ n ≤ (2 : ℝ) ^ (j₀ + n) := by
    exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
  intro k x hx
  apply (D0 k).source_sub
  exact Metric.mem_closedBall.mpr ((Metric.mem_ball.mp hx).le.trans hpow)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [I.Boundaryless] [NeZero (Module.finrank ℝ E)] in
theorem tailBall_image
    (b : ∀ j, M j)
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    (hbase : ∀ j, (Ψ j : M j → M (j + 1)) (b j) = b (j + 1))
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    (hnorm : ∀ j (x : M j) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((g j).inner x v v)))
    (j₀ n : ℕ)
    (D : PartialDiffeomorphMetricApproximation (I := I)
      (Metric.closedBall (b (j₀ + n)) ((2 : ℝ) ^ (j₀ + n))) (1 / 2) 0
      (chainComp (I := I) (Mf := M) Ψ (j₀ + n) 1)
      (g (j₀ + n)) (g ((j₀ + n) + 1))) :
    (chainComp (I := I) (Mf := M) Ψ (j₀ + n) 1 :
        M (j₀ + n) → M ((j₀ + n) + 1)) ''
        (tailBallOpen b j₀ n : Set (M (j₀ + n))) ⊆
      Metric.ball (b ((j₀ + n) + 1)) ((2 : ℝ) ^ (n + 1)) := by
  have hr : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hpow : (2 : ℝ) ^ n ≤ (2 : ℝ) ^ (j₀ + n) := by
    exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
  have hsqrt : Real.sqrt (1 + (1 / 2 : ℝ)) < 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 + 1 / 2)]
  have hR : Real.sqrt (1 + (1 / 2 : ℝ)) * (2 : ℝ) ^ n < (2 : ℝ) ^ (n + 1) := by
    rw [pow_succ]
    nlinarith
  have hK : Metric.closedEBall (b (j₀ + n))
      (ENNReal.ofReal ((2 : ℝ) ^ (j₀ + n))) ⊆
        Metric.closedBall (b (j₀ + n)) ((2 : ℝ) ^ (j₀ + n)) := by
    rw [Metric.closedEBall_ofReal (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (j₀ + n))]
  have hsub : Metric.closedEBall (b (j₀ + n))
      (ENNReal.ofReal ((2 : ℝ) ^ (j₀ + n))) ⊆
        (chainComp (I := I) (Mf := M) Ψ (j₀ + n) 1).source := by
    rw [Metric.closedEBall_ofReal (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (j₀ + n))]
    exact D.source_sub
  have himg := data_image_metric_ball_of_superset (I := I)
    (chainComp (I := I) (Mf := M) Ψ (j₀ + n) 1)
    (hnorm (j₀ + n)) (hnorm ((j₀ + n) + 1)) hr hpow
    (by norm_num : (0 : ℝ) ≤ 1 / 2) hR hK D.forward hsub
  intro y hy
  have hy' := himg hy
  rw [chainComp_base (I := I) (Mf := M) Ψ b hbase (j₀ + n) 1] at hy'
  exact hy'

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [I.Boundaryless] [NeZero (Module.finrank ℝ E)] in
theorem tailClosed_image
    (b : ∀ j, M j)
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) (∞ : WithTop ℕ∞))
    (hbase : ∀ j, (Ψ j : M j → M (j + 1)) (b j) = b (j + 1))
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    (hnorm : ∀ j (x : M j) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((g j).inner x v v)))
    (j₀ n : ℕ) (hj₀ : 1 ≤ j₀)
    (D : PartialDiffeomorphMetricApproximation (I := I)
      (Metric.closedBall (b (j₀ + n)) ((2 : ℝ) ^ (j₀ + n))) (1 / 2) 0
      (chainComp (I := I) (Mf := M) Ψ (j₀ + n) 1)
      (g (j₀ + n)) (g ((j₀ + n) + 1))) :
    (chainComp (I := I) (Mf := M) Ψ (j₀ + n) 1 :
        M (j₀ + n) → M ((j₀ + n) + 1)) ''
        Metric.closedBall (b (j₀ + n)) ((2 : ℝ) ^ n) ⊆
      Metric.ball (b ((j₀ + n) + 1)) ((2 : ℝ) ^ (n + 1)) := by
  let rMid : ℝ := (3 / 2 : ℝ) * (2 : ℝ) ^ n
  have hpowPos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hrMid : 0 < rMid := by
    dsimp only [rMid]
    positivity
  have hr_lt : (2 : ℝ) ^ n < rMid := by
    dsimp only [rMid]
    nlinarith
  have hrr₂ : rMid ≤ (2 : ℝ) ^ (j₀ + n) := by
    have hjpow : (2 : ℝ) ≤ (2 : ℝ) ^ j₀ := by
      simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hj₀
    rw [pow_add]
    dsimp only [rMid]
    nlinarith
  have hsqrt : Real.sqrt (1 + (1 / 2 : ℝ)) < 4 / 3 := by
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 + 1 / 2)
    have hs0 := Real.sqrt_nonneg (1 + (1 / 2 : ℝ))
    nlinarith
  have hR : Real.sqrt (1 + (1 / 2 : ℝ)) * rMid < (2 : ℝ) ^ (n + 1) := by
    rw [pow_succ]
    dsimp only [rMid]
    nlinarith
  have hclosed : Metric.closedBall (b (j₀ + n)) ((2 : ℝ) ^ n) ⊆
      Metric.ball (b (j₀ + n)) rMid := by
    intro x hx
    exact Metric.mem_ball.mpr ((Metric.mem_closedBall.mp hx).trans_lt hr_lt)
  have hK : Metric.closedEBall (b (j₀ + n))
      (ENNReal.ofReal ((2 : ℝ) ^ (j₀ + n))) ⊆
        Metric.closedBall (b (j₀ + n)) ((2 : ℝ) ^ (j₀ + n)) := by
    rw [Metric.closedEBall_ofReal (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (j₀ + n))]
  have hsub : Metric.closedEBall (b (j₀ + n))
      (ENNReal.ofReal ((2 : ℝ) ^ (j₀ + n))) ⊆
        (chainComp (I := I) (Mf := M) Ψ (j₀ + n) 1).source := by
    rw [Metric.closedEBall_ofReal (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (j₀ + n))]
    exact D.source_sub
  have himg := data_image_metric_ball_of_superset (I := I)
    (chainComp (I := I) (Mf := M) Ψ (j₀ + n) 1)
    (hnorm (j₀ + n)) (hnorm ((j₀ + n) + 1)) hrMid hrr₂
    (by norm_num : (0 : ℝ) ≤ 1 / 2) hR hK D.forward hsub
  intro y hy
  have hy' := himg (Set.image_mono hclosed hy)
  rw [chainComp_base (I := I) (Mf := M) Ψ b hbase (j₀ + n) 1] at hy'
  exact hy'

end ApproxData

end HCGCompactness
end DifferentialGeometry
