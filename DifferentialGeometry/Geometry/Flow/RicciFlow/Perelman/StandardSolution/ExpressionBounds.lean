import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.TimeExpression
import DifferentialGeometry.Geometry.Metric.TensorInner.Estimates.TensorProductNorm
import DifferentialGeometry.Geometry.Metric.TensorInner.FiberMetric.Tensor0SMetricIneq
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Scaling
import DifferentialGeometry.Geometry.Connection.MetricTrace.NormBound

set_option autoImplicit false
noncomputable section
open Set Bundle Manifold DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.PDE.RicciFlow
open scoped Manifold ContDiff BigOperators
namespace DifferentialGeometry.PDE.RicciFlow

def CurvatureExpression.maxOrder : {s : ℕ} → CurvatureExpression s → ℕ
  | _, .curvature k => k
  | _, .zero _ => 0
  | _, .add A B => max A.maxOrder B.maxOrder
  | _, .smul _ A => A.maxOrder
  | _, .product A B => max A.maxOrder B.maxOrder
  | _, .perm _ A => A.maxOrder
  | _, .trace A => A.maxOrder

def CurvatureExpression.normBound (d : ℕ) (C : ℝ) : {s : ℕ} → CurvatureExpression s → ℝ
  | _, .curvature _ => C
  | _, .zero _ => 0
  | _, .add A B => A.normBound d C + B.normBound d C
  | _, .smul c A => |c| * A.normBound d C
  | _, .product A B => A.normBound d C * B.normBound d C
  | _, .perm _ A => A.normBound d C
  | s, .trace A => Real.sqrt ((d : ℝ) ^ (s + 2)) * A.normBound d C

theorem CurvatureExpression.normBound_nonneg (d : ℕ) (C : ℝ) (hC : 0 ≤ C)
    {s : ℕ} (A : CurvatureExpression s) : 0 ≤ A.normBound d C := by
  induction A with
  | curvature k => exact hC
  | zero s => exact le_rfl
  | add A B ihA ihB => exact add_nonneg ihA ihB
  | smul c A ih => exact mul_nonneg (abs_nonneg c) ih
  | product A B ihA ihB => exact mul_nonneg ihA ihB
  | perm e A ih => exact ih
  | trace A ih => exact mul_nonneg (Real.sqrt_nonneg _) ih

theorem CurvatureExpression.maxOrder_spatialDerivative_le {s : ℕ} (A : CurvatureExpression s) :
    A.spatialDerivative.maxOrder ≤ A.maxOrder + 1 := by
  induction A with
  | curvature k => exact le_rfl
  | zero s => exact Nat.zero_le _
  | add A B ihA ihB => simp only [spatialDerivative, maxOrder]; omega
  | smul c A ih => exact ih
  | product A B ihA ihB => simp only [spatialDerivative, maxOrder]; omega
  | perm e A ih => exact ih
  | trace A ih => exact ih

private theorem order_sumFin_le {s : ℕ} (n : ℕ) (A : Fin n → CurvatureExpression s)
    (N : ℕ) (hA : ∀ q, (A q).maxOrder ≤ N) : (CurvatureExpression.sumFin n A).maxOrder ≤ N := by
  induction n with
  | zero => exact Nat.zero_le N
  | succ n ih => exact max_le (hA 0) (ih (fun q => A q.succ) (fun q => hA q.succ))

private theorem order_gamma_le (k : ℕ) : (CurvatureExpression.gamma k).maxOrder ≤ k + 1 := by
  simp only [CurvatureExpression.gamma, CurvatureExpression.maxOrder]
  refine max_le (max_le ?_ ?_) ?_
  all_goals
    apply order_sumFin_le
    intro q
    change max 1 k ≤ k + 1
    omega

private theorem order_comm_le (k : ℕ) : (CurvatureExpression.comm k).maxOrder ≤ k + 1 := by
  simp only [CurvatureExpression.comm, CurvatureExpression.maxOrder]
  refine max_le (max_le ?_ ?_) ?_
  · apply order_sumFin_le
    intro q
    change max 1 k ≤ k + 1
    omega
  · apply order_sumFin_le
    intro q
    change max 0 (k + 1) ≤ k + 1
    omega
  · apply order_sumFin_le
    intro q
    split <;> change max (k + 1) 0 ≤ k + 1 <;> omega

theorem CurvatureExpression.maxOrder_residual_le (k : ℕ) : (residual k).maxOrder ≤ k := by
  induction k with
  | zero => change 0 ≤ 0; exact le_rfl
  | succ k ih =>
      have hs := maxOrder_spatialDerivative_le (residual k)
      have hc := order_comm_le k
      have hg := order_gamma_le k
      simp only [residual, maxOrder]
      omega

private theorem order_action_le {s : ℕ} (A : CurvatureExpression s) :
    A.ricciAction.maxOrder ≤ A.maxOrder := by
  apply order_sumFin_le
  intro q
  change max 0 A.maxOrder ≤ A.maxOrder
  omega

private theorem order_timeLeaf_le (k : ℕ) : (CurvatureExpression.timeLeaf k).maxOrder ≤ k + 2 := by
  have hr := CurvatureExpression.maxOrder_residual_le k
  have ha := order_action_le (CurvatureExpression.curvature k)
  change max (max (k + 2) (CurvatureExpression.residual k).maxOrder)
    (CurvatureExpression.curvature k).ricciAction.maxOrder ≤ k + 2
  change (CurvatureExpression.curvature k).ricciAction.maxOrder ≤ k at ha
  omega

theorem CurvatureExpression.maxOrder_timeDerivative_le {s : ℕ} (A : CurvatureExpression s) :
    A.timeDerivative.maxOrder ≤ A.maxOrder + 2 := by
  induction A with
  | curvature k => exact order_timeLeaf_le k
  | zero s => exact Nat.zero_le _
  | add A B ihA ihB => simp only [timeDerivative, maxOrder]; omega
  | smul c A ih => exact ih
  | product A B ihA ihB => simp only [timeDerivative, maxOrder]; omega
  | perm e A ih => exact ih
  | trace A ih => exact ih

theorem CurvatureExpression.maxOrder_timeIter_le {s : ℕ} (A : CurvatureExpression s) (b : ℕ) :
    (A.timeIter b).maxOrder ≤ A.maxOrder + 2 * b := by
  induction b with
  | zero => exact Nat.le_add_right _ _
  | succ b ih =>
      have ht := maxOrder_timeDerivative_le (A.timeIter b)
      change (A.timeIter b).timeDerivative.maxOrder ≤ A.maxOrder + 2 * (b + 1)
      omega

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem CurvatureExpression.eval_norm_le {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : ℝ) (x : M) (C : ℝ) (hC : 0 ≤ C)
    {s : ℕ} (A : CurvatureExpression s)
    (hbound : ∀ k ≤ A.maxOrder, Real.sqrt (nablaKRm04NormSqIntrinsic S k t x) ≤ C) :
    Real.sqrt (normSq0S (S.base.metric t) x s (A.eval S t x)) ≤
      A.normBound (Module.finrank ℝ E) C := by
  let g := S.base.metric t
  obtain ⟨n, frame, basis, _, horth⟩ := exists_orthoBasisFrameAt S t x
  have hinv := metricInverseInBasis_identity_of_orthonormal g basis horth
  induction A with
  | curvature k => exact hbound k le_rfl
  | zero s =>
      have hz : normSq0S g x s (0 : Tensor0SSpace s I x) = 0 := by
        simpa only [zero_smul, zero_pow (by decide : 2 ≠ 0), zero_mul] using
          normSq0S_smul g (0 : ℝ) (0 : Tensor0SSpace s I x)
      change Real.sqrt (normSq0S g x s (0 : Tensor0SSpace s I x)) ≤ 0
      rw [hz, Real.sqrt_zero]
  | @add s A B ihA ihB =>
      have ha := ihA (fun k hk => hbound k (hk.trans (Nat.le_max_left _ _)))
      have hb := ihB (fun k hk => hbound k (hk.trans (Nat.le_max_right _ _)))
      exact (_root_.DifferentialGeometry.Tensor0SBundle.sqrt_normSq0S_add_le g x s (A.eval S t x) (B.eval S t x)).trans
        (add_le_add ha hb)
  | @smul s c A ih =>
      change Real.sqrt (normSq0S g x s (c • A.eval S t x)) ≤ |c| * A.normBound _ C
      rw [sqrt_normSq0S_smul]
      exact mul_le_mul_of_nonneg_left (ih hbound) (abs_nonneg c)
  | @product s q A B ihA ihB =>
      have ha := ihA (fun k hk => hbound k (hk.trans (Nat.le_max_left _ _)))
      have hb := ihB (fun k hk => hbound k (hk.trans (Nat.le_max_right _ _)))
      have he := normSq0S_product g x basis hinv (A.eval S t) (B.eval S t)
      change Real.sqrt (normSq0S g x (s + q) (tensor0SFieldProduct ∞ (A.eval S t) (B.eval S t) x)) ≤
        A.normBound _ C * B.normBound _ C
      rw [he, Real.sqrt_mul (normSq0S_nonneg g x s (A.eval S t x))]
      exact mul_le_mul ha hb (Real.sqrt_nonneg _) (A.normBound_nonneg _ C hC)
  | @perm s s' e A ih =>
      change Real.sqrt (normSq0S g x s' ((A.eval S t x).domDomCongr e)) ≤ A.normBound _ C
      rw [normSq0S_domDomCongr g x basis hinv e (A.eval S t x)]
      exact ih hbound
  | @trace s A ih =>
      have hh := Real.sqrt_le_sqrt (trace_normSq_rank_le g (A.eval S t x))
      rw [Real.sqrt_mul (pow_nonneg (Nat.cast_nonneg _) _)] at hh
      exact hh.trans (mul_le_mul_of_nonneg_left (ih hbound) (Real.sqrt_nonneg _))

variable [CompleteSpace E] [BoundarylessManifold I M] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]

theorem curvature_mixed_time_bound {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (a b : ℕ) (t : RealTimeInterval.RegularTime D) (x : M) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ k ≤ a + 2 * b, Real.sqrt (nablaKRm04NormSqIntrinsic S k (t : ℝ) x) ≤ C) :
    Real.sqrt (normSq0S (S.base.metric (t : ℝ)) x (4 + a)
      (iteratedCovariantTimeDerivWithin S.base.metric
        (fun r => nablaKRm04Field S r a x) D.carrier b (t : ℝ))) ≤
      ((CurvatureExpression.curvature a).timeIter b).normBound (Module.finrank ℝ E) C := by
  have he := CurvatureExpression.eval_timeIter S hS (.curvature a) b t x
  have ho := CurvatureExpression.maxOrder_timeIter_le (.curvature a) b
  have hb := CurvatureExpression.eval_norm_le S (t : ℝ) x C hC
    ((CurvatureExpression.curvature a).timeIter b) (fun k hk => hbound k (hk.trans ho))
  exact (congrArg (fun U : Tensor0SSpace (4 + a) I x =>
    Real.sqrt (normSq0S (S.base.metric (t : ℝ)) x (4 + a) U)) he).trans_le hb
end DifferentialGeometry.PDE.RicciFlow
