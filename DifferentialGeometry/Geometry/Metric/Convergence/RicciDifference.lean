import DifferentialGeometry.Geometry.Curvature.MetricDifference
import DifferentialGeometry.Geometry.Curvature.Bochner.OrthonormalFrameTrace
import DifferentialGeometry.Geometry.Curvature.Bounds.RicciOperatorNorm
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Continuity
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.Compactification.OnePoint.Basic

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff _root_.Topology BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [BoundarylessManifold I M]

local instance metricRicciDifferenceConvergenceOne : IsManifold I 1 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)

local instance metricRicciDifferenceConvergenceTopSucc :
    IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
  change IsManifold I ∞ M
  infer_instance

omit [CompleteSpace E] [T2Space M] [BoundarylessManifold I M] in
private theorem metricRicciDifference_inner_abs (g : SmoothRiemannianMetric I M)
    (x : M) (v w : TangentSpace I x) :
    |g.inner x v w| ≤ Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x w w) := by
  let D := (tangentMetricData (I := I) g x).metric
  let _ : InnerProductSpace.Core ℝ (TangentSpace I x) := D.toCore
  let _ : NormedAddCommGroup (TangentSpace I x) :=
    @InnerProductSpace.Core.toNormedAddCommGroup ℝ (TangentSpace I x) _ _ _ D.toCore
  let _ : InnerProductSpace ℝ (TangentSpace I x) :=
    @InnerProductSpace.ofCore ℝ (TangentSpace I x) _ _ _ D.toCore.toCore
  have hi (a b : TangentSpace I x) : g.inner x a b = inner ℝ a b := by
    rw [← TangentMetricData.inner_eq (tangentMetricData (I := I) g x) a b]
    exact (MetricFiberData.toCore_inner D a b).symm
  simp only [hi, real_inner_self_eq_norm_sq, Real.sqrt_sq_eq_abs, abs_norm]
  exact abs_real_inner_le_norm v w

omit [BoundarylessManifold I M] in
private theorem metricRicciDifference_equivalent_two
    (g h : SmoothRiemannianMetric I M) (x : M) {delta : ℝ}
    (hsmall : (Module.finrank ℝ E : ℝ) * delta ≤ 1 / 2)
    (hzero : metricDerivNorm (I := I) 0 h g g x ≤ delta) :
    MetricUniformEquivalentOn (I := I) {x} g h 2 := by
  have hquad (v : TangentSpace I x) :
      |h.inner x v v - g.inner x v v| ≤ (1 / 2 : ℝ) * g.inner x v v := by
    have ht := metricQuadFormDiff_le_metricDerivNorm (I := I) h g g x v
    have hc : (Module.finrank ℝ E : ℝ) * metricDerivNorm (I := I) 0 h g g x ≤
        1 / 2 :=
      (mul_le_mul_of_nonneg_left hzero (Nat.cast_nonneg _)).trans hsmall
    exact ht.trans (mul_le_mul_of_nonneg_right hc
      (DifferentialGeometry.metric_inner_self_nonneg g x v))
  have ht := metricUniformEquivalentOn_of_quadFormDiff (I := I)
    (K := {x}) (g := g) (h := h) (δ := 1 / 2) (by norm_num) (by norm_num)
    (fun y hy v => by
      rcases Set.mem_singleton_iff.mp hy with rfl
      exact hquad v)
  norm_num at ht
  exact ht

omit [BoundarylessManifold I M] in
private theorem metricRicciDifference_derivNorm_succ
    (g h : SmoothRiemannianMetric I M) (x : M) (a : ℕ) :
    metricDerivNorm (I := I) (a + 1) h g g x =
      metricCovDerivNorm (I := I) (a + 1) h g x := by
  unfold metricDerivNorm metricDiffCovDerivAt
  rw [covDeriv_self_succ]
  change Real.sqrt (normSq0S (I := I) g x (a + 1 + 2)
    (CheegerGromovCompactness.metricCovDeriv (I := I) h g (a + 1) x - 0)) = _
  rw [sub_zero]
  rfl

private theorem ricci_difference_le_two_jets
    (g h : SmoothRiemannianMetric I M) (x : M) {delta : ℝ}
    (heq : MetricUniformEquivalentOn (I := I) {x} g h 2)
    (hjet : ∀ a : ℕ, a ≤ 2 → metricDerivNorm (I := I) a h g g x ≤ delta)
    (v : TangentSpace I x) :
    |ricciTensor (I := I) h x v v - ricciTensor (I := I) g x v v| ≤
      (Module.finrank ℝ E : ℝ) * (48 * delta + 384 * delta ^ 2) * g.inner x v v := by
  classical
  obtain ⟨b, hb⟩ := exists_orthonormal_basis (I := I) g x
  have hdim : Module.finrank ℝ (TangentSpace I x) = Module.finrank ℝ E := rfl
  have h1 : metricCovDerivNorm (I := I) 1 h g x ≤ delta := by
    rw [← metricRicciDifference_derivNorm_succ g h x 0]
    exact hjet 1 (by norm_num)
  have h2 : metricCovDerivNorm (I := I) 2 h g x ≤ delta := by
    rw [← metricRicciDifference_derivNorm_succ g h x 1]
    exact hjet 2 (by norm_num)
  have hv : 0 ≤ g.inner x v v :=
    DifferentialGeometry.metric_inner_self_nonneg g x v
  have hsplit : ricciTensor (I := I) h x v v - ricciTensor (I := I) g x v v =
      ∑ i : Fin (Module.finrank ℝ (TangentSpace I x)),
        g.inner x ((ricciEndo (I := I) h x v v - ricciEndo (I := I) g x v v) (b i))
          (b i) := by
    with_unfolding_all
      rw [ricciTensor_apply, ricciTensor_apply,
        ← map_sub (LinearMap.trace ℝ (TangentSpace I x)),
        trace_eq_ortho_sum (I := I) g x _ b hb]
      rfl
  have hterm (i : Fin (Module.finrank ℝ (TangentSpace I x))) :
      |g.inner x ((ricciEndo (I := I) h x v v - ricciEndo (I := I) g x v v) (b i))
        (b i)| ≤ (48 * delta + 384 * delta ^ 2) * g.inner x v v := by
    have hbi : g.inner x (b i) (b i) = 1 := by simpa only [ite_true] using hb i i
    have hr := riemannOp_difference_le_metric_jets heq h1 h2 (b i) v v
    simp only [hbi, Real.sqrt_one, mul_one] at hr
    have hc := metricRicciDifference_inner_abs g x
      ((ricciEndo (I := I) h x v v - ricciEndo (I := I) g x v v) (b i)) (b i)
    rw [hbi, Real.sqrt_one, mul_one] at hc
    change |g.inner x
      (riemannOp (cov := LeviCivita (I := I) h) x (b i) v v -
        riemannOp (cov := LeviCivita (I := I) g) x (b i) v v) (b i)| ≤ _ at hc
    apply hc.trans
    calc
      _ ≤ (48 * delta + 384 * delta ^ 2) * Real.sqrt (g.inner x v v) *
          Real.sqrt (g.inner x v v) := hr
      _ = _ := by rw [mul_assoc, Real.mul_self_sqrt hv]
  rw [hsplit]
  calc
    _ ≤ ∑ i : Fin (Module.finrank ℝ (TangentSpace I x)),
        |g.inner x ((ricciEndo (I := I) h x v v - ricciEndo (I := I) g x v v)
          (b i)) (b i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin (Module.finrank ℝ (TangentSpace I x)),
        (48 * delta + 384 * delta ^ 2) * g.inner x v v :=
      Finset.sum_le_sum fun i _ => hterm i
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, hdim, mul_assoc]

theorem metricRicci_difference_le_relative_two_jets
    (g h : SmoothRiemannianMetric I M) (x : M) {delta : ℝ}
    (hdelta0 : 0 ≤ delta) (hdelta1 : delta ≤ 1)
    (hsmall : (Module.finrank ℝ E : ℝ) * delta ≤ 1 / 2)
    (hjet : ∀ a : ℕ, a ≤ 2 → metricDerivNorm (I := I) a h g g x ≤ delta)
    (v : TangentSpace I x) :
    |ricciTensor (I := I) h x v v - ricciTensor (I := I) g x v v| ≤
      (Module.finrank ℝ E : ℝ) * (432 * delta) * g.inner x v v := by
  have heq := metricRicciDifference_equivalent_two g h x hsmall (hjet 0 (by norm_num))
  have hb := ricci_difference_le_two_jets g h x heq hjet v
  have hd : delta ^ 2 ≤ delta := by nlinarith
  have hc : 48 * delta + 384 * delta ^ 2 ≤ 432 * delta := by linarith
  exact hb.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg _))
    (DifferentialGeometry.metric_inner_self_nonneg g x v))

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
