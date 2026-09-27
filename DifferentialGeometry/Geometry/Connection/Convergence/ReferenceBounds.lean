import DifferentialGeometry.Geometry.Connection.Convergence.DifferenceDerivativeBound
import DifferentialGeometry.Geometry.Metric.DeTurck.ConnectionDifference.Basic
import DifferentialGeometry.Geometry.Metric.Coordinates.InnerExpansion

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature

open Bundle Set
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

private theorem connection_difference_sub_reference
    (g h R : SmoothRiemannianMetric I M) (x : M) (u w : TangentSpace I x) :
    CovariantDerivative.difference (metricCov h) (metricCov g) x u w =
      CovariantDerivative.difference (metricCov h) (metricCov R) x u w -
        CovariantDerivative.difference (metricCov g) (metricCov R) x u w := by
  obtain ⟨Y, hY⟩ := ContMDiffSection.exists_eq_at
    (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞)) x u
  have hYdiff := Y.mdifferentiableAt (x := x)
  have hpair (g₁ g₂ : SmoothRiemannianMetric I M) :
      CovariantDerivative.difference (metricCov g₁) (metricCov g₂) x u w =
        (metricCov g₁).toFun Y x w - (metricCov g₂).toFun Y x w := by
    have hh := DifferentialGeometry.PDE.DeTurck.connectionDifference_apply
      (I := I) g₁ g₂ hYdiff w
    simpa only [DifferentialGeometry.PDE.DeTurck.connectionDifference,
      metricCov, LeviCivita, hY] using hh
  rw [hpair, hpair, hpair]
  abel

theorem connectionDifference_norm_le_of_reference_metric_bounds
    (R g h : SmoothRiemannianMetric I M) {K : Set M}
    {L₁ L₂ J₁ J₂ : ℝ}
    (hg : MetricUniformEquivalentOn K R g L₁)
    (hh : MetricUniformEquivalentOn K R h L₂)
    (hJg : MetricCovDerivOrderBoundOn K 1 g R J₁)
    (hJh : MetricCovDerivOrderBoundOn K 1 h R J₂)
    {x : M} (hx : x ∈ K) (u w : TangentSpace I x) :
    Real.sqrt (g.inner x
      (CovariantDerivative.difference (metricCov h) (metricCov g) x u w)
      (CovariantDerivative.difference (metricCov h) (metricCov g) x u w)) ≤
      (Real.sqrt L₁ ^ 3 * (3 / 2 * L₂ ^ 3 * J₂ + 3 / 2 * L₁ ^ 3 * J₁)) *
        Real.sqrt (g.inner x u u) * Real.sqrt (g.inner x w w) := by
  let A := CovariantDerivative.difference (metricCov h) (metricCov R) x u w
  let B := CovariantDerivative.difference (metricCov g) (metricCov R) x u w
  let C := 3 / 2 * L₂ ^ 3 * J₂ + 3 / 2 * L₁ ^ 3 * J₁
  have hL₁ : 0 ≤ L₁ := zero_le_one.trans hg.1
  have hL₂ : 0 ≤ L₂ := zero_le_one.trans hh.1
  have hJ₁ : 0 ≤ J₁ := (Real.sqrt_nonneg _).trans (hJg x hx)
  have hJ₂ : 0 ≤ J₂ := (Real.sqrt_nonneg _).trans (hJh x hx)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hA : Real.sqrt (R.inner x A A) ≤
      (3 / 2 * L₂ ^ 3 * J₂) * Real.sqrt (R.inner x u u) *
        Real.sqrt (R.inner x w w) := by
    simpa only [A, metricCov, mul_assoc, mul_comm, mul_left_comm] using
      connectionDifference_gJet_le hh hJh hx w u
  have hB : Real.sqrt (R.inner x B B) ≤
      (3 / 2 * L₁ ^ 3 * J₁) * Real.sqrt (R.inner x u u) *
        Real.sqrt (R.inner x w w) := by
    simpa only [B, metricCov, mul_assoc, mul_comm, mul_left_comm] using
      connectionDifference_gJet_le hg hJg hx w u
  have hsum : Real.sqrt (R.inner x (A - B) (A - B)) ≤
      C * Real.sqrt (R.inner x u u) * Real.sqrt (R.inner x w w) := by
    have htri := DifferentialGeometry.Geometry.Riemannian.sqrt_inner_add_le R x A (-B)
    have hneg : Real.sqrt (R.inner x (-B) (-B)) = Real.sqrt (R.inner x B B) := by
      simpa only [neg_one_smul, abs_neg, abs_one, one_mul] using
        DifferentialGeometry.Geometry.Riemannian.sqrt_inner_smul R x (-1) B
    rw [hneg] at htri
    calc
      _ ≤ Real.sqrt (R.inner x A A) + Real.sqrt (R.inner x B B) := by
        simpa only [sub_eq_add_neg] using htri
      _ ≤ (3 / 2 * L₂ ^ 3 * J₂) * Real.sqrt (R.inner x u u) *
          Real.sqrt (R.inner x w w) +
          (3 / 2 * L₁ ^ 3 * J₁) * Real.sqrt (R.inner x u u) *
          Real.sqrt (R.inner x w w) := add_le_add hA hB
      _ = _ := by dsimp [C]; ring
  have hinput (z : TangentSpace I x) :
      Real.sqrt (R.inner x z z) ≤ Real.sqrt L₁ * Real.sqrt (g.inner x z z) := by
    have hlow : R.inner x z z ≤ L₁ * g.inner x z z := by
      have hmul := mul_le_mul_of_nonneg_left (hg.2 x hx z).1 hL₁
      simpa only [← mul_assoc, mul_inv_cancel₀ (zero_lt_one.trans_le hg.1).ne',
        one_mul] using hmul
    exact (Real.sqrt_le_sqrt hlow).trans_eq (Real.sqrt_mul hL₁ _)
  have houtput : Real.sqrt (g.inner x (A - B) (A - B)) ≤
      Real.sqrt L₁ * Real.sqrt (R.inner x (A - B) (A - B)) :=
    (Real.sqrt_le_sqrt (hg.2 x hx (A - B)).2).trans_eq (Real.sqrt_mul hL₁ _)
  rw [connection_difference_sub_reference g h R x u w]
  change Real.sqrt (g.inner x (A - B) (A - B)) ≤ _
  calc
    _ ≤ Real.sqrt L₁ * (C * Real.sqrt (R.inner x u u) *
        Real.sqrt (R.inner x w w)) :=
      houtput.trans (mul_le_mul_of_nonneg_left hsum (Real.sqrt_nonneg _))
    _ ≤ Real.sqrt L₁ * (C * (Real.sqrt L₁ * Real.sqrt (g.inner x u u)) *
        (Real.sqrt L₁ * Real.sqrt (g.inner x w w))) := by
      apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hinput u) hC)
        (hinput w) (Real.sqrt_nonneg _) (by positivity)
    _ = _ := by dsimp [C]; ring

end DifferentialGeometry.Geometry.Curvature
