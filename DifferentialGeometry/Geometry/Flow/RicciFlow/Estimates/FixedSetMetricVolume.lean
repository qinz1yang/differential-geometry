import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.Bounds.UniformEquivalence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Ricci.Estimate.QuadraticForm
import DifferentialGeometry.Geometry.Measure.MetricComparison

set_option autoImplicit false

noncomputable section

open Bundle MeasureTheory Set
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
variable {D : RealTimeInterval}

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem fixed_set_metric_comparison_of_rm
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T r : ℝ) {U : Set M} (hr : 0 < r)
    (hslab : Icc (T - r ^ 2) T ⊆ D.carrier)
    (hreg : Ioc (T - r ^ 2) T ⊆ D.regular)
    (hRm : ∀ t ∈ Icc (T - r ^ 2) T, ∀ x ∈ U,
      r ^ 4 * normSq0S (I := I) (S.base.metric t) x 4 (S.base.rm04 t x) ≤ 1)
    {eps : ℝ} (heps : 0 < eps) (heps1 : eps < 1) :
    ∀ t ∈ Icc (T - eps * r ^ 2) T, t ∈ D.carrier ∧
      ∀ x ∈ U, ∀ v : TangentSpace I x,
        (S.base.metric T).inner x v v ≤
            Real.exp (2 * (Module.finrank ℝ E : ℝ) ^ 2 * eps) *
              (S.base.metric t).inner x v v ∧
          (S.base.metric t).inner x v v ≤
            Real.exp (2 * (Module.finrank ℝ E : ℝ) ^ 2 * eps) *
              (S.base.metric T).inner x v v := by
  let n : ℝ := Module.finrank ℝ E
  let A : ℝ := n ^ 2 / r ^ 2
  let Q : ℝ := Real.exp (2 * n ^ 2 * eps)
  have hA : 0 ≤ A := div_nonneg (sq_nonneg n) (sq_nonneg r)
  have hQ : 0 < Q := Real.exp_pos _
  have hshort : eps * r ^ 2 < r ^ 2 := by
    simpa only [one_mul] using
      mul_lt_mul_of_pos_right heps1 (sq_pos_of_pos hr)
  have hbig : Icc (T - eps * r ^ 2) T ⊆ Icc (T - r ^ 2) T := by
    intro t ht
    exact ⟨by linarith [ht.1], ht.2⟩
  have hwin : Icc (T - eps * r ^ 2) T ⊆ D.regular := by
    intro t ht
    apply hreg
    exact ⟨by linarith [ht.1], ht.2⟩
  have hT : T ∈ Icc (T - eps * r ^ 2) T :=
    ⟨sub_le_self _ (mul_nonneg heps.le (sq_nonneg r)), le_rfl⟩
  have hsqrt : Real.sqrt (1 / r ^ 4) = 1 / r ^ 2 := by
    rw [show r ^ 4 = (r ^ 2) ^ 2 by ring,
      show 1 / (r ^ 2) ^ 2 = (1 / r ^ 2) ^ 2 by field_simp]
    exact Real.sqrt_sq (one_div_pos.mpr (sq_pos_of_pos hr)).le
  have hric : ∀ t ∈ Icc (T - eps * r ^ 2) T, ∀ x ∈ U,
      ∀ v : TangentSpace I x,
        |S.ricciAt t x (vec2 (I := I) v v)| ≤
          A * (S.base.metric t).inner x v v := by
    intro t ht x hx v
    have hcurv : normSq0S (I := I) (S.base.metric t) x 4
        (S.base.rm04 t x) ≤ 1 / r ^ 4 := by
      apply (le_div_iff₀ (pow_pos hr 4)).2
      simpa only [mul_comm] using hRm t (hbig ht) x hx
    have hquad := ricci_quadratic_form_bound_of_solution_curvature_bound
      (I := I) S x v hcurv
    rw [← metricRicciAt_apply_eq_ricciTensor, hsqrt] at hquad
    simpa only [SolutionOn.ricciAt, SolutionFamily.ricciAt,
      A, n, div_eq_mul_inv, one_mul] using hquad
  have hequiv := metric_uniform_equivalent_on_window_of_solutions (I := I)
    (fun _ : ℕ ↦ S) (fun _ ↦ hS) U (T - eps * r ^ 2) T T 1 A
    (S.base.metric T) hwin hT (by norm_num) hA
    (fun _ ↦ by
      refine ⟨by norm_num, ?_⟩
      intro x hx v
      simp)
    (fun _ t ht x hx v ↦ hric t ht x hx v)
  have hscale : 2 * A * (eps * r ^ 2) = 2 * n ^ 2 * eps := by
    dsimp only [A]
    field_simp [hr.ne']
  intro t ht
  refine ⟨hslab (hbig ht), ?_⟩
  intro x hx v
  have habs : |t - T| ≤ eps * r ^ 2 := by
    rw [abs_of_nonpos (sub_nonpos.mpr ht.2)]
    linarith [ht.1]
  have hFQ : metricEquivalenceFactor 1 A t T ≤ Q := by
    dsimp only [metricEquivalenceFactor, Q]
    rw [one_mul]
    apply Real.exp_le_exp.mpr
    calc
      2 * A * |t - T| ≤ 2 * A * (eps * r ^ 2) :=
        mul_le_mul_of_nonneg_left habs (mul_nonneg (by norm_num) hA)
      _ = 2 * n ^ 2 * eps := hscale
  have hpair := (metricUniformEquivalentOn_of_le
    (hequiv 0 t ht) hFQ).2 x hx v
  change (S.base.metric T).inner x v v ≤ Q * (S.base.metric t).inner x v v ∧
    (S.base.metric t).inner x v v ≤ Q * (S.base.metric T).inner x v v
  refine ⟨?_, hpair.2⟩
  calc
    (S.base.metric T).inner x v v =
        Q * (Q⁻¹ * (S.base.metric T).inner x v v) := by
      field_simp [hQ.ne']
    _ ≤ Q * (S.base.metric t).inner x v v :=
      mul_le_mul_of_nonneg_left hpair.1 hQ.le

theorem fixed_set_volume_comparison_of_rm
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T r : ℝ) {U : Set M} (hU : MeasurableSet U) (hr : 0 < r)
    (hslab : Icc (T - r ^ 2) T ⊆ D.carrier)
    (hreg : Ioc (T - r ^ 2) T ⊆ D.regular)
    (hRm : ∀ t ∈ Icc (T - r ^ 2) T, ∀ x ∈ U,
      r ^ 4 * normSq0S (I := I) (S.base.metric t) x 4 (S.base.rm04 t x) ≤ 1)
    {eps : ℝ} (heps : 0 < eps) (heps1 : eps < 1) :
    T - eps * r ^ 2 ∈ D.carrier ∧
      riemannianVolumeMeasure (I := I) (M := M)
          (S.base.metric (T - eps * r ^ 2)) U ≤
        ENNReal.ofReal (Real.exp ((Module.finrank ℝ E : ℝ) ^ 3 * eps)) *
          riemannianVolumeMeasure (I := I) (M := M) (S.base.metric T) U := by
  have ht : T - eps * r ^ 2 ∈ Icc (T - eps * r ^ 2) T :=
    ⟨le_rfl, sub_le_self _ (mul_nonneg heps.le (sq_nonneg r))⟩
  have hmetric := fixed_set_metric_comparison_of_rm S hS T r hr hslab hreg hRm
    heps heps1 (T - eps * r ^ 2) ht
  refine ⟨hmetric.1, ?_⟩
  have hvolume := DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_apply_le_of_inner_le
    (S.base.metric T) (S.base.metric (T - eps * r ^ 2))
    (Real.exp_pos (2 * (Module.finrank ℝ E : ℝ) ^ 2 * eps)) hU
    (fun x hx v ↦ (hmetric.2 x hx v).2)
  have hfactor : Real.sqrt
      ((Real.exp (2 * (Module.finrank ℝ E : ℝ) ^ 2 * eps)) ^ Module.finrank ℝ E) =
        Real.exp ((Module.finrank ℝ E : ℝ) ^ 3 * eps) := by
    have hexp :
        (Real.exp (2 * (Module.finrank ℝ E : ℝ) ^ 2 * eps)) ^ Module.finrank ℝ E =
          (Real.exp ((Module.finrank ℝ E : ℝ) ^ 3 * eps)) ^ 2 := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
      congr 1
      norm_num
      ring
    rw [hexp, Real.sqrt_sq (Real.exp_pos _).le]
  simpa only [hfactor] using hvolume

end DifferentialGeometry.PDE.RicciFlow

end
