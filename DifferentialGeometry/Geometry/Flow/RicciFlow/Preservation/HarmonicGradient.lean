import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.Scalar.CompleteHeatComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.Cutoff.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.MetricComparison
import DifferentialGeometry.Geometry.Curvature.Bochner.Scalar.TensorFormula
import DifferentialGeometry.Geometry.Curvature.Bochner.Scalar.Rigidity
import DifferentialGeometry.Geometry.Operator.Gradient.NormSquaredTime
import DifferentialGeometry.Geometry.Metric.Family.Regularity.DifferentialOperator
import DifferentialGeometry.Geometry.Metric.TensorInner.Estimates.CotangentNorm

noncomputable section

open Bundle Set
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Analysis.Parabolic
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private theorem differential_norm (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M) :
    normSq0S g x 1 (differential1FormFun (I := I) f x) = normGradSqFun g f x := by
  have hsharp : cotangentSharp g x (differential1FormFun (I := I) f x) = gradientFun g f x := by
    apply tangentFlatLinear_injective g x
    ext v
    change g.inner x (cotangentSharp g x (differential1FormFun (I := I) f x)) v =
      g.inner x (gradientFun g f x) v
    rw [cotangentSharp_inner, cotangentToDual_apply]
    exact differential1FormFun_apply_eq_inner_gradientFun g f x v
  rw [normSq0S_eq_inner, inner0S_one_eq_cotangent, cotangentInner_eq_sharp, hsharp]
  rfl

private theorem normGradSqFun_eq_on_slab_of_harmonic_of_ricci_nonnegative_zero
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {T : ℝ} (hT : 0 < T) (hreg : Icc 0 T ⊆ D.regular)
    (hcomplete : RiemannianMetricComplete (S.base.metric 0))
    (hcurv : ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Icc 0 T, ∀ x,
      normSq0S (S.base.metric t) x 4 (S.base.rm04 t x) ≤ K)
    (hRic : ∀ t ∈ Icc 0 T, BonnetMyers.RicciBoundedBelow (S.base.metric t) 0)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hharmonic : ∀ t ∈ Icc 0 T, ∀ x,
      laplacian (LeviCivita (S.base.metric t)) (S.base.metric t) f x = 0)
    {c : ℝ} (hinitial : ∀ x, normGradSqFun (S.base.metric 0) f x = c) :
    ∀ t ∈ Icc 0 T, ∀ x, normGradSqFun (S.base.metric t) f x = c := by
  classical
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨K, hK, hcurv⟩ := hcurv
  have hslab : Icc 0 T ⊆ D.carrier := hreg.trans D.regular_subset
  let N : ℝ → M → ℝ := fun t => normGradSqFun (S.base.metric t) f
  let G := flowG S
  have hNcont : ContinuousOn (fun p : ℝ × M => N p.1 p.2) (Icc 0 T ×ˢ univ) :=
    hS.smoothMetric.gradient_norm_sq_continuousOn hreg hf
  have hNspace (t : ℝ) : ContMDiff I 𝓘(ℝ, ℝ) ∞ (N t) :=
    normGradSqFun_contMDiff (S.base.metric t) hf
  have hderiv (t : ℝ) (ht : t ∈ Icc 0 T) (x : M) :
      HasDerivAt (fun s => N s x)
        (2 * ricciTensor (S.base.metric t) x
          (gradFun (S.base.metric t) f x) (gradFun (S.base.metric t) f x)) t := by
    have hslots (v w : TangentSpace I x) :
        (fun a : Fin 2 => if a = 0 then v else w) = vec2 v w := by
      funext i
      fin_cases i <;> rfl
    have h := normGradSq_time (x := x) (t := t) S.base.metric (fun _ => f) (fun _ => 0)
      (S.ricci t x) ?_ ?_
    · rw [gradientFun_const, map_zero, zero_apply, mul_zero, add_zero] at h
      simp only [hslots, SolutionOn.ricci, SolutionFamily.ricci_apply, SolutionFamily.ricciAt,
        metricRicciAt_apply_eq_ricciTensor, gradient_eq_gradFun] at h
      exact h
    · intro v w
      simpa only [hslots, SolutionOn.family_metric, SolutionOn.ricci, SolutionOn.ricciAt,
        SolutionFamily.ricci_apply] using metricDerivAt S hS ⟨t, hreg ht⟩ x v w
    · intro v
      simpa [mvfderiv] using hasDerivAt_const t (mvfderiv (I := I) f x v)
  have hpar (t : ℝ) (ht : t ∈ Icc 0 T) (x : M) :
      parabolicOperatorWithDrift G T (fun _ _ => 0) N t x ≤ 0 := by
    have hbochner := laplacian_gradient_norm_sq_eq (S.base.metric t) hf x
    have hzero : (fun y => laplacian (metricCov (S.base.metric t)) (S.base.metric t) f y) =
        fun _ => 0 := funext (hharmonic t ht)
    rw [hzero, gradientFun_const, map_zero, mul_zero, add_zero,
      metricRicciAt_apply_eq_ricciTensor] at hbochner
    simp only [gradient_eq_gradFun] at hbochner
    have hnonneg := normSq0S_nonneg (S.base.metric t) x 2
      (hessianSec (metricCov (S.base.metric t)) (metricCov_smooth (S.base.metric t)) f hf x)
    rw [parabolicOperatorWithDrift_eq, heatOperatorWithDrift_zero_drift,
      (hderiv t ht x).hasDerivWithinAt.derivWithin ((uniqueDiffOn_Icc hT) t ht)]
    change 2 * ricciTensor (S.base.metric t) x _ _ -
      laplacian (LeviCivita (S.base.metric t)) (S.base.metric t) (N t) x ≤ 0
    change laplacian (LeviCivita (S.base.metric t)) (S.base.metric t) (N t) x = _ at hbochner
    linarith only [hbochner, hnonneg]
  let L := (Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt K
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have heq := metricEquiv_Icc S.base.metric
    (metricPDE_Icc S hS hslab (Ioo_subset_Icc_self.trans hreg))
    (fun t ht x v => ricci_quadratic_form_bound_of_solution_curvature_bound S x v (hcurv t ht x))
  have hbound (t : ℝ) (ht : t ∈ Icc 0 T) (x : M) : N t x ≤ Real.exp (2 * L * T) * c := by
    have hmetric (v : TangentSpace I x) : (S.base.metric 0).inner x v v ≤
        Real.exp (2 * L * T) * (S.base.metric t).inner x v v := by
      have h := mul_le_mul_of_nonneg_left (heq t ht x v).1 (Real.exp_pos (2 * L * t)).le
      have he : Real.exp (2 * L * t) * Real.exp (-(2 * L * (t - 0))) = 1 := by
        rw [← Real.exp_add]; simp
      rw [← mul_assoc, he, one_mul] at h
      exact h.trans (mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 (by positivity)))
        (Geometry.Riemannian.Exponential.gInner_self_nonneg (S.base.metric t) x v))
    have hn := normSq0S_one_le_of_metric_le (S.base.metric 0) (S.base.metric t) x
      (Real.exp_pos _).le hmetric (differential1FormFun (I := I) f x)
    simpa only [differential_norm, hinitial] using hn
  have hcut := nonempty_shi_barrier_cutoff_data_of_solution S hS hT hslab
    (Ioc_subset_Icc_self.trans hreg) hcomplete hK hcurv
  have hupper : ∀ t ∈ Icc 0 T, ∀ x, N t x - c ≤ 0 := by
    apply DifferentialGeometry.Analysis.nonpositive_of_heat_subsolution_and_cutoffs G T hT
      (fun t x => N t x - c) (Real.exp (2 * L * T) * c - c)
      (hNcont.sub continuousOn_const)
      (fun t ht _ x => ((hderiv t ht x).sub_const c).differentiableAt.differentiableWithinAt)
      (fun t _ _ => (hNspace t).sub contMDiff_const)
      (fun x => by change normGradSqFun _ _ _ - c ≤ 0; rw [hinitial, sub_self])
      (fun t ht x => sub_le_sub_right (hbound t ht x) c) _ hcut
    intro t ht _ x
    rw [parabolicOperatorWithDrift_eq, heatOperatorWithDrift_zero_drift,
      ((hderiv t ht x).sub_const c).hasDerivWithinAt.derivWithin ((uniqueDiffOn_Icc hT) t ht)]
    change _ - laplacian (LeviCivita (S.base.metric t)) (S.base.metric t) (fun y => N t y - c) x ≤ 0
    rw [laplacian_sub_const _ _ c (fun y => (hNspace t).mdifferentiableAt (by simp))]
    have h := hpar t ht x
    rw [parabolicOperatorWithDrift_eq, heatOperatorWithDrift_zero_drift,
      (hderiv t ht x).hasDerivWithinAt.derivWithin ((uniqueDiffOn_Icc hT) t ht)] at h
    exact h
  intro t ht x
  apply le_antisymm (sub_nonpos.mp (hupper t ht x))
  have hm : MonotoneOn (fun s => N s x) (Icc 0 T) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 T)
    · intro s hs
      exact (hderiv s hs x).continuousAt.continuousWithinAt
    · intro s hs
      exact (hderiv s (interior_subset hs) x).hasDerivWithinAt
    · intro s hs
      have hr := hRic s (interior_subset hs) x (gradFun (S.base.metric s) f x)
      simp only [zero_mul] at hr
      exact mul_nonneg (by norm_num) hr
  simpa only [N, hinitial] using hm ⟨le_rfl, hT.le⟩ ht ht.1

theorem normGradSqFun_eq_on_slab_of_harmonic_of_ricci_nonnegative
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a b : ℝ} (hab : a ≤ b) (hreg : Icc a b ⊆ D.regular)
    (hcomplete : RiemannianMetricComplete (S.base.metric a))
    (hcurv : ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Icc a b, ∀ x,
      normSq0S (S.base.metric t) x 4 (S.base.rm04 t x) ≤ K)
    (hRic : ∀ t ∈ Icc a b, BonnetMyers.RicciBoundedBelow (S.base.metric t) 0)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hharmonic : ∀ t ∈ Icc a b, ∀ x,
      laplacian (LeviCivita (S.base.metric t)) (S.base.metric t) f x = 0)
    {c : ℝ} (hinitial : ∀ x, normGradSqFun (S.base.metric a) f x = c) :
    ∀ t ∈ Icc a b, ∀ x, normGradSqFun (S.base.metric t) f x = c := by
  rcases hab.eq_or_lt with rfl | hab
  · intro t ht x
    have ht' : t = a := le_antisymm ht.2 ht.1
    rw [ht']
    exact hinitial x
  let U := S.timeShift a
  have hU := isSolutionOn_timeShift hS a
  have hsub (t : ℝ) (ht : t ∈ Icc 0 (b - a)) : t + a ∈ Icc a b :=
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hregU : Icc 0 (b - a) ⊆ (D.timeShift a).regular :=
    fun t ht => hreg (hsub t ht)
  have hc : RiemannianMetricComplete (U.base.metric 0) := by
    simpa only [U, SolutionOn.timeShift_base_metric, zero_add] using hcomplete
  have hcurvU : ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Icc 0 (b - a), ∀ x,
      normSq0S (U.base.metric t) x 4 (U.base.rm04 t x) ≤ K := by
    obtain ⟨K, hK, hb⟩ := hcurv
    exact ⟨K, hK, fun t ht x => hb (t + a) (hsub t ht) x⟩
  have h := normGradSqFun_eq_on_slab_of_harmonic_of_ricci_nonnegative_zero U hU
    (sub_pos.mpr hab) hregU hc hcurvU (fun t ht => hRic (t + a) (hsub t ht)) hf
    (fun t ht => hharmonic (t + a) (hsub t ht))
    (by simpa only [U, SolutionOn.timeShift_base_metric, zero_add] using hinitial)
  intro t ht x
  have htx := h (t - a) ⟨sub_nonneg.mpr ht.1, sub_le_sub_right ht.2 a⟩ x
  simpa only [U, SolutionOn.timeShift_base_metric, sub_add_cancel] using htx

theorem covariantDerivative_gradFun_eq_zero_on_slab_of_harmonic_of_ricci_nonnegative
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a b : ℝ} (hab : a ≤ b) (hreg : Icc a b ⊆ D.regular)
    (hcomplete : RiemannianMetricComplete (S.base.metric a))
    (hcurv : ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Icc a b, ∀ x,
      normSq0S (S.base.metric t) x 4 (S.base.rm04 t x) ≤ K)
    (hRic : ∀ t ∈ Icc a b, BonnetMyers.RicciBoundedBelow (S.base.metric t) 0)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hharmonic : ∀ t ∈ Icc a b, ∀ x,
      laplacian (LeviCivita (S.base.metric t)) (S.base.metric t) f x = 0)
    {c : ℝ} (hinitial : ∀ x, normGradSqFun (S.base.metric a) f x = c) :
    ∀ t ∈ Icc a b, ∀ x,
      (LeviCivita (S.base.metric t)).toFun (fun y => gradFun (S.base.metric t) f y) x = 0 := by
  have hnorm := normGradSqFun_eq_on_slab_of_harmonic_of_ricci_nonnegative S hS hab hreg
    hcomplete hcurv hRic hf hharmonic hinitial
  intro t ht x
  apply covariantDerivative_gradFun_eq_zero_of_harmonic_of_locally_constant_norm
    (S.base.metric t) hf x (Filter.Eventually.of_forall (hnorm t ht))
  · apply Filter.Eventually.of_forall
    intro y
    rw [← laplacian_levi_eq]
    exact hharmonic t ht y
  · simpa only [zero_mul] using hRic t ht x (gradFun (S.base.metric t) f x)

end DifferentialGeometry.PDE.RicciFlow
