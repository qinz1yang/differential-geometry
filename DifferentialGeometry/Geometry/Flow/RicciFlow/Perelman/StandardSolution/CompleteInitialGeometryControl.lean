import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.CompleteInitialCurvatureControl
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.MetricComparison
import DifferentialGeometry.Geometry.Curvature.Bounds.ScalarNorm
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Bounds

set_option autoImplicit false

noncomputable section

open Set Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.CheegerGromovCompactness
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.PDE.RicciFlow

variable {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]
  {D : RealTimeInterval}

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
private theorem initialFan_metric_comparison_closed
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T α Q : ℝ) (hT : 0 ≤ T) (hTα : T ≤ α) (hQ : 0 ≤ Q)
    (hslab : Icc (0 : ℝ) T ⊆ D.carrier)
    (hregular : Ioo (0 : ℝ) T ⊆ D.regular)
    (hRic : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M, ∀ v : TangentSpace I x,
      |ricciTensor (I := I) (S.base.metric t) x v v| ≤
        Q * (S.base.metric t).inner x v v) :
    ∀ t ∈ Icc (0 : ℝ) T,
      MetricUniformEquivalentOn univ (S.base.metric 0) (S.base.metric t)
        (Real.exp (2 * Q * α)) := by
  have hα : 0 ≤ α := hT.trans hTα
  have hΛ : 1 ≤ Real.exp (2 * Q * α) := Real.one_le_exp (by positivity)
  intro t ht
  refine ⟨hΛ, ?_⟩
  intro x _ v
  have hg0 : 0 ≤ (S.base.metric 0).inner x v v := by
    by_cases hv : v = 0
    · simp only [hv, map_zero, le_refl]
    · exact ((S.base.metric 0).pos x v hv).le
  by_cases hp : 0 < T
  · have hb : ∀ r ∈ Ico (0 : ℝ) T,
        (Real.exp (2 * Q * α))⁻¹ * (S.base.metric 0).inner x v v ≤
            (S.base.metric r).inner x v v ∧
          (S.base.metric r).inner x v v ≤
            Real.exp (2 * Q * α) * (S.base.metric 0).inner x v v := by
      intro r hr
      let τ := (r + T) / 2
      have hτ : 0 < τ := by dsimp only [τ]; linarith [hr.1]
      have hτT : τ < T := by dsimp only [τ]; linarith [hr.2]
      have hrτ : r ≤ τ := by dsimp only [τ]; linarith [hr.2]
      have hsub : Icc (0 : ℝ) τ ⊆ Icc (0 : ℝ) T :=
        fun s hs ↦ ⟨hs.1, hs.2.trans hτT.le⟩
      have hpde := metricPDE_Icc (I := I) S hS (hsub.trans hslab)
        (fun s hs ↦ hregular ⟨hs.1, hs.2.trans hτT⟩)
      have hh := metricEquiv_Icc (I := I) S.base.metric hpde
        (fun s hs y w ↦ hRic s (hsub hs) y w) r ⟨hr.1, hrτ⟩ x v
      simp only [sub_zero] at hh
      have hscale : 2 * Q * r ≤ 2 * Q * α :=
        mul_le_mul_of_nonneg_left (hr.2.le.trans hTα) (by positivity)
      constructor
      · have he : (Real.exp (2 * Q * α))⁻¹ ≤ Real.exp (-(2 * Q * r)) := by
          rw [← Real.exp_neg]
          exact Real.exp_le_exp.mpr (neg_le_neg hscale)
        exact (mul_le_mul_of_nonneg_right he hg0).trans hh.1
      · exact hh.2.trans
          (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hscale) hg0)
    have hc : ContinuousOn (fun r : ℝ ↦ (S.base.metric r).inner x v v)
        (Icc (0 : ℝ) T) := by
      rw [continuousOn_iff_continuous_domRestrict]
      have hev := hS.smoothMetric.metricTensor_cont.eval_continuous
        (P := {s : ℝ // s ∈ Icc (0 : ℝ) T}) (τ := Subtype.val)
        (b := fun _ ↦ x) continuous_subtype_val (fun p ↦ hslab p.2)
        continuous_const (v := fun _ _ ↦ v) (fun _ ↦ continuous_const)
      refine hev.congr ?_
      intro p
      simp only [metricTensorField_apply, SolutionOn.family_metric, Set.domRestrict]
    have hclosure : closure (Ico (0 : ℝ) T) = Icc (0 : ℝ) T := closure_Ico hp.ne
    rw [← hclosure] at hc
    exact ⟨le_on_closure (fun r hr ↦ (hb r hr).1) continuousOn_const hc
        (by rw [hclosure]; exact ht),
      le_on_closure (fun r hr ↦ (hb r hr).2) hc continuousOn_const
        (by rw [hclosure]; exact ht)⟩
  · have hzero : T = 0 := le_antisymm (le_of_not_gt hp) hT
    have htzero : t = 0 := le_antisymm (ht.2.trans hzero.le) ht.1
    subst t
    constructor
    · have hi : (Real.exp (2 * Q * α))⁻¹ ≤ (1 : ℝ) :=
        inv_le_one_of_one_le₀ hΛ
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hi hg0
    · simpa only [one_mul] using mul_le_mul_of_nonneg_right hΛ hg0

theorem metric_scalar_bounds_from_initial_complete
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T : ℝ) (hT : 0 ≤ T) (K : ℝ)
    (hcomplete : RiemannianMetricComplete (I := I) (S.base.metric 0))
    (hslab : Icc (0 : ℝ) T ⊆ D.carrier)
    (hregular : Ioo (0 : ℝ) T ⊆ D.regular)
    (hbounded : ∃ B : ℝ, ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
      normSq0S (I := I) (S.base.metric t) x 4 (S.base.rm04 t x) ≤ B)
    (hinit : ∀ x : M,
      normSq0S (I := I) (S.base.metric 0) x 4 (S.base.rm04 0 x) ≤ K ^ 2) :
    ∀ t ∈ Icc (0 : ℝ)
        (min T (compactCurvatureControlTime (Module.finrank ℝ E) K)),
      MetricUniformEquivalentOn univ (S.base.metric 0) (S.base.metric t)
        (Real.exp (2 * ((Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt (2 * K ^ 2 + 1)) *
          compactCurvatureControlTime (Module.finrank ℝ E) K)) ∧
      ∀ x : M, |S.scalar t x| ≤
        (Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt (2 * K ^ 2 + 1) := by
  let δ := compactCurvatureControlTime (Module.finrank ℝ E) K
  let τ := min T δ
  let Q := (Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt (2 * K ^ 2 + 1)
  have hδ : 0 < δ := compactCurvatureControlTime_pos _ _
  have hτ : 0 ≤ τ := le_min hT hδ.le
  have hτT : τ ≤ T := min_le_left _ _
  have hτδ : τ ≤ δ := min_le_right _ _
  have hQ : 0 ≤ Q := mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg _)
  have hsub : Icc (0 : ℝ) τ ⊆ Icc (0 : ℝ) T :=
    fun t ht ↦ ⟨ht.1, ht.2.trans hτT⟩
  have hregular' : Ioo (0 : ℝ) τ ⊆ D.regular :=
    fun t ht ↦ hregular ⟨ht.1, ht.2.trans_le hτT⟩
  have hbounded' : ∃ B : ℝ, ∀ t ∈ Icc (0 : ℝ) τ, ∀ x : M,
      normSq0S (I := I) (S.base.metric t) x 4 (S.base.rm04 t x) ≤ B := by
    obtain ⟨B, hB⟩ := hbounded
    exact ⟨B, fun t ht x ↦ hB t (hsub ht) x⟩
  have hcurv := curvature_normSq_bound_from_initial_complete S hS τ hτ K hτδ
    hcomplete (hsub.trans hslab) hregular' hbounded' hinit
  have hRic : ∀ t ∈ Icc (0 : ℝ) τ, ∀ x : M, ∀ v : TangentSpace I x,
      |ricciTensor (I := I) (S.base.metric t) x v v| ≤
        Q * (S.base.metric t).inner x v v :=
    fun t ht x v ↦ ricci_quadratic_form_bound_of_solution_curvature_bound
      (I := I) S x v (hcurv t ht x)
  have hmetric := initialFan_metric_comparison_closed S hS τ δ Q hτ hτδ hQ
    (hsub.trans hslab) hregular' hRic
  intro t ht
  refine ⟨hmetric t ht, ?_⟩
  intro x
  have hs := scalar_abs_le_rm (I := I) (S.base.metric t) x
  have hs' : |S.scalar t x| ≤ (Module.finrank ℝ E : ℝ) ^ 2 *
      Real.sqrt (normSq0S (I := I) (S.base.metric t) x 4 (S.base.rm04 t x)) := by
    simpa only [SolutionOn.scalar, SolutionFamily.scalar, SolutionFamily.rm04,
      metricRm04_apply,
      show Module.finrank ℝ (TangentSpace I x) = Module.finrank ℝ E by rfl] using hs
  exact hs'.trans (mul_le_mul_of_nonneg_left
    (Real.sqrt_le_sqrt (hcurv t ht x)) (sq_nonneg _))

end DifferentialGeometry.PDE.RicciFlow

end
