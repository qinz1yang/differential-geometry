import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.Energy.Basic
import DifferentialGeometry.Geometry.Curvature.Bounds.MixedMetricDerivative
import DifferentialGeometry.Geometry.Metric.TensorInner.FiberMetric.Tensor0SMetricIneq
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.ConnectionDifferenceBound
import DifferentialGeometry.Geometry.Connection.LeviCivita.DifferenceNormBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.Bounds.ClosedInterval

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Manifold Set DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem forwardUniqueDensity_le_of_metric_curvature_connection_bounds
    (g₁ g₂ : ℝ → SmoothRiemannianMetric I M) (t : ℝ) (x : M)
    {C R₁ R₂ A : ℝ} (hC : 1 ≤ C)
    (heq : ∀ v : TangentSpace I x,
      C⁻¹ * (g₁ t).inner x v v ≤ (g₂ t).inner x v v ∧
        (g₂ t).inner x v v ≤ C * (g₁ t).inner x v v)
    (hR₁ : normSq0S (I := I) (g₁ t) x 4 (metricRm04At (I := I) (g₁ t) x) ≤ R₁)
    (hR₂ : normSq0S (I := I) (g₂ t) x 4 (metricRm04At (I := I) (g₂ t) x) ≤ R₂)
    (hA : connectionDifferenceSq (I := I) (g₁ t) (g₂ t) x ≤ A) :
    forwardUniqueDensity (I := I) g₁ g₂ t x ≤
      (2 * (Module.finrank ℝ E : ℝ) + 2 * C ^ 2 * (Module.finrank ℝ E : ℝ)) + A +
        (2 * R₁ + 2 * (Module.finrank ℝ E : ℝ) ^ 7 * C ^ 6 * R₂) := by
  let n : ℝ := Module.finrank ℝ E
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hself (g : SmoothRiemannianMetric I M) :
      normSq0S (I := I) g x 2 (metricTensorField (I := I) g x) = n := by
    obtain ⟨basis, hON⟩ := exists_orthonormal_basis (I := I) g x
    have hinv := metricInverseInBasis_of_orthonormal (I := I) g basis hON
    have hfield : metricTensorField (I := I) g x = metricTensor0S (I := I) g x := by
      ext v
      rw [metricTensorField_apply, metricTensor0S_apply]
    rw [hfield]
    have hcard := normSq0S_metricTensor0S_eq_card (I := I) g basis _ hinv
    rw [Fintype.card_fin,
      show Module.finrank ℝ (TangentSpace I x) = Module.finrank ℝ E from rfl] at hcard
    exact hcard
  have hbackground : normSq0S (I := I) (g₁ t) x 2
      (metricTensorField (I := I) (g₂ t) x) ≤ C ^ 2 * n := by
    have h := normSq0S_upper_le_of_equiv (I := I) (g₂ t) (g₁ t)
      x 2 hC (metric_equiv_symm (I := I) (g₁ t) (g₂ t) x hC heq)
      (metricTensorField (I := I) (g₂ t) x)
    simpa only [hself] using h
  have hmetric : metricDiffSq (I := I) (g₁ t) (g₂ t) x ≤ 2 * n + 2 * C ^ 2 * n := by
    have h := _root_.Tensor0SBundle.normSq0S_sub_le (I := I) (g₁ t) x 2
      (metricTensorField (I := I) (g₁ t) x) (metricTensorField (I := I) (g₂ t) x)
    rw [hself] at h
    change normSq0S (I := I) (g₁ t) x 2
      (metricTensorField (I := I) (g₁ t) x - metricTensorField (I := I) (g₂ t) x) ≤ _
    nlinarith only [h, hbackground]
  have hcross : normSq0S (I := I) (g₁ t) x 4
      (CovariantDerivative.riemannCurvature04At (I := I) (g₁ t)
        (metricCov (I := I) (g₂ t)) (metricCov_smooth (I := I) (g₂ t)) x) ≤
      n ^ 7 * C ^ 6 * R₂ :=
    (norm_sq_cross_curvature_le (I := I) (g₁ t) (g₂ t) x hC heq).trans
      (mul_le_mul_of_nonneg_left hR₂ (by positivity))
  have hriemann : rmDiffSq (I := I) (g₁ t) (g₂ t) x ≤
      2 * R₁ + 2 * n ^ 7 * C ^ 6 * R₂ := by
    have h := _root_.Tensor0SBundle.normSq0S_sub_le (I := I) (g₁ t) x 4
      (metricRm04At (I := I) (g₁ t) x)
      (CovariantDerivative.riemannCurvature04At (I := I) (g₁ t)
        (metricCov (I := I) (g₂ t)) (metricCov_smooth (I := I) (g₂ t)) x)
    change normSq0S (I := I) (g₁ t) x 4
      (metricRm04At (I := I) (g₁ t) x -
        CovariantDerivative.riemannCurvature04At (I := I) (g₁ t)
          (metricCov (I := I) (g₂ t)) (metricCov_smooth (I := I) (g₂ t)) x) ≤ _
    nlinarith only [h, hR₁, hcross]
  exact add_le_add (add_le_add hmetric hA) hriemann

theorem forwardUniqueDensity_uniform_bound_of_curvature_connection_bounds
    (g₁ g₂ : ℝ → SmoothRiemannianMetric I M)
    {J : Set ℝ} {C R₁ R₂ A : ℝ} (hC : 1 ≤ C)
    (heq : ∀ t ∈ J, ∀ x : M, ∀ v : TangentSpace I x,
      C⁻¹ * (g₁ t).inner x v v ≤ (g₂ t).inner x v v ∧
        (g₂ t).inner x v v ≤ C * (g₁ t).inner x v v)
    (hR₁ : ∀ t ∈ J, ∀ x : M,
      normSq0S (I := I) (g₁ t) x 4 (metricRm04At (I := I) (g₁ t) x) ≤ R₁)
    (hR₂ : ∀ t ∈ J, ∀ x : M,
      normSq0S (I := I) (g₂ t) x 4 (metricRm04At (I := I) (g₂ t) x) ≤ R₂)
    (hA : ∀ t ∈ J, ∀ x : M, connectionDifferenceSq (I := I) (g₁ t) (g₂ t) x ≤ A) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ J, ∀ x : M, forwardUniqueDensity (I := I) g₁ g₂ t x ≤ B := by
  let n : ℝ := Module.finrank ℝ E
  let B : ℝ := (2 * n + 2 * C ^ 2 * n) + A + (2 * R₁ + 2 * n ^ 7 * C ^ 6 * R₂)
  refine ⟨max 0 B, le_max_left _ _, fun t ht x => ?_⟩
  exact (forwardUniqueDensity_le_of_metric_curvature_connection_bounds
    g₁ g₂ t x hC (heq t ht x) (hR₁ t ht x) (hR₂ t ht x) (hA t ht x)).trans
      (le_max_right _ _)

end DifferentialGeometry.PDE.RicciFlow

end

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Set DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

theorem forwardUniqueDensity_uniform_bound_on_closed_interval
    {D₁ D₂ : RealTimeInterval} (S₁ : SolutionOn (I := I) (M := M) D₁)
    (S₂ : SolutionOn (I := I) (M := M) D₂)
    (hS₁ : IsSolutionOn S₁) (hS₂ : IsSolutionOn S₂) {a b C₁ C₂ : ℝ}
    (hab : a < b)
    (hcarrier₁ : Icc a b ⊆ D₁.carrier) (hcarrier₂ : Icc a b ⊆ D₂.carrier)
    (hregular₁ : Ioc a b ⊆ D₁.regular) (hregular₂ : Ioc a b ⊆ D₂.regular)
    (hcomplete₁ : RiemannianMetricComplete (I := I) (S₁.base.metric a))
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hcurv₁ : ∀ t ∈ Icc a b, ∀ x : M,
      normSq0S (I := I) (S₁.base.metric t) x 4 (S₁.base.rm04 t x) ≤ C₁)
    (hcurv₂ : ∀ t ∈ Icc a b, ∀ x : M,
      normSq0S (I := I) (S₂.base.metric t) x 4 (S₂.base.rm04 t x) ≤ C₂)
    (hinit : S₁.base.metric a = S₂.base.metric a) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Icc a b, ∀ x : M,
      forwardUniqueDensity (I := I) S₁.base.metric S₂.base.metric t x ≤ B := by
  have hcomplete₂ : RiemannianMetricComplete (I := I) (S₂.base.metric a) := by
    rw [← hinit]
    exact hcomplete₁
  have hcurv₁' : ∀ t ∈ Icc a b, ∀ x : M,
      nablaKRm04NormSqIntrinsic S₁ 0 t x ≤ C₁ := by
    intro t ht x
    simpa only [nablaKRm04NormSqIntrinsic, nablaKRm04Field_zero, Nat.add_zero] using hcurv₁ t ht x
  have hcurv₂' : ∀ t ∈ Icc a b, ∀ x : M,
      nablaKRm04NormSqIntrinsic S₂ 0 t x ≤ C₂ := by
    intro t ht x
    simpa only [nablaKRm04NormSqIntrinsic, nablaKRm04Field_zero, Nat.add_zero] using hcurv₂ t ht x
  obtain ⟨P₁, hP₁, hconn₁⟩ := exists_connection_difference_sqrt_bound_of_complete_bounded_curvature
    S₁ hS₁ hab hcarrier₁ hregular₁ hcomplete₁ hC₁ hcurv₁'
  obtain ⟨P₂, hP₂, hconn₂⟩ := exists_connection_difference_sqrt_bound_of_complete_bounded_curvature
    S₂ hS₂ hab hcarrier₂ hregular₂ hcomplete₂ hC₂ hcurv₂'
  obtain ⟨Λ₁, hΛ₁, heq₁⟩ := exists_uniform_metric_equivalence_on_closed_interval_of_curvature_bound
    S₁ hS₁ hab hcarrier₁ (fun t ht => hregular₁ ⟨ht.1, ht.2.le⟩) hcurv₁
  obtain ⟨Λ₂, hΛ₂, heq₂⟩ := exists_uniform_metric_equivalence_on_closed_interval_of_curvature_bound
    S₂ hS₂ hab hcarrier₂ (fun t ht => hregular₂ ⟨ht.1, ht.2.le⟩) hcurv₂
  have hΛ₁0 : 0 ≤ Λ₁ := zero_le_one.trans hΛ₁
  have hΛ₂0 : 0 ≤ Λ₂ := zero_le_one.trans hΛ₂
  let L₁ : ℝ := P₁ * Real.sqrt (b - a)
  let L₂ : ℝ := P₂ * Real.sqrt (b - a)
  have hL₁ : 0 ≤ L₁ := mul_nonneg hP₁ (Real.sqrt_nonneg _)
  have hL₂ : 0 ≤ L₂ := mul_nonneg hP₂ (Real.sqrt_nonneg _)
  let A : ℝ := (Module.finrank ℝ E : ℝ) ^ 3 * Λ₁ ^ 3 * (L₁ + L₂) ^ 2
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hbound : ∀ t ∈ Icc a b, ∀ x : M,
      connectionDifferenceSq (I := I) (S₁.base.metric t) (S₂.base.metric t) x ≤ A := by
    intro t ht x
    rcases ht.1.eq_or_lt with ha | ha
    · subst t
      rw [← hinit, connectionDifferenceSq_def, connectionDifferenceLowAt_self]
      have hz : normSq0S (I := I) (S₁.base.metric a) x 3 0 = 0 :=
        ((tensor0SMetricData (I := I) (S₁.base.metric a) x 3).inner_self_eq_zero_iff 0).2 rfl
      rw [hz]
      exact hA
    · have ht' : t ∈ Ioc a b := ⟨ha, ht.2⟩
      apply connectionDifferenceSq_le_of_common_connection_bounds
        (S₁.base.metric a) (S₁.base.metric t) (S₂.base.metric t)
        (metricCov (I := I) (S₁.base.metric a)) x hΛ₁ hL₁ hL₂
        ((heq₁ t ht).2 x (mem_univ x))
      · intro u w
        have h := hconn₁ t ht' x u w
        refine h.trans ?_
        apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
        apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
        exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (sub_le_sub_right ht.2 a)) hP₁
      · intro u w
        have h := hconn₂ t ht' x u w
        rw [← hinit] at h
        refine h.trans ?_
        apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
        apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
        exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (sub_le_sub_right ht.2 a)) hP₂
  have hpair : ∀ t ∈ Icc a b,
      MetricUniformEquivalentOn (I := I) univ
        (S₁.base.metric t) (S₂.base.metric t) (Λ₁ * Λ₂) := by
    intro t ht
    have heq₂' : MetricUniformEquivalentOn (I := I) univ
        (S₁.base.metric a) (S₂.base.metric t) Λ₂ := by
      rw [hinit]
      exact heq₂ t ht
    exact (metricUniformEquivalentOn_symm (heq₁ t ht)).trans heq₂'
  apply forwardUniqueDensity_uniform_bound_of_curvature_connection_bounds
    S₁.base.metric S₂.base.metric
    (C := Λ₁ * Λ₂) (R₁ := C₁) (R₂ := C₂) (A := A)
    (by simpa only [one_mul] using mul_le_mul hΛ₁ hΛ₂ (by norm_num) hΛ₁0)
    (fun t ht x v => (hpair t ht).2 x (mem_univ x) v)
  · intro t ht x
    exact hcurv₁ t ht x
  · intro t ht x
    exact hcurv₂ t ht x
  · exact hbound

end DifferentialGeometry.PDE.RicciFlow
