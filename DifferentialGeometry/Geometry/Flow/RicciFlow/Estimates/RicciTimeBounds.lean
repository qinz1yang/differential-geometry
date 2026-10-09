import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.CurvatureContinuity
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Coordinates.MetricComparison
import Mathlib.Analysis.Calculus.MeanValue
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.ExpressionBounds

set_option autoImplicit false
noncomputable section

open Set Bundle Manifold DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.PDE.RicciFlow
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow

private def ordinaryRicciTimeExpression : CurvatureExpression 2 :=
  .add CurvatureExpression.ricci.timeDerivative
    (.smul (-1) CurvatureExpression.ricci.ricciAction)

private theorem ordinaryRicciTimeExpression_order :
    ordinaryRicciTimeExpression.maxOrder ≤ 2 := by
  have ht := CurvatureExpression.maxOrder_timeDerivative_le CurvatureExpression.ricci
  have ha : CurvatureExpression.ricci.ricciAction.maxOrder = 0 := rfl
  change max CurvatureExpression.ricci.timeDerivative.maxOrder
    CurvatureExpression.ricci.ricciAction.maxOrder ≤ 2
  rw [ha]
  exact max_le (show CurvatureExpression.ricci.timeDerivative.maxOrder ≤ 2 from ht) (by decide)

def ricciOrdinaryTimeBound (d : ℕ) (C : ℝ) : ℝ :=
  ordinaryRicciTimeExpression.normBound d C

theorem ricciOrdinaryTimeBound_nonneg (d : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    0 ≤ ricciOrdinaryTimeBound d C :=
  ordinaryRicciTimeExpression.normBound_nonneg d C hC

section Generic

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [BoundarylessManifold I M]

private theorem ordinaryRicciTimeExpression_eval {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (t : RealTimeInterval.RegularTime D) (x : M) :
    derivWithin (fun r => metricRicciAt (S.base.metric r) x) D.carrier (t : ℝ) =
      ordinaryRicciTimeExpression.eval S (t : ℝ) x := by
  have ht := CurvatureExpression.ricci.eval_timeDerivative S hS t x
  have ha := CurvatureExpression.ricci.eval_ricciAction S (t : ℝ) x
  simp only [covariantTimeDerivWithin, CurvatureExpression.eval_ricci] at ht
  simp only [CurvatureExpression.eval_ricci] at ha
  rw [← ha] at ht
  change derivWithin (fun r => metricRicciAt (S.base.metric r) x) D.carrier (t : ℝ) =
    CurvatureExpression.ricci.timeDerivative.eval S (t : ℝ) x +
      (-1 : ℝ) • CurvatureExpression.ricci.ricciAction.eval S (t : ℝ) x
  rw [neg_one_smul]
  simpa only [sub_eq_add_neg] using (eq_sub_iff_add_eq.mpr ht)

theorem metricRicciAt_differentiableWithinAt {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (t : RealTimeInterval.RegularTime D) (x : M) :
    DifferentiableWithinAt ℝ (fun r => metricRicciAt (S.base.metric r) x)
      D.carrier (t : ℝ) := by
  simpa only [CurvatureExpression.eval_ricci] using
    CurvatureExpression.ricci.eval_differentiableWithinAt S hS t x

theorem ricci_ordinary_time_derivative_bound {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (t : RealTimeInterval.RegularTime D) (x : M) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ k ≤ 2,
      Real.sqrt (nablaKRm04NormSqIntrinsic S k (t : ℝ) x) ≤ C) :
    Real.sqrt (normSq0S (S.base.metric (t : ℝ)) x 2
      (derivWithin (fun r => metricRicciAt (S.base.metric r) x) D.carrier (t : ℝ))) ≤
        ricciOrdinaryTimeBound (Module.finrank ℝ E) C := by
  rw [ordinaryRicciTimeExpression_eval S hS t x]
  exact ordinaryRicciTimeExpression.eval_norm_le S (t : ℝ) x C hC
    (fun k hk => hbound k (hk.trans ordinaryRicciTimeExpression_order))

end Generic

end DifferentialGeometry.PDE.RicciFlow
end

set_option autoImplicit false
noncomputable section
open Set Filter Bundle Manifold
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff Topology NNReal
namespace DifferentialGeometry.PDE.RicciFlow
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

variable [BoundarylessManifold I M]

private theorem ricciTensor_lipschitz_of_time_derivative_bound
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (R : SmoothRiemannianMetric I M) (x : M) {a b Λ B : ℝ}
    (hΛ : 0 ≤ Λ) (hB : 0 ≤ B)
    (hcarrier : Icc a b ⊆ D.carrier) (hregular : Ioo a b ⊆ D.regular)
    (hmetric : ∀ r ∈ Ioo a b, ∀ v : TangentSpace I x,
      (S.base.metric r).inner x v v ≤ Λ * R.inner x v v)
    (hdifferentiable : ∀ r ∈ Ioo a b,
      DifferentiableWithinAt ℝ (fun z => metricRicciAt (S.base.metric z) x) D.carrier r)
    (hderiv : ∀ r ∈ Ioo a b,
      Real.sqrt (normSq0S (S.base.metric r) x 2
        (derivWithin (fun z => metricRicciAt (S.base.metric z) x) D.carrier r)) ≤ B)
    {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (v w : TangentSpace I x) :
    |ricciTensor (S.base.metric s) x v w - ricciTensor (S.base.metric t) x v w| ≤
      Λ * B * Real.sqrt (R.inner x v v) * Real.sqrt (R.inner x w w) * |s - t| := by
  have hab : a ≤ b := hs.1.trans hs.2
  rcases hab.eq_or_lt with heq | hab
  · have hst : s = t := by rcases heq with rfl; exact (le_antisymm hs.2 hs.1).trans (le_antisymm ht.1 ht.2)
    simp only [hst, sub_self, abs_zero, mul_zero, le_refl]
  let f : ℝ → ℝ := fun r => ricciTensor (S.base.metric r) x v w
  let f' : ℝ → ℝ := fun r =>
    (derivWithin (fun z => metricRicciAt (S.base.metric z) x) D.carrier r) (vec2 v w)
  let A := Λ * B * Real.sqrt (R.inner x v v) * Real.sqrt (R.inner x w w)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hcont : ContinuousOn f (Icc a b) := (hS.continuousOn_ricciTensor x v w).mono hcarrier
  have hdiff (r : ℝ) (hr : r ∈ Ioo a b) : HasDerivAt f (f' r) r := by
    have hh := (tensor0SEvalCLM (I := I) (vec2 v w)).hasFDerivAt.comp_hasDerivWithinAt
      (f := fun z => metricRicciAt (S.base.metric z) x) r
      (hdifferentiable r hr).hasDerivWithinAt
    have hactual : HasDerivAt
        (fun z => metricRicciAt (S.base.metric z) x (vec2 v w)) (f' r) r :=
      hh.hasDerivAt (D.regular_mem_nhds (hregular hr))
    exact hactual.congr_of_eventuallyEq (Eventually.of_forall
      (fun z => (metricRicciAt_apply_eq_ricciTensor (S.base.metric z) x v w).symm))
  have hbound (r : ℝ) (hr : r ∈ Ioo a b) : |f' r| ≤ A := by
    obtain ⟨basis, hON⟩ := exists_orthonormal_basis (S.base.metric r) x
    have heval := abs_apply_le_sqrt_normSq0S (S.base.metric r) x 2 basis hON
      (derivWithin (fun z => metricRicciAt (S.base.metric z) x) D.carrier r) (vec2 v w)
    have hpair : |f' r| ≤
        Real.sqrt (normSq0S (S.base.metric r) x 2
          (derivWithin (fun z => metricRicciAt (S.base.metric z) x) D.carrier r)) *
            Real.sqrt ((S.base.metric r).inner x v v) *
              Real.sqrt ((S.base.metric r).inner x w w) := by
      simpa [f', vec2, mul_assoc] using heval
    have hsqrt (z : TangentSpace I x) : Real.sqrt ((S.base.metric r).inner x z z) ≤
        Real.sqrt Λ * Real.sqrt (R.inner x z z) :=
      (Real.sqrt_le_sqrt (hmetric r hr z)).trans_eq (Real.sqrt_mul hΛ _)
    calc |f' r|
        ≤ Real.sqrt (normSq0S (S.base.metric r) x 2
          (derivWithin (fun z => metricRicciAt (S.base.metric z) x) D.carrier r)) *
            Real.sqrt ((S.base.metric r).inner x v v) *
              Real.sqrt ((S.base.metric r).inner x w w) := hpair
      _ ≤ B * (Real.sqrt Λ * Real.sqrt (R.inner x v v)) *
          (Real.sqrt Λ * Real.sqrt (R.inner x w w)) := by
        gcongr
        · exact hderiv r hr
        · exact hsqrt v
        · exact hsqrt w
      _ = (Real.sqrt Λ * Real.sqrt Λ) * B * Real.sqrt (R.inner x v v) *
          Real.sqrt (R.inner x w w) := by ring
      _ = A := by rw [Real.mul_self_sqrt hΛ]
  have hinterior : LipschitzOnWith ⟨A, hA⟩ f (Ioo a b) := by
    apply (convex_Ioo a b).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun r hr => (hdiff r hr).hasDerivWithinAt)
    intro r hr
    change ‖f' r‖ ≤ A
    rw [Real.norm_eq_abs]
    exact hbound r hr
  have hclosure : ContinuousOn f (closure (Ioo a b)) := by rwa [closure_Ioo hab.ne]
  have hfull := LipschitzOnWith.closure hclosure hinterior
  rw [closure_Ioo hab.ne] at hfull
  exact hfull.dist_le_mul s hs t ht


theorem IsSolutionOn.ricciTensor_lipschitz_of_curvature_derivative_bound [I.Boundaryless]
    {D : RealTimeInterval} {S : SolutionOn (I := I) (M := M) D} (hS : IsSolutionOn S)
    (R : SmoothRiemannianMetric I M) (x : M) {a b Λ C : ℝ}
    (hΛ : 0 ≤ Λ) (hC : 0 ≤ C)
    (hcarrier : Icc a b ⊆ D.carrier) (hregular : Ioo a b ⊆ D.regular)
    (hmetric : ∀ r ∈ Ioo a b, ∀ v : TangentSpace I x,
      (S.base.metric r).inner x v v ≤ Λ * R.inner x v v)
    (hcurv : ∀ r ∈ Ioo a b, ∀ k ≤ 2,
      Real.sqrt (nablaKRm04NormSqIntrinsic S k r x) ≤ C)
    {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (v w : TangentSpace I x) :
    |ricciTensor (S.base.metric s) x v w - ricciTensor (S.base.metric t) x v w| ≤
      Λ * ricciOrdinaryTimeBound (Module.finrank ℝ E) C *
        Real.sqrt (R.inner x v v) * Real.sqrt (R.inner x w w) * |s - t| := by
  by_cases hdim : Module.finrank ℝ E = 0
  · let _ : Subsingleton E := Module.finrank_zero_iff.mp hdim
    have hv : v = 0 := by
      change (show E from v) = 0
      exact Subsingleton.elim _ _
    simp only [hv, map_zero, zero_apply, sub_self, abs_zero, Real.sqrt_zero, mul_zero, zero_mul, le_refl]
  let _ : NeZero (Module.finrank ℝ E) := ⟨hdim⟩
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact ricciTensor_lipschitz_of_time_derivative_bound S hS R x hΛ
    (ricciOrdinaryTimeBound_nonneg _ _ hC) hcarrier hregular hmetric
    (fun r hr => metricRicciAt_differentiableWithinAt S hS ⟨r, hregular hr⟩ x)
    (fun r hr => ricci_ordinary_time_derivative_bound S hS ⟨r, hregular hr⟩ x C hC (hcurv r hr))
    hs ht v w

theorem IsSolutionOn.ricciTensor_lower_bound_of_curvature_derivative_bound [I.Boundaryless]
    {D : RealTimeInterval} {S : SolutionOn (I := I) (M := M) D} (hS : IsSolutionOn S)
    (x : M) {a b Λ C κ c : ℝ} (hΛ : 0 ≤ Λ) (hC : 0 ≤ C) (hc : 0 ≤ c)
    (hcarrier : Icc a b ⊆ D.carrier) (hregular : Ioo a b ⊆ D.regular)
    (hmetric : ∀ r ∈ Icc a b, ∀ v : TangentSpace I x,
      (S.base.metric r).inner x v v ≤ Λ * (S.base.metric a).inner x v v)
    (hcurv : ∀ r ∈ Ioo a b, ∀ k ≤ 2,
      Real.sqrt (nablaKRm04NormSqIntrinsic S k r x) ≤ C)
    (hinitial : ∀ v : TangentSpace I x,
      κ * (S.base.metric a).inner x v v ≤ ricciTensor (S.base.metric a) x v v)
    (hbudget : c * Λ + Λ * ricciOrdinaryTimeBound (Module.finrank ℝ E) C * (b - a) ≤ κ)
    {t : ℝ} (ht : t ∈ Icc a b) (v : TangentSpace I x) :
    c * (S.base.metric t).inner x v v ≤ ricciTensor (S.base.metric t) x v v := by
  have hnonneg := metric_inner_self_nonneg (S.base.metric a) x v
  have hB := ricciOrdinaryTimeBound_nonneg (Module.finrank ℝ E) C hC
  have hdiff := hS.ricciTensor_lipschitz_of_curvature_derivative_bound
    (S.base.metric a) x hΛ hC hcarrier hregular
    (fun r hr => hmetric r (Ioo_subset_Icc_self hr)) hcurv ht
    (show a ∈ Icc a b from ⟨le_rfl, ht.1.trans ht.2⟩) v v
  rw [mul_assoc (Λ * ricciOrdinaryTimeBound (Module.finrank ℝ E) C)
    (Real.sqrt ((S.base.metric a).inner x v v)) (Real.sqrt ((S.base.metric a).inner x v v)),
    Real.mul_self_sqrt hnonneg, abs_of_nonneg (sub_nonneg.mpr ht.1)] at hdiff
  have hb := mul_le_mul_of_nonneg_right hbudget hnonneg
  have hct := mul_le_mul_of_nonneg_left (hmetric t ht v) hc
  have hinterval := mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2 a)
    (mul_nonneg (mul_nonneg hΛ hB) hnonneg)
  nlinarith [(abs_le.mp hdiff).1, hinitial v]


end DifferentialGeometry.PDE.RicciFlow
