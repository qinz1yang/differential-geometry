import DifferentialGeometry.Analysis.Calculus.Derivative.Normalize
import DifferentialGeometry.Geometry.Connection.ParallelTransport.Derivative.CovariantDerivativeAlong
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith

open Bundle Manifold Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Riemannian.Variation

open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

omit [FiniteDimensional ℝ E] [I.Boundaryless] in
private theorem contDiffAt_chart_coordinates
    {γ : ℝ → M} {V : ∀ s, TangentSpace I (γ s)} (A : E →L[ℝ] F) (β : M) {x : ℝ}
    (hV : ContMDiffAt 𝓘(ℝ, ℝ) I.tangent 1
      (fun s => (TotalSpace.mk' E (γ s) (V s) : TangentBundle I M)) x)
    (hβ : γ x ∈ (chartAt H β).source) :
    ContDiffAt ℝ 1 (fun s => A (chartRepAtBase β γ V s)) x := by
  exact A.contDiff.contDiffAt.comp x (contDiffAt_chartRepAtBase β hV hβ)

theorem norm_deriv_normalize_chartRepAtBase_le
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {V : ∀ s, TangentSpace I (γ s)}
    (A : E →L[ℝ] F) (β : M) {x C K : ℝ} (hC : 0 < C) (hK : 0 ≤ K)
    (hV : MDifferentiableAt 𝓘(ℝ, ℝ) I.tangent
      (fun s => (TotalSpace.mk' E (γ s) (V s) : TangentBundle I M)) x)
    (hβ : γ x ∈ (chartAt H β).source) (hunit : g.inner (γ x) (V x) (V x) = 1)
    (hlower : ∀ W : TangentSpace I (γ x), Real.sqrt (g.inner (γ x) W W) ≤
      C * ‖A ((trivializationAt E (TangentSpace I) β).continuousLinearMapAt ℝ (γ x) W)‖)
    (hupper : ∀ W : TangentSpace I (γ x),
      ‖A ((trivializationAt E (TangentSpace I) β).continuousLinearMapAt ℝ (γ x) W)‖ ≤
        C * Real.sqrt (g.inner (γ x) W W))
    (hΓ : ∀ u v : E, ‖A (chartChristoffelContraction g β u v (chartCurve (I := I) β γ x))‖ ≤
      K * ‖A u‖ * ‖A v‖) :
    ‖deriv (fun s => NormedSpace.normalize (A (chartRepAtBase β γ V s))) x‖ ≤
      C ^ 2 * Real.sqrt (g.inner (γ x) (covDerivAlong g γ V x) (covDerivAlong g γ V x)) +
        K * C * Real.sqrt (g.inner (γ x) (mfderiv 𝓘(ℝ, ℝ) I γ x (1 : ℝ))
          (mfderiv 𝓘(ℝ, ℝ) I γ x (1 : ℝ))) := by
  let w := fun s => A (chartRepAtBase β γ V s)
  let u := chartCurve (I := I) β γ
  let D := covDerivAlong g γ V x
  let L := (trivializationAt E (TangentSpace I) β).continuousLinearMapAt ℝ (γ x)
  have hdiff := mdifferentiableAt_tangentField_iff.mp hV
  have hrep := chartRep_base_diff γ V x β hdiff.1 hβ hdiff.2
  have hw : DifferentiableAt ℝ w x := A.differentiableAt.comp x hrep
  have hlow : 1 ≤ C * ‖w x‖ := by
    simpa only [hunit, Real.sqrt_one, w, chartRepAtBase_apply] using hlower (V x)
  have hwpos : 0 < ‖w x‖ := by
    by_contra h
    have hz : ‖w x‖ = 0 := le_antisymm (le_of_not_gt h) (norm_nonneg _)
    rw [hz, mul_zero] at hlow
    linarith only [hlow]
  have hwne : w x ≠ 0 := norm_pos_iff.mp hwpos
  have hcoord : L D = deriv (chartRepAtBase β γ V) x +
      chartChristoffelContraction g β (deriv u x) (chartRepAtBase β γ V x) (u x) := by
    rw [show L D = L (covDerivAlong g γ V x) from rfl,
      ← covDeriv_chartAt g γ V x β hdiff.1 hβ hdiff.2]
    have hmem : γ x ∈ (trivializationAt E (TangentSpace I) β).baseSet := by
      rwa [TangentBundle.trivializationAt_baseSet]
    rw [(trivializationAt E (TangentSpace I) β).continuousLinearMapAt_symmL (R := ℝ) hmem]
    rfl
  have hderiv : deriv w x = A (L D) -
      A (chartChristoffelContraction g β (deriv u x) (chartRepAtBase β γ V x) (u x)) := by
    have hd : deriv w x = A (deriv (chartRepAtBase β γ V) x) :=
      (A.hasFDerivAt.comp_hasDerivAt x hrep.hasDerivAt).deriv
    rw [hd, hcoord, map_add, add_sub_cancel_right]
  have hvel : A (deriv u x) = A (L (mfderiv 𝓘(ℝ, ℝ) I γ x (1 : ℝ))) := by
    congr 1
    exact (MFDerivAlongCurve.chartCoord_mfderiv_along_curve_eq_fderiv_of_mdifferentiableAt
      hdiff.1 β hβ).symm
  have hn : ‖deriv w x‖ ≤ C * Real.sqrt (g.inner (γ x) D D) +
      K * C * Real.sqrt (g.inner (γ x) (mfderiv 𝓘(ℝ, ℝ) I γ x (1 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) I γ x (1 : ℝ))) * ‖w x‖ := by
    rw [hderiv]
    refine (norm_sub_le _ _).trans (add_le_add (hupper D) ?_)
    refine (hΓ (deriv u x) (chartRepAtBase β γ V x)).trans ?_
    rw [hvel]
    have h := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hupper (mfderiv 𝓘(ℝ, ℝ) I γ x (1 : ℝ))) hK) (norm_nonneg (w x))
    simpa only [mul_assoc] using h
  refine (DifferentialGeometry.Analysis.norm_deriv_normalize_le hw hwne).trans ?_
  apply (div_le_iff₀ hwpos).mpr
  have h := mul_le_mul_of_nonneg_left hlow
    (mul_nonneg hC.le (Real.sqrt_nonneg (g.inner (γ x) D D)))
  nlinarith only [hn, h]

omit [FiniteDimensional ℝ E] [I.Boundaryless] in
private theorem continuousAt_metric_norm
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {W : ∀ s, TangentSpace I (γ s)} {x : ℝ}
    (hW : ContinuousAt (fun s => (TotalSpace.mk' E (γ s) (W s) : TangentBundle I M)) x) :
    ContinuousAt (fun s => Real.sqrt (g.inner (γ s) (W s) (W s))) x := by
  have hγ : ContinuousAt γ x := (FiberBundle.continuous_proj E (TangentSpace I)).continuousAt.comp hW
  have hpair : ContinuousAt (fun s => (TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ)
      (γ s) (g.inner (γ s) (W s) (W s)))) x :=
    (g.contMDiff.continuous.continuousAt.comp hγ).clm_bundle_apply₂ (F₁ := E) (F₂ := E) hW hW
  exact ((FiberBundle.continuousAt_totalSpace ℝ _).mp hpair).2.sqrt

theorem integral_norm_deriv_normalize_chartRepAtBase_le
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M} {V : ∀ s, TangentSpace I (γ s)}
    (A : E →L[ℝ] F) (β : M) {a b C K : ℝ} (hab : a ≤ b) (hC : 0 < C) (hK : 0 ≤ K)
    (hV : ∀ x ∈ Icc a b, ContMDiffAt 𝓘(ℝ, ℝ) I.tangent 1
      (fun s => (TotalSpace.mk' E (γ s) (V s) : TangentBundle I M)) x)
    (hβ : ∀ x ∈ Icc a b, γ x ∈ (chartAt H β).source)
    (hunit : ∀ x ∈ Icc a b, g.inner (γ x) (V x) (V x) = 1)
    (hlower : ∀ x ∈ Icc a b, ∀ W : TangentSpace I (γ x), Real.sqrt (g.inner (γ x) W W) ≤
      C * ‖A ((trivializationAt E (TangentSpace I) β).continuousLinearMapAt ℝ (γ x) W)‖)
    (hupper : ∀ x ∈ Icc a b, ∀ W : TangentSpace I (γ x),
      ‖A ((trivializationAt E (TangentSpace I) β).continuousLinearMapAt ℝ (γ x) W)‖ ≤
        C * Real.sqrt (g.inner (γ x) W W))
    (hΓ : ∀ x ∈ Icc a b, ∀ u v : E,
      ‖A (chartChristoffelContraction g β u v (chartCurve (I := I) β γ x))‖ ≤
        K * ‖A u‖ * ‖A v‖) :
    (∫ x in a..b, ‖deriv (fun s => NormedSpace.normalize (A (chartRepAtBase β γ V s))) x‖) ≤
      C ^ 2 * (∫ x in a..b, Real.sqrt
        (g.inner (γ x) (covDerivAlong g γ V x) (covDerivAlong g γ V x))) +
      K * C * (∫ x in a..b, Real.sqrt (g.inner (γ x)
        (mfderiv 𝓘(ℝ, ℝ) I γ x (1 : ℝ)) (mfderiv 𝓘(ℝ, ℝ) I γ x (1 : ℝ)))) := by
  have hcov : IntervalIntegrable (fun x => Real.sqrt
      (g.inner (γ x) (covDerivAlong g γ V x) (covDerivAlong g γ V x))) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    intro x hx
    exact (continuousAt_metric_norm g
      (contMDiffAt_covDerivAlong g (m := 0) (n := 1) (by norm_num) (hV x hx)).continuousAt).continuousWithinAt
  have hvel : IntervalIntegrable (fun x => Real.sqrt (g.inner (γ x)
      (mfderiv 𝓘(ℝ, ℝ) I γ x (1 : ℝ)) (mfderiv 𝓘(ℝ, ℝ) I γ x (1 : ℝ)))) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    intro x hx
    have hγ := (contMDiffAt_tangentField_iff.mp (hV x hx)).1
    exact (continuousAt_metric_norm g (hγ.velocityLift (m := 0) (by norm_num)).continuousAt).continuousWithinAt
  let w := fun s => A (chartRepAtBase β γ V s)
  have hw (x : ℝ) (hx : x ∈ Icc a b) : ContDiffAt ℝ 1 w x :=
    contDiffAt_chart_coordinates A β (hV x hx) (hβ x hx)
  have hwne (x : ℝ) (hx : x ∈ Icc a b) : w x ≠ 0 := by
    have hlow : 1 ≤ C * ‖w x‖ := by
      simpa only [hunit x hx, Real.sqrt_one, w, chartRepAtBase_apply] using hlower x hx (V x)
    intro hzero
    rw [hzero, norm_zero, mul_zero] at hlow
    linarith only [hlow]
  have hT (x : ℝ) (hx : x ∈ Icc a b) :
      ContDiffAt ℝ 1 (fun s => NormedSpace.normalize (w s)) x := by
    exact ((hw x hx).norm ℝ (hwne x hx)).inv (norm_ne_zero_iff.mpr (hwne x hx)) |>.smul (hw x hx)
  have hi : IntervalIntegrable
      (fun x => ‖deriv (fun s => NormedSpace.normalize (w s)) x‖) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    intro x hx
    exact (((hT x hx).derivWithin (m := 0) (by norm_num)).continuousAt.norm).continuousWithinAt
  have h := intervalIntegral.integral_mono_on hab hi
    ((hcov.const_mul (C ^ 2)).add (hvel.const_mul (K * C)))
    (fun x hx => norm_deriv_normalize_chartRepAtBase_le g A β hC hK
      ((hV x hx).mdifferentiableAt one_ne_zero) (hβ x hx) (hunit x hx)
      (hlower x hx) (hupper x hx) (hΓ x hx))
  simpa only [intervalIntegral.integral_add (hcov.const_mul (C ^ 2)) (hvel.const_mul (K * C)),
    intervalIntegral.integral_const_mul] using h

end DifferentialGeometry.Geometry.Riemannian.Variation
