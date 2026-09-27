import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.CompleteInitialGeometryControl
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.CarrierActionContinuity
import DifferentialGeometry.Geometry.Exponential.MinimizingGeodesic
import DifferentialGeometry.Geometry.Metric.Comparison.DistanceScaling
import DifferentialGeometry.Bundle.TangentSpace
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Defs

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set MeasureTheory
open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped ContDiff Manifold Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow

variable {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

private theorem initialArc_velocity_affine
    (gamma : ℝ → M) (c a s : ℝ)
    (hgamma : MDifferentiableAt (modelWithCornersSelf ℝ ℝ) I gamma (c * (s - a))) :
    lVelocity (I := I) (fun r : ℝ ↦ gamma (c * (r - a))) s =
      c • lVelocity (I := I) gamma (c * (s - a)) := by
  let A : TangentSpace (modelWithCornersSelf ℝ ℝ) s →L[ℝ]
      TangentSpace (modelWithCornersSelf ℝ ℝ) (c * (s - a)) :=
    modelLinearMapToTangent
      (x := s) (y := c * (s - a)) (A := c • ContinuousLinearMap.id ℝ ℝ)
  have hclock : HasMFDerivAt (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ ℝ) (fun r : ℝ ↦ c * (r - a)) s A := by
    exact HasFDerivAt.hasMFDerivAt_model
      (((hasFDerivAt_id s).sub_const a).const_mul c)
  have hcomp := hgamma.hasMFDerivAt.comp s hclock
  have hmodel := congrArg tangentLinearMapToModel hcomp.mfderiv
  rw [tangentLinearMapToModel_comp] at hmodel
  have hA : tangentLinearMapToModel A = c • ContinuousLinearMap.id ℝ ℝ :=
    tangentLinearMapToModel_modelLinearMapToTangent
  rw [hA] at hmodel
  have happ := congrArg (fun L : ℝ →L[ℝ] E ↦ L 1) hmodel
  have hfun : (gamma ∘ fun r : ℝ ↦ c * (r - a)) =
      (fun r : ℝ ↦ gamma (c * (r - a))) := rfl
  rw [hfun] at happ
  apply (tangentSpaceModelContinuousLinearEquiv
    (I := I) (gamma (c * (s - a)))).injective
  simpa only [lVelocity, tangentLinearMapToModel_apply,
    tangentSpaceModelContinuousLinearEquiv_apply,
    tangentSpaceModelContinuousLinearEquiv_symm_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    Function.comp_apply, smul_apply, id_eq, map_smul] using happ

variable [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless] [IsManifold I ∞ M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem initialArc_exists_geodesic
    (g : SmoothRiemannianMetric I M)
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (q y : M) (hfin : riemannianEDistOf (I := I) g q y ≠ (⊤ : ENNReal))
    (a b : ℝ) (hab : a < b) :
    ∃ beta : ℝ → M,
      ContMDiff (modelWithCornersSelf ℝ ℝ) I 1 beta ∧
      beta a = q ∧ beta b = y ∧
      ∀ s : ℝ,
        g.inner (beta s) (lVelocity (I := I) beta s) (lVelocity (I := I) beta s) =
          (riemannianEDistOf (I := I) g q y).toReal ^ 2 / (b - a) ^ 2 := by
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let : T3Space M := inferInstance
  let : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let : PseudoEMetricSpace M :=
    (EMetricSpace.ofRiemannianMetric I M).toPseudoEMetricSpace
  let : CompleteSpace M := hcomplete.complete
  have hEnorm : IsMetricNorm (I := I) (M := M) g := by
    intro x v
    exact tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) g x v
  have hfin' : riemannianEDist I q y ≠ (⊤ : ENNReal) := by
    rwa [riemannianEDistOf_eq_riemannianEDist (I := I) g hEnorm] at hfin
  obtain ⟨v, hvend, hvnorm⟩ := minExp_of_ne_top (I := I) g hEnorm q y hfin'
  let gamma := intrinsicGeodesic (I := I) g hEnorm q v
  let beta : ℝ → M := fun s ↦ gamma ((b - a)⁻¹ * (s - a))
  have hgamma : ContMDiff (modelWithCornersSelf ℝ ℝ) I 1 gamma :=
    contMDiffOn_univ.mp (intrinsicGeodesic_contMDiffOn (I := I) g hEnorm q v)
  have hclock : ContMDiff (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ ℝ) 1 (fun s : ℝ ↦ (b - a)⁻¹ * (s - a)) := by
    exact (contDiff_const.mul (contDiff_id.sub contDiff_const)).contMDiff
  have hbeta : ContMDiff (modelWithCornersSelf ℝ ℝ) I 1 beta :=
    hgamma.comp hclock
  have hstart : beta a = q := by
    simp only [beta, sub_self, mul_zero, gamma, intrinsicGeodesic_zero]
  have hend : beta b = y := by
    simp only [beta, inv_mul_cancel₀ (sub_pos.mpr hab).ne']
    exact hvend
  have hnorm : Real.sqrt (g.inner q v v) =
      (riemannianEDistOf (I := I) g q y).toReal := by
    rw [riemannianEDistOf_eq_riemannianEDist (I := I) g hEnorm]
    exact hvnorm
  have hsq : g.inner q v v =
      (riemannianEDistOf (I := I) g q y).toReal ^ 2 := by
    rw [← hnorm, Real.sq_sqrt (gInner_self_nonneg (I := I) g q v)]
  refine ⟨beta, hbeta, hstart, hend, ?_⟩
  intro s
  have hvel := initialArc_velocity_affine gamma (b - a)⁻¹ a s
    (hgamma.mdifferentiableAt (by simp))
  have hspeed := intrinsicGeodesic_speedSq_eq (I := I) g hEnorm q v
    ((b - a)⁻¹ * (s - a))
  change g.inner (gamma ((b - a)⁻¹ * (s - a)))
    (lVelocity (I := I) gamma ((b - a)⁻¹ * (s - a)))
    (lVelocity (I := I) gamma ((b - a)⁻¹ * (s - a))) = g.inner q v v at hspeed
  change g.inner (gamma ((b - a)⁻¹ * (s - a)))
    (lVelocity (I := I) (fun r ↦ gamma ((b - a)⁻¹ * (r - a))) s)
    (lVelocity (I := I) (fun r ↦ gamma ((b - a)⁻¹ * (r - a))) s) = _
  rw [hvel, gInner_smul_self, hspeed, hsq]
  simp only [div_eq_mul_inv, inv_pow]
  ring

variable {D : RealTimeInterval}

theorem exists_initial_geodesic_arc_action_le
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T : ℝ) (hT : 0 ≤ T) (K : ℝ)
    (hcomplete : RiemannianMetricComplete (I := I) (S.base.metric 0))
    (hslab : Icc (0 : ℝ) T ⊆ D.carrier)
    (hregular : Ioo (0 : ℝ) T ⊆ D.regular)
    (hbounded : ∃ B : ℝ, ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
      normSq0S (I := I) (S.base.metric t) x 4 (S.base.rm04 t x) ≤ B)
    (hinit : ∀ x : M,
      normSq0S (I := I) (S.base.metric 0) x 4 (S.base.rm04 0 x) ≤ K ^ 2)
    (q y : M) (r : ℝ) (hr : 0 < r)
    (hy : riemannianEDistOf (I := I) (S.base.metric 0) q y < ENNReal.ofReal r)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) (hbT : b ^ 2 ≤ T)
    (hearly : T - a ^ 2 ≤ compactCurvatureControlTime (Module.finrank ℝ E) K) :
    ∃ beta : ℝ → M,
      ContMDiff (modelWithCornersSelf ℝ ℝ) I 1 beta ∧
      beta a = q ∧ beta b = y ∧
      lRegularizedAction S T beta a b ≤
        Real.exp (2 * ((Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt (2 * K ^ 2 + 1)) *
          compactCurvatureControlTime (Module.finrank ℝ E) K) * r ^ 2 / (2 * (b - a)) +
        (2 / 3 : ℝ) * ((Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt (2 * K ^ 2 + 1)) *
          (b ^ 3 - a ^ 3) := by
  let δ := compactCurvatureControlTime (Module.finrank ℝ E) K
  let Q := (Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt (2 * K ^ 2 + 1)
  let Λ := Real.exp (2 * Q * δ)
  have hΛ : 0 < Λ := Real.exp_pos _
  have hdelta : 0 < b - a := sub_pos.mpr hab
  have hfin : riemannianEDistOf (I := I) (S.base.metric 0) q y ≠ (⊤ : ENNReal) :=
    (hy.trans (ENNReal.ofReal_lt_top)).ne
  have hd : (riemannianEDistOf (I := I) (S.base.metric 0) q y).toReal ≤ r :=
    ENNReal.toReal_le_of_le_ofReal hr.le hy.le
  obtain ⟨beta, hbeta, hstart, hend, hspeed⟩ :=
    initialArc_exists_geodesic (S.base.metric 0) hcomplete q y hfin a b hab
  have hgeometry := metric_scalar_bounds_from_initial_complete S hS T hT K
    hcomplete hslab hregular hbounded hinit
  have hback : ∀ s ∈ Icc a b,
      T - s ^ 2 ∈ Icc (0 : ℝ) (min T δ) := by
    intro s hs
    have hs0 : 0 ≤ s := ha.trans hs.1
    have hasq : a ^ 2 ≤ s ^ 2 := (sq_le_sq₀ ha hs0).mpr hs.1
    have hbsq : s ^ 2 ≤ b ^ 2 := (sq_le_sq₀ hs0 (ha.trans hab.le)).mpr hs.2
    refine ⟨sub_nonneg.mpr (hbsq.trans hbT), le_min (sub_le_self _ (sq_nonneg s)) ?_⟩
    exact (sub_le_sub_left hasq T).trans hearly
  have hLag : IntervalIntegrable (lRegularizedLagrangian S T beta) volume a b :=
    lRegLag_integrable_on_carrier S hS.smoothMetric ⟨hS.scalarCont⟩ T a b beta hbeta
      (fun s hs ↦ hslab ⟨(hback s (by simpa only [uIcc_of_le hab.le] using hs)).1,
        (hback s (by simpa only [uIcc_of_le hab.le] using hs)).2.trans (min_le_left _ _)⟩)
  let C : ℝ := Λ * r ^ 2 / (2 * (b - a) ^ 2)
  have hpotInt : IntervalIntegrable (fun s : ℝ ↦ 2 * s ^ 2 * Q) volume a b :=
    ((continuous_const.mul (continuous_id.pow 2)).mul continuous_const).intervalIntegrable a b
  have hpolyInt : IntervalIntegrable (fun s : ℝ ↦ C + 2 * s ^ 2 * Q) volume a b :=
    intervalIntegrable_const.add hpotInt
  have hpoint : ∀ s ∈ Icc a b, lRegularizedLagrangian S T beta s ≤ C + 2 * s ^ 2 * Q := by
    intro s hs
    have hgeom := hgeometry (T - s ^ 2) (hback s hs)
    have hspeedle : (S.base.metric 0).inner (beta s)
        (lVelocity (I := I) beta s) (lVelocity (I := I) beta s) ≤ r ^ 2 / (b - a) ^ 2 := by
      rw [hspeed s]
      exact div_le_div_of_nonneg_right
        ((sq_le_sq₀ ENNReal.toReal_nonneg hr.le).mpr hd) (sq_nonneg _)
    have hmetric := ((hgeom.1.2 (beta s) (mem_univ _) (lVelocity (I := I) beta s)).2).trans
      (mul_le_mul_of_nonneg_left hspeedle hΛ.le)
    have hscalar : S.scalar (T - s ^ 2) (beta s) ≤ Q :=
      (le_abs_self _).trans (hgeom.2 (beta s))
    have hpot := mul_le_mul_of_nonneg_left hscalar
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (sq_nonneg s))
    calc
      lRegularizedLagrangian S T beta s ≤ (1 / 2 : ℝ) * (Λ * (r ^ 2 / (b - a) ^ 2)) +
          2 * s ^ 2 * Q :=
        add_le_add (mul_le_mul_of_nonneg_left hmetric (by norm_num)) hpot
      _ = C + 2 * s ^ 2 * Q := by
        dsimp only [C]
        field_simp [hdelta.ne']
  have hmono := intervalIntegral.integral_mono_on hab.le hLag hpolyInt hpoint
  have hpoly : (∫ s in a..b, C + 2 * s ^ 2 * Q) =
      Λ * r ^ 2 / (2 * (b - a)) + (2 / 3 : ℝ) * Q * (b ^ 3 - a ^ 3) := by
    rw [intervalIntegral.integral_add intervalIntegrable_const hpotInt,
      intervalIntegral.integral_const, intervalIntegral.integral_mul_const,
      intervalIntegral.integral_const_mul, integral_pow]
    simp only [smul_eq_mul]
    dsimp only [C]
    field_simp [hdelta.ne']
    ring
  rw [hpoly] at hmono
  exact ⟨beta, hbeta, hstart, hend, hmono⟩

end DifferentialGeometry.PDE.RicciFlow

end
