import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.CarrierActionContinuity
import DifferentialGeometry.Bundle.TangentSpace
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Defs

set_option autoImplicit false

noncomputable section

open Bundle Filter Function MeasureTheory Set
open DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped ContDiff Manifold Topology Interval

namespace DifferentialGeometry.PDE.RicciFlow

variable {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [IsManifold I ∞ M] in
private theorem lVelocity_comp_mul_of_mdifferentiableAt
    (alpha : ℝ → M) (c s : ℝ)
    (halpha : MDifferentiableAt (modelWithCornersSelf ℝ ℝ) I alpha (c * s)) :
    lVelocity (I := I) (fun r : ℝ ↦ alpha (c * r)) s =
      c • lVelocity (I := I) alpha (c * s) := by
  let A : TangentSpace (modelWithCornersSelf ℝ ℝ) s →L[ℝ]
      TangentSpace (modelWithCornersSelf ℝ ℝ) (c * s) :=
    modelLinearMapToTangent
      (x := s) (y := c * s) (A := c • ContinuousLinearMap.id ℝ ℝ)
  have hscaleM : HasMFDerivAt (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ ℝ) (fun r : ℝ ↦ c * r) s A := by
    exact HasFDerivAt.hasMFDerivAt_model
      ((hasFDerivAt_id s).const_mul c)
  have hcomp := halpha.hasMFDerivAt.comp s hscaleM
  have hmodel := congrArg tangentLinearMapToModel hcomp.mfderiv
  rw [tangentLinearMapToModel_comp] at hmodel
  have hA : tangentLinearMapToModel A =
      c • ContinuousLinearMap.id ℝ ℝ :=
    tangentLinearMapToModel_modelLinearMapToTangent
  rw [hA] at hmodel
  have happ := congrArg (fun L : ℝ →L[ℝ] E ↦ L 1) hmodel
  have hfun : (alpha ∘ fun r : ℝ ↦ c * r) =
      (fun r : ℝ ↦ alpha (c * r)) := rfl
  rw [hfun] at happ
  apply (tangentSpaceModelContinuousLinearEquiv
    (I := I) (alpha (c * s))).injective
  simpa only [lVelocity, tangentLinearMapToModel_apply,
    tangentSpaceModelContinuousLinearEquiv_apply,
    tangentSpaceModelContinuousLinearEquiv_symm_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    Function.comp_apply, smul_apply, id_eq, map_smul] using happ

variable [FiniteDimensional ℝ E] {D : RealTimeInterval}

private def dilatedActionIntegrand
    (S : SolutionOn (I := I) (M := M) D) (T B : ℝ)
    (alpha : ℝ → M) (b u : ℝ) : ℝ :=
  b * ((1 / 2 : ℝ) * (B / b) ^ 2 *
      (S.base.metric (T - (b * u) ^ 2)).inner (alpha (B * u))
        (lVelocity (I := I) alpha (B * u))
        (lVelocity (I := I) alpha (B * u)) +
    2 * (b * u) ^ 2 * S.scalar (T - (b * u) ^ 2) (alpha (B * u)))

private theorem lRegAction_dilate_eq_unit
    (S : SolutionOn (I := I) (M := M) D) (T B b : ℝ) (hb : b ≠ 0)
    (alpha : ℝ → M)
    (halpha : ContMDiff (modelWithCornersSelf ℝ ℝ) I 1 alpha) :
    lRegularizedAction S T (fun s : ℝ ↦ alpha (B * s / b)) 0 b =
      ∫ u in (0 : ℝ)..1, dilatedActionIntegrand S T B alpha b u := by
  have hcurve : (fun s : ℝ ↦ alpha (B * s / b)) =
      (fun s : ℝ ↦ alpha ((B / b) * s)) := by
    funext s
    congr 1
    ring
  rw [hcurve]
  calc
    lRegularizedAction S T (fun s : ℝ ↦ alpha ((B / b) * s)) 0 b =
        ∫ u in (0 : ℝ)..1,
          b * lRegularizedLagrangian S T (fun s : ℝ ↦ alpha ((B / b) * s)) (b * u) := by
      symm
      simpa only [lRegularizedAction, smul_eq_mul, mul_zero, mul_one,
        intervalIntegral.integral_const_mul] using
        (intervalIntegral.smul_integral_comp_mul_left
          (a := (0 : ℝ)) (b := (1 : ℝ))
          (fun s : ℝ ↦ lRegularizedLagrangian S T (fun r : ℝ ↦ alpha ((B / b) * r)) s) b)
    _ = ∫ u in (0 : ℝ)..1,
        dilatedActionIntegrand S T B alpha b u := by
      apply intervalIntegral.integral_congr
      intro u _hu
      have hscale : (B / b) * (b * u) = B * u := by
        field_simp [hb]
      have hvel := lVelocity_comp_mul_of_mdifferentiableAt
        (I := I) alpha (B / b) (b * u)
        (halpha.contMDiffAt.mdifferentiableAt (by simp))
      let g := S.base.metric (T - (b * u) ^ 2)
      have hquad : g.inner (alpha ((B / b) * (b * u)))
          (lVelocity (I := I) (fun s : ℝ ↦ alpha ((B / b) * s)) (b * u))
          (lVelocity (I := I) (fun s : ℝ ↦ alpha ((B / b) * s)) (b * u)) =
          (B / b) ^ 2 * g.inner (alpha ((B / b) * (b * u)))
            (lVelocity (I := I) alpha ((B / b) * (b * u)))
            (lVelocity (I := I) alpha ((B / b) * (b * u))) := by
        rw [hvel]
        simp only [map_smul, smul_apply, smul_eq_mul]
        ring
      have hquad' := hquad.trans (congrArg (fun v : ℝ ↦
        (B / b) ^ 2 * g.inner (alpha v)
          (lVelocity (I := I) alpha v) (lVelocity (I := I) alpha v)) hscale)
      have hpot := congrArg
        (fun v : ℝ ↦ S.scalar (T - (b * u) ^ 2) (alpha v)) hscale
      change b * ((1 / 2 : ℝ) * g.inner (alpha ((B / b) * (b * u)))
          (lVelocity (I := I) (fun s : ℝ ↦ alpha ((B / b) * s)) (b * u))
          (lVelocity (I := I) (fun s : ℝ ↦ alpha ((B / b) * s)) (b * u)) +
        2 * (b * u) ^ 2 * S.scalar (T - (b * u) ^ 2)
          (alpha ((B / b) * (b * u)))) = _
      rw [hquad', hpot]
      dsimp only [dilatedActionIntegrand, g]
      ring

theorem lRegAction_dilation_tendsto_on_carrier
    (S : SolutionOn (I := I) (M := M) D)
    (hMet : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric)
    (hSc : ScalarSTContOn (I := I) (M := M) S)
    (T B : ℝ) (hB : 0 < B)
    (hslab : Icc (T - B ^ 2) T ⊆ D.carrier)
    (alpha : ℝ → M)
    (halpha : ContMDiff (modelWithCornersSelf ℝ ℝ) I 1 alpha) :
    Tendsto
      (fun b : ℝ ↦ lRegularizedAction S T (fun s : ℝ ↦ alpha (B * s / b)) 0 b)
      (𝓝[Ioc (0 : ℝ) B] B)
      (𝓝 (lRegularizedAction S T alpha 0 B)) := by
  let J : Set ℝ := Icc (B / 2) B
  let Q : Set (ℝ × ℝ) := J ×ˢ Icc (0 : ℝ) 1
  let P := {q : ℝ × ℝ // q ∈ Q}
  have hBmem : B ∈ J := ⟨half_le_self hB.le, le_rfl⟩
  have hbpos : ∀ q : P, 0 < q.1.1 := by
    intro q
    exact (half_pos hB).trans_le q.2.1.1
  have hclock : ∀ q : P, T - (q.1.1 * q.1.2) ^ 2 ∈ Icc (T - B ^ 2) T := by
    intro q
    have hprod0 : 0 ≤ q.1.1 * q.1.2 := mul_nonneg (hbpos q).le q.2.2.1
    have hprodB : q.1.1 * q.1.2 ≤ B :=
      (mul_le_of_le_one_right (hbpos q).le q.2.2.2).trans q.2.1.2
    have hsq : (q.1.1 * q.1.2) ^ 2 ≤ B ^ 2 :=
      (sq_le_sq₀ hprod0 hB.le).mpr hprodB
    exact ⟨sub_le_sub_left hsq T, sub_le_self T (sq_nonneg _)⟩
  let timeLift : P → {t : ℝ // t ∈ D.carrier} := fun q ↦
    ⟨T - (q.1.1 * q.1.2) ^ 2, hslab (hclock q)⟩
  let velLift : P → TangentBundle I M := fun q ↦
    ⟨alpha (B * q.1.2), lVelocity (I := I) alpha (B * q.1.2)⟩
  have hbcont : Continuous (fun q : P ↦ q.1.1) :=
    continuous_fst.comp continuous_subtype_val
  have hucont : Continuous (fun q : P ↦ q.1.2) :=
    continuous_snd.comp continuous_subtype_val
  have htime : Continuous timeLift :=
    (continuous_const.sub ((hbcont.mul hucont).pow 2)).subtype_mk _
  have hparam : Continuous (fun q : P ↦ B * q.1.2) :=
    continuous_const.mul hucont
  have hvel : Continuous velLift := by
    exact
      (DifferentialGeometry.Geometry.Riemannian.MFDerivAlongCurve.continuous_tangentMap_unitLift
        (I := I) (M := M) (n := (1 : WithTop ℕ∞)) (by simp) halpha).comp hparam
  have hbase : Continuous (fun q : P ↦ alpha (B * q.1.2)) :=
    halpha.continuous.comp hparam
  have hquad := metricTimeBundleQuad_cont_of_metricFamilySmoothOn
    (I := I) (M := M) S.family.metric hMet
    (K := D.carrier) (fun _ ht ↦ ht)
  have hkin : Continuous (fun q : P ↦
      (S.base.metric (T - (q.1.1 * q.1.2) ^ 2)).inner (alpha (B * q.1.2))
        (lVelocity (I := I) alpha (B * q.1.2))
        (lVelocity (I := I) alpha (B * q.1.2))) := by
    have h := hquad.comp (htime.prodMk hvel)
    change Continuous (fun q : P ↦
      (S.base.metric (T - (q.1.1 * q.1.2) ^ 2)).inner (alpha (B * q.1.2))
        (lVelocity (I := I) alpha (B * q.1.2))
        (lVelocity (I := I) alpha (B * q.1.2))) at h
    exact h
  have hscalar := hSc.continuous_subtype.comp (htime.prodMk hbase)
  have hratio : Continuous (fun q : P ↦ B / q.1.1) :=
    continuous_const.div hbcont (fun q ↦ (hbpos q).ne')
  have hFsub : Continuous (fun q : P ↦
      dilatedActionIntegrand S T B alpha q.1.1 q.1.2) := by
    change Continuous (fun q : P ↦ q.1.1 *
      ((1 / 2 : ℝ) * (B / q.1.1) ^ 2 *
          (S.base.metric (T - (q.1.1 * q.1.2) ^ 2)).inner (alpha (B * q.1.2))
            (lVelocity (I := I) alpha (B * q.1.2))
            (lVelocity (I := I) alpha (B * q.1.2)) +
        2 * (q.1.1 * q.1.2) ^ 2 *
          S.scalar (T - (q.1.1 * q.1.2) ^ 2) (alpha (B * q.1.2))))
    exact hbcont.mul (((continuous_const.mul (hratio.pow 2)).mul hkin).add
      ((continuous_const.mul ((hbcont.mul hucont).pow 2)).mul hscalar))
  have hF : ContinuousOn
      (fun q : ℝ × ℝ ↦ dilatedActionIntegrand S T B alpha q.1 q.2) Q := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact hFsub
  have hQcpt : IsCompact Q := isCompact_Icc.prod isCompact_Icc
  obtain ⟨C, hC⟩ := hQcpt.exists_bound_of_continuousOn hF
  have hInt : ContinuousWithinAt
      (fun b : ℝ ↦ ∫ u in (0 : ℝ)..1, dilatedActionIntegrand S T B alpha b u)
      J B := by
    apply intervalIntegral.continuousWithinAt_of_dominated_interval
      (F := fun b u : ℝ ↦ dilatedActionIntegrand S T B alpha b u)
      (bound := fun _ : ℝ ↦ C)
    · filter_upwards [self_mem_nhdsWithin] with b hb
      have hslice : ContinuousOn
          (dilatedActionIntegrand S T B alpha b) (uIoc (0 : ℝ) 1) := by
        apply hF.comp (continuous_const.prodMk continuous_id).continuousOn
        intro u hu
        refine ⟨hb, ?_⟩
        simpa only [uIcc_of_le zero_le_one, id_eq] using uIoc_subset_uIcc hu
      exact hslice.aestronglyMeasurable measurableSet_uIoc
    · filter_upwards [self_mem_nhdsWithin] with b hb
      exact ae_of_all _ fun u hu ↦ hC (b, u) ⟨hb, by
        simpa only [uIcc_of_le zero_le_one, id_eq] using uIoc_subset_uIcc hu⟩
    · exact intervalIntegrable_const
    · exact ae_of_all _ fun u hu ↦ by
        have hu' : u ∈ Icc (0 : ℝ) 1 := by
          simpa only [uIcc_of_le zero_le_one, id_eq] using uIoc_subset_uIcc hu
        have hslice : ContinuousOn
            (fun b : ℝ ↦ dilatedActionIntegrand S T B alpha b u) J := by
          exact hF.comp (continuous_id.prodMk continuous_const).continuousOn
            (fun b hb ↦ ⟨hb, hu'⟩)
        exact hslice B hBmem
  have hnear : J ∈ 𝓝[Ioc (0 : ℝ) B] B := by
    have hhalf : Ioi (B / 2) ∈ 𝓝[Ioc (0 : ℝ) B] B :=
      mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (half_lt_self hB))
    filter_upwards [self_mem_nhdsWithin, hhalf] with b hb hbhalf
    exact ⟨hbhalf.le, hb.2⟩
  have hlim : Tendsto
      (fun b : ℝ ↦ ∫ u in (0 : ℝ)..1, dilatedActionIntegrand S T B alpha b u)
      (𝓝[Ioc (0 : ℝ) B] B)
      (𝓝 (∫ u in (0 : ℝ)..1, dilatedActionIntegrand S T B alpha B u)) :=
    hInt.mono_of_mem_nhdsWithin hnear
  have hterminal : (∫ u in (0 : ℝ)..1,
      dilatedActionIntegrand S T B alpha B u) = lRegularizedAction S T alpha 0 B := by
    rw [← lRegAction_dilate_eq_unit S T B B hB.ne' alpha halpha]
    have hcurve : (fun s : ℝ ↦ alpha (B * s / B)) = alpha := by
      funext s
      congr 1
      field_simp [hB.ne']
    rw [hcurve]
  rw [hterminal] at hlim
  have heq :
      (fun b : ℝ ↦ ∫ u in (0 : ℝ)..1, dilatedActionIntegrand S T B alpha b u)
        =ᶠ[𝓝[Ioc (0 : ℝ) B] B]
      (fun b : ℝ ↦ lRegularizedAction S T (fun s : ℝ ↦ alpha (B * s / b)) 0 b) := by
    filter_upwards [self_mem_nhdsWithin] with b hb
    exact (lRegAction_dilate_eq_unit S T B b hb.1.ne' alpha halpha).symm
  exact hlim.congr' heq

end DifferentialGeometry.PDE.RicciFlow

end
