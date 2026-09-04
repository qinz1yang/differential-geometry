import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Quadratic.C1Regularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Chart.ForceRegularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Chart.VelocityRegularity
import Mathlib.MeasureTheory.Measure.OpenPos

set_option autoImplicit false

noncomputable section

open Filter MeasureTheory Set
open scoped Manifold Topology ContDiff Interval

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Geometry.Curvature

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I (∞ : WithTop ℕ∞) M] [T2Space M]
variable {D : RealTimeInterval}

theorem lChartAction_minimizer_momentum_contDiffOn_one
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T a : Real) (p : M)
    {L : Real} (hL : 0 < L) (u : timeH1 E L)
    (hreg : ∀ r ∈ Icc (0 : Real) L, T - (a + r) ^ 2 ∈ D.regular)
    (hchart : MapsTo u.toFun (Icc (0 : Real) L)
      (interior (extChartAt I p).target))
    (hmin : IsLocalMinOn (lChartAction S T a p) (sameTimeEnds u) u) :
    ∃ q P : Real → E,
      ContinuousOn q (Icc (0 : Real) L) ∧
      u.deriv =ᵐ[timeMeasure L] q ∧
      ContDiffOn Real 1 u.toFun (Icc (0 : Real) L) ∧
      EqOn (derivWithin u.toFun (Icc (0 : Real) L)) q
        (Icc (0 : Real) L) ∧
      ContDiffOn Real 1 P (Icc (0 : Real) L) ∧
      EqOn P
        (fun r ↦ (2 : Real) •
          chartGramOp (I := I) S.family p
            (T - (a + r) ^ 2, u.toFun r) (q r))
        (Icc (0 : Real) L) ∧
      EqOn (derivWithin P (Icc (0 : Real) L))
        (fun r ↦ (2 : Real) •
          lChartForceRepresentative (I := I) S T a p u q r)
        (Icc (0 : Real) L) := by
  let τ : Real → Real := fun r ↦ T - (a + r) ^ 2
  let K : Set E := u.toFun '' Icc (0 : Real) L
  have hτc : ContinuousOn τ (Icc (0 : Real) L) := by
    exact (continuous_const.sub
      ((continuous_const.add continuous_id).pow 2)).continuousOn
  have hτreg : MapsTo τ (Icc (0 : Real) L) D.regular := hreg
  have hKc : IsCompact K :=
    isCompact_Icc.image_of_continuousOn u.continuousOn_toFun
  have hKchart : K ⊆ interior (extChartAt I p).target := by
    rintro x ⟨r, hr, rfl⟩
    exact hchart hr
  have huK : MapsTo u.toFun (Icc (0 : Real) L) K := by
    intro r hr
    exact ⟨r, hr, rfl⟩
  obtain ⟨C, hA, hC⟩ := exists_chartGramOp_ae_bound hS.smoothMetric p τ hτc hτreg
    hKc hKchart u huK
  obtain ⟨q, hq, hqae, huc1, huderiv⟩ :=
    lChartAction_minimizer_contDiffOn_one (I := I) S hS T a p hL u hreg hchart hmin
  obtain ⟨hForce, hWeak⟩ :=
    lChartAction_weak_euler_lagrange_of_isLocalMinOn (I := I) S hS T a p hL u hreg hchart hmin
  have hForceRep : ContinuousOn
      (lChartForceRepresentative (I := I) S T a p u q) (Icc (0 : Real) L) :=
    continuousOn_lChartForceRepresentative (I := I) S hS T a p u q hreg hchart hq
  have hForceAE : lChartForce (I := I) S T a p u =ᵐ[timeMeasure L]
      lChartForceRepresentative (I := I) S T a p u q :=
    lChartForce_ae_eq_lChartForceRepresentative (I := I) S hS T a p u q hreg hchart hqae
  let F : Real → E := fun r ↦
    (2 : Real) • lChartForceRepresentative (I := I) S T a p u q r
  have hF : ContinuousOn F (Icc (0 : Real) L) := by
    exact (hForceRep.const_smul (2 : Real)).congr fun _ _ ↦ rfl
  have hEuler : ∀ v : timeH1 E L, v.init = 0 → v.toFun L = 0 →
      2 * inner Real
          (timeOp (fun r ↦ chartGramOp (I := I) S.family p
            (τ r, u.toFun r)) hA C hC u.deriv) v.deriv +
        ∫ r in Icc (0 : Real) L, inner Real (F r) (v.toFun r) = 0 := by
    intro v hv0 hvL
    have hvmeas : AEStronglyMeasurable v.toFun
        (volume.restrict (Icc (0 : Real) L)) :=
      v.continuousOn_toFun.aestronglyMeasurable measurableSet_Icc
    obtain ⟨V, hV⟩ := IsCompact.exists_bound_of_continuousOn
      isCompact_Icc v.continuousOn_toFun
    have hForcePair : IntegrableOn
        (fun r ↦ inner Real (lChartForce (I := I) S T a p u r) (v.toFun r))
        (Icc (0 : Real) L) volume := by
      refine Integrable.mono' (hForce.norm.const_mul V)
        (hForce.aestronglyMeasurable.inner hvmeas) ?_
      filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
      calc
        ‖inner Real (lChartForce (I := I) S T a p u r) (v.toFun r)‖
            ≤ ‖lChartForce (I := I) S T a p u r‖ * ‖v.toFun r‖ :=
          norm_inner_le_norm _ _
        _ ≤ ‖lChartForce (I := I) S T a p u r‖ * V :=
          mul_le_mul_of_nonneg_left (hV r hr) (norm_nonneg _)
        _ = V * ‖lChartForce (I := I) S T a p u r‖ := mul_comm _ _
    have hForcePairI : IntervalIntegrable
        (fun r ↦ inner Real (lChartForce (I := I) S T a p u r) (v.toFun r))
        volume 0 L := by
      apply IntegrableOn.intervalIntegrable
      simpa only [uIcc_of_le hL.le] using hForcePair
    have hMomPairI : IntervalIntegrable
        (fun r ↦ inner Real
          (chartGramOp (I := I) S.family p (τ r, u.toFun r) (u.deriv r))
          (v.deriv r)) volume 0 L := by
      have hMom : Integrable
          (fun r ↦ inner Real
            (chartGramOp (I := I) S.family p
              (τ r, u.toFun r) (u.deriv r)) (v.deriv r))
          (timeMeasure L) := by
        refine (L2.integrable_inner
          (timeOp (fun r ↦ chartGramOp (I := I) S.family p
            (τ r, u.toFun r)) hA C hC u.deriv) v.deriv).congr ?_
        filter_upwards [timeOp_apply_ae
          (fun r ↦ chartGramOp (I := I) S.family p (τ r, u.toFun r))
          hA C hC u.deriv] with r hr
        rw [hr]
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le hL.le]
      change Integrable
        (fun r ↦ inner Real
          (chartGramOp (I := I) S.family p (τ r, u.toFun r) (u.deriv r))
          (v.deriv r)) (volume.restrict (Icc (0 : Real) L))
      simpa only [timeMeasure] using hMom
    have hWeak' := hWeak v hv0 hvL
    rw [intervalIntegral.integral_add hForcePairI hMomPairI] at hWeak'
    have hMomEq :
        inner Real
            (timeOp (fun r ↦ chartGramOp (I := I) S.family p
              (τ r, u.toFun r)) hA C hC u.deriv) v.deriv =
          ∫ r in (0 : Real)..L,
            inner Real
              (chartGramOp (I := I) S.family p
                (τ r, u.toFun r) (u.deriv r)) (v.deriv r) := by
      rw [L2.inner_def, intervalIntegral.integral_of_le hL.le,
        ← integral_Icc_eq_integral_Ioc]
      apply integral_congr_ae
      filter_upwards [timeOp_apply_ae
        (fun r ↦ chartGramOp (I := I) S.family p (τ r, u.toFun r))
        hA C hC u.deriv] with r hr
      rw [hr]
    have hForceEq :
        (∫ r in Icc (0 : Real) L, inner Real (F r) (v.toFun r)) =
          2 * ∫ r in (0 : Real)..L,
            inner Real (lChartForce (I := I) S T a p u r) (v.toFun r) := by
      calc
        (∫ r in Icc (0 : Real) L, inner Real (F r) (v.toFun r)) =
            ∫ r in Icc (0 : Real) L,
              2 * inner Real
                (lChartForce (I := I) S T a p u r) (v.toFun r) := by
          apply integral_congr_ae
          have hForceAE' : lChartForce (I := I) S T a p u
              =ᵐ[volume.restrict (Icc (0 : Real) L)]
                lChartForceRepresentative (I := I) S T a p u q := by
            simpa only [timeMeasure] using hForceAE
          filter_upwards [hForceAE'] with r hr
          change inner Real
            ((2 : Real) • lChartForceRepresentative (I := I) S T a p u q r)
              (v.toFun r) = _
          rw [← hr, real_inner_smul_left]
        _ = 2 * ∫ r in Icc (0 : Real) L,
              inner Real (lChartForce (I := I) S T a p u r) (v.toFun r) := by
          rw [integral_const_mul]
        _ = 2 * ∫ r in (0 : Real)..L,
              inner Real (lChartForce (I := I) S T a p u r) (v.toFun r) := by
          rw [intervalIntegral.integral_of_le hL.le,
            integral_Icc_eq_integral_Ioc]
    rw [hMomEq, hForceEq]
    linarith
  obtain ⟨c, hMomAE, hPc1, hPderiv⟩ := mom_rep_c1 hL
    (fun r ↦ chartGramOp (I := I) S.family p (τ r, u.toFun r))
    hA C hC u F hF hEuler
  let P : Real → E := fun r ↦ c + ∫ s in (0 : Real)..r, F s
  let momQ : Real → E := fun r ↦ (2 : Real) •
    chartGramOp (I := I) S.family p (τ r, u.toFun r) (q r)
  let J : Set Real := τ '' Icc (0 : Real) L
  have hJreg : J ⊆ D.regular := by
    rintro t ⟨r, hr, rfl⟩
    exact hτreg hr
  have hpair : ContinuousOn (fun r ↦ (τ r, u.toFun r))
      (Icc (0 : Real) L) := hτc.prodMk u.continuousOn_toFun
  have hAcont : ContinuousOn
      (fun r ↦ chartGramOp (I := I) S.family p (τ r, u.toFun r))
      (Icc (0 : Real) L) :=
    (chartGramOp_cont (I := I) hS.smoothMetric hJreg p hKchart).comp
      hpair fun r hr ↦ ⟨⟨r, hr, rfl⟩, huK hr⟩
  have hMomQcont : ContinuousOn momQ (Icc (0 : Real) L) := by
    exact ((hAcont.clm_apply hq).const_smul (2 : Real)).congr fun _ _ ↦ rfl
  have hqIoo : u.deriv =ᵐ[volume.restrict (Ioo (0 : Real) L)] q := by
    simpa only [timeMeasure, Measure.restrict_congr_set Ioo_ae_eq_Icc]
      using hqae
  have hPMomIoo : P =ᵐ[volume.restrict (Ioo (0 : Real) L)] momQ := by
    filter_upwards [hMomAE, hqIoo] with r hrP hrq
    change c + ∫ s in (0 : Real)..r, F s =
      (2 : Real) •
        chartGramOp (I := I) S.family p (τ r, u.toFun r) (q r)
    rw [← hrq]
    exact hrP.symm
  have hPMomIcc : P =ᵐ[volume.restrict (Icc (0 : Real) L)] momQ := by
    simpa only [Measure.restrict_congr_set Ioo_ae_eq_Icc] using hPMomIoo
  have hPeq : EqOn P momQ (Icc (0 : Real) L) :=
    MeasureTheory.Measure.eqOn_Icc_of_ae_eq
      (volume : Measure Real) hL.ne hPMomIcc hPc1.continuousOn hMomQcont
  refine ⟨q, P, hq, hqae, huc1, huderiv, ?_, ?_, ?_⟩
  · simpa only [P] using hPc1
  · simpa only [momQ, τ] using hPeq
  · simpa only [P, F] using hPderiv

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
