import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeH1C1
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ActionVelocity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ActionWeakEuler

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

theorem lChart_min_c1
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T a : Real) (p : M)
    {L : Real} (hL : 0 < L) (u : timeH1 E L)
    (hreg : ∀ r ∈ Icc (0 : Real) L, T - (a + r) ^ 2 ∈ D.regular)
    (hchart : MapsTo u.toFun (Icc (0 : Real) L)
      (interior (extChartAt I p).target))
    (hmin : IsLocalMinOn (lChartAct S T a p) (sameTimeEnds u) u) :
    ∃ q : Real → E,
      ContinuousOn q (Icc (0 : Real) L) ∧
      u.deriv =ᵐ[timeMeasure L] q ∧
      ContDiffOn Real 1 u.toFun (Icc (0 : Real) L) ∧
      EqOn (derivWithin u.toFun (Icc (0 : Real) L)) q
        (Icc (0 : Real) L) := by
  let τ : Real → Real := fun r ↦ T - (a + r) ^ 2
  let K : Set E := u.toFun '' Icc (0 : Real) L
  have hτc : ContinuousOn τ (Icc (0 : Real) L) := by
    exact (continuous_const.sub ((continuous_const.add continuous_id).pow 2)).continuousOn
  have hτreg : MapsTo τ (Icc (0 : Real) L) D.regular := by
    exact hreg
  have hKc : IsCompact K :=
    isCompact_Icc.image_of_continuousOn u.continuousOn_toFun
  have hKchart : K ⊆ interior (extChartAt I p).target := by
    rintro x ⟨r, hr, rfl⟩
    exact hchart hr
  have huK : MapsTo u.toFun (Icc (0 : Real) L) K := by
    intro r hr
    exact ⟨r, hr, rfl⟩
  obtain ⟨C, hA, hC⟩ := chartGram_time hS.smoothMetric p τ hτc hτreg
    hKc hKchart u huK
  obtain ⟨hForce, hWeak⟩ :=
    lChart_weak_euler (I := I) S hS T a p hL u hreg hchart hmin
  let F : Real → E := fun r ↦ (2 : Real) • lChartForce (I := I) S T a p u r
  have hF : IntegrableOn F (Icc (0 : Real) L) volume := by
    change Integrable F (volume.restrict (Icc (0 : Real) L))
    exact (Integrable.smul (2 : Real) hForce).congr
      (Eventually.of_forall fun _ ↦ rfl)
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
            (chartGramOp (I := I) S.family p (τ r, u.toFun r) (u.deriv r))
            (v.deriv r)) (timeMeasure L) := by
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
      rw [integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le hL.le,
        ← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro r _
      simp only [F, real_inner_smul_left]
    rw [hMomEq, hForceEq]
    linarith
  obtain ⟨q, hq, hqae⟩ := chartVel_rep_cont hS.smoothMetric p hL τ
    hτc hτreg hKchart u huK hA C hC F hF hEuler
  have hqtime : u.deriv =ᵐ[timeMeasure L] q := by
    have hae : ae (volume.restrict (Ioo (0 : Real) L)) =
        ae (timeMeasure L) := by
      congr 1
      unfold timeMeasure
      exact restrict_Ioo_eq_restrict_Icc
    rw [← hae]
    exact hqae
  obtain ⟨hc1, hderiv⟩ := toFun_c1_of_rep hL u q hq hqtime
  exact ⟨q, hq, hqtime, hc1, hderiv⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
