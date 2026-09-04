import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Quadratic.Regularity
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Quadratic.L1Regularity
import DifferentialGeometry.Geometry.Operator.MetricFamilyGramInv

set_option autoImplicit false

noncomputable section

open Filter MeasureTheory Set
open scoped Manifold Topology ContDiff Interval

namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev

open DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I (∞ : WithTop ℕ∞) M]

theorem exists_chartGramOp_ae_bound {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    (alpha : M) {L : Real} (τ : Real → Real)
    (hτc : ContinuousOn τ (Icc (0 : Real) L))
    (hτreg : MapsTo τ (Icc (0 : Real) L) D.regular)
    {K : Set E} (hKc : IsCompact K)
    (hKchart : K ⊆ interior (extChartAt I alpha).target)
    (u : timeH1 E L) (huK : MapsTo u.toFun (Icc (0 : Real) L) K) :
    ∃ (C : NNReal)
      (_ : AEStronglyMeasurable
        (fun r ↦ chartGramOp (I := I) G alpha (τ r, u.toFun r)) (timeMeasure L)),
      ∀ᵐ r ∂timeMeasure L,
        ‖chartGramOp (I := I) G alpha (τ r, u.toFun r)‖ ≤ (C : Real) := by
  let J : Set Real := τ '' Icc (0 : Real) L
  have hJc : IsCompact J := isCompact_Icc.image_of_continuousOn hτc
  have hJreg : J ⊆ D.regular := by
    rintro t ⟨r, hr, rfl⟩
    exact hτreg hr
  let A : Real → E →L[Real] E := fun r ↦
    chartGramOp (I := I) G alpha (τ r, u.toFun r)
  have hpair : ContinuousOn (fun r ↦ (τ r, u.toFun r)) (Icc (0 : Real) L) :=
    hτc.prodMk u.continuousOn_toFun
  have hAcont : ContinuousOn A (Icc (0 : Real) L) := by
    exact (chartGramOp_cont (I := I) hG hJreg alpha hKchart).comp hpair
      fun r hr ↦ ⟨⟨r, hr, rfl⟩, huK hr⟩
  have hA : AEStronglyMeasurable A (timeMeasure L) := by
    simpa only [timeMeasure] using hAcont.aestronglyMeasurable measurableSet_Icc
  obtain ⟨C, hC⟩ := chartGramOp_bound (I := I) hG hJreg hJc alpha hKchart hKc
  refine ⟨C, hA, ?_⟩
  filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
  exact hC (τ r, u.toFun r) ⟨⟨r, hr, rfl⟩, huK hr⟩

theorem exists_continuous_velocity_representative_of_momentum {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    (alpha : M) {L : Real} (τ : Real → Real)
    (hτc : ContinuousOn τ (Icc (0 : Real) L))
    (hτreg : MapsTo τ (Icc (0 : Real) L) D.regular)
    {K : Set E} (hKchart : K ⊆ interior (extChartAt I alpha).target)
    (u : timeH1 E L) (huK : MapsTo u.toFun (Icc (0 : Real) L) K)
    (p : Real → E)
    (hp : (fun t ↦ (2 : Real) •
      chartGramOp (I := I) G alpha (τ t, u.toFun t) (u.deriv t))
        =ᵐ[volume.restrict (Ioo (0 : Real) L)] p)
    (hpcont : ContinuousOn p (Icc (0 : Real) L)) :
    ∃ q : Real → E, ContinuousOn q (Icc (0 : Real) L) ∧
      u.deriv =ᵐ[volume.restrict (Ioo (0 : Real) L)] q := by
  let J : Set Real := τ '' Icc (0 : Real) L
  have hJreg : J ⊆ D.regular := by
    rintro t ⟨r, hr, rfl⟩
    exact hτreg hr
  have hpair : ContinuousOn (fun t ↦ (τ t, u.toFun t)) (Icc (0 : Real) L) :=
    hτc.prodMk u.continuousOn_toFun
  have hinv : ContinuousOn
      (fun t ↦ Ring.inverse (chartGramOp (I := I) G alpha (τ t, u.toFun t)))
      (Icc (0 : Real) L) := by
    exact (chartGramInv_cont (I := I) hG hJreg alpha hKchart).comp hpair
      fun t ht ↦ ⟨⟨t, ht, rfl⟩, huK ht⟩
  let q : Real → E := fun t ↦ (1 / 2 : Real) •
    Ring.inverse (chartGramOp (I := I) G alpha (τ t, u.toFun t)) (p t)
  refine ⟨q, (hinv.clm_apply hpcont).const_smul _, ?_⟩
  filter_upwards [hp, ae_restrict_mem measurableSet_Ioo] with t ht htime
  dsimp only [q]
  rw [← ht]
  rw [ContinuousLinearMap.map_smul, smul_smul]
  have hunit := chartGramOp_unit (I := I) hG hJreg alpha hKchart
    (τ t, u.toFun t) ⟨⟨t, ⟨htime.1.le, htime.2.le⟩, rfl⟩,
      huK ⟨htime.1.le, htime.2.le⟩⟩
  have hmul := congrArg (fun A : E →L[Real] E ↦ A (u.deriv t))
    (Ring.inverse_mul_cancel _ hunit)
  have hhalf : (1 / 2 : Real) * 2 = 1 := by norm_num
  rw [hhalf, one_smul]
  simpa only [mul_apply_eq_comp, one_apply_eq_self] using hmul.symm

theorem exists_continuous_velocity_representative_of_weak_euler {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    (alpha : M) {L : Real} (hL : 0 < L) (τ : Real → Real)
    (hτc : ContinuousOn τ (Icc (0 : Real) L))
    (hτreg : MapsTo τ (Icc (0 : Real) L) D.regular)
    {K : Set E} (hKchart : K ⊆ interior (extChartAt I alpha).target)
    (u : timeH1 E L) (huK : MapsTo u.toFun (Icc (0 : Real) L) K)
    (hA : AEStronglyMeasurable
      (fun t ↦ chartGramOp (I := I) G alpha (τ t, u.toFun t)) (timeMeasure L))
    (C : NNReal) (hC : ∀ᵐ t ∂timeMeasure L,
      ‖chartGramOp (I := I) G alpha (τ t, u.toFun t)‖ ≤ (C : Real))
    (F : Real → E) (hF : IntegrableOn F (Icc (0 : Real) L) volume)
    (hEuler : ∀ v : timeH1 E L, v.init = 0 → v.toFun L = 0 →
      2 * inner Real
          (timeOp (fun t ↦ chartGramOp (I := I) G alpha (τ t, u.toFun t))
            hA C hC u.deriv) v.deriv +
        ∫ t in Icc (0 : Real) L, inner Real (F t) (v.toFun t) = 0) :
    ∃ q : Real → E, ContinuousOn q (Icc (0 : Real) L) ∧
      u.deriv =ᵐ[volume.restrict (Ioo (0 : Real) L)] q := by
  obtain ⟨c, hmom, hcont⟩ := mom_rep_cont_l1 hL
    (fun t ↦ chartGramOp (I := I) G alpha (τ t, u.toFun t)) hA C hC u F hF hEuler
  exact exists_continuous_velocity_representative_of_momentum hG alpha τ hτc hτreg hKchart u huK
    (fun t ↦ c + ∫ r in (0 : Real)..t, F r) hmom hcont

end DifferentialGeometry.Analysis.Parabolic.TimeSobolev
