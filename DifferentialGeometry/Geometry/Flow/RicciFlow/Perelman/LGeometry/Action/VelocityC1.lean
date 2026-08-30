import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeH1C1
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeQuadraticRegularC1
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Velocity
import DifferentialGeometry.Geometry.Operator.MetricFamilyGramInv

set_option autoImplicit false

noncomputable section

open Filter MeasureTheory Set
open scoped Manifold Topology ContDiff Interval

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I (∞ : WithTop ℕ∞) M]

theorem chartVel_c1_of_mom {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    (alpha : M) {L : Real} (tau : Real → Real)
    (htau1 : ContDiffOn Real 1 tau (Icc (0 : Real) L))
    (htaureg : MapsTo tau (Icc (0 : Real) L) D.regular)
    {K : Set E} (hKchart : K ⊆ interior (extChartAt I alpha).target)
    (u : timeH1 E L) (huK : MapsTo u.toFun (Icc (0 : Real) L) K)
    (hu1 : ContDiffOn Real 1 u.toFun (Icc (0 : Real) L))
    (p : Real → E)
    (hp : (fun t ↦ (2 : Real) •
      chartGramOp (I := I) G alpha (tau t, u.toFun t) (u.deriv t))
        =ᵐ[volume.restrict (Ioo (0 : Real) L)] p)
    (hp1 : ContDiffOn Real 1 p (Icc (0 : Real) L)) :
    ∃ q : Real → E,
      ContDiffOn Real 1 q (Icc (0 : Real) L) ∧
      u.deriv =ᵐ[volume.restrict (Ioo (0 : Real) L)] q := by
  let J : Set Real := tau '' Icc (0 : Real) L
  have hJreg : J ⊆ D.regular := by
    rintro t ⟨r, hr, rfl⟩
    exact htaureg hr
  have hpair1 : ContDiffOn Real 1 (fun t ↦ (tau t, u.toFun t))
      (Icc (0 : Real) L) := htau1.prodMk hu1
  have hinv1 : ContDiffOn Real 1
      (fun t ↦ Ring.inverse
        (chartGramOp (I := I) G alpha (tau t, u.toFun t)))
      (Icc (0 : Real) L) := by
    exact ((chartGramInv_smooth (I := I) hG hJreg alpha hKchart).of_le
      (by norm_num)).comp hpair1 fun t ht ↦
        ⟨⟨t, ht, rfl⟩, huK ht⟩
  let q : Real → E := fun t ↦ (1 / 2 : Real) •
    Ring.inverse (chartGramOp (I := I) G alpha (tau t, u.toFun t)) (p t)
  refine ⟨q, (hinv1.clm_apply hp1).const_smul _, ?_⟩
  filter_upwards [hp, ae_restrict_mem measurableSet_Ioo] with t ht htime
  dsimp only [q]
  rw [← ht, ContinuousLinearMap.map_smul, smul_smul]
  have hunit := chartGramOp_unit (I := I) hG hJreg alpha hKchart
    (tau t, u.toFun t) ⟨⟨t, ⟨htime.1.le, htime.2.le⟩, rfl⟩,
      huK ⟨htime.1.le, htime.2.le⟩⟩
  have hmul := congrArg (fun A : E →L[Real] E ↦ A (u.deriv t))
    (Ring.inverse_mul_cancel _ hunit)
  have hhalf : (1 / 2 : Real) * 2 = 1 := by norm_num
  rw [hhalf, one_smul]
  simpa only [mul_apply_eq_comp, one_apply_eq_self]
    using hmul.symm

theorem chartVel_rep_c1 {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    (alpha : M) {L : Real} (hL : 0 < L) (tau : Real → Real)
    (htau1 : ContDiffOn Real 1 tau (Icc (0 : Real) L))
    (htaureg : MapsTo tau (Icc (0 : Real) L) D.regular)
    {K : Set E} (hKchart : K ⊆ interior (extChartAt I alpha).target)
    (u : timeH1 E L) (huK : MapsTo u.toFun (Icc (0 : Real) L) K)
    (hA : AEStronglyMeasurable
      (fun t ↦ chartGramOp (I := I) G alpha (tau t, u.toFun t))
        (timeMeasure L))
    (C : NNReal) (hC : ∀ᵐ t ∂timeMeasure L,
      ‖chartGramOp (I := I) G alpha (tau t, u.toFun t)‖ ≤ (C : Real))
    (F : Real → E) (hF : ContinuousOn F (Icc (0 : Real) L))
    (hEuler : ∀ v : timeH1 E L, v.init = 0 → v.toFun L = 0 →
      2 * inner Real
          (timeOp (fun t ↦ chartGramOp (I := I) G alpha
            (tau t, u.toFun t)) hA C hC u.deriv) v.deriv +
        ∫ t in Icc (0 : Real) L, inner Real (F t) (v.toFun t) = 0) :
    ∃ q : Real → E,
      ContDiffOn Real 1 q (Icc (0 : Real) L) ∧
      u.deriv =ᵐ[volume.restrict (Ioo (0 : Real) L)] q ∧
      EqOn (derivWithin u.toFun (Icc (0 : Real) L)) q
        (Icc (0 : Real) L) := by
  obtain ⟨c, hmom, hp1, _⟩ := mom_rep_c1 hL
    (fun t ↦ chartGramOp (I := I) G alpha (tau t, u.toFun t))
    hA C hC u F hF hEuler
  let p : Real → E := fun t ↦ c + ∫ r in (0 : Real)..t, F r
  have hmom' : (fun t ↦ (2 : Real) •
      chartGramOp (I := I) G alpha (tau t, u.toFun t) (u.deriv t))
        =ᵐ[volume.restrict (Ioo (0 : Real) L)] p := by
    simpa only [p] using hmom
  have hp1' : ContDiffOn Real 1 p (Icc (0 : Real) L) := by
    simpa only [p] using hp1
  obtain ⟨q0, hq0cont, hq0ae⟩ := chartVel_of_mom hG alpha tau
    htau1.continuousOn htaureg hKchart u huK p hmom' hp1'.continuousOn
  have hq0time : u.deriv =ᵐ[timeMeasure L] q0 := by
    simpa only [timeMeasure, Measure.restrict_congr_set Ioo_ae_eq_Icc]
      using hq0ae
  obtain ⟨hu1, _⟩ := toFun_c1_of_rep hL u q0 hq0cont hq0time
  obtain ⟨q, hq1, hqae⟩ := chartVel_c1_of_mom hG alpha tau htau1
    htaureg hKchart u huK hu1 p hmom' hp1'
  have hqtime : u.deriv =ᵐ[timeMeasure L] q := by
    simpa only [timeMeasure, Measure.restrict_congr_set Ioo_ae_eq_Icc]
      using hqae
  obtain ⟨_, hderiv⟩ := toFun_c1_of_rep hL u q hq1.continuousOn hqtime
  exact ⟨q, hq1, hqae, hderiv⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
