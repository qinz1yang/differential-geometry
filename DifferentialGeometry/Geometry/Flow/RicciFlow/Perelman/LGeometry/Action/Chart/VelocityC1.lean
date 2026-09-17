import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Chart.ForceRegularity
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.MetricFamily.C1Velocity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Chart.MomentumRegularity
import DifferentialGeometry.Geometry.Operator.Family.Gram.Inverse
import Mathlib.Analysis.Calculus.ContDiff.Deriv

set_option autoImplicit false

noncomputable section

open Filter MeasureTheory Set
open scoped ContDiff Interval Manifold Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Geometry.Curvature

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
variable {D : RealTimeInterval}

omit [NeZero (Module.finrank Real E)] [I.Boundaryless]
  [SigmaCompactSpace M] in
theorem lChartAction_minimizer_velocity_contDiffOn_one
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T a : Real) (p : M)
    {L : Real} (hL : 0 < L) (u : timeH1 E L)
    (hreg : ∀ r ∈ Icc (0 : Real) L, T - (a + r) ^ 2 ∈ D.regular)
    (hchart : MapsTo u.toFun (Icc (0 : Real) L)
      (interior (extChartAt I p).target))
    (q0 : Real → E) (hq0 : ContinuousOn q0 (Icc (0 : Real) L))
    (hq0ae : u.deriv =ᵐ[timeMeasure L] q0)
    (hEuler : ∀ v : timeH1 E L, v.initial = 0 → v.toFun L = 0 →
      (∫ r in (0 : Real)..L,
        inner Real (lChartForce (I := I) S T a p u r) (v.toFun r) +
          inner Real
            (chartGramOp (I := I) S.family p
              (T - (a + r) ^ 2, u.toFun r) (u.deriv r))
            (v.deriv r)) = 0) :
    ∃ q : Real → E,
      ContDiffOn Real 1 q (Icc (0 : Real) L) ∧
      u.deriv =ᵐ[volume.restrict (Ioo (0 : Real) L)] q ∧
      EqOn (derivWithin u.toFun (Icc (0 : Real) L)) q
        (Icc (0 : Real) L) := by
  let tau : Real → Real := fun r ↦ T - (a + r) ^ 2
  let K : Set E := u.toFun '' Icc (0 : Real) L
  have htau1 : ContDiffOn Real 1 tau (Icc (0 : Real) L) := by
    exact (contDiff_const.sub ((contDiff_const.add contDiff_id).pow 2)).contDiffOn
  have htaureg : MapsTo tau (Icc (0 : Real) L) D.regular := hreg
  have hKc : IsCompact K :=
    isCompact_Icc.image_of_continuousOn u.continuousOn_toFun
  have hKchart : K ⊆ interior (extChartAt I p).target := by
    rintro x ⟨r, hr, rfl⟩
    exact hchart hr
  have huK : MapsTo u.toFun (Icc (0 : Real) L) K :=
    fun r hr ↦ ⟨r, hr, rfl⟩
  obtain ⟨C, hA, hC⟩ := exists_chartGramOp_ae_bound hS.smoothMetric p tau
    htau1.continuousOn htaureg hKc hKchart u huK
  let F0 : Real → E := lChartForceRepresentative (I := I) S T a p u q0
  let F : Real → E := fun r ↦ (2 : Real) • F0 r
  have hF0 : ContinuousOn F0 (Icc (0 : Real) L) := by
    simpa only [F0] using
      continuousOn_lChartForceRepresentative (I := I) S hS T a p u q0 hreg hchart hq0
  have hF : ContinuousOn F (Icc (0 : Real) L) :=
    hF0.const_smul (2 : Real)
  have hraw : lChartForce (I := I) S T a p u =ᵐ[timeMeasure L] F0 := by
    simpa only [F0] using
      lChartForce_ae_eq_lChartForceRepresentative (I := I) S hS T a p u q0 hreg hchart hq0ae
  have hEuler' : ∀ v : timeH1 E L, v.initial = 0 → v.toFun L = 0 →
      2 * inner Real
          (timeOp (fun r ↦ chartGramOp (I := I) S.family p
            (tau r, u.toFun r)) hA C hC u.deriv) v.deriv +
        ∫ r in Icc (0 : Real) L, inner Real (F r) (v.toFun r) = 0 := by
    intro v hv0 hvL
    have he := hEuler v hv0 hvL
    have hmom : inner Real
        (timeOp (fun r ↦ chartGramOp (I := I) S.family p
          (tau r, u.toFun r)) hA C hC u.deriv) v.deriv =
        ∫ r in Icc (0 : Real) L,
          inner Real
            (chartGramOp (I := I) S.family p
              (tau r, u.toFun r) (u.deriv r)) (v.deriv r) := by
      rw [L2.inner_def]
      apply MeasureTheory.integral_congr_ae
      filter_upwards [timeOp_apply_ae
        (fun r ↦ chartGramOp (I := I) S.family p
          (tau r, u.toFun r)) hA C hC u.deriv] with r hr
      rw [hr]
    have hkin : IntegrableOn
        (fun r ↦ inner Real
          (chartGramOp (I := I) S.family p
            (tau r, u.toFun r) (u.deriv r)) (v.deriv r))
        (Icc (0 : Real) L) volume := by
      change Integrable
        (fun r ↦ inner Real
          (chartGramOp (I := I) S.family p
            (tau r, u.toFun r) (u.deriv r)) (v.deriv r))
        (timeMeasure L)
      refine (L2.integrable_inner
        (timeOp (fun r ↦ chartGramOp (I := I) S.family p
          (tau r, u.toFun r)) hA C hC u.deriv) v.deriv).congr ?_
      filter_upwards [timeOp_apply_ae
        (fun r ↦ chartGramOp (I := I) S.family p
          (tau r, u.toFun r)) hA C hC u.deriv] with r hr
      rw [hr]
    have hforce : IntegrableOn
        (fun r ↦ inner Real (F0 r) (v.toFun r))
        (Icc (0 : Real) L) volume :=
      (hF0.inner v.continuousOn_toFun).integrableOn_compact isCompact_Icc
    have hFscale :
        (∫ r in Icc (0 : Real) L, inner Real (F r) (v.toFun r)) =
          2 * ∫ r in Icc (0 : Real) L,
            inner Real (F0 r) (v.toFun r) := by
      rw [← MeasureTheory.integral_const_mul]
      apply MeasureTheory.integral_congr_ae
      filter_upwards [] with r
      simp only [F, real_inner_smul_left]
    have hsum :
        (∫ r in Icc (0 : Real) L,
          inner Real
              (chartGramOp (I := I) S.family p
                (tau r, u.toFun r) (u.deriv r)) (v.deriv r) +
            inner Real (F0 r) (v.toFun r)) =
          ∫ r in Icc (0 : Real) L,
            inner Real (lChartForce (I := I) S T a p u r) (v.toFun r) +
              inner Real
                (chartGramOp (I := I) S.family p
                  (tau r, u.toFun r) (u.deriv r)) (v.deriv r) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [hraw] with r hr
      rw [hr]
      ring
    have he' :
        (∫ r in Icc (0 : Real) L,
          inner Real (lChartForce (I := I) S T a p u r) (v.toFun r) +
            inner Real
              (chartGramOp (I := I) S.family p
                (tau r, u.toFun r) (u.deriv r)) (v.deriv r)) = 0 := by
      simpa only [tau, intervalIntegral.integral_of_le hL.le,
        ← integral_Icc_eq_integral_Ioc] using he
    rw [hmom, hFscale]
    calc
      2 * (∫ r in Icc (0 : Real) L,
          inner Real
            (chartGramOp (I := I) S.family p
              (tau r, u.toFun r) (u.deriv r)) (v.deriv r)) +
          2 * ∫ r in Icc (0 : Real) L,
            inner Real (F0 r) (v.toFun r) =
          2 * ((∫ r in Icc (0 : Real) L,
            inner Real
              (chartGramOp (I := I) S.family p
                (tau r, u.toFun r) (u.deriv r)) (v.deriv r)) +
              ∫ r in Icc (0 : Real) L,
                inner Real (F0 r) (v.toFun r)) := by ring
      _ = 2 * ∫ r in Icc (0 : Real) L,
          (inner Real
              (chartGramOp (I := I) S.family p
                (tau r, u.toFun r) (u.deriv r)) (v.deriv r) +
            inner Real (F0 r) (v.toFun r)) := by
          rw [MeasureTheory.integral_add hkin hforce]
      _ = 2 * ∫ r in Icc (0 : Real) L,
          (inner Real (lChartForce (I := I) S T a p u r) (v.toFun r) +
            inner Real
              (chartGramOp (I := I) S.family p
                (tau r, u.toFun r) (u.deriv r)) (v.deriv r)) := by
          rw [hsum]
      _ = 0 := by rw [he', mul_zero]
  exact exists_contDiffOn_one_velocity_representative_of_weak_euler hS.smoothMetric p hL tau htau1 htaureg
    hKchart u huK hA C hC F hF hEuler'

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
section

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Filter Set
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Geometry.Curvature

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]
variable {D : RealTimeInterval}

theorem lChartAction_minimizer_contDiffOn_two_of_spatial_derivatives
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T a : Real) (p : M)
    {L : Real} (hL : 0 < L) (u : timeH1 E L)
    {J : Set Real} (hJ : J ⊆ D.carrier)
    (htime : ∀ r ∈ Icc (0 : Real) L, T - (a + r) ^ 2 ∈ J)
    (hreg : ∀ r ∈ Ioo (0 : Real) L, T - (a + r) ^ 2 ∈ D.regular)
    (hGramFd : ContinuousOn (fun z : Real × E => fderiv Real
      (fun y : E => chartGramOp (I := I) S.family p (z.1, y)) z.2)
      (J ×ˢ interior (extChartAt I p).target))
    (hScalFd : ContinuousOn (fun z : Real × E => fderiv Real
      (DifferentialGeometry.Tensor.Coordinates.scalarOnE (I := I) p (S.scalar z.1)) z.2)
      (J ×ˢ interior (extChartAt I p).target))
    (hchart : MapsTo u.toFun (Icc (0 : Real) L)
      (interior (extChartAt I p).target))
    (hmin : IsLocalMinOn (lChartAction S T a p) (sameTimeEnds u) u) :
    ContDiffOn Real 2 u.toFun (Ioo (0 : Real) L) := by
  obtain ⟨q, P, _, _, hu1, huder, hP1, hPeq, _⟩ :=
    lChartAction_minimizer_momentum_contDiffOn_one_of_spatial_derivatives S hS T a p hL u
      hJ htime hreg hGramFd hScalFd hchart hmin
  have htau : ContDiffOn Real 1 (fun r : Real => T - (a + r) ^ 2)
      (Ioo (0 : Real) L) :=
    (contDiff_const.sub ((contDiff_const.add contDiff_id).pow 2)).contDiffOn
  have hq1 : ContDiffOn Real 1 q (Ioo (0 : Real) L) := by
    exact contDiffOn_chart_velocity_of_momentum hS.smoothMetric p
      (fun r : Real => T - (a + r) ^ 2) u.toFun q P htau (hu1.mono Ioo_subset_Icc_self) (hP1.mono Ioo_subset_Icc_self) hreg
      (fun r hr => hchart ⟨hr.1.le, hr.2.le⟩)
      (fun r hr => hPeq ⟨hr.1.le, hr.2.le⟩)
  have hderiv : ContDiffOn Real 1 (deriv u.toFun) (Ioo (0 : Real) L) := by
    apply hq1.congr
    intro r hr
    have hIcc : Icc (0 : Real) L ∈ nhds r :=
      mem_of_superset (Ioo_mem_nhds hr.1 hr.2) Ioo_subset_Icc_self
    rw [← derivWithin_of_mem_nhds hIcc]
    exact huder ⟨hr.1.le, hr.2.le⟩
  change ContDiffOn Real ((1 : ℕ∞ω) + 1) u.toFun (Ioo (0 : Real) L)
  exact (contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo).2
    ⟨(hu1.mono Ioo_subset_Icc_self).differentiableOn (by norm_num), by simp, hderiv⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman

end

end
