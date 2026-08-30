import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.ForceC1
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.VelocityC1

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
theorem lChartVel_c1
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T a : Real) (p : M)
    {L : Real} (hL : 0 < L) (u : timeH1 E L)
    (hreg : ∀ r ∈ Icc (0 : Real) L, T - (a + r) ^ 2 ∈ D.regular)
    (hchart : MapsTo u.toFun (Icc (0 : Real) L)
      (interior (extChartAt I p).target))
    (q0 : Real → E) (hq0 : ContinuousOn q0 (Icc (0 : Real) L))
    (hq0ae : u.deriv =ᵐ[timeMeasure L] q0)
    (hEuler : ∀ v : timeH1 E L, v.init = 0 → v.toFun L = 0 →
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
  obtain ⟨C, hA, hC⟩ := chartGram_time hS.smoothMetric p tau
    htau1.continuousOn htaureg hKc hKchart u huK
  let F0 : Real → E := lChartForceRep (I := I) S T a p u q0
  let F : Real → E := fun r ↦ (2 : Real) • F0 r
  have hF0 : ContinuousOn F0 (Icc (0 : Real) L) := by
    simpa only [F0] using
      lChartForceRep_cont (I := I) S hS T a p u q0 hreg hchart hq0
  have hF : ContinuousOn F (Icc (0 : Real) L) :=
    hF0.const_smul (2 : Real)
  have hraw : lChartForce (I := I) S T a p u =ᵐ[timeMeasure L] F0 := by
    simpa only [F0] using
      lChartForceRep_ae (I := I) S hS T a p u q0 hreg hchart hq0ae
  have hEuler' : ∀ v : timeH1 E L, v.init = 0 → v.toFun L = 0 →
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
  exact chartVel_rep_c1 hS.smoothMetric p hL tau htau1 htaureg
    hKchart u huK hA C hC F hF hEuler'

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
