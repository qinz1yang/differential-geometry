import DifferentialGeometry.Geometry.Curvature.RicciOperatorNormBoundFlow

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Metric equivalence on canonical open-interval windows

This file isolates the order-zero time-direction estimate used by the P4
producer.  A uniform Riemann-curvature bound gives a uniform Ricci quadratic
bound, and the Ricci-flow equation then compares every time-slice metric with
the time-zero metric.  The result is independent of Shi estimates and of the
Cheeger--Gromov comparison maps.
-/

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff Topology
open DifferentialGeometry.Integral.Connection

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [Module.Finite Real E] [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

namespace CurvBoundInput

/-- On one canonical compact window, the time-zero metrics uniformly control
all time-slice metrics.  The curvature/Ricci constant and the finite window
majorant are chosen before the sequence member. -/
theorem metricEquiv_open
    {a b : Real} (h0 : (0 : Real) ∈ Set.Ioo a b)
    (X : PointedFlowSeq.{u, uE, uH} (I := I))
    (hD : X.D = RealTimeInterval.openInterval a b 0 h0)
    (hcurv : CurvBoundInput (I := I) X) (n : Nat) :
    let beta := RealTimeInterval.openWindowLeft a 0 n
    let psi := RealTimeInterval.openWindowRight b 0 n
    ∃ A Bmax : Real, 0 ≤ A ∧ 1 ≤ Bmax ∧
      (∀ t : Real, t ∈ Set.Icc beta psi →
        metricEquivalenceFactor 1 A t 0 ≤ Bmax) ∧
      ∀ k : Nat,
        letI : TopologicalSpace (X.term k).M := (X.term k).topology
        letI : ChartedSpace H (X.term k).M := (X.term k).charted
        letI : T2Space (X.term k).M := (X.term k).t2
        letI : IsManifold I ∞ (X.term k).M := (X.term k).smooth
        letI : SigmaCompactSpace (X.term k).M := (X.term k).sigmaCompact
        MetricUniformEquivalentOnWindow (I := I) Set.univ beta psi
          ((X.term k).S.family.metric 0)
          (fun _ t => (X.term k).S.family.metric t)
          (fun t => metricEquivalenceFactor 1 A t 0) := by
  dsimp only
  let beta := RealTimeInterval.openWindowLeft a 0 n
  let psi := RealTimeInterval.openWindowRight b 0 n
  have hzeroWindow : (0 : Real) ∈ Set.Icc beta psi := by
    simpa only [beta, psi, RealTimeInterval.openWindow] using
      RealTimeInterval.initial_mem_window h0 n
  have hbetaPsi : beta ≤ psi := hzeroWindow.1.trans hzeroWindow.2
  have hcarrier : Set.Icc beta psi ⊆ X.D.carrier := by
    intro t ht
    rw [hD]
    exact RealTimeInterval.openWindow_subset h0 n ht
  have hregular : Set.Icc beta psi ⊆ X.D.regular := by
    intro t ht
    rw [hD]
    exact RealTimeInterval.openWindow_subset h0 n ht
  obtain ⟨C, hC, hcurvC⟩ := hcurv.bound_on_window beta psi hcarrier
  let A : Real := (Module.finrank Real E : Real) ^ 2 * Real.sqrt C
  have hA : 0 ≤ A := by
    dsimp only [A]
    positivity
  let timeRadius : Real := |beta| + |psi|
  have hRadius : 0 ≤ timeRadius := by
    dsimp only [timeRadius]
    positivity
  let Bmax : Real := Real.exp (2 * A * timeRadius)
  have hBmax : 1 ≤ Bmax := by
    dsimp only [Bmax]
    exact Real.one_le_exp (mul_nonneg (mul_nonneg (by norm_num) hA) hRadius)
  have habs : ∀ t : Real, t ∈ Set.Icc beta psi → |t| ≤ timeRadius := by
    intro t ht
    have hbeta0 : beta ≤ 0 := hzeroWindow.1
    have hzeroPsi : 0 ≤ psi := hzeroWindow.2
    by_cases ht0 : t ≤ 0
    · dsimp only [timeRadius]
      rw [abs_of_nonpos ht0, abs_of_nonpos hbeta0, abs_of_nonneg hzeroPsi]
      have hneg : -t ≤ -beta := neg_le_neg ht.1
      linarith
    · have hzeroT : 0 ≤ t := le_of_not_ge ht0
      dsimp only [timeRadius]
      rw [abs_of_nonneg hzeroT, abs_of_nonpos hbeta0, abs_of_nonneg hzeroPsi]
      have hnegBeta : 0 ≤ -beta := neg_nonneg.mpr hbeta0
      have htPsi : t ≤ psi := ht.2
      linarith
  have hB : ∀ t : Real, t ∈ Set.Icc beta psi →
      metricEquivalenceFactor 1 A t 0 ≤ Bmax := by
    intro t ht
    rw [metricEquivalenceFactor]
    simp only [one_mul, sub_zero]
    dsimp only [Bmax]
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left (habs t ht)
      (mul_nonneg (by norm_num) hA)
  refine ⟨A, Bmax, hA, hBmax, hB, ?_⟩
  intro k
  letI : TopologicalSpace (X.term k).M := (X.term k).topology
  letI : ChartedSpace H (X.term k).M := (X.term k).charted
  letI : T2Space (X.term k).M := (X.term k).t2
  letI : IsManifold I ∞ (X.term k).M := (X.term k).smooth
  letI : SigmaCompactSpace (X.term k).M := (X.term k).sigmaCompact
  let Sseq : Nat → PDE.RicciFlow.SolutionOn (I := I) (M := (X.term k).M) X.D :=
    fun _ => (X.term k).S
  have hSseq : ∀ i : Nat, PDE.RicciFlow.IsSolutionOn (I := I) (Sseq i) :=
    fun _ => (X.term k).isSolution
  have hquad := twoTensorQuadBound_of_solutions (I := I) Sseq Set.univ
    beta psi C hC hcarrier (fun _ t ht x _ => by
      simpa only [PointedFlowData.rmNormSq, Sseq] using hcurvC k t ht x)
  have hequiv0 : ∀ i : Nat,
      MetricUniformEquivalentOn (I := I) Set.univ
        ((X.term k).S.family.metric 0) ((Sseq i).family.metric 0) 1 := by
    intro i
    refine ⟨le_rfl, ?_⟩
    intro x _ v
    simp only [Sseq, inv_one, one_mul]
    exact ⟨le_rfl, le_rfl⟩
  have hequiv := metricUniformEquivalentOnWindow_of_solutions' (I := I)
    Sseq hSseq Set.univ beta psi 0 1 A ((X.term k).S.family.metric 0)
    hregular hzeroWindow le_rfl hA hequiv0 hquad.2
  simpa only [Sseq] using hequiv

end CurvBoundInput

end HCGCompactness
end DifferentialGeometry
