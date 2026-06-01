import DifferentialGeometry.PDE.RicciFlow.ShortTimeParabolic.HScaleLipschitz
import DifferentialGeometry.PDE.RicciFlow.HamiltonDeTurckPullbackFlat
import DifferentialGeometry.PDE.RicciFlow.Pullback.EvaluationFormChainRule
import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckRemainderStrongExists
import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization.DeTurckGeometricNonlinearity
import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.EigenCombination
import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization.TensorHsRealize
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.ChartLocalPicard
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.ChartOverlapUniqueness
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.BareFlowFromJointC1
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.SmoothInSpace.VariationalLiftFlatIdentity
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.SmoothDependence.GlobalClosedManifold

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open scoped Manifold ContDiff NNReal ENNReal Topology BigOperators
open DifferentialGeometry
open DifferentialGeometry.PDE
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.DeTurck
open DifferentialGeometry.PDE.RicciFlow.ODE
open DifferentialGeometry.PDE.RicciFlow.Pullback
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- **Spectral strong (`timeH1`) DeTurck-remainder solution (parent re-anchor).**

Re-anchored onto the *same* continuous realize-based nonlinearity `N_cont` as
`deturckN_hscale_lipschitz` (A5) and `forcing_continuous_interior` (A4), for
coherence: the spectral engine `deTurckRemainder_strong_shortTime_exists` takes a
**generic** first-order nonlinearity `{N : H^{a+1} → Hᵃ}` (verified: it is a bound
implicit fed straight to
`quasilinear_strong_existence_locallyLipschitz_smallTime_stayDischarged_ofCompact`),
so swapping `deTurckGeometricN → N_cont` in the forcing fixed-point conjunct does
not break it.

The construction data `N_cont`, `repr`, `Nsec` and the construction/realize
hypotheses `hN_coeff`, `hNsec_realize`, `hrepr_small` are IDENTICAL in shape to
A4/A5 (coordinate/realize identities, NOT the existence conclusion). The
`gforce =ᵐ (fun t => N_cont (…))` conjunct now references the same `N_cont`. -/
theorem deturck_mildsolution_timeh1
    (g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha : Module.finrank ℝ E < 2 * (a - 2))
    (u₀ : tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 2))
    (N_cont : tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 1) →
      tensorHs (I := I) (M := M) g_bg 0 2 (a : ℝ))
    (repr : tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 1) →
      DifferentialGeometry.Integral.L2.SmoothCcTensor g_bg 0 2)
    (Nsec : tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 1) →
      DifferentialGeometry.Integral.L2.SmoothCcTensor g_bg 0 2)
    (hN_coeff : ∀ (u : tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 1))
        (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
          (I := I) (M := M) g_bg 0 2),
      (N_cont u).coeff i =
        tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g_bg 0 2)
          (DifferentialGeometry.Integral.L2.SmoothCcTensor.toL2 (Nsec u)) i)
    (hNsec_realize : ∀ (u : tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 1))
        (x : M) (v w : TangentSpace I x),
      ccTensorBilinSymm (I := I) g_bg (Nsec u) x v w =
        ccTensorBilinSymm (I := I) g_bg (repr u) x v w)
    (hrepr_small : ∀ u : tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 1),
      ∃ δ' : ℝ, δ' < 1 ∧
        gFibreOpBound (I := I) (M := M) g_bg
          (ccTensorBilinSymm (I := I) g_bg (repr u)) δ')
    (hNsec_lip : ∃ K : ℝ≥0, ∀ u u' : tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 1),
      Summable (fun i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
            (I := I) (M := M) g_bg 0 2 =>
          tensorSobolevWeight (I := I) (M := M) i (a : ℝ) *
            (tensorL2Coeff (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M) g_bg 0 2)
                (DifferentialGeometry.Integral.L2.SmoothCcTensor.toL2 (Nsec u)
                  - DifferentialGeometry.Integral.L2.SmoothCcTensor.toL2 (Nsec u')) i) ^ 2)
        ∧ (∑' i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
              (I := I) (M := M) g_bg 0 2,
            tensorSobolevWeight (I := I) (M := M) i (a : ℝ) *
              (tensorL2Coeff (I := I) (M := M)
                  (tensorResolventL2_isCompactOperator (I := I) (M := M) g_bg 0 2)
                  (DifferentialGeometry.Integral.L2.SmoothCcTensor.toL2 (Nsec u)
                    - DifferentialGeometry.Integral.L2.SmoothCcTensor.toL2 (Nsec u')) i) ^ 2)
            ≤ ((K : ℝ) * dist u u') ^ 2) :
    ∃ T : ℝ, ∃ (hT : 0 < T) (hT1 : T ≤ 1)
        (u : MaxRegSolutionSpace (I := I) (M := M) (a : ℝ) T)
        (gforce : timeL2 (tensorHs (I := I) (M := M) g_bg 0 2 (a : ℝ)) T),
        ContinuousOn (timeH1.toFun u) (Set.Icc 0 T) ∧
          timeH1.trace0 _ T u =
            tensorHsInclusion (I := I) (M := M) (g := g_bg) (r := 0) (s := 2)
              (show (a : ℝ) ≤ (a : ℝ) + 2 by linarith) u₀ ∧
          u = maxRegDuhamelMap (I := I) (M := M) (a : ℝ) hT hT1 u₀ gforce ∧
          gforce =ᵐ[timeMeasure T]
            (fun t => N_cont
              (maxRegDuhamelSolFieldHa1 (I := I) (M := M) (a : ℝ) hT hT1 u₀ gforce t)) := by
  obtain ⟨L_R, R, hR, hLip⟩ :=
    deturckN_hscale_lipschitz (I := I) (M := M) g_bg a u₀ N_cont repr Nsec
      hN_coeff hNsec_realize hrepr_small hNsec_lip
  obtain ⟨T₀, hT₀_pos, hsol⟩ :=
    deTurckRemainder_strong_shortTime_exists (I := I) (M := M) g_bg
      (a := (a : ℝ)) (N := N_cont) (L_R := L_R) (R := R) hR u₀ hLip
  refine ⟨min T₀ 1, lt_min hT₀_pos one_pos, min_le_right _ _, ?_⟩
  obtain ⟨u, gforce, hduh, hforce, htrace, _hderiv⟩ :=
    hsol (lt_min hT₀_pos one_pos) (min_le_left _ _) (min_le_right _ _)
  exact ⟨u, gforce, timeH1.continuousOn_toFun u, htrace, hduh, hforce⟩

end DifferentialGeometry.PDE.RicciFlow
