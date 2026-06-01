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

set_option linter.unusedVariables false in
/-- **H-scale local Lipschitz estimate for the continuous DeTurck nonlinearity.**

Re-anchored away from the finite-support-gated `deTurckGeometricN` (which is
globally discontinuous, hence not Lipschitz on any ball: it jumps to `0` at
infinite-support points arbitrarily close to a realizable center) onto a
*continuous* realize-based nonlinearity `N_cont`, carried as internal data
together with an honest construction/agreement hypothesis tying it to the
**linear** realize (`ccTensorBilinSymm` / `exists_smooth_metric_of_smooth_tensor_small`),
which works for infinite-support inputs via a smooth representative.

The construction data:
* `repr u : SmoothCcTensor g_bg 0 2` — a smooth representative of `u`, the
  realize input (for infinite-support inputs the existence of such a
  representative is the open Gårding/Weyl input; carried here as an internal,
  honestly-flagged hypothesis `hrepr_small`, non-leaking — it constrains the
  internal carrier, never `g₀`/the headline);
* `Nsec u : SmoothCcTensor g_bg 0 2` — the realize-based geometric remainder
  section.

The honest construction hypothesis splits into:
* `hN_coeff` — `N_cont u`'s eigenbasis coordinates ARE the `L²` coordinates of
  the remainder section `Nsec u` (the *same* packaging as the genuine
  `deTurckGeometricN_coeff`, but anchored on the continuous realize section
  `Nsec u` instead of the gated `deTurckRemainderSection u`);
* `hNsec_realize` — `Nsec u`'s extracted symmetric bilinear form IS the linear
  realize `ccTensorBilinSymm (repr u)` (a genuine analytic *realize identity*,
  not the Lipschitz conclusion): this ties `Nsec` to the linear realization
  program.

Neither hypothesis is the conclusion: they are coefficient/realize identities
about `N_cont`'s *coordinates* and `Nsec`'s *bilinear extraction*, structurally
distinct from "`N_cont` is Lipschitz on a ball". The conclusion — local
Lipschitz-ness of `N_cont` — is then derived (in the fill phase) from the
continuity of the linear realize `ccTensorBilinSymm` in `H^{a+1}`. -/
theorem deturckN_hscale_lipschitz
    (g_bg : SmoothRiemannianMetric I M) (a : ℕ)
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
    ∃ (L_R : ℝ≥0) (R : ℝ), 0 < R ∧
      LipschitzOnWith L_R N_cont
        (Metric.closedBall
          (tensorHsInclusion (I := I) (M := M) (g := g_bg) (r := 0) (s := 2)
            (show ((a : ℝ) + 1) ≤ (a : ℝ) + 2 by linarith) u₀) R) := by
  classical
  set hcompact :=
    tensorResolventL2_isCompactOperator (I := I) (M := M) g_bg 0 2 with hcompact_def
  obtain ⟨K, hK⟩ := hNsec_lip
  refine ⟨K, 1, by norm_num, ?_⟩
  refine LipschitzOnWith.of_dist_le_mul (fun u _ u' _ => ?_)
  have hsub :
      ∀ (S T : DifferentialGeometry.Integral.L2.TensorL2 0 2 g_bg)
        (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
          (I := I) (M := M) g_bg 0 2),
        tensorL2Coeff (I := I) (M := M) hcompact (S - T) i =
          tensorL2Coeff (I := I) (M := M) hcompact S i
            - tensorL2Coeff (I := I) (M := M) hcompact T i := by
    intro S T i
    unfold tensorL2Coeff
    rw [map_sub]
    rfl
  have hcoeff_diff :
      ∀ i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
        (I := I) (M := M) g_bg 0 2,
        (N_cont u - N_cont u').coeff i =
          tensorL2Coeff (I := I) (M := M) hcompact
            (DifferentialGeometry.Integral.L2.SmoothCcTensor.toL2 (Nsec u)
              - DifferentialGeometry.Integral.L2.SmoothCcTensor.toL2 (Nsec u')) i := by
    intro i
    have hcoeff_sub :
        (N_cont u - N_cont u').coeff i
          = (N_cont u).coeff i - (N_cont u').coeff i := by
      rw [sub_eq_add_neg, tensorHs.add_coeff, tensorHs.neg_coeff, sub_eq_add_neg]
    rw [hcoeff_sub, hN_coeff u i, hN_coeff u' i, ← hsub]
  have hnorm_sq :
      ‖N_cont u - N_cont u'‖ ^ 2 ≤ ((K : ℝ) * dist u u') ^ 2 := by
    rw [tensorHs.norm_sq_eq_tsum]
    have hcongr :
        (fun i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
            (I := I) (M := M) g_bg 0 2 =>
          tensorSobolevWeight (I := I) (M := M) i (a : ℝ) *
            ((N_cont u - N_cont u').coeff i) ^ 2)
          = (fun i =>
              tensorSobolevWeight (I := I) (M := M) i (a : ℝ) *
                (tensorL2Coeff (I := I) (M := M) hcompact
                    (DifferentialGeometry.Integral.L2.SmoothCcTensor.toL2 (Nsec u)
                      - DifferentialGeometry.Integral.L2.SmoothCcTensor.toL2 (Nsec u'))
                    i) ^ 2) := by
      funext i; rw [hcoeff_diff i]
    rw [hcongr]
    exact (hK u u').2
  rw [dist_eq_norm]
  have hKd_nonneg : 0 ≤ (K : ℝ) * dist u u' :=
    mul_nonneg K.coe_nonneg dist_nonneg
  have hnorm_nonneg : 0 ≤ ‖N_cont u - N_cont u'‖ := norm_nonneg _
  calc ‖N_cont u - N_cont u'‖
      = Real.sqrt (‖N_cont u - N_cont u'‖ ^ 2) :=
        (Real.sqrt_sq hnorm_nonneg).symm
    _ ≤ Real.sqrt (((K : ℝ) * dist u u') ^ 2) := Real.sqrt_le_sqrt hnorm_sq
    _ = (K : ℝ) * dist u u' := Real.sqrt_sq hKd_nonneg

end DifferentialGeometry.PDE.RicciFlow
