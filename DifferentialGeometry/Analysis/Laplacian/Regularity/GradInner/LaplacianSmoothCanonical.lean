import DifferentialGeometry.Analysis.Laplacian.Regularity.Hessian.BridgeSmoothLp
import DifferentialGeometry.Analysis.Laplacian.Regularity.GradInner.LaplacianSmooth

/-!
# Full smooth-case gradient-inner-Laplacian regularity theorem (unconditional on
the Christoffel discharge + per-chart transferability hypotheses)

For a closed Riemannian manifold `(M, g)`, a smooth scalar
`φ : C^∞⟮I, M; ℝ⟯`, and a smooth scalar `v : SmoothScalar g`, this module
combines the smooth-case Lp-class Hessian bridge (delivered conditional on
`christoffelDischargeSmoothCase` + `perChartAeTransferableSmoothCase` in
`HessianBridgeSmoothLp`) with the existing smooth-case regularity theorem
(conditional on the Hessian bridge in `GradInnerLaplacianSmoothFull`)
to deliver the **full smooth-case regularity theorem** conditional only on
the two clean hypotheses.

## Hypotheses

The smooth-case regularity theorem is now conditional on two clean
hypotheses (replacing the broader Hessian-bridge hypothesis):

1. **Christoffel discharge** (`christoffelDischargeSmoothCase g φ v`):
   the POU-weighted Christoffel diff vanishes pointwise.

2. **Per-chart ae-transferability** (`perChartAeTransferableSmoothCase g φ v`):
   per-chart LapDom contribution ae-equals POU-weighted Euclidean pairing.

## Main results

* `gradInnerCLM_eq_H1ComplToLp_resolvent_unconditional_smooth_of_christoffel_discharge`
  — the smooth-case regularity theorem in resolvent-of-candidate form,
  conditional on both hypotheses.

* `smoothCase_full_unconditional_of_christoffel_discharge`
  — the smooth-case image-membership form, conditional on both.

* `smoothMulH1Compl_smoothToH1Compl_mem_laplacianDomainPow_two_unconditional_of_christoffel_discharge`
  — the iterated-closure form, conditional on both.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace GradInnerLaplacianSmoothCanonical

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Laplacian.GradInnerLpIdentity
open DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Laplacian.HessianPairingChart
open DifferentialGeometry.Analysis.Laplacian.HessianPairingLapDom
open DifferentialGeometry.Analysis.Laplacian.HessianBridgeSmoothLp
open DifferentialGeometry.Analysis.Laplacian.HessianChartAlphaChristoffelDischarge
open DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianCandidate
open DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational
open DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM
open DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianFinal
open DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLpFull
open DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianSmoothFull

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- **Smooth-case regularity theorem, resolvent-of-candidate form, conditional
on Christoffel discharge and per-chart transferability.** -/
theorem gradInnerCLM_eq_H1ComplToLp_resolvent_unconditional_smooth_of_christoffel_discharge
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (h_transfer : perChartAeTransferableSmoothCase (I := I) (M := M) g φ v)
    (h_discharge : christoffelDischargeSmoothCase (I := I) (M := M) g φ v) :
    gradInnerCLM (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g v) =
      H1ComplToLp (I := I) (M := M) g
        (resolvent (I := I) (M := M) g
          (gradInnerLaplacianCandidateUnconditional (I := I) (M := M) g φ
            (smoothToH1Compl_mem_laplacianDomainPow_two
              (I := I) (M := M) g v))) :=
  gradInnerCLM_eq_H1ComplToLp_resolvent_unconditional_smooth_of_hessHypothesis
    (I := I) (M := M) g φ v
    (hessPairingLpOnLapDom_eq_hessPairingSmoothLp_smoothCase_connector
      (I := I) (M := M) g φ v h_transfer h_discharge)

/-- **Smooth-case conclusion (image-membership form) via the unconditional
candidate, conditional on Christoffel discharge and per-chart transferability.** -/
theorem smoothCase_full_unconditional_of_christoffel_discharge
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (h_transfer : perChartAeTransferableSmoothCase (I := I) (M := M) g φ v)
    (h_discharge : christoffelDischargeSmoothCase (I := I) (M := M) g φ v) :
    gradInnerCLM (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g v) ∈
      Set.image (H1ComplToLp (I := I) (M := M) g)
        (laplacianDomain (I := I) (M := M) g : Set (H1Compl g)) :=
  smoothCase_full_unconditional_of_hessHypothesis
    (I := I) (M := M) g φ v
    (hessPairingLpOnLapDom_eq_hessPairingSmoothLp_smoothCase_connector
      (I := I) (M := M) g φ v h_transfer h_discharge)

/-- **Smooth-case iterated-closure form via the unconditional candidate,
conditional on Christoffel discharge and per-chart transferability.** -/
theorem smoothMulH1Compl_smoothToH1Compl_mem_laplacianDomainPow_two_unconditional_of_christoffel_discharge
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (h_transfer : perChartAeTransferableSmoothCase (I := I) (M := M) g φ v)
    (h_discharge : christoffelDischargeSmoothCase (I := I) (M := M) g φ v) :
    smoothMulH1Compl (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g v) ∈
      laplacianDomainPow (I := I) (M := M) g 2 :=
  smoothMulH1Compl_smoothToH1Compl_mem_laplacianDomainPow_two_via_candidate
    (I := I) (M := M) g φ v
    (hessPairingLpOnLapDom_eq_hessPairingSmoothLp_smoothCase_connector
      (I := I) (M := M) g φ v h_transfer h_discharge)

/-- **Compact restatement.** The smooth-case variational identity holds
for the unconditional candidate, conditional on Christoffel discharge and
per-chart transferability. -/
theorem smoothCase_variational_identity_unconditional_of_christoffel_discharge
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (h_transfer : perChartAeTransferableSmoothCase (I := I) (M := M) g φ v)
    (h_discharge : christoffelDischargeSmoothCase (I := I) (M := M) g φ v) :
    gradInnerCLM (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g v) =
      H1ComplToLp (I := I) (M := M) g
        (resolvent (I := I) (M := M) g
          (gradInnerLaplacianCandidateUnconditional (I := I) (M := M) g φ
            (smoothToH1Compl_mem_laplacianDomainPow_two
              (I := I) (M := M) g v))) :=
  gradInnerCLM_eq_H1ComplToLp_resolvent_unconditional_smooth_of_christoffel_discharge
    (I := I) (M := M) g φ v h_transfer h_discharge

/-- **Smooth-case regularity theorem, resolvent-of-candidate form, conditional
only on the Christoffel discharge.** Per-chart ae-transferability is discharged
unconditionally upstream. -/
theorem gradInnerCLM_eq_H1ComplToLp_resolvent_smoothCase_of_discharge
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (h_discharge : christoffelDischargeSmoothCase (I := I) (M := M) g φ v) :
    gradInnerCLM (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g v) =
      H1ComplToLp (I := I) (M := M) g
        (resolvent (I := I) (M := M) g
          (gradInnerLaplacianCandidateUnconditional (I := I) (M := M) g φ
            (smoothToH1Compl_mem_laplacianDomainPow_two
              (I := I) (M := M) g v))) :=
  gradInnerCLM_eq_H1ComplToLp_resolvent_unconditional_smooth_of_christoffel_discharge
    (I := I) (M := M) g φ v
    (perChartAeTransferableSmoothCase_holds (I := I) (M := M) g φ v) h_discharge

/-- **Smooth-case conclusion (image-membership form), conditional only on
the Christoffel discharge.** -/
theorem smoothCase_full_of_discharge
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (h_discharge : christoffelDischargeSmoothCase (I := I) (M := M) g φ v) :
    gradInnerCLM (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g v) ∈
      Set.image (H1ComplToLp (I := I) (M := M) g)
        (laplacianDomain (I := I) (M := M) g : Set (H1Compl g)) :=
  smoothCase_full_unconditional_of_christoffel_discharge
    (I := I) (M := M) g φ v
    (perChartAeTransferableSmoothCase_holds (I := I) (M := M) g φ v) h_discharge

/-- **Smooth-case iterated-closure form, conditional only on the Christoffel
discharge.** -/
theorem smoothMulH1Compl_smoothToH1Compl_mem_laplacianDomainPow_two_of_discharge
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (h_discharge : christoffelDischargeSmoothCase (I := I) (M := M) g φ v) :
    smoothMulH1Compl (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g v) ∈
      laplacianDomainPow (I := I) (M := M) g 2 :=
  smoothMulH1Compl_smoothToH1Compl_mem_laplacianDomainPow_two_unconditional_of_christoffel_discharge
    (I := I) (M := M) g φ v
    (perChartAeTransferableSmoothCase_holds (I := I) (M := M) g φ v) h_discharge

/-- **Headline compact restatement, conditional only on the Christoffel
discharge.** -/
theorem smoothCase_variational_identity_of_discharge
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (h_discharge : christoffelDischargeSmoothCase (I := I) (M := M) g φ v) :
    gradInnerCLM (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g v) =
      H1ComplToLp (I := I) (M := M) g
        (resolvent (I := I) (M := M) g
          (gradInnerLaplacianCandidateUnconditional (I := I) (M := M) g φ
            (smoothToH1Compl_mem_laplacianDomainPow_two
              (I := I) (M := M) g v))) :=
  gradInnerCLM_eq_H1ComplToLp_resolvent_smoothCase_of_discharge
    (I := I) (M := M) g φ v h_discharge

end GradInnerLaplacianSmoothCanonical
end Laplacian
end Analysis
end DifferentialGeometry

end
