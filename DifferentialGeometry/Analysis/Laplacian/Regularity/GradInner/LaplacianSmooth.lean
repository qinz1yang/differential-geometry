import DifferentialGeometry.Analysis.Laplacian.Regularity.Bochner.PolarisedLpFull

/-!
# Full smooth-case discharge of the gradient-inner-Laplacian regularity theorem via the unconditional candidate

For a closed Riemannian manifold `(M, g)`, a smooth scalar
`φ : C^∞⟮I, M; ℝ⟯`, and a smooth scalar `v : SmoothScalar g`, this module
combines the smooth-case `smoothCandidate_identification_target`
(established in `BochnerPolarisedLpFull.lean`, conditional on the
Hessian-bridge hypothesis) with the existing variational identity
infrastructure
(`gradInnerCLM_smoothToH1Compl_eq_H1ComplToLp_resolvent_smoothCandidate`)
to deliver the full smooth-case regularity theorem via the unconditional
Bochner candidate's resolvent:

```
gradInnerCLM g φ (smoothToH1Compl v) =
  H1ComplToLp(resolvent g (gradInnerLaplacianCandidateUnconditional g φ
                              (smoothToH1Compl_mem_laplacianDomainPow_two g v)))
```

This is the **conditional** smooth-case regularity theorem: conditional
on the Hessian-bridge hypothesis identifying the chart-side Hessian
pairing with the smooth Hessian pairing for `smoothToH1Compl v`.

## Main results

* `gradInnerCLM_eq_H1ComplToLp_resolvent_unconditional_smooth_of_hessHypothesis`
  — the smooth-case regularity theorem in resolvent-of-candidate form,
  conditional on the Hessian-bridge hypothesis.

* `smoothCase_full_unconditional_of_hessHypothesis` — the smooth-case
  regularity theorem (image membership form), conditional on the
  Hessian-bridge hypothesis.

* `smoothMulH1Compl_smoothToH1Compl_mem_laplacianDomainPow_two_via_candidate` —
  the iterated-closure form of the smooth-case conclusion via the
  unconditional candidate's resolvent (conditional on the Hessian-bridge
  hypothesis).

## Hessian-bridge hypothesis

The hypothesis takes the form:

```
hessPairingLpOnLapDom g φ (...) = hessPairingSmoothLp g φ v
```

where the LHS uses the chart-side weak Hessian of `smoothToH1Compl v`
(via the `LaplacianDomain` chart machinery) and the RHS uses the smooth
chart Hessian of `v` directly. The two are pointwise equal on smooth
inputs (by `laplacianDomainHessianChart_smooth_case` and chart-pullback
identifications), but bridging at the `Lp 2` class level requires
substantial chart machinery and is reserved for follow-up work.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace GradInnerLaplacianSmoothFull

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
open DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianCandidate
open DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianVariational
open DifferentialGeometry.Analysis.Laplacian.RicciPairingCLM
open DifferentialGeometry.Analysis.Laplacian.GradInnerLaplacianFinal
open DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLpFull

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- **The smooth-case regularity theorem, resolvent-of-candidate form,
conditional on the Hessian-bridge hypothesis.** For smooth `v`, the
gradient inner product `gradInnerCLM g φ (smoothToH1Compl v)` equals
`H1ComplToLp` of the resolvent of the unconditional Bochner candidate. -/
theorem gradInnerCLM_eq_H1ComplToLp_resolvent_unconditional_smooth_of_hessHypothesis
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (h_hess :
      hessPairingLpOnLapDom (I := I) (M := M) g φ
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1
            (smoothToH1Compl_mem_laplacianDomainPow_two
              (I := I) (M := M) g v)) =
        hessPairingSmoothLp (I := I) (M := M) g φ v) :
    gradInnerCLM (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g v) =
      H1ComplToLp (I := I) (M := M) g
        (resolvent (I := I) (M := M) g
          (gradInnerLaplacianCandidateUnconditional (I := I) (M := M) g φ
            (smoothToH1Compl_mem_laplacianDomainPow_two
              (I := I) (M := M) g v))) :=
  smoothCase_via_candidate_identification (I := I) (M := M) g φ v
    (smoothCandidate_identification_target_of_hessHypothesis
      (I := I) (M := M) g φ v h_hess)

/-- **The smooth-case conclusion via the unconditional candidate's
resolvent, conditional on the Hessian-bridge hypothesis**. For smooth `v`,
`gradInnerCLM g φ (smoothToH1Compl v)` lies in `H1ComplToLp ''
laplacianDomain g`, with the witness being the resolvent of the
unconditional Bochner candidate. -/
theorem smoothCase_full_unconditional_of_hessHypothesis
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (h_hess :
      hessPairingLpOnLapDom (I := I) (M := M) g φ
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1
            (smoothToH1Compl_mem_laplacianDomainPow_two
              (I := I) (M := M) g v)) =
        hessPairingSmoothLp (I := I) (M := M) g φ v) :
    gradInnerCLM (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g v) ∈
      Set.image (H1ComplToLp (I := I) (M := M) g)
        (laplacianDomain (I := I) (M := M) g : Set (H1Compl g)) :=
  gradInnerCLM_smoothCase_mem_image_laplacianDomain_via_candidate
    (I := I) (M := M) g φ v
    (smoothCandidate_identification_target_of_hessHypothesis
      (I := I) (M := M) g φ v h_hess)

/-- **Smooth-case iterated closure via the unconditional candidate**.
For smooth `v`, `smoothMulH1Compl g φ (smoothToH1Compl v) ∈
laplacianDomainPow g 2`, with the witness construction going through the
resolvent of the unconditional Bochner candidate (conditional on the
Hessian-bridge hypothesis). -/
theorem smoothMulH1Compl_smoothToH1Compl_mem_laplacianDomainPow_two_via_candidate
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (h_hess :
      hessPairingLpOnLapDom (I := I) (M := M) g φ
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1
            (smoothToH1Compl_mem_laplacianDomainPow_two
              (I := I) (M := M) g v)) =
        hessPairingSmoothLp (I := I) (M := M) g φ v) :
    smoothMulH1Compl (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g v) ∈
      laplacianDomainPow (I := I) (M := M) g 2 :=
  smoothMulH1Compl_mem_pow_two_of_variational_identity
    (I := I) (M := M) g φ
    (smoothToH1Compl_mem_laplacianDomainPow_two (I := I) (M := M) g v)
    (gradInnerCLM_eq_H1ComplToLp_resolvent_unconditional_smooth_of_hessHypothesis
      (I := I) (M := M) g φ v h_hess)

/-- Compact restatement: the smooth-case variational identity holds for
the unconditional candidate, conditional on the Hessian bridge. -/
theorem smoothCase_variational_identity_of_hessHypothesis
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g)
    (h_hess :
      hessPairingLpOnLapDom (I := I) (M := M) g φ
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1
            (smoothToH1Compl_mem_laplacianDomainPow_two
              (I := I) (M := M) g v)) =
        hessPairingSmoothLp (I := I) (M := M) g φ v) :
    gradInnerCLM (I := I) (M := M) g φ
        (smoothToH1Compl (I := I) (M := M) g v) =
      H1ComplToLp (I := I) (M := M) g
        (resolvent (I := I) (M := M) g
          (gradInnerLaplacianCandidateUnconditional (I := I) (M := M) g φ
            (smoothToH1Compl_mem_laplacianDomainPow_two
              (I := I) (M := M) g v))) :=
  gradInnerCLM_eq_H1ComplToLp_resolvent_unconditional_smooth_of_hessHypothesis
    (I := I) (M := M) g φ v h_hess

end GradInnerLaplacianSmoothFull
end Laplacian
end Analysis
end DifferentialGeometry

end
