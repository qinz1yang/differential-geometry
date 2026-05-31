import RicciFlower.HCGCompactness.SolutionCompactness

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Hamilton Compactness Theorem Interface

This is the RicciFlower-native theorem shape corresponding to MSM135 Chapter 3,
Theorem "Compactness for solutions".  The real compactness frontier now lives
in `MetricCompactness.metricCompactness`; this file is a public solution-facing
wrapper.
-/

noncomputable section

universe u uE uH

namespace RicciFlower
namespace HCGCompactness

open scoped Manifold ContDiff

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}

/-- Hamilton--Cheeger--Gromov compactness for pointed Ricci-flow solutions.

A sequence of complete pointed Ricci-flow solutions on a common real time
interval admits a smoothly convergent pointed subsequence once the time-zero
metric compactness inputs, spacetime derivative input, and smooth-flow upgrade
backend are supplied.  This is the honest theorem-facing form of MSM135
Theorem 3.10 before Shi estimates and spacetime Arzela--Ascoli are formalized.

The legacy `_hinj : InjInput` argument is retained for import compatibility but
is not the real injectivity-radius hypothesis; the proof consumes
`hflowInj : FlowBaseInjBound`. -/
theorem compactnessSol
    [I.Boundaryless]
    (X : PointedFlowSeq.{u, uE, uH} (I := I))
    (_hcomplete : CompleteInput (I := I) X)
    (_hcurv : CurvBoundInput (I := I) X)
    (_hinj : InjInput (I := I) X)
    (hcomplete0 : SeqMetricComplete (I := I) (X.atZero (I := I)))
    (hflowCurv : SpacetimeCurvBound (I := I) X)
    (hflowInj : FlowBaseInjBound (I := I) X)
    (hderiv : FlowDerivativeInput (I := I) X)
    (hflow : SmoothFlowLimitInput (I := I) X) :
    CompactnessConclusion (I := I) X :=
  solutionCompactness (I := I) X hcomplete0 hflowCurv hflowInj hderiv hflow

/-- Compatibility wrapper for the older HCG interface.

The `NoncollapseInput` argument is not part of the injectivity-radius
compactness theorem itself.  It remains here only because Hamilton Section 12
currently records Perelman noncollapse separately before the future
noncollapse-to-injectivity bridge is formalized.  Likewise, `_hinj : InjInput`
is legacy compatibility data; `hflowInj : FlowBaseInjBound` is the contentful
basepoint injectivity-radius input. -/
theorem hamiltonCompactness
    [I.Boundaryless]
    (X : PointedFlowSeq.{u, uE, uH} (I := I))
    (_hcomplete : CompleteInput (I := I) X)
    (_hcurv : CurvBoundInput (I := I) X)
    (_hinj : InjInput (I := I) X)
    (_hnoncollapse : NoncollapseInput (I := I) X)
    (hcomplete0 : SeqMetricComplete (I := I) (X.atZero (I := I)))
    (hflowCurv : SpacetimeCurvBound (I := I) X)
    (hflowInj : FlowBaseInjBound (I := I) X)
    (hderiv : FlowDerivativeInput (I := I) X)
    (hflow : SmoothFlowLimitInput (I := I) X) :
    CompactnessConclusion (I := I) X :=
  compactnessSol (I := I) X _hcomplete _hcurv _hinj
    hcomplete0 hflowCurv hflowInj hderiv hflow

end HCGCompactness
end RicciFlower
