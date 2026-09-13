import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.Deformation


noncomputable section

open Bundle Manifold Set MeasureTheory Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Families

open Surgery.Topology Width CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
    [SigmaCompactSpace Q] [hT2 : T2Space Q] [hCompact : CompactSpace Q]
    [hConnected : ConnectedSpace Q] [hBoundary : I.Boundaryless]
    {D : RealTimeInterval} {a b : ℝ}

include hT2 hCompact hConnected hBoundary

omit [SigmaCompactSpace Q] hBoundary in
theorem rfs_rampAlternativeData_of_frontier
    (B : RicciBackground (I := I) (M := Q) D a b)
    (hdim : Module.finrank ℝ E = 3) (ell epsilon : ℝ) (hell : 0 < ell) (hepsilon : 0 < epsilon)
    (hproduct : RampProductBounds (I := I) (Q := Q) (D := D) (a := a) (b := b) B)
    (harea : ∀ A : ℝ, 0 ≤ A →
      RampAreaBounds (I := I) (Q := Q) (D := D) (a := a) (b := b) B A)
    (hwindow : ∀ (L Theta A : ℝ), 0 ≤ L → 0 ≤ Theta → 0 ≤ A →
      ∀ eta : ℝ, 0 < eta → eta < 1 → ∀ threshold : ℝ, 1 ≤ threshold →
      ∀ d : ℝ, 0 < d →
        RampWindowInput (I := I) (Q := Q) (D := D) (a := a) (b := b) B L Theta A ell eta
          threshold d) :
    RampAlternativeData (I := I) (Q := Q) (D := D) (a := a) (b := b) B ell epsilon := by
  intro L Theta A hL hTheta hA
  exact rfs_uniform_ramp_alternative_of_frontier B hdim L Theta A hL hTheta hA ell (epsilon / 2)
    hell (by linarith) hproduct (harea A hA) (hwindow L Theta A hL hTheta hA)

omit [SigmaCompactSpace Q] hCompact hConnected hBoundary in
theorem rfs_preparedFamilyFlowData_of_frontier
    (B : RicciBackground (I := I) (M := Q) D a b) {d : ℕ}
    (e : SmoothLoopEmbedding (I := I) (Q := Q) d) (L₀ Theta₀ : ℝ)
    (hinit : ∀ (lambda : ℝ), 0 < lambda → lambda ≤ 1 →
      ∀ prepared : RegularFamily (I := I) (Q := Q) (Sphere 2),
        HasContinuousSmoothLoopJets e prepared →
        ∀ p, (initialRamp (prepared p).1).SmoothOn (I := I) {0} ∧
          (initialRamp (prepared p).1).length (fun _ => B.family.metric a) lambda 0 ≤
            L₀ ∧
          (initialRamp (prepared p).1).totalCurvature (fun _ => B.family.metric a) lambda 0 ≤
            Theta₀)
    (hsolutions : ∀ (lambda : ℝ), 0 < lambda → lambda ≤ 1 →
      ∀ prepared : RegularFamily (I := I) (Q := Q) (Sphere 2),
        HasContinuousSmoothLoopJets e prepared →
        RampFamilyFlowSolutions (I := I) (Q := Q) (D := D) (a := a) (b := b) B e prepared
          lambda)
    (hprojected : ∀ (lambda : ℝ), 0 < lambda → lambda ≤ 1 →
      ∀ prepared : RegularFamily (I := I) (Q := Q) (Sphere 2),
        HasContinuousSmoothLoopJets e prepared →
        RampFamilyProjectedDeformation (I := I) (Q := Q) (D := D) (a := a) (b := b) B e prepared
          lambda) :
    PreparedFamilyFlowData (I := I) (Q := Q) (D := D) (a := a) (b := b) B e L₀ Theta₀ := by
  intro lambda hlambda hlambda_one prepared hsmooth
  obtain ⟨solutions, projected, hcont, hdata, hprojeq, hat, hjets, hclass⟩ :=
    rfs_prepared_family_flow_of_frontier B e prepared hsmooth lambda hlambda hlambda_one
      (hsolutions lambda hlambda hlambda_one prepared hsmooth)
      (hprojected lambda hlambda hlambda_one prepared hsmooth)
  exact ⟨solutions, projected, hcont,
    (fun p => ⟨(hdata p).1, (hdata p).2.1, (hdata p).2.2.1⟩), hprojeq, hat, hjets, hclass,
    rfs_prepared_family_solution_initial_bounds B lambda L₀ Theta₀ prepared solutions
      (hinit lambda hlambda hlambda_one prepared hsmooth)
      (fun p => (hdata p).1) (fun p z => (hdata p).2.2.2 z)⟩

end DifferentialGeometry.PDE.RicciFlow.Extinction.Families
