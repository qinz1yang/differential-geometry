import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.RampFamilyExtinctionReduction

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

def RampFamilyDeformationProducers (B : RicciBackground (I := I) (M := Q) D a b)
    {d : ℕ} (e : SmoothLoopEmbedding (I := I) (Q := Q) d)
    (Γ : RegularFamily (I := I) (Q := Q) (Sphere 2)) (ell epsilon : ℝ) : Prop :=
  ∃ L₀ Theta₀ Ainit : ℝ,
    0 ≤ L₀ ∧ 0 ≤ Theta₀ ∧ 0 ≤ Ainit ∧
      (∀ (lambda : ℝ), 0 < lambda → lambda ≤ 1 →
        ∀ prepared : RegularFamily (I := I) (Q := Q) (Sphere 2),
          HasContinuousSmoothLoopJets e prepared →
          @Continuous (Sphere 2) (ProductCurve Q) inferInstance
            (smoothProductInitialTopology e a) (fun p => initialRamp ((prepared p).1))) ∧
      (∀ (lambda : ℝ), 0 < lambda → lambda ≤ 1 →
        RampExistenceInput (I := I) (M := Q) (D := D) (a := a) (b := b) B lambda) ∧
      (∀ (lambda : ℝ), 0 < lambda → lambda ≤ 1 →
        RampFamilyInput (I := I) (M := Q) (D := D) (a := a) (b := b) (N := d) B lambda e) ∧
      PreparedFamilyInitialLengthCurvatureFront (I := I) (Q := Q) (D := D) (a := a) (b := b)
        B e L₀ Theta₀ ∧
      RampFamilyProjectedDeformationFrontier (I := I) (Q := Q) (D := D) (a := a) (b := b) B e ∧
      PreparedFamilyApproximation (I := I) (Q := Q) (D := D) (a := a) (b := b)
        B e Γ L₀ Theta₀ Ainit ∧
      RampAlternativeData (I := I) (Q := Q) (D := D) (a := a) (b := b) B ell epsilon

theorem rfs_family_deformation_of_producers (B : RicciBackground (I := I) (M := Q) D a b)
    {d : ℕ} (e : SmoothLoopEmbedding (I := I) (Q := Q) d)
    (Γ : RegularFamily (I := I) (Q := Q) (Sphere 2))
    (epsilon ell : ℝ) (hepsilon : 0 < epsilon)
    (h : RampFamilyDeformationProducers (I := I) (Q := Q) (D := D) (a := a) (b := b)
      B e Γ ell epsilon) :
    ∃ lambda : ℝ, 0 < lambda ∧ lambda ≤ 1 ∧
      ∃ solutions : Sphere 2 → ProductCurve Q,
        ∃ deformed : C(Icc a b, RegularFamily (I := I) (Q := Q) (Sphere 2)),
          @Continuous (Sphere 2) (ProductCurve Q) inferInstance
            (smoothProductCylinderTopology e (Icc a b)) solutions ∧
          (∀ p, (solutions p).IsSolutionOn B.family.metric lambda (Icc a b) ∧
            (solutions p).IsRampOn B.family.metric lambda (Icc a b) ∧ (solutions p).degree = 1) ∧
          (∀ t : Icc a b, ∀ p z,
            ((deformed t) p).1 z = (solutions p).projection z t) ∧
          (∀ t : Icc a b, HasContinuousSmoothLoopJets e (deformed t) ∧
            FreeHomotopyClass.mk (contractibleRegularLoopInclusion.comp (deformed t)) =
              FreeHomotopyClass.mk (contractibleRegularLoopInclusion.comp Γ)) ∧
          (∀ p, |regularLeastArea (B.family.metric a) ((deformed ⟨a, le_rfl, B.lt.le⟩) p) -
            regularLeastArea (B.family.metric a) (Γ p)| < epsilon) ∧
          ∀ p,
            loopLength (B.family.metric b)
              (((deformed ⟨b, B.lt.le, le_rfl⟩) p).1.toContinuousLoop) < ell ∨
            regularLeastArea (B.family.metric b) ((deformed ⟨b, B.lt.le, le_rfl⟩) p) ≤
              affineComparison B.family a b (regularLeastArea (B.family.metric a) (Γ p)) + epsilon := by
  obtain ⟨L₀, Theta₀, Ainit, hL₀, hTheta₀, hAinit, hcontinuous, hexists, hfamily, hbounds,
    hprojected, hprepared, halt⟩ := h
  exact rfs_family_deformation_of_ramp_producers B e Γ epsilon ell hepsilon L₀ Theta₀ Ainit
    hL₀ hTheta₀ hAinit hcontinuous hexists hfamily hbounds hprojected hprepared halt

end DifferentialGeometry.PDE.RicciFlow.Extinction.Families
