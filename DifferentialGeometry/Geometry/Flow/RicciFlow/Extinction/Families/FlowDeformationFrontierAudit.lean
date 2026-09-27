import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.FlowReduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.RampFrontierData



noncomputable section

open Bundle Manifold Set MeasureTheory
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

omit [SigmaCompactSpace Q] hCompact hConnected hBoundary in
def RampFamilyFlowSolutionsFrontier (B : RicciBackground (I := I) (M := Q) D a b) {d : ℕ}
    (e : SmoothLoopEmbedding (I := I) (Q := Q) d) : Prop :=
  ∀ (lambda : ℝ), 0 < lambda → lambda ≤ 1 →
    ∀ prepared : RegularFamily (I := I) (Q := Q) (Sphere 2),
      HasContinuousSmoothLoopJets e prepared →
      RampFamilyFlowSolutions (I := I) (Q := Q) (D := D) (a := a) (b := b) B e prepared lambda

omit [SigmaCompactSpace Q] hCompact hConnected hBoundary in
def RampFamilyProjectedDeformationFrontier (B : RicciBackground (I := I) (M := Q) D a b)
    {d : ℕ} (e : SmoothLoopEmbedding (I := I) (Q := Q) d) : Prop :=
  ∀ (lambda : ℝ), 0 < lambda → lambda ≤ 1 →
    ∀ prepared : RegularFamily (I := I) (Q := Q) (Sphere 2),
      HasContinuousSmoothLoopJets e prepared →
      RampFamilyProjectedDeformation (I := I) (Q := Q) (D := D) (a := a) (b := b) B e prepared
        lambda

omit [SigmaCompactSpace Q] hCompact hConnected hBoundary in
def PreparedFamilyFlowConclusion (B : RicciBackground (I := I) (M := Q) D a b) {d : ℕ}
    (e : SmoothLoopEmbedding (I := I) (Q := Q) d) : Prop :=
  ∀ (lambda : ℝ), 0 < lambda → lambda ≤ 1 →
    ∀ prepared : RegularFamily (I := I) (Q := Q) (Sphere 2),
      HasContinuousSmoothLoopJets e prepared →
      ∃ solutions : Sphere 2 → ProductCurve Q,
        ∃ projected : C(Icc a b, RegularFamily (I := I) (Q := Q) (Sphere 2)),
          @Continuous (Sphere 2) (ProductCurve Q) inferInstance
            (smoothProductCylinderTopology e (Icc a b)) solutions ∧
          (∀ p, (solutions p).IsSolutionOn B.family.metric lambda (Icc a b) ∧
            (solutions p).IsRampOn B.family.metric lambda (Icc a b) ∧
            (solutions p).degree = 1 ∧
            ∀ z, (solutions p).map z a = ((prepared p).1 z, z)) ∧
          (∀ t : Icc a b, ∀ p z,
            ((projected t) p).1 z = (solutions p).projection z t) ∧
          projected ⟨a, le_rfl, B.lt.le⟩ = prepared ∧
          (∀ t : Icc a b, HasContinuousSmoothLoopJets e (projected t)) ∧
          ∀ t : Icc a b,
            FreeHomotopyClass.mk (contractibleRegularLoopInclusion.comp (projected t)) =
              FreeHomotopyClass.mk (contractibleRegularLoopInclusion.comp prepared)

omit [SigmaCompactSpace Q] hCompact hConnected hBoundary in
theorem preparedFamilyFlowInput_iff_rampFamilyFrontiers
    (B : RicciBackground (I := I) (M := Q) D a b) {d : ℕ}
    (e : SmoothLoopEmbedding (I := I) (Q := Q) d) :
    PreparedFamilyFlowInput (I := I) (Q := Q) (D := D) (a := a) (b := b) B e ↔
      RampFamilyFlowSolutionsFrontier (I := I) (Q := Q) (D := D) (a := a) (b := b) B e ∧
        RampFamilyProjectedDeformationFrontier (I := I) (Q := Q) (D := D) (a := a) (b := b)
          B e :=
  Iff.rfl

omit [SigmaCompactSpace Q] hCompact hConnected hBoundary in
theorem rampFamilyFlowSolutionsFrontier_of_input
    (B : RicciBackground (I := I) (M := Q) D a b) {d : ℕ}
    (e : SmoothLoopEmbedding (I := I) (Q := Q) d)
    (h : PreparedFamilyFlowInput (I := I) (Q := Q) (D := D) (a := a) (b := b) B e) :
    RampFamilyFlowSolutionsFrontier (I := I) (Q := Q) (D := D) (a := a) (b := b) B e :=
  h.1

omit [SigmaCompactSpace Q] hCompact hConnected hBoundary in
theorem preparedFamilyFlowInput_of_conclusion_and_unique
    (B : RicciBackground (I := I) (M := Q) D a b) {d : ℕ}
    (e : SmoothLoopEmbedding (I := I) (Q := Q) d)
    (hunique : ∀ (lambda : ℝ), 0 < lambda → lambda ≤ 1 →
      ∀ prepared : RegularFamily (I := I) (Q := Q) (Sphere 2),
        HasContinuousSmoothLoopJets e prepared →
        ∀ s₁ s₂ : Sphere 2 → ProductCurve Q,
          (∀ p, (s₁ p).IsSolutionOn B.family.metric lambda (Icc a b) ∧
            (s₁ p).IsRampOn B.family.metric lambda (Icc a b) ∧ (s₁ p).degree = 1 ∧
            ∀ z, (s₁ p).map z a = ((prepared p).1 z, z)) →
          (∀ p, (s₂ p).IsSolutionOn B.family.metric lambda (Icc a b) ∧
            (s₂ p).IsRampOn B.family.metric lambda (Icc a b) ∧ (s₂ p).degree = 1 ∧
            ∀ z, (s₂ p).map z a = ((prepared p).1 z, z)) →
          s₁ = s₂)
    (hc : PreparedFamilyFlowConclusion (I := I) (Q := Q) (D := D) (a := a) (b := b) B e) :
    PreparedFamilyFlowInput (I := I) (Q := Q) (D := D) (a := a) (b := b) B e := by
  refine ⟨fun lambda hlambda hlambda_one prepared hsmooth => ?_, ?_⟩
  · obtain ⟨solutions, _projected, hcont, hdata, _hproj, _hat, _hjets, _hclass⟩ :=
      hc lambda hlambda hlambda_one prepared hsmooth
    exact ⟨solutions, hcont, hdata⟩
  · intro lambda hlambda hlambda_one prepared hsmooth solutions hcont hdata
    obtain ⟨sol, projected, _hcont', hdata', hproj, hat, hjets, hclass⟩ :=
      hc lambda hlambda hlambda_one prepared hsmooth
    have heq : solutions = sol :=
      hunique lambda hlambda hlambda_one prepared hsmooth solutions sol hdata hdata'
    subst heq
    exact ⟨projected, hproj, hat, hjets, hclass⟩

omit [SigmaCompactSpace Q] hCompact hConnected hBoundary in
theorem preparedFamilyFlowConclusion_of_input
    (B : RicciBackground (I := I) (M := Q) D a b) {d : ℕ}
    (e : SmoothLoopEmbedding (I := I) (Q := Q) d)
    (h : PreparedFamilyFlowInput (I := I) (Q := Q) (D := D) (a := a) (b := b) B e) :
    PreparedFamilyFlowConclusion (I := I) (Q := Q) (D := D) (a := a) (b := b) B e :=
  fun lambda hlambda hlambda_one prepared hsmooth =>
    rfs_prepared_family_flow_of_frontier B e prepared hsmooth lambda hlambda hlambda_one
      (h.1 lambda hlambda hlambda_one prepared hsmooth)
      (h.2 lambda hlambda hlambda_one prepared hsmooth)

theorem rampFamilyFlowSolutionsFrontier_of_ramp_fronts
    (B : RicciBackground (I := I) (M := Q) D a b) {d : ℕ}
    (e : SmoothLoopEmbedding (I := I) (Q := Q) d)
    (hcontinuous : ∀ (lambda : ℝ), 0 < lambda → lambda ≤ 1 →
      ∀ prepared : RegularFamily (I := I) (Q := Q) (Sphere 2),
        HasContinuousSmoothLoopJets e prepared →
        @Continuous (Sphere 2) (ProductCurve Q) inferInstance
          (smoothProductInitialTopology e a) (fun p => initialRamp ((prepared p).1)))
    (hexists : ∀ (lambda : ℝ), 0 < lambda → lambda ≤ 1 →
      RampExistenceInput (I := I) (M := Q) (D := D) (a := a) (b := b) B lambda)
    (hfamily : ∀ (lambda : ℝ), 0 < lambda → lambda ≤ 1 →
      RampFamilyInput (I := I) (M := Q) (D := D) (a := a) (b := b) (N := d) B lambda e) :
    RampFamilyFlowSolutionsFrontier (I := I) (Q := Q) (D := D) (a := a) (b := b) B e :=
  fun lambda hlambda hlambda_one prepared hsmooth =>
    rfs_rampFamilyFlowSolutions_of_ramp_frontiers B e prepared hsmooth lambda hlambda hlambda_one
      (hcontinuous lambda hlambda hlambda_one prepared hsmooth)
      (hexists lambda hlambda hlambda_one) (hfamily lambda hlambda hlambda_one)

omit [SigmaCompactSpace Q] hCompact hConnected hBoundary in
theorem preparedFamilyFlowInput_iff_conclusion_and_projected
    (B : RicciBackground (I := I) (M := Q) D a b) {d : ℕ}
    (e : SmoothLoopEmbedding (I := I) (Q := Q) d) :
    PreparedFamilyFlowInput (I := I) (Q := Q) (D := D) (a := a) (b := b) B e ↔
      PreparedFamilyFlowConclusion (I := I) (Q := Q) (D := D) (a := a) (b := b) B e ∧
        RampFamilyProjectedDeformationFrontier (I := I) (Q := Q) (D := D) (a := a) (b := b)
          B e := by
  constructor
  · intro h
    exact ⟨preparedFamilyFlowConclusion_of_input B e h, h.2⟩
  · rintro ⟨hc, hproj⟩
    refine ⟨fun lambda hlambda hlambda_one prepared hsmooth => ?_, hproj⟩
    obtain ⟨solutions, _projected, hcont, hdata, _hproj, _hat, _hjets, _hclass⟩ :=
      hc lambda hlambda hlambda_one prepared hsmooth
    exact ⟨solutions, hcont, hdata⟩

theorem rfs_prepared_family_flow_of_projected_frontier
    (B : RicciBackground (I := I) (M := Q) D a b) {d : ℕ}
    (e : SmoothLoopEmbedding (I := I) (Q := Q) d)
    (hcontinuous : ∀ (lambda : ℝ), 0 < lambda → lambda ≤ 1 →
      ∀ prepared : RegularFamily (I := I) (Q := Q) (Sphere 2),
        HasContinuousSmoothLoopJets e prepared →
        @Continuous (Sphere 2) (ProductCurve Q) inferInstance
          (smoothProductInitialTopology e a) (fun p => initialRamp ((prepared p).1)))
    (hexists : ∀ (lambda : ℝ), 0 < lambda → lambda ≤ 1 →
      RampExistenceInput (I := I) (M := Q) (D := D) (a := a) (b := b) B lambda)
    (hfamily : ∀ (lambda : ℝ), 0 < lambda → lambda ≤ 1 →
      RampFamilyInput (I := I) (M := Q) (D := D) (a := a) (b := b) (N := d) B lambda e)
    (hprojected : RampFamilyProjectedDeformationFrontier (I := I) (Q := Q) (D := D) (a := a)
      (b := b) B e)
    (prepared : RegularFamily (I := I) (Q := Q) (Sphere 2))
    (hsmooth : HasContinuousSmoothLoopJets e prepared)
    (lambda : ℝ) (hlambda : 0 < lambda) (hlambda_one : lambda ≤ 1) :
    ∃ solutions : Sphere 2 → ProductCurve Q,
      ∃ projected : C(Icc a b, RegularFamily (I := I) (Q := Q) (Sphere 2)),
        @Continuous (Sphere 2) (ProductCurve Q) inferInstance
          (smoothProductCylinderTopology e (Icc a b)) solutions ∧
        (∀ p, (solutions p).IsSolutionOn B.family.metric lambda (Icc a b) ∧
          (solutions p).IsRampOn B.family.metric lambda (Icc a b) ∧
          (solutions p).degree = 1 ∧
          ∀ z, (solutions p).map z a = ((prepared p).1 z, z)) ∧
        (∀ t : Icc a b, ∀ p z,
          ((projected t) p).1 z = (solutions p).projection z t) ∧
        projected ⟨a, le_rfl, B.lt.le⟩ = prepared ∧
        (∀ t : Icc a b, HasContinuousSmoothLoopJets e (projected t)) ∧
        ∀ t : Icc a b,
          FreeHomotopyClass.mk (contractibleRegularLoopInclusion.comp (projected t)) =
            FreeHomotopyClass.mk (contractibleRegularLoopInclusion.comp prepared) :=
  rfs_prepared_family_flow_of_frontier B e prepared hsmooth lambda hlambda hlambda_one
    (rfs_rampFamilyFlowSolutions_of_ramp_frontiers B e prepared hsmooth lambda hlambda hlambda_one
      (hcontinuous lambda hlambda hlambda_one prepared hsmooth)
      (hexists lambda hlambda hlambda_one) (hfamily lambda hlambda hlambda_one))
    (hprojected lambda hlambda hlambda_one prepared hsmooth)

omit [SigmaCompactSpace Q] hCompact hConnected hBoundary in
def PreparedFamilyInitialBoundsFront (B : RicciBackground (I := I) (M := Q) D a b) {d : ℕ}
    (e : SmoothLoopEmbedding (I := I) (Q := Q) d) (L₀ Theta₀ : ℝ) : Prop :=
  ∀ (lambda : ℝ), 0 < lambda → lambda ≤ 1 →
    ∀ prepared : RegularFamily (I := I) (Q := Q) (Sphere 2),
      HasContinuousSmoothLoopJets e prepared →
      ∀ p, (initialRamp (prepared p).1).SmoothOn (I := I) {0} ∧
        (initialRamp (prepared p).1).length (fun _ => B.family.metric a) lambda 0 ≤ L₀ ∧
        (initialRamp (prepared p).1).totalCurvature (fun _ => B.family.metric a) lambda 0 ≤
          Theta₀

theorem preparedFamilyFlowData_of_ramp_frontiers
    (B : RicciBackground (I := I) (M := Q) D a b) {d : ℕ}
    (e : SmoothLoopEmbedding (I := I) (Q := Q) d) (L₀ Theta₀ : ℝ)
    (hcontinuous : ∀ (lambda : ℝ), 0 < lambda → lambda ≤ 1 →
      ∀ prepared : RegularFamily (I := I) (Q := Q) (Sphere 2),
        HasContinuousSmoothLoopJets e prepared →
        @Continuous (Sphere 2) (ProductCurve Q) inferInstance
          (smoothProductInitialTopology e a) (fun p => initialRamp ((prepared p).1)))
    (hexists : ∀ (lambda : ℝ), 0 < lambda → lambda ≤ 1 →
      RampExistenceInput (I := I) (M := Q) (D := D) (a := a) (b := b) B lambda)
    (hfamily : ∀ (lambda : ℝ), 0 < lambda → lambda ≤ 1 →
      RampFamilyInput (I := I) (M := Q) (D := D) (a := a) (b := b) (N := d) B lambda e)
    (hbounds : PreparedFamilyInitialBoundsFront (I := I) (Q := Q) (D := D) (a := a) (b := b)
      B e L₀ Theta₀)
    (hprojected : RampFamilyProjectedDeformationFrontier (I := I) (Q := Q) (D := D) (a := a)
      (b := b) B e) :
    PreparedFamilyFlowData (I := I) (Q := Q) (D := D) (a := a) (b := b) B e L₀ Theta₀ :=
  rfs_preparedFamilyFlowData_of_frontier B e L₀ Theta₀ hbounds
    (rampFamilyFlowSolutionsFrontier_of_ramp_fronts B e hcontinuous hexists hfamily) hprojected

theorem rfs_family_deformation_of_projected_frontier
    (B : RicciBackground (I := I) (M := Q) D a b) {d : ℕ}
    (e : SmoothLoopEmbedding (I := I) (Q := Q) d)
    (Γ : RegularFamily (I := I) (Q := Q) (Sphere 2))
    (epsilon ell : ℝ) (hepsilon : 0 < epsilon)
    (L₀ Theta₀ Ainit : ℝ) (hL₀ : 0 ≤ L₀) (hTheta₀ : 0 ≤ Theta₀) (hAinit : 0 ≤ Ainit)
    (hcontinuous : ∀ (lambda : ℝ), 0 < lambda → lambda ≤ 1 →
      ∀ prepared : RegularFamily (I := I) (Q := Q) (Sphere 2),
        HasContinuousSmoothLoopJets e prepared →
        @Continuous (Sphere 2) (ProductCurve Q) inferInstance
          (smoothProductInitialTopology e a) (fun p => initialRamp ((prepared p).1)))
    (hexists : ∀ (lambda : ℝ), 0 < lambda → lambda ≤ 1 →
      RampExistenceInput (I := I) (M := Q) (D := D) (a := a) (b := b) B lambda)
    (hfamily : ∀ (lambda : ℝ), 0 < lambda → lambda ≤ 1 →
      RampFamilyInput (I := I) (M := Q) (D := D) (a := a) (b := b) (N := d) B lambda e)
    (hbounds : PreparedFamilyInitialBoundsFront (I := I) (Q := Q) (D := D) (a := a) (b := b)
      B e L₀ Theta₀)
    (hprojected : RampFamilyProjectedDeformationFrontier (I := I) (Q := Q) (D := D) (a := a)
      (b := b) B e)
    (hprepared : PreparedFamilyApproximation (I := I) (Q := Q) (D := D) (a := a) (b := b)
      B e Γ L₀ Theta₀ Ainit)
    (halt : RampAlternativeData (I := I) (Q := Q) (D := D) (a := a) (b := b) B ell epsilon) :
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
              affineComparison B.family a b (regularLeastArea (B.family.metric a) (Γ p)) + epsilon :=
  rfs_family_deformation_of_frontier B e Γ epsilon ell hepsilon L₀ Theta₀ Ainit hL₀ hTheta₀
    hAinit hprepared
    (preparedFamilyFlowData_of_ramp_frontiers B e L₀ Theta₀ hcontinuous hexists hfamily hbounds
      hprojected)
    halt

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace Q] hCompact hConnected
  hBoundary hT2 in
theorem not_isRampOn_zero_of_nonempty (c : ProductCurve Q) (g : ℝ → SmoothRiemannianMetric I Q)
    {J : Set ℝ} (hJ : J.Nonempty) : ¬ c.IsRampOn g 0 J := by
  rintro ⟨-, hangle⟩
  obtain ⟨t, ht⟩ := hJ
  have hzero : c.angle g 0 0 t = 0 := by
    simp [ProductCurve.angle, ProductCurve.inner, ProductCurve.unitTangent,
      ProductCurve.verticalUnit]
  have hpos := hangle 0 t ht
  rw [hzero] at hpos
  exact lt_irrefl 0 hpos

omit [SigmaCompactSpace Q] hCompact hConnected hBoundary in
theorem rampFamilyProjectedDeformation_zero
    (B : RicciBackground (I := I) (M := Q) D a b) {d : ℕ}
    (e : SmoothLoopEmbedding (I := I) (Q := Q) d)
    (prepared : RegularFamily (I := I) (Q := Q) (Sphere 2)) :
    RampFamilyProjectedDeformation (I := I) (Q := Q) (D := D) (a := a) (b := b) B e prepared 0 := by
  intro solutions _ hdata
  let p : Sphere 2 :=
    ⟨PiLp.single 2 (0 : Fin 3) (1 : ℝ), by
      rw [mem_sphere_zero_iff_norm, PiLp.norm_single, norm_one]⟩
  exact absurd (hdata p).2.1
    (not_isRampOn_zero_of_nonempty (solutions p) B.family.metric ⟨a, le_rfl, B.lt.le⟩)

end DifferentialGeometry.PDE.RicciFlow.Extinction.Families
