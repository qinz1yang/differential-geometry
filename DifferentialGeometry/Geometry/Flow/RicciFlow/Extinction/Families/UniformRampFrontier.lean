import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.RampFrontierData
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.RampLengthEvolution
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.RampFamilySatisfiability

set_option autoImplicit false

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
def RampUniformBoundsInput (B : RicciBackground (I := I) (M := Q) D a b)
    (Ainit : ℝ) : Prop :=
  RampProductBounds (I := I) (Q := Q) (D := D) (a := a) (b := b) B ∧
    RampAreaBounds (I := I) (Q := Q) (D := D) (a := a) (b := b) B Ainit

omit [SigmaCompactSpace Q] hCompact hConnected hBoundary in
theorem rfs_ramp_uniform_bounds_of_input
    (B : RicciBackground (I := I) (M := Q) D a b)
    (L₀ Theta₀ Ainit : ℝ) (hL₀ : 0 ≤ L₀) (hTheta₀ : 0 ≤ Theta₀)
    (hAinit : 0 ≤ Ainit) (h : RampUniformBoundsInput B Ainit) :
    let delta := b - a
    let Lbar := Real.exp (B.B₀ * delta) * L₀
    let Thetabar := (Theta₀ + L₀) * Real.exp ((B.C + B.B₀) * delta)
    let Abar := Real.exp (2 * B.B₀ * delta) * (Ainit + delta * Thetabar)
    let Cup := Real.exp (2 * B.B₀ * delta) * (2 * B.B₀ * Abar + Thetabar)
    ∀ lambda : ℝ, 0 < lambda → lambda ≤ 1 → ∀ c : ProductCurve Q,
      c.IsSolutionOn B.family.metric lambda (Icc a b) →
      c.IsRampOn B.family.metric lambda (Icc a b) → c.degree = 1 →
      ∀ γ : ℝ → ContinuousFreeLoop Q,
        (∀ t ∈ Icc a b, ∀ z, γ t z = c.projection z t) →
        (∀ t ∈ Icc a b, IsContractibleLoop (γ t)) →
        c.length B.family.metric lambda a ≤ L₀ →
        c.totalCurvature B.family.metric lambda a ≤ Theta₀ →
        loopFamilyLeastArea B.family.metric γ a ≤ Ainit →
        ContinuousOn (loopFamilyLeastArea B.family.metric γ) (Icc a b) ∧
        (∀ t ∈ Icc a b,
          c.length B.family.metric lambda t ≤ Lbar ∧
          c.totalCurvature B.family.metric lambda t ≤ Thetabar ∧
          0 ≤ loopFamilyLeastArea B.family.metric γ t ∧
          loopFamilyLeastArea B.family.metric γ t ≤ Abar) ∧
        (∫ t in a..b, c.energy B.family.metric lambda t) ≤ Lbar ∧
        ∀ s ∈ Icc a b, ∀ t ∈ Icc s b,
          loopFamilyLeastArea B.family.metric γ t - loopFamilyLeastArea B.family.metric γ s ≤
            Cup * (t - s) :=
  rfs_ramp_uniform_bounds_of_frontier B L₀ Theta₀ Ainit hL₀ hTheta₀ hAinit h.1 h.2

omit [SigmaCompactSpace Q] hCompact hConnected hBoundary in
def PreparedFamilyFlowInput (B : RicciBackground (I := I) (M := Q) D a b) {d : ℕ}
    (e : SmoothLoopEmbedding (I := I) (Q := Q) d) : Prop :=
  (∀ (lambda : ℝ), 0 < lambda → lambda ≤ 1 →
    ∀ prepared : RegularFamily (I := I) (Q := Q) (Sphere 2),
      HasContinuousSmoothLoopJets e prepared →
      RampFamilyFlowSolutions B e prepared lambda) ∧
    ∀ (lambda : ℝ), 0 < lambda → lambda ≤ 1 →
      ∀ prepared : RegularFamily (I := I) (Q := Q) (Sphere 2),
        HasContinuousSmoothLoopJets e prepared →
        RampFamilyProjectedDeformation B e prepared lambda

omit [SigmaCompactSpace Q] hCompact hConnected hBoundary in
theorem rfs_prepared_family_flow_of_input
    (B : RicciBackground (I := I) (M := Q) D a b) {d : ℕ}
    (e : SmoothLoopEmbedding (I := I) (Q := Q) d)
    (prepared : RegularFamily (I := I) (Q := Q) (Sphere 2))
    (hsmooth : HasContinuousSmoothLoopJets e prepared)
    (lambda : ℝ) (hlambda : 0 < lambda) (hlambda_one : lambda ≤ 1)
    (h : PreparedFamilyFlowInput B e) :
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
    (h.1 lambda hlambda hlambda_one prepared hsmooth)
    (h.2 lambda hlambda hlambda_one prepared hsmooth)

omit [SigmaCompactSpace Q] hBoundary in
def UniformRampAlternativeInput (B : RicciBackground (I := I) (M := Q) D a b)
    (L₀ Theta₀ Ainit : ℝ) (ell _epsilon : ℝ) : Prop :=
  RampProductBounds (I := I) (Q := Q) (D := D) (a := a) (b := b) B ∧
    RampAreaBounds (I := I) (Q := Q) (D := D) (a := a) (b := b) B Ainit ∧
    ∀ eta : ℝ, 0 < eta → eta < 1 → ∀ threshold : ℝ, 1 ≤ threshold →
      ∀ epsilon : ℝ, 0 < epsilon → ∃ d : ℝ, 0 < d ∧ d < epsilon ∧
        RampWindowInput (I := I) (Q := Q) (D := D) (a := a) (b := b) B
          L₀ Theta₀ Ainit ell eta threshold d

omit [SigmaCompactSpace Q] hBoundary in
theorem rfs_uniform_ramp_alternative_of_input
    (B : RicciBackground (I := I) (M := Q) D a b)
    (hdim : Module.finrank ℝ E = 3)
    (L₀ Theta₀ Ainit : ℝ) (hL₀ : 0 ≤ L₀) (hTheta₀ : 0 ≤ Theta₀)
    (hAinit : 0 ≤ Ainit) (ell epsilon : ℝ) (hell : 0 < ell)
    (hepsilon : 0 < epsilon) (h : UniformRampAlternativeInput B L₀ Theta₀ Ainit ell epsilon) :
    ∃ lambda₀ : ℝ, 0 < lambda₀ ∧ lambda₀ ≤ 1 ∧
      ∀ lambda : ℝ, 0 < lambda → lambda ≤ lambda₀ → ∀ c : ProductCurve Q,
        c.IsSolutionOn B.family.metric lambda (Icc a b) →
        c.IsRampOn B.family.metric lambda (Icc a b) → c.degree = 1 →
        ∀ γ : ℝ → ContinuousFreeLoop Q,
          (∀ t ∈ Icc a b, ∀ z, γ t z = c.projection z t) →
          (∀ t ∈ Icc a b, IsContractibleLoop (γ t)) →
          c.length B.family.metric lambda a ≤ L₀ →
          c.totalCurvature B.family.metric lambda a ≤ Theta₀ →
          loopFamilyLeastArea B.family.metric γ a ≤ Ainit →
          loopLength (B.family.metric b) (γ b) < ell ∨
            loopFamilyLeastArea B.family.metric γ b ≤
              affineComparison B.family a b (loopFamilyLeastArea B.family.metric γ a) +
                epsilon :=
  rfs_uniform_ramp_alternative_of_frontier B hdim L₀ Theta₀ Ainit hL₀ hTheta₀ hAinit
    ell epsilon hell hepsilon h.1 h.2.1 h.2.2

omit [SigmaCompactSpace Q] hBoundary in
def FamilyDeformationInput (B : RicciBackground (I := I) (M := Q) D a b) {d : ℕ}
    (e : SmoothLoopEmbedding (I := I) (Q := Q) d)
    (Γ : RegularFamily (I := I) (Q := Q) (Sphere 2)) (ell epsilon : ℝ) : Prop :=
  ∃ L₀ Theta₀ Ainit : ℝ,
    0 ≤ L₀ ∧ 0 ≤ Theta₀ ∧ 0 ≤ Ainit ∧
      PreparedFamilyApproximation B e Γ L₀ Theta₀ Ainit ∧
      PreparedFamilyFlowData (I := I) (Q := Q) (D := D) (a := a) (b := b) B e L₀ Theta₀ ∧
      RampAlternativeData (I := I) (Q := Q) (D := D) (a := a) (b := b) B ell epsilon

omit [SigmaCompactSpace Q] hBoundary in
theorem rfs_family_deformation_of_input
    (B : RicciBackground (I := I) (M := Q) D a b) {d : ℕ}
    (e : SmoothLoopEmbedding (I := I) (Q := Q) d)
    (Γ : RegularFamily (I := I) (Q := Q) (Sphere 2))
    (epsilon ell : ℝ) (hepsilon : 0 < epsilon)
    (h : FamilyDeformationInput B e Γ ell epsilon) :
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
  obtain ⟨L₀, Theta₀, Ainit, hL₀, hTheta₀, hAinit, hprepared, hflow, halt⟩ := h
  exact rfs_family_deformation_of_frontier B e Γ epsilon ell hepsilon
    L₀ Theta₀ Ainit hL₀ hTheta₀ hAinit hprepared hflow halt

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace Q] hCompact hConnected
  hBoundary hT2 in
private theorem productCurve_not_isRampOn_zero_of_nonempty
    (c : ProductCurve Q) (g : ℝ → SmoothRiemannianMetric I Q) {J : Set ℝ}
    (hJ : J.Nonempty) : ¬ c.IsRampOn g 0 J := by
  rintro ⟨-, hangle⟩
  obtain ⟨t, ht⟩ := hJ
  have hzero : c.angle g 0 0 t = 0 := by
    simp [ProductCurve.angle, ProductCurve.inner, ProductCurve.unitTangent,
      ProductCurve.verticalUnit]
  have hpos := hangle 0 t ht
  rw [hzero] at hpos
  exact lt_irrefl 0 hpos

omit [SigmaCompactSpace Q] hCompact hConnected hBoundary in
theorem not_rampFamilyFlowSolutions_zero
    (B : RicciBackground (I := I) (M := Q) D a b) {d : ℕ}
    (e : SmoothLoopEmbedding (I := I) (Q := Q) d)
    (prepared : RegularFamily (I := I) (Q := Q) (Sphere 2)) :
    ¬ RampFamilyFlowSolutions (I := I) (Q := Q) (D := D) (a := a) (b := b) B e prepared 0 := by
  rintro ⟨solutions, _hcont, hdata⟩
  let p : Sphere 2 :=
    ⟨PiLp.single 2 (0 : Fin 3) (1 : ℝ), by
      rw [mem_sphere_zero_iff_norm, PiLp.norm_single, norm_one]⟩
  have hIcc : (Set.Icc a b).Nonempty := ⟨a, le_rfl, B.lt.le⟩
  exact productCurve_not_isRampOn_zero_of_nonempty (solutions p) B.family.metric
    hIcc (hdata p).2.1

end DifferentialGeometry.PDE.RicciFlow.Extinction.Families
