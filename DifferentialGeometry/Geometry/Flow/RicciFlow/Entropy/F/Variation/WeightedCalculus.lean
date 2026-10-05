import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.Green.Identities
import DifferentialGeometry.Analysis.Integration.Measure.Family.VolumeVariation
import DifferentialGeometry.Analysis.Integration.Entropy.Perelman.F.Functional
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator

set_option autoImplicit false

open DifferentialGeometry.Geometry.Connection
namespace DifferentialGeometry.PDE.RicciFlow.Entropy

noncomputable section

open Filter MeasureTheory
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff

variable {M : Type*}

section Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem weightedIBP
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {potential : M -> Real}
    (hpotential : ContMDiff I 𝓘(Real, Real) ∞ potential)
    (hmeas :
      AEMeasurable
        (fun x : M => ENNReal.ofReal (DifferentialGeometry.Analysis.Entropy.Perelman.expNegPotentialDensity potential x))
        (riemannianVolumeMeasure (I := I) (M := M) g))
    (hlap :
      Integrable (fun x : M =>
        DifferentialGeometry.Analysis.Entropy.Perelman.expNegPotentialDensity potential x *
          DifferentialGeometry.Geometry.Operator.ΔG
            (I := I) g ⟨_, hpotential⟩ x)
        (riemannianVolumeMeasure (I := I) (M := M) g))
    (hgrad :
      Integrable (fun x : M =>
        DifferentialGeometry.Analysis.Entropy.Perelman.expNegPotentialDensity potential x *
          g.inner x
            ((DifferentialGeometry.Geometry.Operator.gradG
              (I := I) g ⟨_, hpotential⟩ :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
            ((DifferentialGeometry.Geometry.Operator.gradG
              (I := I) g ⟨_, hpotential⟩ :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x))
        (riemannianVolumeMeasure (I := I) (M := M) g)) :
    ∫ x,
      (DifferentialGeometry.Geometry.Operator.ΔG
          (I := I) g ⟨_, hpotential⟩ x -
        g.inner x
          ((DifferentialGeometry.Geometry.Operator.gradG
            (I := I) g ⟨_, hpotential⟩ :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
          ((DifferentialGeometry.Geometry.Operator.gradG
            (I := I) g ⟨_, hpotential⟩ :
            Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x))
      ∂(DifferentialGeometry.Analysis.Entropy.Perelman.expNegPotentialWeightedMeasure
          (riemannianVolumeMeasure (I := I) (M := M) g) potential) = 0 := by
  apply DifferentialGeometry.Analysis.Entropy.Perelman.integral_expNegPotentialWeightedMeasure_eq_zero_of_integral_eq_zero
    (mu := riemannianVolumeMeasure (I := I) (M := M) g)
    (potential := potential)
    (lapPotential :=
      DifferentialGeometry.Geometry.Operator.ΔG
        (I := I) g ⟨_, hpotential⟩)
    (gradPotentialNormSq := fun x : M =>
      g.inner x
        ((DifferentialGeometry.Geometry.Operator.gradG
          (I := I) g ⟨_, hpotential⟩ :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ((DifferentialGeometry.Geometry.Operator.gradG
          (I := I) g ⟨_, hpotential⟩ :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x))
  · exact hmeas
  · simpa [DifferentialGeometry.Analysis.Entropy.Perelman.expNegPotentialDensity] using
      DifferentialGeometry.Integral.DivergenceTheorem.expNegIBP
        (I := I) g hpotential hlap hgrad

omit [TopologicalSpace M] in
theorem bracket_eq_closed_of_ibp [MeasurableSpace M]
    (mu : Measure M)
    (scalarCurvature lapPotential gradPotentialNormSq potential : M -> Real)
    (hscalar_int :
      Integrable scalarCurvature
        (DifferentialGeometry.Analysis.Entropy.Perelman.expNegPotentialWeightedMeasure mu potential))
    (hlap_int :
      Integrable lapPotential
        (DifferentialGeometry.Analysis.Entropy.Perelman.expNegPotentialWeightedMeasure mu potential))
    (hgrad_int :
      Integrable gradPotentialNormSq
        (DifferentialGeometry.Analysis.Entropy.Perelman.expNegPotentialWeightedMeasure mu potential))
    (hibp :
      ∫ x, (lapPotential x - gradPotentialNormSq x)
        ∂(DifferentialGeometry.Analysis.Entropy.Perelman.expNegPotentialWeightedMeasure mu potential) = 0) :
    (∫ x, DifferentialGeometry.Analysis.Entropy.Perelman.fFunctionalBracket scalarCurvature gradPotentialNormSq x
      ∂(DifferentialGeometry.Analysis.Entropy.Perelman.expNegPotentialWeightedMeasure mu potential)) =
      ∫ x, DifferentialGeometry.Analysis.Entropy.Perelman.fFunctionalClosedBracket scalarCurvature lapPotential x
        ∂(DifferentialGeometry.Analysis.Entropy.Perelman.expNegPotentialWeightedMeasure mu potential) := by
  let μw := DifferentialGeometry.Analysis.Entropy.Perelman.expNegPotentialWeightedMeasure mu potential
  have hdiff :
      (∫ x, lapPotential x ∂μw) =
        ∫ x, gradPotentialNormSq x ∂μw := by
    have hsub :
        (∫ x, (lapPotential x - gradPotentialNormSq x) ∂μw) =
          (∫ x, lapPotential x ∂μw) -
            ∫ x, gradPotentialNormSq x ∂μw := by
      exact integral_sub hlap_int hgrad_int
    rw [hsub] at hibp
    linarith
  calc
    (∫ x, DifferentialGeometry.Analysis.Entropy.Perelman.fFunctionalBracket scalarCurvature gradPotentialNormSq x ∂μw)
        =
      ∫ x, scalarCurvature x + gradPotentialNormSq x ∂μw := by
        rfl
    _ =
      (∫ x, scalarCurvature x ∂μw) +
        ∫ x, gradPotentialNormSq x ∂μw := by
        exact integral_add hscalar_int hgrad_int
    _ =
      (∫ x, scalarCurvature x ∂μw) +
        ∫ x, lapPotential x ∂μw := by
        rw [hdiff]
    _ =
      ∫ x, scalarCurvature x + lapPotential x ∂μw := by
        exact (integral_add hscalar_int hlap_int).symm
    _ =
      ∫ x, DifferentialGeometry.Analysis.Entropy.Perelman.fFunctionalClosedBracket scalarCurvature lapPotential x ∂μw := by
        rfl

theorem weightedGreen
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {potential q : M -> Real}
    (hpotential : ContMDiff I 𝓘(Real, Real) ∞ potential)
    (hq : ContMDiff I 𝓘(Real, Real) ∞ q)
    (hmeas :
      AEMeasurable
        (fun x : M => ENNReal.ofReal (DifferentialGeometry.Analysis.Entropy.Perelman.expNegPotentialDensity potential x))
        (riemannianVolumeMeasure (I := I) (M := M) g)) :
    ∫ x,
        DifferentialGeometry.Geometry.Operator.ΔG
          (I := I) g ⟨_, hq⟩ x
      ∂(DifferentialGeometry.Analysis.Entropy.Perelman.expNegPotentialWeightedMeasure
          (riemannianVolumeMeasure (I := I) (M := M) g) potential) =
      ∫ x,
        q x *
          (-DifferentialGeometry.Geometry.Operator.ΔG
              (I := I) g ⟨_, hpotential⟩ x +
            g.inner x
              ((DifferentialGeometry.Geometry.Operator.gradG
                (I := I) g ⟨_, hpotential⟩ :
                Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
              ((DifferentialGeometry.Geometry.Operator.gradG
                (I := I) g ⟨_, hpotential⟩ :
                Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x))
      ∂(DifferentialGeometry.Analysis.Entropy.Perelman.expNegPotentialWeightedMeasure
          (riemannianVolumeMeasure (I := I) (M := M) g) potential) := by
  classical
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  let gradSq : M -> Real := fun x =>
    g.inner x
      ((DifferentialGeometry.Geometry.Operator.gradG
        (I := I) g ⟨_, hpotential⟩ :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
      ((DifferentialGeometry.Geometry.Operator.gradG
        (I := I) g ⟨_, hpotential⟩ :
        Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
  rw [DifferentialGeometry.Analysis.Entropy.Perelman.expNegPotentialWeightedMeasure_integral_eq_base
    (mu := μ) (potential := potential)
    (integrand := fun x : M =>
      DifferentialGeometry.Geometry.Operator.ΔG (I := I) g ⟨_, hq⟩ x)
    hmeas]
  rw [DifferentialGeometry.Analysis.Entropy.Perelman.expNegPotentialWeightedMeasure_integral_eq_base
    (mu := μ) (potential := potential)
    (integrand := fun x : M =>
      q x *
        (-DifferentialGeometry.Geometry.Operator.ΔG
            (I := I) g ⟨_, hpotential⟩ x + gradSq x))
    hmeas]
  calc
    ∫ x,
        DifferentialGeometry.Analysis.Entropy.Perelman.expNegPotentialDensity potential x *
          DifferentialGeometry.Geometry.Operator.ΔG (I := I) g ⟨_, hq⟩ x ∂μ =
      ∫ x,
        q x *
          (DifferentialGeometry.Analysis.Entropy.Perelman.expNegPotentialDensity potential x *
            (-DifferentialGeometry.Geometry.Operator.ΔG
                (I := I) g ⟨_, hpotential⟩ x + gradSq x)) ∂μ := by
      simpa [μ, DifferentialGeometry.Analysis.Entropy.Perelman.expNegPotentialDensity, gradSq] using
        DifferentialGeometry.Integral.DivergenceTheorem.expNegGreen
          (I := I) g hpotential hq
    _ =
      ∫ x,
        DifferentialGeometry.Analysis.Entropy.Perelman.expNegPotentialDensity potential x *
          (q x *
            (-DifferentialGeometry.Geometry.Operator.ΔG
                (I := I) g ⟨_, hpotential⟩ x + gradSq x)) ∂μ := by
      apply integral_congr_ae
      refine Filter.Eventually.of_forall ?_
      intro x
      ring

theorem weightedDivZero
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {potential weightedDivergenceTrace : M -> Real}
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hmeas :
      AEMeasurable
        (fun x : M => ENNReal.ofReal (DifferentialGeometry.Analysis.Entropy.Perelman.expNegPotentialDensity potential x))
        (riemannianVolumeMeasure (I := I) (M := M) g))
    (hdiv :
      ∀ x : M,
        DifferentialGeometry.Integral.DivergenceTheorem.divergenceG
            (I := I) g X x =
          DifferentialGeometry.Analysis.Entropy.Perelman.expNegPotentialDensity potential x * weightedDivergenceTrace x) :
    ∫ x, weightedDivergenceTrace x
      ∂(DifferentialGeometry.Analysis.Entropy.Perelman.expNegPotentialWeightedMeasure
          (riemannianVolumeMeasure (I := I) (M := M) g) potential) = 0 := by
  classical
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  rw [DifferentialGeometry.Analysis.Entropy.Perelman.expNegPotentialWeightedMeasure_integral_eq_base
    (mu := μ) (potential := potential)
    (integrand := weightedDivergenceTrace) hmeas]
  calc
    ∫ x, DifferentialGeometry.Analysis.Entropy.Perelman.expNegPotentialDensity potential x * weightedDivergenceTrace x ∂μ =
        ∫ x, DifferentialGeometry.Integral.DivergenceTheorem.divergenceG
          (I := I) g X x ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => (hdiv x).symm
    _ = 0 := by
      simpa [μ] using
        DifferentialGeometry.Integral.DivergenceTheorem.integral_divergence_eq_zero_of_compact
          (I := I) g X

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem expNegPotentialDensity_contMDiff
    {potential : M -> Real}
    (hpotential : ContMDiff I 𝓘(Real, Real) ∞ potential) :
    ContMDiff I 𝓘(Real, Real) ∞ (DifferentialGeometry.Analysis.Entropy.Perelman.expNegPotentialDensity potential) := by
  change ContMDiff I 𝓘(Real, Real) ∞ (fun x => Real.exp (-(potential x)))
  have h := Real.contDiff_exp.contMDiff.comp hpotential.neg
  simpa only [Function.comp_def] using h

omit [FiniteDimensional ℝ E] in
theorem tangentSectionAction_expNeg
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M -> Type _)⟯)
    {potential : M -> Real}
    (hpotential : ContMDiff I 𝓘(Real, Real) ∞ potential) (x : M) :
    DifferentialGeometry.Integral.DivergenceTheorem.tangentSectionAction
        (I := I) X (DifferentialGeometry.Analysis.Entropy.Perelman.expNegPotentialDensity potential) x =
      -DifferentialGeometry.Analysis.Entropy.Perelman.expNegPotentialDensity potential x *
        DifferentialGeometry.Integral.DivergenceTheorem.tangentSectionAction
          (I := I) X potential x := by
  have hmf :=
    DifferentialGeometry.Integral.DivergenceTheorem.mfderiv_exp_neg_toLinearMap
      (I := I) (f := potential) (x := x)
      (hpotential.mdifferentiableAt (by simp))
  unfold DifferentialGeometry.Integral.DivergenceTheorem.tangentSectionAction
    DifferentialGeometry.Analysis.Entropy.Perelman.expNegPotentialDensity
  change
    (show ℝ from mfderiv I 𝓘(ℝ, ℝ) (fun y : M => Real.exp (-(potential y))) x (X x)) =
      -Real.exp (-(potential x)) *
        (show ℝ from mfderiv I 𝓘(ℝ, ℝ) potential x (X x))
  have happly := congrArg
    (fun L : TangentSpace I x →ₗ[ℝ] ℝ => L (X x)) hmf
  change
    (show ℝ from mfderiv I 𝓘(ℝ, ℝ) (fun y : M => Real.exp (-(potential y))) x (X x)) =
      -Real.exp (-(potential x)) *
        (show ℝ from mfderiv I 𝓘(ℝ, ℝ) potential x (X x)) at happly
  exact happly

def connTraceVec
    {potential : M -> Real}
    (hpotential : ContMDiff I 𝓘(Real, Real) ∞ potential)
    (traceVec : Cₛ^∞⟮I; E, (TangentSpace I : M -> Type _)⟯) :
    Cₛ^∞⟮I; E, (TangentSpace I : M -> Type _)⟯ :=
  DifferentialGeometry.Integral.DivergenceTheorem.smoothSmul
    (I := I) (DifferentialGeometry.Analysis.Entropy.Perelman.expNegPotentialDensity potential)
    (expNegPotentialDensity_contMDiff (I := I) hpotential) traceVec

theorem connTraceDivEq
    [I.Boundaryless] (g : SmoothRiemannianMetric I M)
    {potential weightedDivergenceTrace rawTrace actionTrace : M -> Real}
    (hpotential : ContMDiff I 𝓘(Real, Real) ∞ potential)
    (traceVec : Cₛ^∞⟮I; E, (TangentSpace I : M -> Type _)⟯)
    (hdivTrace :
      ∀ x : M,
        DifferentialGeometry.Integral.DivergenceTheorem.divergenceG
            (I := I) g traceVec x =
          rawTrace x)
    (hactionTrace :
      ∀ x : M,
        DifferentialGeometry.Integral.DivergenceTheorem.tangentSectionAction
            (I := I) traceVec potential x =
          actionTrace x)
    (hweighted :
      ∀ x : M,
        weightedDivergenceTrace x = rawTrace x - actionTrace x) :
    ∀ x : M,
      DifferentialGeometry.Integral.DivergenceTheorem.divergenceG
          (I := I) g
          (connTraceVec (I := I) hpotential traceVec) x =
        DifferentialGeometry.Analysis.Entropy.Perelman.expNegPotentialDensity potential x * weightedDivergenceTrace x := by
  intro x
  rw [connTraceVec]
  rw [DifferentialGeometry.Integral.DivergenceTheorem.divergence_g_smoothSmul
    (I := I) g (DifferentialGeometry.Analysis.Entropy.Perelman.expNegPotentialDensity potential)
    (expNegPotentialDensity_contMDiff (I := I) hpotential) traceVec x]
  rw [hdivTrace x]
  rw [tangentSectionAction_expNeg (I := I) traceVec hpotential x]
  rw [hactionTrace x, hweighted x]
  ring

theorem weightedDivZero_of_connTrace
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {potential weightedDivergenceTrace rawTrace actionTrace : M -> Real}
    (hpotential : ContMDiff I 𝓘(Real, Real) ∞ potential)
    (traceVec : Cₛ^∞⟮I; E, (TangentSpace I : M -> Type _)⟯)
    (hmeas :
      AEMeasurable
        (fun x : M => ENNReal.ofReal (DifferentialGeometry.Analysis.Entropy.Perelman.expNegPotentialDensity potential x))
        (riemannianVolumeMeasure (I := I) (M := M) g))
    (hdivTrace :
      ∀ x : M,
        DifferentialGeometry.Integral.DivergenceTheorem.divergenceG
            (I := I) g traceVec x =
          rawTrace x)
    (hactionTrace :
      ∀ x : M,
        DifferentialGeometry.Integral.DivergenceTheorem.tangentSectionAction
            (I := I) traceVec potential x =
          actionTrace x)
    (hweighted :
      ∀ x : M,
        weightedDivergenceTrace x = rawTrace x - actionTrace x) :
    ∫ x, weightedDivergenceTrace x
      ∂(DifferentialGeometry.Analysis.Entropy.Perelman.expNegPotentialWeightedMeasure
          (riemannianVolumeMeasure (I := I) (M := M) g) potential) = 0 := by
  exact weightedDivZero (I := I) g
    (connTraceVec (I := I) hpotential traceVec) hmeas
    (connTraceDivEq (I := I) g hpotential traceVec hdivTrace
      hactionTrace hweighted)

theorem weighted_grad_zero
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {potential q : M -> Real}
    (hpotential : ContMDiff I 𝓘(Real, Real) ∞ potential)
    (hq : ContMDiff I 𝓘(Real, Real) ∞ q) :
    ∫ x,
        (DifferentialGeometry.Geometry.Operator.ΔG
            (I := I) g ⟨_, hq⟩ x -
          g.inner x
            ((DifferentialGeometry.Geometry.Operator.gradG
              (I := I) g ⟨_, hq⟩) x)
            ((DifferentialGeometry.Geometry.Operator.gradG
              (I := I) g ⟨_, hpotential⟩) x))
      ∂(DifferentialGeometry.Analysis.Entropy.Perelman.expNegPotentialWeightedMeasure
          (riemannianVolumeMeasure (I := I) (M := M) g) potential) = 0 := by
  have hmeas :
      AEMeasurable
        (fun x : M => ENNReal.ofReal (DifferentialGeometry.Analysis.Entropy.Perelman.expNegPotentialDensity potential x))
        (riemannianVolumeMeasure (I := I) (M := M) g) :=
    (ENNReal.continuous_ofReal.comp
      (expNegPotentialDensity_contMDiff (I := I) hpotential).continuous).aemeasurable
  exact weightedDivZero_of_connTrace (I := I) g hpotential
    (DifferentialGeometry.Geometry.Operator.gradG (I := I) g ⟨_, hq⟩)
    hmeas
    (fun x =>
      (DifferentialGeometry.Geometry.Operator.Δ_g_def
        (I := I) g ⟨_, hq⟩ x).symm)
    (fun x =>
      DifferentialGeometry.Geometry.Operator.tangentSectionAction_eq_inner_grad_g
        (I := I) g ⟨_, hpotential⟩
        (DifferentialGeometry.Geometry.Operator.gradG (I := I) g ⟨_, hq⟩) x)
    (fun _ => rfl)

theorem shiftIntEq
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M)
    {potential q shiftedTrace potentialVariation metricVariationTrace :
      M -> Real}
    (hpotential : ContMDiff I 𝓘(Real, Real) ∞ potential)
    (hq : ContMDiff I 𝓘(Real, Real) ∞ q)
    (hmeas :
      AEMeasurable
        (fun x : M => ENNReal.ofReal (DifferentialGeometry.Analysis.Entropy.Perelman.expNegPotentialDensity potential x))
        (riemannianVolumeMeasure (I := I) (M := M) g))
    (hshift :
      ∀ x : M,
        shiftedTrace x =
          DifferentialGeometry.Geometry.Operator.ΔG
            (I := I) g ⟨_, hq⟩ x)
    (hqeq :
      ∀ x : M,
        q x = potentialVariation x - metricVariationTrace x / 2) :
    ∫ x, shiftedTrace x
      ∂(DifferentialGeometry.Analysis.Entropy.Perelman.expNegPotentialWeightedMeasure
          (riemannianVolumeMeasure (I := I) (M := M) g) potential) =
      ∫ x,
        DifferentialGeometry.Analysis.Entropy.Perelman.expWeightedMeasureVariationFactor potentialVariation
          metricVariationTrace x *
          (DifferentialGeometry.Geometry.Operator.ΔG
              (I := I) g ⟨_, hpotential⟩ x -
            g.inner x
              ((DifferentialGeometry.Geometry.Operator.gradG
                (I := I) g ⟨_, hpotential⟩ :
                Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
              ((DifferentialGeometry.Geometry.Operator.gradG
                (I := I) g ⟨_, hpotential⟩ :
                Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x))
      ∂(DifferentialGeometry.Analysis.Entropy.Perelman.expNegPotentialWeightedMeasure
          (riemannianVolumeMeasure (I := I) (M := M) g) potential) := by
  calc
    ∫ x, shiftedTrace x
      ∂(DifferentialGeometry.Analysis.Entropy.Perelman.expNegPotentialWeightedMeasure
          (riemannianVolumeMeasure (I := I) (M := M) g) potential) =
        ∫ x,
          DifferentialGeometry.Geometry.Operator.ΔG (I := I) g ⟨_, hq⟩ x
        ∂(DifferentialGeometry.Analysis.Entropy.Perelman.expNegPotentialWeightedMeasure
            (riemannianVolumeMeasure (I := I) (M := M) g) potential) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hshift
    _ = ∫ x,
        q x *
          (-DifferentialGeometry.Geometry.Operator.ΔG
              (I := I) g ⟨_, hpotential⟩ x +
            g.inner x
              ((DifferentialGeometry.Geometry.Operator.gradG
                (I := I) g ⟨_, hpotential⟩ :
                Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
              ((DifferentialGeometry.Geometry.Operator.gradG
                (I := I) g ⟨_, hpotential⟩ :
                Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x))
        ∂(DifferentialGeometry.Analysis.Entropy.Perelman.expNegPotentialWeightedMeasure
            (riemannianVolumeMeasure (I := I) (M := M) g) potential) := by
      exact weightedGreen (I := I) g hpotential hq hmeas
    _ = ∫ x,
        DifferentialGeometry.Analysis.Entropy.Perelman.expWeightedMeasureVariationFactor potentialVariation
          metricVariationTrace x *
          (DifferentialGeometry.Geometry.Operator.ΔG
              (I := I) g ⟨_, hpotential⟩ x -
            g.inner x
              ((DifferentialGeometry.Geometry.Operator.gradG
                (I := I) g ⟨_, hpotential⟩ :
                Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
              ((DifferentialGeometry.Geometry.Operator.gradG
                (I := I) g ⟨_, hpotential⟩ :
                Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x))
        ∂(DifferentialGeometry.Analysis.Entropy.Perelman.expNegPotentialWeightedMeasure
            (riemannianVolumeMeasure (I := I) (M := M) g) potential) := by
      apply integral_congr_ae
      refine Filter.Eventually.of_forall ?_
      intro x
      dsimp
      rw [hqeq x]
      unfold DifferentialGeometry.Analysis.Entropy.Perelman.expWeightedMeasureVariationFactor
      ring

theorem expWeightedMeasureIntegral_hasDerivAt_at
    [T2Space M] [CompactSpace M]
    (G : DifferentialGeometry.Geometry.Curvature.MetricConnectionFamily (I := I) (M := M) Real)
    {potentialPath phiPath : Real -> M -> Real}
    {s0 : Real}
    {potentialVariation metricVariationTrace phiVariation : M -> Real}
    (hpotential_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => potentialPath s x)
          (potentialVariation x) s0)
    (hphi_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => phiPath s x)
          (phiVariation x) s0)
    (htrace :
      ∀ x : M,
        traceTimeDerivMetricAt (I := I) G s0 x = metricVariationTrace x)
    (hmetric_regularity :
      MetricFamilyRegularAt (I := I)
        (metricFamilyForMeasure (I := I) (M := M) G) s0)
    (hintegrand_regularity :
      FunctionRegularAt
        (fun s : Real => fun x : M =>
          DifferentialGeometry.Analysis.Entropy.Perelman.expNegPotentialDensity (potentialPath s) x * phiPath s x)
        s0) :
    HasDerivAt
      (fun s : Real =>
        ∫ x,
          DifferentialGeometry.Analysis.Entropy.Perelman.expNegPotentialDensity (potentialPath s) x * phiPath s x
          ∂(volumeMeasureFamily (I := I) (M := M) G s))
      (∫ x,
        DifferentialGeometry.Analysis.Entropy.Perelman.expWeightedIntegralVariationIntegrand
          (potentialPath s0) potentialVariation metricVariationTrace
          (phiPath s0) phiVariation x
        ∂(volumeMeasureFamily (I := I) (M := M) G s0))
      s0 := by
  have hvol :=
    volume_variation_formula_at
      (I := I) (M := M) G
      (f := fun s : Real => fun x : M =>
        DifferentialGeometry.Analysis.Entropy.Perelman.expNegPotentialDensity (potentialPath s) x * phiPath s x)
      (t₀ := s0) hmetric_regularity hintegrand_regularity
  refine hvol.congr_deriv ?_
  apply integral_congr_ae
  refine Filter.Eventually.of_forall ?_
  intro x
  have hdens :=
    DifferentialGeometry.Analysis.Entropy.Perelman.expNegPotentialDensity_hasDerivAt
      (M := M) (potentialPath := potentialPath)
      (potentialVariation := potentialVariation)
      hpotential_deriv x
  have hprod :
      HasDerivAt
        (fun s : Real =>
          DifferentialGeometry.Analysis.Entropy.Perelman.expNegPotentialDensity (potentialPath s) x * phiPath s x)
        (-(potentialVariation x) *
            DifferentialGeometry.Analysis.Entropy.Perelman.expNegPotentialDensity (potentialPath s0) x * phiPath s0 x +
          DifferentialGeometry.Analysis.Entropy.Perelman.expNegPotentialDensity (potentialPath s0) x * phiVariation x)
        s0 :=
    hdens.mul (hphi_deriv x)
  have hderiv := hprod.deriv
  change
    deriv
        (fun s : Real =>
          DifferentialGeometry.Analysis.Entropy.Perelman.expNegPotentialDensity (potentialPath s) x * phiPath s x)
        s0 +
      1 / 2 * traceTimeDerivMetricAt (I := I) G s0 x *
        (DifferentialGeometry.Analysis.Entropy.Perelman.expNegPotentialDensity (potentialPath s0) x * phiPath s0 x) =
    DifferentialGeometry.Analysis.Entropy.Perelman.expWeightedIntegralVariationIntegrand
      (potentialPath s0) potentialVariation metricVariationTrace
      (phiPath s0) phiVariation x
  rw [hderiv, htrace x]
  unfold DifferentialGeometry.Analysis.Entropy.Perelman.expWeightedIntegralVariationIntegrand
    DifferentialGeometry.Analysis.Entropy.Perelman.expWeightedMeasureVariationFactor
  ring

def fFunctionalBracketVariation
    (scalarCurvatureVariation gradPotentialNormSqVariation : M -> Real) :
    M -> Real :=
  fun x => scalarCurvatureVariation x + gradPotentialNormSqVariation x

omit [TopologicalSpace M] in
theorem fFunctionalBracket_hasDerivAt
    {scalarCurvaturePath gradPotentialNormSqPath : Real -> M -> Real}
    {s0 : Real}
    {scalarCurvatureVariation gradPotentialNormSqVariation : M -> Real}
    (hscalar_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => scalarCurvaturePath s x)
          (scalarCurvatureVariation x) s0)
    (hgrad_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => gradPotentialNormSqPath s x)
          (gradPotentialNormSqVariation x) s0)
    (x : M) :
    HasDerivAt
      (fun s : Real =>
        DifferentialGeometry.Analysis.Entropy.Perelman.fFunctionalBracket (scalarCurvaturePath s)
          (gradPotentialNormSqPath s) x)
      (fFunctionalBracketVariation scalarCurvatureVariation
        gradPotentialNormSqVariation x)
      s0 := by
  have h := (hscalar_deriv x).add (hgrad_deriv x)
  change HasDerivAt
    (fun s : Real => scalarCurvaturePath s x + gradPotentialNormSqPath s x)
    (scalarCurvatureVariation x + gradPotentialNormSqVariation x) s0
  exact h

omit [TopologicalSpace M] in
theorem closedBracket_deriv
    {scalarCurvaturePath lapPotentialPath : Real -> M -> Real}
    {s0 : Real}
    {scalarCurvatureVariation lapPotentialVariation : M -> Real}
    (hscalar_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => scalarCurvaturePath s x)
          (scalarCurvatureVariation x) s0)
    (hlap_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => lapPotentialPath s x)
          (lapPotentialVariation x) s0)
    (x : M) :
    HasDerivAt
      (fun s : Real =>
        DifferentialGeometry.Analysis.Entropy.Perelman.fFunctionalClosedBracket (scalarCurvaturePath s)
          (lapPotentialPath s) x)
      (DifferentialGeometry.Analysis.Entropy.Perelman.fFunctionalClosedBracketVariation scalarCurvatureVariation
        lapPotentialVariation x)
      s0 := by
  have h := (hscalar_deriv x).add (hlap_deriv x)
  change HasDerivAt
    (fun s : Real => scalarCurvaturePath s x + lapPotentialPath s x)
    (scalarCurvatureVariation x + lapPotentialVariation x) s0
  exact h

theorem fFunctionalBaseIntegral_hasDerivAt_at
    [T2Space M] [CompactSpace M]
    (G : DifferentialGeometry.Geometry.Curvature.MetricConnectionFamily (I := I) (M := M) Real)
    {scalarCurvaturePath gradPotentialNormSqPath potentialPath :
      Real -> M -> Real}
    {s0 : Real}
    {scalarCurvatureVariation gradPotentialNormSqVariation potentialVariation
      metricVariationTrace : M -> Real}
    (hscalar_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => scalarCurvaturePath s x)
          (scalarCurvatureVariation x) s0)
    (hgrad_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => gradPotentialNormSqPath s x)
          (gradPotentialNormSqVariation x) s0)
    (hpotential_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => potentialPath s x)
          (potentialVariation x) s0)
    (htrace :
      ∀ x : M,
        traceTimeDerivMetricAt (I := I) G s0 x = metricVariationTrace x)
    (hmetric_regularity :
      MetricFamilyRegularAt (I := I)
        (metricFamilyForMeasure (I := I) (M := M) G) s0)
    (hintegrand_regularity :
      FunctionRegularAt
        (fun s : Real => fun x : M =>
          DifferentialGeometry.Analysis.Entropy.Perelman.expNegPotentialDensity (potentialPath s) x *
            DifferentialGeometry.Analysis.Entropy.Perelman.fFunctionalBracket (scalarCurvaturePath s)
              (gradPotentialNormSqPath s) x)
        s0) :
    HasDerivAt
      (fun s : Real =>
        ∫ x,
          DifferentialGeometry.Analysis.Entropy.Perelman.expNegPotentialDensity (potentialPath s) x *
            DifferentialGeometry.Analysis.Entropy.Perelman.fFunctionalBracket (scalarCurvaturePath s)
              (gradPotentialNormSqPath s) x
          ∂(volumeMeasureFamily (I := I) (M := M) G s))
      (∫ x,
        DifferentialGeometry.Analysis.Entropy.Perelman.expWeightedIntegralVariationIntegrand
          (potentialPath s0) potentialVariation metricVariationTrace
          (DifferentialGeometry.Analysis.Entropy.Perelman.fFunctionalBracket (scalarCurvaturePath s0)
            (gradPotentialNormSqPath s0))
          (fFunctionalBracketVariation scalarCurvatureVariation
            gradPotentialNormSqVariation) x
        ∂(volumeMeasureFamily (I := I) (M := M) G s0))
      s0 :=
  expWeightedMeasureIntegral_hasDerivAt_at
    (I := I) (M := M) G
    (potentialPath := potentialPath)
    (phiPath := fun s : Real => fun x : M =>
      DifferentialGeometry.Analysis.Entropy.Perelman.fFunctionalBracket (scalarCurvaturePath s)
        (gradPotentialNormSqPath s) x)
    (s0 := s0)
    (potentialVariation := potentialVariation)
    (metricVariationTrace := metricVariationTrace)
    (phiVariation :=
      fFunctionalBracketVariation scalarCurvatureVariation
        gradPotentialNormSqVariation)
    hpotential_deriv
    (fFunctionalBracket_hasDerivAt
      (M := M) (scalarCurvaturePath := scalarCurvaturePath)
      (gradPotentialNormSqPath := gradPotentialNormSqPath)
      (s0 := s0)
      (scalarCurvatureVariation := scalarCurvatureVariation)
      (gradPotentialNormSqVariation := gradPotentialNormSqVariation)
      hscalar_deriv hgrad_deriv)
    htrace hmetric_regularity hintegrand_regularity

theorem closedBase_deriv
    [T2Space M] [CompactSpace M]
    (G : DifferentialGeometry.Geometry.Curvature.MetricConnectionFamily (I := I) (M := M) Real)
    {scalarCurvaturePath lapPotentialPath potentialPath :
      Real -> M -> Real}
    {s0 : Real}
    {scalarCurvatureVariation lapPotentialVariation potentialVariation
      metricVariationTrace : M -> Real}
    (hscalar_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => scalarCurvaturePath s x)
          (scalarCurvatureVariation x) s0)
    (hlap_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => lapPotentialPath s x)
          (lapPotentialVariation x) s0)
    (hpotential_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => potentialPath s x)
          (potentialVariation x) s0)
    (htrace :
      ∀ x : M,
        traceTimeDerivMetricAt (I := I) G s0 x = metricVariationTrace x)
    (hmetric_regularity :
      MetricFamilyRegularAt (I := I)
        (metricFamilyForMeasure (I := I) (M := M) G) s0)
    (hintegrand_regularity :
      FunctionRegularAt
        (fun s : Real => fun x : M =>
          DifferentialGeometry.Analysis.Entropy.Perelman.expNegPotentialDensity (potentialPath s) x *
            DifferentialGeometry.Analysis.Entropy.Perelman.fFunctionalClosedBracket (scalarCurvaturePath s)
              (lapPotentialPath s) x)
        s0) :
    HasDerivAt
      (fun s : Real =>
        ∫ x,
          DifferentialGeometry.Analysis.Entropy.Perelman.expNegPotentialDensity (potentialPath s) x *
            DifferentialGeometry.Analysis.Entropy.Perelman.fFunctionalClosedBracket (scalarCurvaturePath s)
              (lapPotentialPath s) x
          ∂(volumeMeasureFamily (I := I) (M := M) G s))
      (∫ x,
        DifferentialGeometry.Analysis.Entropy.Perelman.expWeightedIntegralVariationIntegrand
          (potentialPath s0) potentialVariation metricVariationTrace
          (DifferentialGeometry.Analysis.Entropy.Perelman.fFunctionalClosedBracket (scalarCurvaturePath s0)
            (lapPotentialPath s0))
          (DifferentialGeometry.Analysis.Entropy.Perelman.fFunctionalClosedBracketVariation scalarCurvatureVariation
            lapPotentialVariation) x
        ∂(volumeMeasureFamily (I := I) (M := M) G s0))
      s0 :=
  expWeightedMeasureIntegral_hasDerivAt_at
    (I := I) (M := M) G
    (potentialPath := potentialPath)
    (phiPath := fun s : Real => fun x : M =>
      DifferentialGeometry.Analysis.Entropy.Perelman.fFunctionalClosedBracket (scalarCurvaturePath s)
        (lapPotentialPath s) x)
    (s0 := s0)
    (potentialVariation := potentialVariation)
    (metricVariationTrace := metricVariationTrace)
    (phiVariation :=
      DifferentialGeometry.Analysis.Entropy.Perelman.fFunctionalClosedBracketVariation scalarCurvatureVariation
        lapPotentialVariation)
    hpotential_deriv
    (closedBracket_deriv
      (M := M) (scalarCurvaturePath := scalarCurvaturePath)
      (lapPotentialPath := lapPotentialPath) (s0 := s0)
      (scalarCurvatureVariation := scalarCurvatureVariation)
      (lapPotentialVariation := lapPotentialVariation)
      hscalar_deriv hlap_deriv)
    htrace hmetric_regularity hintegrand_regularity

omit [TopologicalSpace M] in
theorem FFunctionalHasFirstVariationAt_of_baseIntegral_hasDerivAt
    [MeasurableSpace M]
    {muPath : Real -> Measure M}
    {scalarCurvaturePath gradPotentialNormSqPath potentialPath :
      Real -> M -> Real}
    {s0 firstVariation : Real}
    (hbase_eq :
      (fun s : Real =>
        DifferentialGeometry.Analysis.Entropy.Perelman.fFunctional (muPath s) (scalarCurvaturePath s)
          (gradPotentialNormSqPath s) (potentialPath s))
        =ᶠ[nhds s0]
      fun s : Real =>
        ∫ x,
          DifferentialGeometry.Analysis.Entropy.Perelman.expNegPotentialDensity (potentialPath s) x *
            DifferentialGeometry.Analysis.Entropy.Perelman.fFunctionalBracket (scalarCurvaturePath s)
              (gradPotentialNormSqPath s) x
          ∂(muPath s))
    (hbase :
      HasDerivAt
        (fun s : Real =>
          ∫ x,
            DifferentialGeometry.Analysis.Entropy.Perelman.expNegPotentialDensity (potentialPath s) x *
              DifferentialGeometry.Analysis.Entropy.Perelman.fFunctionalBracket (scalarCurvaturePath s)
                (gradPotentialNormSqPath s) x
            ∂(muPath s))
        firstVariation s0) :
    HasDerivAt (DifferentialGeometry.Analysis.Entropy.Perelman.fFunctionalAlong muPath scalarCurvaturePath gradPotentialNormSqPath potentialPath) firstVariation s0 := by
  unfold DifferentialGeometry.Analysis.Entropy.Perelman.fFunctionalAlong
  exact hbase.congr_of_eventuallyEq hbase_eq

theorem FFunctionalHasFirstVariationAt_of_volumeVariation
    [T2Space M] [CompactSpace M]
    (G : DifferentialGeometry.Geometry.Curvature.MetricConnectionFamily (I := I) (M := M) Real)
    {scalarCurvaturePath gradPotentialNormSqPath potentialPath :
      Real -> M -> Real}
    {s0 : Real}
    {scalarCurvatureVariation gradPotentialNormSqVariation potentialVariation
      metricVariationTrace : M -> Real}
    (hbase_eq :
      (fun s : Real =>
        DifferentialGeometry.Analysis.Entropy.Perelman.fFunctional (volumeMeasureFamily (I := I) (M := M) G s)
          (scalarCurvaturePath s) (gradPotentialNormSqPath s)
          (potentialPath s))
        =ᶠ[nhds s0]
      fun s : Real =>
        ∫ x,
          DifferentialGeometry.Analysis.Entropy.Perelman.expNegPotentialDensity (potentialPath s) x *
            DifferentialGeometry.Analysis.Entropy.Perelman.fFunctionalBracket (scalarCurvaturePath s)
              (gradPotentialNormSqPath s) x
          ∂(volumeMeasureFamily (I := I) (M := M) G s))
    (hscalar_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => scalarCurvaturePath s x)
          (scalarCurvatureVariation x) s0)
    (hgrad_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => gradPotentialNormSqPath s x)
          (gradPotentialNormSqVariation x) s0)
    (hpotential_deriv :
      ∀ x : M,
        HasDerivAt (fun s : Real => potentialPath s x)
          (potentialVariation x) s0)
    (htrace :
      ∀ x : M,
        traceTimeDerivMetricAt (I := I) G s0 x = metricVariationTrace x)
    (hmetric_regularity :
      MetricFamilyRegularAt (I := I)
        (metricFamilyForMeasure (I := I) (M := M) G) s0)
    (hintegrand_regularity :
      FunctionRegularAt
        (fun s : Real => fun x : M =>
          DifferentialGeometry.Analysis.Entropy.Perelman.expNegPotentialDensity (potentialPath s) x *
            DifferentialGeometry.Analysis.Entropy.Perelman.fFunctionalBracket (scalarCurvaturePath s)
              (gradPotentialNormSqPath s) x)
        s0) :
    HasDerivAt (DifferentialGeometry.Analysis.Entropy.Perelman.fFunctionalAlong (volumeMeasureFamily (I := I) (M := M) G) scalarCurvaturePath gradPotentialNormSqPath potentialPath) (∫ x,
        DifferentialGeometry.Analysis.Entropy.Perelman.expWeightedIntegralVariationIntegrand
          (potentialPath s0) potentialVariation metricVariationTrace
          (DifferentialGeometry.Analysis.Entropy.Perelman.fFunctionalBracket (scalarCurvaturePath s0)
            (gradPotentialNormSqPath s0))
          (fFunctionalBracketVariation scalarCurvatureVariation
            gradPotentialNormSqVariation) x
        ∂(volumeMeasureFamily (I := I) (M := M) G s0)) s0 := by
  exact FFunctionalHasFirstVariationAt_of_baseIntegral_hasDerivAt
    (M := M)
    (muPath := volumeMeasureFamily (I := I) (M := M) G)
    hbase_eq
    (fFunctionalBaseIntegral_hasDerivAt_at
      (I := I) (M := M) G
      hscalar_deriv hgrad_deriv hpotential_deriv htrace hmetric_regularity
      hintegrand_regularity)

end Geometry

end

end DifferentialGeometry.PDE.RicciFlow.Entropy
