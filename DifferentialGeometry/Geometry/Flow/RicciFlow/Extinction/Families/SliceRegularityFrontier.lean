import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.InitialRampBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.LocalRegularity

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

def CurveShorteningSliceRegularity (B : RicciBackground (I := I) (M := Q) D a b)
    (L₀ : ℝ) : Prop :=
  ∀ (lambda : ℝ), 0 < lambda → lambda ≤ 1 → ∀ c : ProductCurve Q,
    c.IsSolutionOn B.family.metric lambda (Icc a b) →
    c.length B.family.metric lambda a ≤ L₀ →
    ∀ t ∈ Icc a b, c.SliceRegularity B.family.metric lambda t

omit [SigmaCompactSpace Q] hCompact hConnected hBoundary in
theorem CurveShorteningEnergyInput.sliceRegularity
    (B : RicciBackground (I := I) (M := Q) D a b) {L₀ : ℝ}
    (E : CurveShorteningEnergyInput (I := I) (M := Q) (D := D) (a := a) (b := b) B L₀) :
    CurveShorteningSliceRegularity (I := I) (Q := Q) (D := D) (a := a) (b := b) B L₀ :=
  fun lambda hlambda hlambda_one c hsol hlen t ht =>
    E.slice_product lambda hlambda hlambda_one b B.lt le_rfl (Icc a b) (Or.inr rfl) c hsol hlen t ht

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ Q]
  [SigmaCompactSpace Q] [T2Space Q] [CompactSpace Q] [ConnectedSpace Q] [I.Boundaryless] in
theorem initialRamp_constantLoop_projection_not_immersedOn (q : Q) :
    ¬ (initialRamp (fun _ : Surgery.Topology.Circle => q)).projection.ImmersedOn (I := I)
      (univ : Set ℝ) := by
  intro h
  have hX : (initialRamp (fun _ : Surgery.Topology.Circle => q)).projection.X (I := I) 0 0 = 0 := by
    change mfderiv 𝓘(ℝ, ℝ) I
      (fun y : ℝ => (initialRamp fun _ : Surgery.Topology.Circle => q).projection.lift y 0)
      0 (1 : ℝ) = 0
    have hlift : (fun y : ℝ => (initialRamp fun _ : Surgery.Topology.Circle => q).projection.lift y 0)
        = fun _ => q := rfl
    rw [hlift, mfderiv_const]
    rfl
  exact h 0 0 (mem_univ 0) hX

omit hT2 hCompact hConnected hBoundary [FiniteDimensional ℝ E] [CompleteSpace E]
  [SigmaCompactSpace Q] in
theorem initialRamp_constantLoop_rampData (g : SmoothRiemannianMetric I Q) {lambda : ℝ}
    (hlambda : 0 < lambda) (q : Q) :
    (initialRamp (fun _ : Surgery.Topology.Circle => q)).SmoothOn (I := I) (univ : Set ℝ) ∧
      (initialRamp (fun _ : Surgery.Topology.Circle => q)).IsRampOn (fun _ : ℝ => g) lambda
        (univ : Set ℝ) ∧
      (initialRamp (fun _ : Surgery.Topology.Circle => q)).degree = 1 ∧
      ¬ (initialRamp (fun _ : Surgery.Topology.Circle => q)).projection.ImmersedOn (I := I)
        (univ : Set ℝ) :=
  ⟨initialRamp_smoothOn (I := I) (Q := Q) contMDiff_const,
    initialRamp_isRampOn (I := I) g hlambda (fun _ : Surgery.Topology.Circle => q),
    rfl,
    initialRamp_constantLoop_projection_not_immersedOn (I := I) (Q := Q) q⟩

end DifferentialGeometry.PDE.RicciFlow.Extinction.Families
