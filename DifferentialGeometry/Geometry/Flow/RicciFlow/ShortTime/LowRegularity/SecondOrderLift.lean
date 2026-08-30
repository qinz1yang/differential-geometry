import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.NonautonomousL2Lift
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.TimeDependentLowOrderOperators
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.ExponentCongr

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal NNReal InnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Analysis.Calculus
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private abbrev metricH2 (g : SmoothRiemannianMetric I M) :=
  TensorHs (I := I) (M := M) g 0 2 (2 : ℝ)

private abbrev metricThirdOrderSobolev (g : SmoothRiemannianMetric I M) :=
  TensorHs (I := I) (M := M) g 0 2 (3 : ℝ)

private abbrev incl32 (g : SmoothRiemannianMetric I M) :
    metricThirdOrderSobolev (I := I) (M := M) g →L[ℝ] metricH2 (I := I) (M := M) g :=
  tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
    (by norm_num)

theorem lowRadialHs_eq_self
    (g : SmoothRiemannianMetric I M) {ρ : ℝ} (hρ : 0 ≤ ρ)
    {v : metricH2 (I := I) (M := M) g}
    (hsymm : symmHs (I := I) (M := M) g (by norm_num : (0 : ℝ) ≤ 2) v = v)
    (hv : ‖v‖ ≤ ρ) :
    lowRadialHs (I := I) (M := M) g ρ v = v := by
  refine (lowRadialHs_eq (I := I) (M := M) g hρ v).trans ?_
  refine Eq.trans (congrArg (ballRetraction ρ) hsymm) ?_
  exact ballRetraction_eq_self_of_mem hv

theorem lowRadialH3_eq_self
    (g : SmoothRiemannianMetric I M) {ρ : ℝ} (hρ : 0 < ρ)
    {u : metricThirdOrderSobolev (I := I) (M := M) g}
    (hsymm : symmHs (I := I) (M := M) g (by norm_num : (0 : ℝ) ≤ 3) u = u)
    (hu : ‖incl32 (I := I) (M := M) g u‖ ≤ ρ) :
    lowRadialH3 (I := I) (M := M) g ρ u = u := by
  refine (lowRadialH3_eq (I := I) (M := M) g hρ u).trans ?_
  refine Eq.trans
    (congrArg (lowScaleCutoff (incl32 (I := I) (M := M) g) ρ) hsymm) ?_
  exact lowScaleCutoff_eq_self _
    (tensorHsInclusion_injective (I := I) (M := M) (g := g)
      (r := 0) (s := 2) (by norm_num)) hu

theorem low_radial_retractions_eq_self_almost_everywhere
    (g : SmoothRiemannianMetric I M) {T ρ R : ℝ} (hρ : 0 < ρ) (hRρ : R ≤ ρ)
    {u : ℝ → metricThirdOrderSobolev (I := I) (M := M) g}
    (hsymm : ∀ᵐ t ∂timeMeasure T,
      symmHs (I := I) (M := M) g (by norm_num : (0 : ℝ) ≤ 3) (u t) = u t)
    (hball : ∀ᵐ t ∂timeMeasure T,
      ‖incl32 (I := I) (M := M) g (u t)‖ ≤ R) :
    (∀ᵐ t ∂timeMeasure T,
        lowRadialH3 (I := I) (M := M) g ρ (u t) = u t) ∧
      (∀ᵐ t ∂timeMeasure T,
        lowRadialHs (I := I) (M := M) g ρ
            (incl32 (I := I) (M := M) g (u t)) =
          incl32 (I := I) (M := M) g (u t)) := by
  constructor
  · filter_upwards [hsymm, hball] with t hs hb
    exact lowRadialH3_eq_self (I := I) (M := M) g hρ hs (hb.trans hRρ)
  · filter_upwards [hsymm, hball] with t hs hb
    refine lowRadialHs_eq_self (I := I) (M := M) g hρ.le ?_ (hb.trans hRρ)
    have hcomm := DFunLike.congr_fun
      (symmHs_incl (I := I) (M := M) g
        (τ := (2 : ℝ)) (σ := (3 : ℝ))
        (by norm_num) (by norm_num) (by norm_num)) (u t)
    simp only [ContinuousLinearMap.comp_apply] at hcomm
    refine hcomm.symm.trans ?_
    exact congrArg (incl32 (I := I) (M := M) g) hs

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem liftCompat_congr {g : SmoothRiemannianMetric I M}
    {aLo aHi pLo pHi qLo qHi : ℝ}
    (hLo : pLo = qLo) (hHi : pHi = qHi)
    (hOrd : aLo ≤ aHi) (hp : pLo ≤ pHi) (hq : qLo ≤ qHi)
    (AHi : TensorHs (I := I) (M := M) g 0 2 qHi →L[ℝ]
      TensorHs (I := I) (M := M) g 0 2 aHi)
    (ALo : TensorHs (I := I) (M := M) g 0 2 qLo →L[ℝ]
      TensorHs (I := I) (M := M) g 0 2 aLo)
    (hsq : (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          hOrd).comp AHi =
        ALo.comp
          (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            hq)) :
    (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          hOrd).comp
        (AHi.comp (tensorHsCongrL (I := I) (M := M) g 0 2 hHi)) =
      (ALo.comp (tensorHsCongrL (I := I) (M := M) g 0 2 hLo)).comp
        (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2) hp) := by
  have hnat := tensorHsCongrL_incl (I := I) (M := M) (g := g) (r := 0) (s := 2)
    hLo hHi hp hq
  rw [ContinuousLinearMap.comp_assoc, hnat,
    ← ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.comp_assoc, hsq]

omit [BoundarylessManifold I M] in
theorem exists_compatible_cross_scale_solution
    {g : SmoothRiemannianMetric I M} {T aLo aHi : ℝ}
    (hlo : aLo = aHi - 1) (hOrd : aLo ≤ aHi)
    (hOrdA1 : aLo + 1 ≤ aHi + 1) (hOrdSt : aLo + 2 ≤ aHi + 2)
    (hT : 0 < T) (hT1 : T ≤ 1)
    (A2Hi : ℝ → TensorHs (I := I) (M := M) g 0 2 (aHi + 2) →L[ℝ]
      TensorHs (I := I) (M := M) g 0 2 aHi)
    (hA2Hi : AEStronglyMeasurable A2Hi (timeMeasure T))
    (C2Hi : NNReal) (hC2Hi : ∀ᵐ t ∂timeMeasure T, ‖A2Hi t‖ ≤ (C2Hi : ℝ))
    (A1Hi : ℝ → TensorHs (I := I) (M := M) g 0 2 (aHi + 1) →L[ℝ]
      TensorHs (I := I) (M := M) g 0 2 aHi)
    (hA1Hi : MemLp A1Hi 2 (timeMeasure T))
    (f0Hi : timeL2 (TensorHs (I := I) (M := M) g 0 2 aHi) T)
    (hsmallHi : (C2Hi : ℝ) * (1 + T) +
      2 * Real.sqrt (1 + T) * ‖hA1Hi.toLp A1Hi‖ < 1)
    (A2Lo : ℝ → TensorHs (I := I) (M := M) g 0 2 (aLo + 2) →L[ℝ]
      TensorHs (I := I) (M := M) g 0 2 aLo)
    (hA2Lo : AEStronglyMeasurable A2Lo (timeMeasure T))
    (C2Lo : NNReal) (hC2Lo : ∀ᵐ t ∂timeMeasure T, ‖A2Lo t‖ ≤ (C2Lo : ℝ))
    (A1Lo : ℝ → TensorHs (I := I) (M := M) g 0 2 (aLo + 1) →L[ℝ]
      TensorHs (I := I) (M := M) g 0 2 aLo)
    (hA1Lo : MemLp A1Lo 2 (timeMeasure T))
    (f0Lo : timeL2 (TensorHs (I := I) (M := M) g 0 2 aLo) T)
    (hsmallLo : (C2Lo : ℝ) * (1 + T) +
      2 * Real.sqrt (1 + T) * ‖hA1Lo.toLp A1Lo‖ < 1)
    (hA2compat : ∀ᵐ t ∂timeMeasure T,
      (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          hOrd).comp (A2Hi t) =
        (A2Lo t).comp
          (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            hOrdSt))
    (hA1compat : ∀ᵐ t ∂timeMeasure T,
      (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          hOrd).comp (A1Hi t) =
        (A1Lo t).comp
          (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            hOrdA1))
    (hf0 : timeL2Inclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
        hOrd f0Hi = f0Lo)
    (fLo : timeL2 (TensorHs (I := I) (M := M) g 0 2 aLo) T)
    (hfLo : fLo =
      nonautL2Map (I := I) (M := M) hT hT1
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
          A2Lo hA2Lo C2Lo hC2Lo A1Lo hA1Lo fLo + f0Lo) :
    ∃ (uHi : MaxRegSolutionSpace (I := I) (M := M)
        (g := g) (r := 0) (s := 2) aHi T)
      (fHi : timeL2 (TensorHs (I := I) (M := M) g 0 2 aHi) T),
      uHi = maxRegDuhamelMap (I := I) (M := M) aHi hT 0 fHi ∧
        fHi =
          nonautL2Map (I := I) (M := M) hT hT1
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
              A2Hi hA2Hi C2Hi hC2Hi A1Hi hA1Hi fHi +
            f0Hi ∧
        timeH1.trace0 _ T uHi = 0 ∧
        timeH1.timeDeriv _ T uHi =
          timeScaleLaplacian (I := I) (M := M) aHi
              (maxRegDuhamelSolField (I := I) (M := M) aHi hT 0 fHi) +
            (timeOp A2Hi hA2Hi C2Hi hC2Hi
                (maxRegDuhamelSolField (I := I) (M := M) aHi hT 0 fHi) +
              a1L2Term (I := I) (M := M) hT hT1
                (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
                A1Hi hA1Hi fHi +
              f0Hi) ∧
        timeL2Inclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            hOrd fHi = fLo ∧
        timeL2Inclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            hOrdSt
            (maxRegDuhamelSolField (I := I) (M := M) aHi hT 0 fHi) =
          maxRegDuhamelSolField (I := I) (M := M) aLo hT 0 fLo ∧
        (∀ᵐ t ∂timeMeasure T,
          tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
              hOrd (fHi t) = fLo t) ∧
        (∀ᵐ t ∂timeMeasure T,
          tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
              hOrdSt
              (maxRegDuhamelSolField (I := I) (M := M)
                aHi hT 0 fHi t) =
            maxRegDuhamelSolField (I := I) (M := M) aLo hT 0 fLo t) := by
  subst hlo
  obtain ⟨uHi, fHi, huHi, hfHi, htrace, hderiv, hforce, hfield⟩ :=
    nonautL2_lift (I := I) (M := M) hT hT1
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
      A2Hi hA2Hi C2Hi hC2Hi A1Hi hA1Hi f0Hi hsmallHi
      A2Lo hA2Lo C2Lo hC2Lo A1Lo hA1Lo f0Lo hsmallLo
      hA2compat hA1compat hf0 fLo hfLo
  refine ⟨uHi, fHi, huHi, hfHi, htrace, hderiv, hforce, hfield, ?_, ?_⟩
  · have hcoe :
        timeL2Inclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            hOrd fHi =ᵐ[timeMeasure T]
          fun t =>
            tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
              hOrd (fHi t) :=
      (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
        hOrd).coeFn_compLpL (p := 2) (μ := timeMeasure T) fHi
    have hcoe2 :
        fLo =ᵐ[timeMeasure T]
          fun t =>
            tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
              hOrd (fHi t) := by
      rw [← hforce]
      exact hcoe
    filter_upwards [hcoe2] with t ht
    exact ht.symm
  · have hcoe :
        timeL2Inclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            hOrdSt
            (maxRegDuhamelSolField (I := I) (M := M)
              aHi hT 0 fHi) =ᵐ[timeMeasure T]
          fun t =>
            tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
              hOrdSt
              (maxRegDuhamelSolField (I := I) (M := M)
                aHi hT 0 fHi t) :=
      (tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
        hOrdSt).coeFn_compLpL (p := 2) (μ := timeMeasure T)
          (maxRegDuhamelSolField (I := I) (M := M) aHi hT 0 fHi)
    have hcoe2 :
        maxRegDuhamelSolField (I := I) (M := M)
            (aHi - 1) hT 0 fLo =ᵐ[timeMeasure T]
          fun t =>
            tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
              hOrdSt
              (maxRegDuhamelSolField (I := I) (M := M)
                aHi hT 0 fHi t) := by
      rw [← hfield]
      exact hcoe
    filter_upwards [hcoe2] with t ht
    exact ht.symm

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
