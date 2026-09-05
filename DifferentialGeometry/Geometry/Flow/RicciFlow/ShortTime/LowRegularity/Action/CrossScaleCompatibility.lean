import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Lifting.SecondOrder
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Remainder.Symmetry
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Nonautonomous.L2.Realization
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Time.Actions

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal NNReal InnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Spectral.MetricRealization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem congrOp_aemeas {g : SmoothRiemannianMetric I M} {p q b T : ℝ}
    (hpq : p = q)
    (A : ℝ → TensorHs (I := I) (M := M) g 0 2 q →L[ℝ]
      TensorHs (I := I) (M := M) g 0 2 b)
    (hA : AEStronglyMeasurable A (timeMeasure T)) :
    AEStronglyMeasurable
      (fun t => (A t).comp (tensorHsCongrL (I := I) (M := M) g 0 2 hpq))
      (timeMeasure T) := by
  cases hpq
  simpa only [tensorHsCongrL_refl, ContinuousLinearMap.comp_id] using hA

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem congrOp_memLp {g : SmoothRiemannianMetric I M} {p q b T : ℝ}
    (hpq : p = q)
    (A : ℝ → TensorHs (I := I) (M := M) g 0 2 q →L[ℝ]
      TensorHs (I := I) (M := M) g 0 2 b)
    (hA : MemLp A 2 (timeMeasure T)) :
    MemLp (fun t => (A t).comp (tensorHsCongrL (I := I) (M := M) g 0 2 hpq)) 2
      (timeMeasure T) := by
  cases hpq
  simpa only [tensorHsCongrL_refl, ContinuousLinearMap.comp_id] using hA

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem congrOp_norm_le {g : SmoothRiemannianMetric I M} {p q b T C : ℝ}
    (hpq : p = q)
    (A : ℝ → TensorHs (I := I) (M := M) g 0 2 q →L[ℝ]
      TensorHs (I := I) (M := M) g 0 2 b)
    (hC : ∀ᵐ t ∂timeMeasure T, ‖A t‖ ≤ C) :
    ∀ᵐ t ∂timeMeasure T,
      ‖(A t).comp (tensorHsCongrL (I := I) (M := M) g 0 2 hpq)‖ ≤ C := by
  filter_upwards [hC] with t ht
  exact (opNorm_comp_congr_le (I := I) (M := M) hpq (A t)).trans ht

def liftSecondOrderActionToH2 (g : SmoothRiemannianMetric I M) {ρ δ : ℝ}
    (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    {T R : ℝ} (hT : 0 < T)
    (f : timeL2 (TensorHs (I := I) (M := M) g 0 2 (1 : ℝ)) T)
    (hR : 0 ≤ R)
    (hball : ∀ᵐ t ∂timeMeasure T,
      ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
        (show (1 : ℝ) + 1 ≤ (1 : ℝ) + 2 by linarith)
        (maximalRegularityDuhamelSolutionField (I := I) (M := M) (1 : ℝ) hT
          (0 : TensorHs (I := I) (M := M) g 0 2 ((1 : ℝ) + 2)) f t)‖ ≤ R) :
    ℝ → (TensorHs (I := I) (M := M) g 0 2 ((2 : ℝ) + 2) →L[ℝ]
      TensorHs (I := I) (M := M) g 0 2 (2 : ℝ)) :=
  fun t =>
    (lowRegularitySecondOrderActionTotal (I := I) (M := M) g hρ hδ0 hδ_le hreal hT f hR hball
      t).comp
      (tensorHsCongrL (I := I) (M := M) g 0 2
        (show (2 : ℝ) + 2 = (4 : ℝ) by norm_num))

theorem liftSecondOrderActionToH2_measurable_and_bounded
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) {ρ₀ δ : ℝ}
    (hρ₀ : 0 < ρ₀) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ₀ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ) :
    ∃ ρ C : ℝ, 0 < ρ ∧ ρ ≤ ρ₀ ∧ 0 ≤ C ∧
      ∀ (hρ0 : 0 ≤ ρ)
        (hreal' : ∀ S : SmoothCcTensor g 0 2,
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
            gFibreOpBound (I := I) (M := M) g
              (ccTensorBilinSymm (I := I) g S) δ)
        {R : ℝ} (hR : 0 ≤ R), R ≤ ρ →
        ∀ {T : ℝ} (hT : 0 < T)
          (f : timeL2 (TensorHs (I := I) (M := M) g 0 2 (1 : ℝ)) T)
          (hball : ∀ᵐ t ∂timeMeasure T,
            ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
              (show (1 : ℝ) + 1 ≤ (1 : ℝ) + 2 by linarith)
              (maximalRegularityDuhamelSolutionField (I := I) (M := M) (1 : ℝ) hT
                (0 : TensorHs (I := I) (M := M) g 0 2 ((1 : ℝ) + 2))
                f t)‖ ≤ R),
          AEStronglyMeasurable
              (liftSecondOrderActionToH2 (I := I) (M := M) g hρ0 hδ0 hδ_le hreal' hT f hR
                hball)
              (timeMeasure T) ∧
            (∀ᵐ t ∂timeMeasure T,
              ‖liftSecondOrderActionToH2 (I := I) (M := M) g hρ0 hδ0 hδ_le hreal' hT f hR
                hball t‖ ≤ C * ρ) := by
  obtain ⟨ρ, C, hρ, hρle, hC, hdata⟩ :=
    lowRegularitySecondOrderActionTotal_measurable_and_bounded (I := I) (M := M) hDim g hρ₀ hδ0 hδ_le hreal
  refine ⟨ρ, C, hρ, hρle, hC, ?_⟩
  intro hρ0 hreal' R hR hRρ T hT f hball
  obtain ⟨hmeas, hbd⟩ := hdata hρ0 hreal' hR hRρ hT f hball
  exact ⟨congrOp_aemeas (I := I) (M := M) _ _ hmeas,
    congrOp_norm_le (I := I) (M := M) _ _ hbd⟩

def liftFirstOrderActionToH2 (g : SmoothRiemannianMetric I M) {ρ δ : ℝ}
    (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    {T : ℝ} (hT : 0 < T)
    (f : timeL2 (TensorHs (I := I) (M := M) g 0 2 (1 : ℝ)) T) :
    ℝ → (TensorHs (I := I) (M := M) g 0 2 ((2 : ℝ) + 1) →L[ℝ]
      TensorHs (I := I) (M := M) g 0 2 (2 : ℝ)) :=
  fun t =>
    (lowRegularityFirstOrderActionTime (I := I) (M := M) g hρ hδ0 hδ_le hreal hT f t).comp
      (tensorHsCongrL (I := I) (M := M) g 0 2
        (show (2 : ℝ) + 1 = (3 : ℝ) by norm_num))

theorem liftFirstOrderActionToH2_memLp
    (g : SmoothRiemannianMetric I M) {ρ δ : ℝ}
    (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (hcont : Continuous (lowerScaleFirstOrderActionThirdToSecondOrder (I := I) (M := M) g hρ hδ0 hδ_le hreal))
    {Φ : ℝ} (hΦ : 0 ≤ Φ)
    (hlin : ∀ v : TensorHs (I := I) (M := M) g 0 2 (3 : ℝ),
      ‖show TensorHs (I := I) (M := M) g 0 2 (3 : ℝ) →L[ℝ]
          TensorHs (I := I) (M := M) g 0 2 (2 : ℝ) from
        lowerScaleFirstOrderActionThirdToSecondOrder (I := I) (M := M) g hρ hδ0 hδ_le hreal v‖ ≤ Φ * (1 + ‖v‖))
    {T : ℝ} (hT : 0 < T)
    (f : timeL2 (TensorHs (I := I) (M := M) g 0 2 (1 : ℝ)) T) :
    AEStronglyMeasurable
        (liftFirstOrderActionToH2 (I := I) (M := M) g hρ hδ0 hδ_le hreal hT f)
        (timeMeasure T) ∧
      MemLp (liftFirstOrderActionToH2 (I := I) (M := M) g hρ hδ0 hδ_le hreal hT f) 2
        (timeMeasure T) := by
  obtain ⟨hmeas, -, hmem⟩ :=
    lowRegularityFirstOrderActionTime_memLp (I := I) (M := M) g hρ hδ0 hδ_le hreal hcont hΦ hlin hT f
  exact ⟨congrOp_aemeas (I := I) (M := M) _ _ hmeas,
    congrOp_memLp (I := I) (M := M) _ _ hmem⟩

omit [BoundarylessManifold I M] in
theorem exists_compatible_cross_scale_field_realization
    {g : SmoothRiemannianMetric I M} {T aLo aHi : ℝ}
    (hlo : aLo = aHi - 1) (hOrd : aLo ≤ aHi)
    (hOrdA1 : aLo + 1 ≤ aHi + 1) (hOrdSt : aLo + 2 ≤ aHi + 2)
    (hOrdUp : aHi ≤ aHi + 1) (hOrdRp : aLo + 2 ≤ aHi + 1)
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
    ∃ (uHi : MaximalRegularitySolutionSpace (I := I) (M := M)
        (g := g) (r := 0) (s := 2) aHi T)
      (fHi : timeL2 (TensorHs (I := I) (M := M) g 0 2 aHi) T)
      (u : CrossScaleField (I := I) (M := M) g 0 2 aHi T),
      u.lowRegularity = uHi ∧
        u.highRegularity = maximalRegularityDuhamelSolutionField (I := I) (M := M) aHi hT 0 fHi ∧
        fHi =
          nonautL2Map (I := I) (M := M) hT hT1
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
              A2Hi hA2Hi C2Hi hC2Hi A1Hi hA1Hi fHi +
            f0Hi ∧
        timeH1.trace0 _ T u.lowRegularity =
          (0 : TensorHs (I := I) (M := M) g 0 2 aHi) ∧
        timeH1.timeDeriv _ T u.lowRegularity =
          timeScaleLaplacian (I := I) (M := M) aHi u.highRegularity + fHi ∧
        timeL2Inclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
            hOrd fHi = fLo ∧
        (∀ᵐ t ∂timeMeasure T,
          tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
              hOrd (fHi t) = fLo t) ∧
        (∀ t ∈ Icc (0 : ℝ) T,
          tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
              hOrd (u.lowRegularity.toFun t) =
            (maximalRegularityDuhamelMap (I := I) (M := M) aLo hT 0 fLo).toFun t) ∧
        u.repr 0 = (0 : TensorHs (I := I) (M := M) g 0 2 (aHi + 1)) ∧
        ContinuousOn (fun t => ‖u.repr t‖ ^ 2) (Icc (0 : ℝ) T) ∧
        (∀ t ∈ Icc (0 : ℝ) T,
          tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
              hOrdUp (u.repr t) = u.lowRegularity.toFun t) ∧
        (fun t => tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          hOrdRp (u.repr t)) =ᵐ[timeMeasure T]
            fun t => maximalRegularityDuhamelSolutionField (I := I) (M := M)
              aLo hT 0 fLo t := by
  subst hlo
  obtain ⟨uHi, fHi, huHi, hfHi, htrace, hderiv, hforce, hfield, hforce_ae, -⟩ :=
    exists_compatible_cross_scale_solution (I := I) (M := M) (g := g)
      rfl hOrd hOrdA1 hOrdSt hT hT1
      A2Hi hA2Hi C2Hi hC2Hi A1Hi hA1Hi f0Hi hsmallHi
      A2Lo hA2Lo C2Lo hC2Lo A1Lo hA1Lo f0Lo hsmallLo
      hA2compat hA1compat hf0 fLo hfLo
  obtain ⟨u, hulo, huhi, htrace', hpde', -, hcarrier, hzero, hcontsq,
      hreprlo, hreprlow⟩ :=
    nonautL2_realize (I := I) (M := M) hT hT1
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
      A2Hi hA2Hi C2Hi hC2Hi A1Hi hA1Hi f0Hi fLo uHi fHi huHi hfHi htrace
      hderiv hforce hfield
  exact ⟨uHi, fHi, u, hulo, huhi, hfHi, htrace', hpde', hforce, hforce_ae,
    hcarrier, hzero, hcontsq, hreprlo, hreprlow⟩

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem norm_incl_congr (g : SmoothRiemannianMetric I M)
    {a b c d : ℝ} (hac : a = c) (hbd : b = d) (hab : a ≤ b) (hcd : c ≤ d)
    (u : TensorHs (I := I) (M := M) g 0 2 b) :
    ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2) hcd
        (tensorHsCongr (I := I) (M := M) g 0 2 hbd u)‖ =
      ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2) hab u‖ := by
  rw [← tensorHsCongr_incl (I := I) (M := M) hac hbd hab hcd u,
    norm_tensorHsCongr]

theorem low_radial_retractions_fix_maximal_regularity_solution
    (g₀ g_bg : SmoothRiemannianMetric I M) {R δ T ρ : ℝ}
    (hR : 0 < R) (hδ : δ < 1)
    (hreal : ∀ S : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀
        (((1 : ℕ) : ℝ) + 1) S‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ S) δ)
    (hcont : Continuous (deTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg hR hδ hreal))
    (hcore : Continuous (deTurckRemainderOnSmoothCore (I := I) (M := M) g₀ g_bg hδ hreal))
    (hρ : 0 < ρ) (hRρ : R ≤ ρ) (hT : 0 < T)
    (u : ℝ → lowerState (I := I) (M := M) g₀ 1 R)
    (gforce : timeL2 (TensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T)
    (hforce : gforce =ᵐ[timeMeasure T]
      fun t => deTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg hR hδ hreal (u t))
    (hball : ∀ᵐ t ∂timeMeasure T,
      maximalRegularityDuhamelSolutionField (I := I) (M := M) ((1 : ℕ) : ℝ) hT
          (0 : TensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2)) gforce t ∈
        lowerState (I := I) (M := M) g₀ 1 R) :
    (∀ᵐ t ∂timeMeasure T,
        lowRadialH3 (I := I) (M := M) g₀ ρ
            (tensorHsCongr (I := I) (M := M) g₀ 0 2
              (show ((1 : ℕ) : ℝ) + 2 = (3 : ℝ) by norm_num)
              (maximalRegularityDuhamelSolutionField (I := I) (M := M) ((1 : ℕ) : ℝ) hT
                (0 : TensorHs (I := I) (M := M) g₀ 0 2
                  (((1 : ℕ) : ℝ) + 2)) gforce t)) =
          tensorHsCongr (I := I) (M := M) g₀ 0 2
            (show ((1 : ℕ) : ℝ) + 2 = (3 : ℝ) by norm_num)
            (maximalRegularityDuhamelSolutionField (I := I) (M := M) ((1 : ℕ) : ℝ) hT
              (0 : TensorHs (I := I) (M := M) g₀ 0 2
                (((1 : ℕ) : ℝ) + 2)) gforce t)) ∧
      (∀ᵐ t ∂timeMeasure T,
        lowRadialHs (I := I) (M := M) g₀ ρ
            (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show (2 : ℝ) ≤ (3 : ℝ) by norm_num)
              (tensorHsCongr (I := I) (M := M) g₀ 0 2
                (show ((1 : ℕ) : ℝ) + 2 = (3 : ℝ) by norm_num)
                (maximalRegularityDuhamelSolutionField (I := I) (M := M) ((1 : ℕ) : ℝ) hT
                  (0 : TensorHs (I := I) (M := M) g₀ 0 2
                    (((1 : ℕ) : ℝ) + 2)) gforce t))) =
          tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
            (show (2 : ℝ) ≤ (3 : ℝ) by norm_num)
            (tensorHsCongr (I := I) (M := M) g₀ 0 2
              (show ((1 : ℕ) : ℝ) + 2 = (3 : ℝ) by norm_num)
              (maximalRegularityDuhamelSolutionField (I := I) (M := M) ((1 : ℕ) : ℝ) hT
                (0 : TensorHs (I := I) (M := M) g₀ 0 2
                  (((1 : ℕ) : ℝ) + 2)) gforce t))) := by
  have hsymm := duhamel_solution_of_deTurck_remainder_symmetric_h3_ae (I := I) (M := M) g₀ g_bg hR hδ hreal
    hcont hcore (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hT u gforce hforce
  have hballT : ∀ᵐ t ∂timeMeasure T,
      ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          (show (2 : ℝ) ≤ (3 : ℝ) by norm_num)
          (tensorHsCongr (I := I) (M := M) g₀ 0 2
            (show ((1 : ℕ) : ℝ) + 2 = (3 : ℝ) by norm_num)
            (maximalRegularityDuhamelSolutionField (I := I) (M := M) ((1 : ℕ) : ℝ) hT
              (0 : TensorHs (I := I) (M := M) g₀ 0 2
                (((1 : ℕ) : ℝ) + 2)) gforce t))‖ ≤ R := by
    filter_upwards [hball] with t ht
    rw [norm_incl_congr (I := I) (M := M) g₀
      (show ((1 : ℕ) : ℝ) + 1 = (2 : ℝ) by norm_num)
      (show ((1 : ℕ) : ℝ) + 2 = (3 : ℝ) by norm_num)
      (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
      (show (2 : ℝ) ≤ (3 : ℝ) by norm_num)]
    exact ht
  exact low_radial_retractions_eq_self_almost_everywhere
    (I := I) (M := M) g₀ hρ hRρ hsymm hballT

def deTurckRemainderOnSmoothCoreAt (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ) {R δ : ℝ}
    (hδ : δ < 1)
    (hreal : ∀ S : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 1) S‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ S) δ) :
    smoothCore (I := I) (M := M) g₀ R →
      TensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ) :=
  fun x => deTurckSmoothN (I := I) (M := M) g₀ g_bg a
    (ccTensor02Symm (I := I) (M := M) g₀ (coreRep g₀ x)) hδ
    (hreal _ (coreSymm_h2 (I := I) (M := M) g₀ x))

theorem deTurckRemainderOnSmoothCoreAt_one (g₀ g_bg : SmoothRiemannianMetric I M) {R δ : ℝ}
    (hδ : δ < 1)
    (hreal : ∀ S : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 1) S‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ S) δ) :
    deTurckRemainderOnSmoothCoreAt (I := I) (M := M) g₀ g_bg 1 hδ hreal =
      deTurckRemainderOnSmoothCore (I := I) (M := M) g₀ g_bg hδ hreal :=
  rfl

theorem deTurckSmoothN_incl (g₀ g_bg : SmoothRiemannianMetric I M)
    {a b : ℕ} (hab : (a : ℝ) ≤ (b : ℝ)) (S : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ S) δ) :
    tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2) hab
        (deTurckSmoothN (I := I) (M := M) g₀ g_bg b S hδ_lt hδ) =
      deTurckSmoothN (I := I) (M := M) g₀ g_bg a S hδ_lt hδ := by
  rw [smoothN_eq_embed (I := I) (M := M) g₀ g_bg b S hδ_lt hδ,
    smoothN_eq_embed (I := I) (M := M) g₀ g_bg a S hδ_lt hδ,
    tensorHsInclusion_smoothCcToTensorHs (I := I) (M := M) g₀ hab]

theorem coreNAt_incl (g₀ g_bg : SmoothRiemannianMetric I M) {R δ : ℝ}
    {a b : ℕ} (hab : (a : ℝ) ≤ (b : ℝ)) (hδ : δ < 1)
    (hreal : ∀ S : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 1) S‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ S) δ)
    (x : smoothCore (I := I) (M := M) g₀ R) :
    tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2) hab
        (deTurckRemainderOnSmoothCoreAt (I := I) (M := M) g₀ g_bg b hδ hreal x) =
      deTurckRemainderOnSmoothCoreAt (I := I) (M := M) g₀ g_bg a hδ hreal x :=
  deTurckSmoothN_incl (I := I) (M := M) g₀ g_bg hab _ hδ _

theorem included_high_order_forcing_eq_deTurck_remainder_ae
    (g₀ g_bg : SmoothRiemannianMetric I M) {R δ T σ : ℝ}
    (hR : 0 < R) (hδ : δ < 1)
    (hreal : ∀ S : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀
        (((1 : ℕ) : ℝ) + 1) S‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ S) δ)
    (hOrd : ((1 : ℕ) : ℝ) ≤ σ)
    (state : ℝ → lowerState (I := I) (M := M) g₀ 1 R)
    (fHi : timeL2 (TensorHs (I := I) (M := M) g₀ 0 2 σ) T)
    (fLo : timeL2 (TensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T)
    (hincl : ∀ᵐ t ∂timeMeasure T,
      tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        hOrd (fHi t) = fLo t)
    (hforce : fLo =ᵐ[timeMeasure T]
      fun t => deTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg hR hδ hreal (state t)) :
    ∀ᵐ t ∂timeMeasure T,
      tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          hOrd (fHi t) =
        deTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg hR hδ hreal (state t) := by
  filter_upwards [hincl, hforce] with t h1 h2
  rw [h1, h2]

theorem high_order_forcing_eq_lifted_deTurck_remainder_ae
    (g₀ g_bg : SmoothRiemannianMetric I M) {R δ T σ : ℝ}
    (hR : 0 < R) (hδ : δ < 1)
    (hreal : ∀ S : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀
        (((1 : ℕ) : ℝ) + 1) S‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ S) δ)
    (hOrd : ((1 : ℕ) : ℝ) ≤ σ)
    (state : ℝ → lowerState (I := I) (M := M) g₀ 1 R)
    (fHi : timeL2 (TensorHs (I := I) (M := M) g₀ 0 2 σ) T)
    (fLo : timeL2 (TensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T)
    (N2 : lowerState (I := I) (M := M) g₀ 1 R →
      TensorHs (I := I) (M := M) g₀ 0 2 σ)
    (hN2 : ∀ v : lowerState (I := I) (M := M) g₀ 1 R,
      tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
          hOrd (N2 v) =
        deTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg hR hδ hreal v)
    (hincl : ∀ᵐ t ∂timeMeasure T,
      tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        hOrd (fHi t) = fLo t)
    (hforce : fLo =ᵐ[timeMeasure T]
      fun t => deTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg hR hδ hreal (state t)) :
    (fun t => fHi t) =ᵐ[timeMeasure T] fun t => N2 (state t) := by
  filter_upwards [included_high_order_forcing_eq_deTurck_remainder_ae (I := I) (M := M) g₀ g_bg hR hδ hreal hOrd
    state fHi fLo hincl hforce] with t ht
  exact tensorHsInclusion_injective (I := I) (M := M) (g := g₀)
    (r := 0) (s := 2) hOrd (ht.trans (hN2 (state t)).symm)

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
