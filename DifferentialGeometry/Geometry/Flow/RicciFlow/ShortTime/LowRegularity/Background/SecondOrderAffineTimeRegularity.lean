import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Background.Time
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Background.SecondOrderSmallPerturbationBounds

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal NNReal InnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Analysis.Spectral
  (ccTensorToHs ccTensorToHs_smul ccToHsLin ccToHsLin_dense)

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private abbrev metricH4 (g : SmoothRiemannianMetric I M) :=
  TensorHs (I := I) (M := M) g 0 2 (4 : ℝ)

private abbrev metricThirdOrderSobolev (g : SmoothRiemannianMetric I M) :=
  TensorHs (I := I) (M := M) g 0 2 (3 : ℝ)

private abbrev metricH2 (g : SmoothRiemannianMetric I M) :=
  TensorHs (I := I) (M := M) g 0 2 (2 : ℝ)

private abbrev metricH1 (g : SmoothRiemannianMetric I M) :=
  TensorHs (I := I) (M := M) g 0 2 (1 : ℝ)

private abbrev a2HiOp (g : SmoothRiemannianMetric I M) :=
  metricH4 (I := I) (M := M) g →L[ℝ] metricH2 (I := I) (M := M) g

private abbrev a2LoOp (g : SmoothRiemannianMetric I M) :=
  metricThirdOrderSobolev (I := I) (M := M) g →L[ℝ] metricH1 (I := I) (M := M) g

private noncomputable abbrev incl32
    (g : SmoothRiemannianMetric I M) :
    metricThirdOrderSobolev (I := I) (M := M) g →L[ℝ]
      metricH2 (I := I) (M := M) g :=
  tensorHsInclusion (I := I) (M := M) (g := g)
    (r := 0) (s := 2) (by norm_num)

private noncomputable abbrev incl12
    (g : SmoothRiemannianMetric I M) :
    metricH2 (I := I) (M := M) g →L[ℝ]
      metricH1 (I := I) (M := M) g :=
  tensorHsInclusion (I := I) (M := M) (g := g)
    (r := 0) (s := 2) (by norm_num)

private noncomputable abbrev incl34
    (g : SmoothRiemannianMetric I M) :
    metricH4 (I := I) (M := M) g →L[ℝ]
      metricThirdOrderSobolev (I := I) (M := M) g :=
  tensorHsInclusion (I := I) (M := M) (g := g)
    (r := 0) (s := 2) (by norm_num)

private theorem a2HiBackground_total_le
    (g gB : SmoothRiemannianMetric I M) {ρ δ c : ℝ}
    (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (hcont : Continuous
      (lowerScaleSecondOrderActionFourthToSecondOrderBackground (I := I) (M := M) g gB hρ hδ0 hδ_le hreal))
    (hcore : ∀ S : SmoothCcTensor g 0 2,
      lowerScaleSecondOrderActionFourthToSecondOrderBackground (I := I) (M := M) g gB hρ hδ0 hδ_le hreal
          (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ) S) =
        (lowCoreActionCoefficientsBackground (I := I) (M := M)
          g gB hρ hδ0 hδ_le hreal S).secondOrderActionFourthToSecondOrder (I := I) (M := M))
    (hbd : ∀ S : SmoothCcTensor g 0 2,
      ‖(lowCoreActionCoefficientsBackground (I := I) (M := M)
          g gB hρ hδ0 hδ_le hreal S).secondOrderActionFourthToSecondOrder (I := I) (M := M)‖ ≤ c)
    (v : metricH2 (I := I) (M := M) g) :
    ‖show a2HiOp (I := I) (M := M) g from
      lowerScaleSecondOrderActionFourthToSecondOrderBackground (I := I) (M := M) g gB hρ hδ0 hδ_le hreal v‖ ≤ c := by
  have hdense : DenseRange
      (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ)) :=
    ccToHsLin_dense (I := I) (M := M) g 2 (by norm_num)
  have hclosed : IsClosed {w : metricH2 (I := I) (M := M) g |
      ‖show a2HiOp (I := I) (M := M) g from
        lowerScaleSecondOrderActionFourthToSecondOrderBackground (I := I) (M := M)
          g gB hρ hδ0 hδ_le hreal w‖ ≤ c} :=
    isClosed_le
      (Continuous.comp
        (continuous_norm (E := a2HiOp (I := I) (M := M) g)) hcont)
      continuous_const
  refine hdense.induction_on v hclosed ?_
  intro S
  have h := hbd S
  rw [← hcore S] at h
  exact h

private theorem a2LoBackground_total_le
    (g gB : SmoothRiemannianMetric I M) {ρ δ c : ℝ}
    (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (hcont : Continuous
      (lowerScaleSecondOrderActionThirdToFirstOrderBackground (I := I) (M := M) g gB hρ hδ0 hδ_le hreal))
    (hcore : ∀ S : SmoothCcTensor g 0 2,
      lowerScaleSecondOrderActionThirdToFirstOrderBackground (I := I) (M := M) g gB hρ hδ0 hδ_le hreal
          (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ) S) =
        (lowCoreActionCoefficientsBackground (I := I) (M := M)
          g gB hρ hδ0 hδ_le hreal S).secondOrderActionThirdToFirstOrder (I := I) (M := M))
    (hbd : ∀ S : SmoothCcTensor g 0 2,
      ‖(lowCoreActionCoefficientsBackground (I := I) (M := M)
          g gB hρ hδ0 hδ_le hreal S).secondOrderActionThirdToFirstOrder (I := I) (M := M)‖ ≤ c)
    (v : metricH2 (I := I) (M := M) g) :
    ‖show a2LoOp (I := I) (M := M) g from
      lowerScaleSecondOrderActionThirdToFirstOrderBackground (I := I) (M := M) g gB hρ hδ0 hδ_le hreal v‖ ≤ c := by
  have hdense : DenseRange
      (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ)) :=
    ccToHsLin_dense (I := I) (M := M) g 2 (by norm_num)
  have hclosed : IsClosed {w : metricH2 (I := I) (M := M) g |
      ‖show a2LoOp (I := I) (M := M) g from
        lowerScaleSecondOrderActionThirdToFirstOrderBackground (I := I) (M := M)
          g gB hρ hδ0 hδ_le hreal w‖ ≤ c} :=
    isClosed_le
      (Continuous.comp
        (continuous_norm (E := a2LoOp (I := I) (M := M) g)) hcont)
      continuous_const
  refine hdense.induction_on v hclosed ?_
  intro S
  have h := hbd S
  rw [← hcore S] at h
  exact h

theorem radialSecondOrderActionBackground_pairing_bound
    (hDim : Module.finrank ℝ E = 3)
    (g gB : SmoothRiemannianMetric I M)
    {ρ₀ δ : ℝ} (hρ₀ : 0 < ρ₀) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ₀ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ) :
    ∃ (ρ C : ℝ) (hρ_le : ρ ≤ ρ₀), 0 < ρ ∧ 0 ≤ C ∧
      ∀ {r : ℝ} (hr0 : 0 ≤ r) (hr_le : r ≤ ρ)
        (T : SmoothCcTensor g 0 2),
      let hreal' : ∀ S : SmoothCcTensor g 0 2,
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ r →
            gFibreOpBound (I := I) (M := M) g
              (ccTensorBilinSymm (I := I) g S) δ :=
        fun S hS => hreal S (hS.trans (hr_le.trans hρ_le))
      let A := lowCoreActionCoefficientsBackground (I := I) (M := M)
        g gB hr0 hδ0 hδ_le hreal' T
      ‖A.secondOrderActionFourthToSecondOrder (I := I) (M := M)‖ ≤ C * r ∧
        ‖A.secondOrderActionThirdToFirstOrder (I := I) (M := M)‖ ≤ C * r ∧
        (tensorHsInclusion (I := I) (M := M) (g := g)
            (r := 0) (s := 2) (show (1 : ℝ) ≤ 2 by norm_num)).comp
              (A.secondOrderActionFourthToSecondOrder (I := I) (M := M)) =
          (A.secondOrderActionThirdToFirstOrder (I := I) (M := M)).comp
            (tensorHsInclusion (I := I) (M := M) (g := g)
              (r := 0) (s := 2) (show (3 : ℝ) ≤ 4 by norm_num)) := by
  obtain ⟨ρ₂, C₂, hρ₂, hC₂, hc₂⟩ :=
    exists_lowerScaleSecondOrderCoefficient_background_smallPerturbation_secondOrder_bound (I := I) (M := M) hDim g gB
  obtain ⟨Cₐ, hCₐ, hpair⟩ :=
    secondOrderAction_sobolev_extension_bounds (I := I) (M := M) hDim g
  refine ⟨min ρ₀ ρ₂, Cₐ * C₂, min_le_left _ _, lt_min hρ₀ hρ₂,
    mul_nonneg hCₐ hC₂, ?_⟩
  intro r hr0 hr_le T
  dsimp only
  let S : SmoothCcTensor g 0 2 :=
    lowRadial (I := I) (M := M) g r T
  have hSr :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ r :=
    lowRadial_norm (I := I) (M := M) g hr0 T
  have hSδ :
      gFibreOpBound (I := I) (M := M) g
        (ccTensorBilinSymm (I := I) g S) δ :=
    hreal S (hSr.trans (hr_le.trans (min_le_left _ _)))
  have hzeroHs :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
        (0 : SmoothCcTensor g 0 2)‖ ≤ ρ₀ := by
    rw [show (0 : SmoothCcTensor g 0 2) =
        (0 : ℝ) • (0 : SmoothCcTensor g 0 2) by simp,
      ccTensorToHs_smul, zero_smul, norm_zero]
    exact hρ₀.le
  have hZδ :
      gFibreOpBound (I := I) (M := M) g
        (ccTensorBilinSymm (I := I) g
          (0 : SmoothCcTensor g 0 2)) δ :=
    hreal _ hzeroHs
  let A : LowerScaleActionCoefficients g :=
    lowCoreActionCoefficientsBackground (I := I) (M := M) g gB hr0 hδ0 hδ_le
      (fun P hP => hreal P (hP.trans (hr_le.trans (min_le_left _ _)))) T
  obtain ⟨hpoint, hjet⟩ :=
    hc₂ S
      (lowRadial_symm (I := I) (M := M) g r T)
      hδ_le hδ0 hSδ hZδ hr0 (hr_le.trans (min_le_right _ _)) hSr
  have hB : 0 ≤ C₂ * r := mul_nonneg hC₂ hr0
  obtain ⟨hHi, hLo, -, -, hcompat⟩ :=
    hpair A (C₂ * r) hB (by
      simpa only [A, lowCoreActionCoefficientsBackground, S] using hpoint) (by
      simpa only [A, lowCoreActionCoefficientsBackground, S] using hjet)
  exact ⟨hHi.trans_eq (by ring), hLo.trans_eq (by ring), hcompat⟩


theorem lowerScaleSecondOrderActionBackground_small
    (hDim : Module.finrank ℝ E = 3)
    (g gB : SmoothRiemannianMetric I M) {ρ₀ δ : ℝ}
    (hρ₀ : 0 < ρ₀) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ₀ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ) :
    ∃ (ρ C : ℝ) (_hρ : 0 < ρ) (hρ_le : ρ ≤ ρ₀), 0 ≤ C ∧
      ∀ {r : ℝ} (hr0 : 0 ≤ r) (hr_le : r ≤ ρ),
        let hreal' : ∀ S : SmoothCcTensor g 0 2,
            ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ r →
              gFibreOpBound (I := I) (M := M) g
                (ccTensorBilinSymm (I := I) g S) δ :=
          fun S hS => hreal S (hS.trans (hr_le.trans hρ_le))
        Continuous (lowerScaleSecondOrderActionFourthToSecondOrderBackground (I := I) (M := M)
            g gB hr0 hδ0 hδ_le hreal') ∧
          Continuous (lowerScaleSecondOrderActionThirdToFirstOrderBackground (I := I) (M := M)
            g gB hr0 hδ0 hδ_le hreal') ∧
          (∀ v : metricH2 (I := I) (M := M) g,
            ‖show a2HiOp (I := I) (M := M) g from
              lowerScaleSecondOrderActionFourthToSecondOrderBackground (I := I) (M := M)
                g gB hr0 hδ0 hδ_le hreal' v‖ ≤ C * r) ∧
          (∀ v : metricH2 (I := I) (M := M) g,
            ‖show a2LoOp (I := I) (M := M) g from
              lowerScaleSecondOrderActionThirdToFirstOrderBackground (I := I) (M := M)
                g gB hr0 hδ0 hδ_le hreal' v‖ ≤ C * r) ∧
          ∀ v : metricH2 (I := I) (M := M) g,
            (incl12 (I := I) (M := M) g).comp
                (lowerScaleSecondOrderActionFourthToSecondOrderBackground (I := I) (M := M)
                  g gB hr0 hδ0 hδ_le hreal' v) =
              (lowerScaleSecondOrderActionThirdToFirstOrderBackground (I := I) (M := M)
                  g gB hr0 hδ0 hδ_le hreal' v).comp
                (incl34 (I := I) (M := M) g) := by
  obtain ⟨ρL, CL, hρL, hρL_le, hlipdata⟩ :=
    radialSecondOrderActionBackground_lipschitz (I := I) (M := M)
      hDim g gB hρ₀ hδ0 hδ_le hreal
  obtain ⟨ρP, CP, hρP_le, hρP, hCP, hpair⟩ :=
    radialSecondOrderActionBackground_pairing_bound (I := I) (M := M)
      hDim g gB hρ₀ hδ0 hδ_le hreal
  let ρ : ℝ := min ρL ρP
  have hρ : 0 < ρ := lt_min hρL hρP
  have hρ_le : ρ ≤ ρ₀ := (min_le_left _ _).trans hρL_le
  refine ⟨ρ, CP, hρ, hρ_le, hCP, ?_⟩
  intro r hr0 hr_le
  dsimp only
  let hreal' : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ r →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ :=
    fun S hS => hreal S (hS.trans (hr_le.trans hρ_le))
  have hrL : r ≤ ρL := hr_le.trans (min_le_left _ _)
  have hrP : r ≤ ρP := hr_le.trans (min_le_right _ _)
  obtain ⟨hlipHi, hlipLo, hcoreHi, hcoreLo, hsq⟩ :=
    hlipdata (r := r) hr0 hrL
  have hcoreBd : ∀ T : SmoothCcTensor g 0 2,
      ‖(lowCoreActionCoefficientsBackground (I := I) (M := M)
          g gB hr0 hδ0 hδ_le hreal' T).secondOrderActionFourthToSecondOrder (I := I) (M := M)‖ ≤ CP * r ∧
        ‖(lowCoreActionCoefficientsBackground (I := I) (M := M)
          g gB hr0 hδ0 hδ_le hreal' T).secondOrderActionThirdToFirstOrder (I := I) (M := M)‖ ≤ CP * r := by
    intro T
    obtain ⟨hHi, hLo, -⟩ := hpair hr0 hrP T
    exact ⟨hHi, hLo⟩
  refine ⟨hlipHi.continuous, hlipLo.continuous, ?_, ?_, hsq⟩
  · intro v
    exact a2HiBackground_total_le (I := I) (M := M)
      g gB hr0 hδ0 hδ_le hreal' hlipHi.continuous hcoreHi
        (fun T => (hcoreBd T).1) v
  · intro v
    exact a2LoBackground_total_le (I := I) (M := M)
      g gB hr0 hδ0 hδ_le hreal' hlipLo.continuous hcoreLo
        (fun T => (hcoreBd T).2) v

noncomputable def highAffineSecondOrderActionBackground
    (g : SmoothRiemannianMetric I M) {ρ δ : ℝ}
    (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (u : ℝ → metricThirdOrderSobolev (I := I) (M := M) g) :
    ℝ → a2HiOp (I := I) (M := M) g :=
  fun t =>
    (lowerScaleSecondOrderActionFourthToSecondOrderBackground (I := I) (M := M)
      g g hρ hδ0 hδ_le hreal (incl32 (I := I) (M := M) g (u t))).comp
        (radialCLM (I := I) (M := M) g (by norm_num) ρ
          (incl32 (I := I) (M := M) g (u t)))

noncomputable def lowAffineSecondOrderActionBackground
    (g : SmoothRiemannianMetric I M) {ρ δ : ℝ}
    (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (u : ℝ → metricThirdOrderSobolev (I := I) (M := M) g) :
    ℝ → a2LoOp (I := I) (M := M) g :=
  fun t =>
    (lowerScaleSecondOrderActionThirdToFirstOrderBackground (I := I) (M := M)
      g g hρ hδ0 hδ_le hreal (incl32 (I := I) (M := M) g (u t))).comp
        (radialCLM (I := I) (M := M) g (by norm_num) ρ
          (incl32 (I := I) (M := M) g (u t)))

theorem highAffineSecondOrderActionBackground_norm_le
    (g : SmoothRiemannianMetric I M) {ρ δ : ℝ}
    (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (u : ℝ → metricThirdOrderSobolev (I := I) (M := M) g) (t : ℝ) :
    ‖highAffineSecondOrderActionBackground (I := I) (M := M) g hρ hδ0 hδ_le hreal u t‖ ≤
      ‖lowerScaleSecondOrderActionFourthToSecondOrderBackground (I := I) (M := M)
        g g hρ hδ0 hδ_le hreal (incl32 (I := I) (M := M) g (u t))‖ := by
  let A2 := lowerScaleSecondOrderActionFourthToSecondOrderBackground (I := I) (M := M)
    g g hρ hδ0 hδ_le hreal (incl32 (I := I) (M := M) g (u t))
  let R4 := radialCLM (I := I) (M := M) g
    (show (0 : ℝ) ≤ 4 by norm_num) ρ
      (incl32 (I := I) (M := M) g (u t))
  have hR4 : ‖R4‖ ≤ 1 :=
    radialCLM_norm (I := I) (M := M) g (by norm_num) hρ _
  change ‖A2.comp R4‖ ≤ ‖A2‖
  calc
    ‖A2.comp R4‖ ≤ ‖A2‖ * ‖R4‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖A2‖ * 1 := mul_le_mul_of_nonneg_left hR4 (norm_nonneg A2)
    _ = ‖A2‖ := mul_one _

theorem lowAffineSecondOrderActionBackground_norm_le
    (g : SmoothRiemannianMetric I M) {ρ δ : ℝ}
    (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (u : ℝ → metricThirdOrderSobolev (I := I) (M := M) g) (t : ℝ) :
    ‖lowAffineSecondOrderActionBackground (I := I) (M := M) g hρ hδ0 hδ_le hreal u t‖ ≤
      ‖lowerScaleSecondOrderActionThirdToFirstOrderBackground (I := I) (M := M)
        g g hρ hδ0 hδ_le hreal (incl32 (I := I) (M := M) g (u t))‖ := by
  let A2 := lowerScaleSecondOrderActionThirdToFirstOrderBackground (I := I) (M := M)
    g g hρ hδ0 hδ_le hreal (incl32 (I := I) (M := M) g (u t))
  let R3 := radialCLM (I := I) (M := M) g
    (show (0 : ℝ) ≤ 3 by norm_num) ρ
      (incl32 (I := I) (M := M) g (u t))
  have hR3 : ‖R3‖ ≤ 1 :=
    radialCLM_norm (I := I) (M := M) g (by norm_num) hρ _
  change ‖A2.comp R3‖ ≤ ‖A2‖
  calc
    ‖A2.comp R3‖ ≤ ‖A2‖ * ‖R3‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖A2‖ * 1 := mul_le_mul_of_nonneg_left hR3 (norm_nonneg A2)
    _ = ‖A2‖ := mul_one _

theorem affineSecondOrderActionBackground_extensions_commute
    (g : SmoothRiemannianMetric I M) {ρ δ : ℝ}
    (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (hcoef : ∀ v : metricH2 (I := I) (M := M) g,
      (incl12 (I := I) (M := M) g).comp
          (lowerScaleSecondOrderActionFourthToSecondOrderBackground (I := I) (M := M)
            g g hρ hδ0 hδ_le hreal v) =
        (lowerScaleSecondOrderActionThirdToFirstOrderBackground (I := I) (M := M)
            g g hρ hδ0 hδ_le hreal v).comp
          (incl34 (I := I) (M := M) g))
    (u : ℝ → metricThirdOrderSobolev (I := I) (M := M) g) (t : ℝ) :
    (incl12 (I := I) (M := M) g).comp
        (highAffineSecondOrderActionBackground (I := I) (M := M)
          g hρ hδ0 hδ_le hreal u t) =
      (lowAffineSecondOrderActionBackground (I := I) (M := M)
          g hρ hδ0 hδ_le hreal u t).comp
        (incl34 (I := I) (M := M) g) := by
  let J12 := incl12 (I := I) (M := M) g
  let J34 := incl34 (I := I) (M := M) g
  let v := incl32 (I := I) (M := M) g (u t)
  let AHi := lowerScaleSecondOrderActionFourthToSecondOrderBackground (I := I) (M := M)
    g g hρ hδ0 hδ_le hreal v
  let ALo := lowerScaleSecondOrderActionThirdToFirstOrderBackground (I := I) (M := M)
    g g hρ hδ0 hδ_le hreal v
  let R4 := radialCLM (I := I) (M := M) g
    (show (0 : ℝ) ≤ 4 by norm_num) ρ v
  let R3 := radialCLM (I := I) (M := M) g
    (show (0 : ℝ) ≤ 3 by norm_num) ρ v
  have hcoef' : J12.comp AHi = ALo.comp J34 := hcoef v
  have hrad : J34.comp R4 = R3.comp J34 :=
    radialCLM_incl (I := I) (M := M) g
      (show (0 : ℝ) ≤ 3 by norm_num) (show (0 : ℝ) ≤ 4 by norm_num)
      (show (3 : ℝ) ≤ 4 by norm_num) ρ v
  apply ContinuousLinearMap.ext
  intro x
  simp only [highAffineSecondOrderActionBackground, lowAffineSecondOrderActionBackground, ContinuousLinearMap.comp_apply]
  rw [show J12 (AHi (R4 x)) = ALo (J34 (R4 x)) by
      exact DFunLike.congr_fun hcoef' (R4 x)]
  rw [show J34 (R4 x) = R3 (J34 x) by
      exact DFunLike.congr_fun hrad x]


theorem affineSecondOrderActionBackground_data
    (g : SmoothRiemannianMetric I M) {ρ δ c : ℝ}
    (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (hcontHi : Continuous
      (lowerScaleSecondOrderActionFourthToSecondOrderBackground (I := I) (M := M) g g hρ hδ0 hδ_le hreal))
    (hcontLo : Continuous
      (lowerScaleSecondOrderActionThirdToFirstOrderBackground (I := I) (M := M) g g hρ hδ0 hδ_le hreal))
    (hsmallHi : ∀ v : metricH2 (I := I) (M := M) g,
      ‖show a2HiOp (I := I) (M := M) g from
        lowerScaleSecondOrderActionFourthToSecondOrderBackground (I := I) (M := M)
          g g hρ hδ0 hδ_le hreal v‖ ≤ c)
    (hsmallLo : ∀ v : metricH2 (I := I) (M := M) g,
      ‖show a2LoOp (I := I) (M := M) g from
        lowerScaleSecondOrderActionThirdToFirstOrderBackground (I := I) (M := M)
          g g hρ hδ0 hδ_le hreal v‖ ≤ c)
    {T : ℝ} (u : ℝ → metricThirdOrderSobolev (I := I) (M := M) g)
    (hu : AEStronglyMeasurable u (timeMeasure T)) :
    AEStronglyMeasurable
        (highAffineSecondOrderActionBackground (I := I) (M := M)
          g hρ hδ0 hδ_le hreal u) (timeMeasure T) ∧
      (∀ᵐ t ∂timeMeasure T,
        ‖highAffineSecondOrderActionBackground (I := I) (M := M)
          g hρ hδ0 hδ_le hreal u t‖ ≤ c) ∧
      AEStronglyMeasurable
        (lowAffineSecondOrderActionBackground (I := I) (M := M)
          g hρ hδ0 hδ_le hreal u) (timeMeasure T) ∧
      (∀ᵐ t ∂timeMeasure T,
        ‖lowAffineSecondOrderActionBackground (I := I) (M := M)
          g hρ hδ0 hδ_le hreal u t‖ ≤ c) := by
  have hju : AEStronglyMeasurable
      (fun t => incl32 (I := I) (M := M) g (u t)) (timeMeasure T) :=
    (incl32 (I := I) (M := M) g).continuous.comp_aestronglyMeasurable hu
  have hAHi : AEStronglyMeasurable
      (fun t => lowerScaleSecondOrderActionFourthToSecondOrderBackground (I := I) (M := M)
        g g hρ hδ0 hδ_le hreal
          (incl32 (I := I) (M := M) g (u t))) (timeMeasure T) :=
    hcontHi.comp_aestronglyMeasurable hju
  have hALo : AEStronglyMeasurable
      (fun t => lowerScaleSecondOrderActionThirdToFirstOrderBackground (I := I) (M := M)
        g g hρ hδ0 hδ_le hreal
          (incl32 (I := I) (M := M) g (u t))) (timeMeasure T) :=
    hcontLo.comp_aestronglyMeasurable hju
  have hR4 : AEStronglyMeasurable
      (fun t => radialCLM (I := I) (M := M) g
        (show (0 : ℝ) ≤ 4 by norm_num) ρ
          (incl32 (I := I) (M := M) g (u t))) (timeMeasure T) :=
    radialCLM_aemeas (I := I) (M := M) g (by norm_num) hju
  have hR3 : AEStronglyMeasurable
      (fun t => radialCLM (I := I) (M := M) g
        (show (0 : ℝ) ≤ 3 by norm_num) ρ
          (incl32 (I := I) (M := M) g (u t))) (timeMeasure T) :=
    radialCLM_aemeas (I := I) (M := M) g (by norm_num) hju
  have hmeasHi : AEStronglyMeasurable
      (highAffineSecondOrderActionBackground (I := I) (M := M)
        g hρ hδ0 hδ_le hreal u) (timeMeasure T) := by
    have hraw :=
      (ContinuousLinearMap.compL ℝ
        (metricH4 (I := I) (M := M) g)
        (metricH4 (I := I) (M := M) g)
        (metricH2 (I := I) (M := M) g)).continuous₂
          |>.comp_aestronglyMeasurable₂ hAHi hR4
    with_unfolding_all
      change @AEStronglyMeasurable ℝ (a2HiOp (I := I) (M := M) g)
        PseudoMetricSpace.toUniformSpace.toTopologicalSpace
        Real.measurableSpace Real.measurableSpace
        (highAffineSecondOrderActionBackground (I := I) (M := M)
          g hρ hδ0 hδ_le hreal u) (timeMeasure T)
      refine hraw.congr (Filter.Eventually.of_forall fun t => ?_)
      rfl
  have hmeasLo : AEStronglyMeasurable
      (lowAffineSecondOrderActionBackground (I := I) (M := M)
        g hρ hδ0 hδ_le hreal u) (timeMeasure T) := by
    have hraw :=
      (ContinuousLinearMap.compL ℝ
        (metricThirdOrderSobolev (I := I) (M := M) g)
        (metricThirdOrderSobolev (I := I) (M := M) g)
        (metricH1 (I := I) (M := M) g)).continuous₂
          |>.comp_aestronglyMeasurable₂ hALo hR3
    with_unfolding_all
      change @AEStronglyMeasurable ℝ (a2LoOp (I := I) (M := M) g)
        PseudoMetricSpace.toUniformSpace.toTopologicalSpace
        Real.measurableSpace Real.measurableSpace
        (lowAffineSecondOrderActionBackground (I := I) (M := M)
          g hρ hδ0 hδ_le hreal u) (timeMeasure T)
      refine hraw.congr (Filter.Eventually.of_forall fun t => ?_)
      rfl
  refine ⟨hmeasHi, Filter.Eventually.of_forall fun t => ?_, hmeasLo,
    Filter.Eventually.of_forall fun t => ?_⟩
  · exact (highAffineSecondOrderActionBackground_norm_le (I := I) (M := M)
      g hρ hδ0 hδ_le hreal u t).trans
        (hsmallHi (incl32 (I := I) (M := M) g (u t)))
  · exact (lowAffineSecondOrderActionBackground_norm_le (I := I) (M := M)
      g hρ hδ0 hδ_le hreal u t).trans
        (hsmallLo (incl32 (I := I) (M := M) g (u t)))

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
