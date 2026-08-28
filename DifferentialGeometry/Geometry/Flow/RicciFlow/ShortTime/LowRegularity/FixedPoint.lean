import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.TimeDependentLowOrderOperators
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.ZeroStateForcing
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.TameForcingFixedPoint

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped Manifold Topology ContDiff ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Spectral.MetricRealization

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private abbrev metricH1 (g : SmoothRiemannianMetric I M) :=
  tensorHs (I := I) (M := M) g 0 2 (1 : ℝ)

private abbrev metricH2 (g : SmoothRiemannianMetric I M) :=
  tensorHs (I := I) (M := M) g 0 2 (2 : ℝ)

private abbrev metricThirdOrderSobolev (g : SmoothRiemannianMetric I M) :=
  tensorHs (I := I) (M := M) g 0 2 (3 : ℝ)

private noncomputable abbrev incl32 (g : SmoothRiemannianMetric I M) :
    metricThirdOrderSobolev (I := I) (M := M) g →L[ℝ]
      metricH2 (I := I) (M := M) g :=
  tensorHsInclusion (I := I) (M := M) (g := g)
    (r := 0) (s := 2) (by norm_num)

private noncomputable abbrev incl21 (g : SmoothRiemannianMetric I M) :
    metricH2 (I := I) (M := M) g →L[ℝ]
      metricH1 (I := I) (M := M) g :=
  tensorHsInclusion (I := I) (M := M) (g := g)
    (r := 0) (s := 2) (by norm_num)

private theorem clm_apply_sub_le
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (A B : X →L[ℝ] Y) (x y : X) :
    ‖A x - B y‖ ≤ ‖A - B‖ * ‖x‖ + ‖B‖ * ‖x - y‖ := by
  rw [show A x - B y = (A - B) x + B (x - y) by
    simp only [sub_apply, map_sub]
    module]
  exact (norm_add_le _ _).trans
    (add_le_add ((A - B).le_opNorm x) (B.le_opNorm (x - y)))

noncomputable def lowerScaleForce (g : SmoothRiemannianMetric I M) :
    metricH1 (I := I) (M := M) g :=
  incl21 (I := I) (M := M) g
    (zeroStateDeTurckRemainderH2 (I := I) (M := M) g g)

theorem lowerScaleForce_core (g : SmoothRiemannianMetric I M) :
    lowerScaleForce (I := I) (M := M) g =
      ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ)
        (deTurckSmoothRemainder (I := I) g g
          (0 : SmoothCcTensor g 0 2) (by norm_num)
          (gFibreOpBound_ccTensorBilinSymm_zero (I := I) (M := M) g)) := by
  apply tensorHs.ext
  funext i
  simp only [lowerScaleForce, incl21, zeroStateDeTurckRemainderH2,
    tensorHsInclusion_coeff_apply, ccTensorToHs_coeff]

noncomputable def lowerScaleN
    (g : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (u : metricThirdOrderSobolev (I := I) (M := M) g) :
    metricH1 (I := I) (M := M) g :=
  lowerScaleForce (I := I) (M := M) g +
    lowerScaleSecondOrderActionThirdToFirstOrder (I := I) (M := M) g hρ hδ0 hδ_le hreal
      (incl32 (I := I) (M := M) g u)
      (lowRadialH3 (I := I) (M := M) g ρ u) +
    lowerScaleFirstOrderActionSecondToFirstOrder (I := I) (M := M) g hρ hδ0 hδ_le hreal u
      (lowRadialHs (I := I) (M := M) g ρ
        (incl32 (I := I) (M := M) g u))

noncomputable def lowerScaleA
    (g : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (u : metricThirdOrderSobolev (I := I) (M := M) g) :
    metricThirdOrderSobolev (I := I) (M := M) g →L[ℝ]
      metricH1 (I := I) (M := M) g :=
  (lowerScaleSecondOrderActionThirdToFirstOrder (I := I) (M := M) g hρ hδ0 hδ_le hreal
      (incl32 (I := I) (M := M) g u)).comp
      (radialCLM (I := I) (M := M) g (by norm_num) ρ
        (incl32 (I := I) (M := M) g u)) +
    (lowerScaleFirstOrderActionSecondToFirstOrder (I := I) (M := M) g hρ hδ0 hδ_le hreal u).comp
      ((radialCLM (I := I) (M := M) g (by norm_num) ρ
        (incl32 (I := I) (M := M) g u)).comp
          (incl32 (I := I) (M := M) g))

theorem lowerScaleN_frozen
    (g : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 < ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (u : metricThirdOrderSobolev (I := I) (M := M) g) :
    lowerScaleN (I := I) (M := M) g hρ.le hδ0 hδ_le hreal u =
      lowerScaleForce (I := I) (M := M) g +
        lowerScaleA (I := I) (M := M) g hρ.le hδ0 hδ_le hreal u u := by
  simp only [lowerScaleN, lowerScaleA, add_apply,
    ContinuousLinearMap.comp_apply]
  rw [radialCLM_h3 (I := I) (M := M) g hρ,
    radialCLM_h2 (I := I) (M := M) g hρ.le]
  module

theorem lowerScaleA_le
    (g : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (u : metricThirdOrderSobolev (I := I) (M := M) g) :
    ‖lowerScaleA (I := I) (M := M) g hρ hδ0 hδ_le hreal u‖ ≤
      ‖lowerScaleSecondOrderActionThirdToFirstOrder (I := I) (M := M) g hρ hδ0 hδ_le hreal
        (incl32 (I := I) (M := M) g u)‖ +
      ‖lowerScaleFirstOrderActionSecondToFirstOrder (I := I) (M := M) g hρ hδ0 hδ_le hreal u‖ := by
  let R3 :=
    radialCLM (I := I) (M := M) g (show (0 : ℝ) ≤ 3 by norm_num) ρ
      (incl32 (I := I) (M := M) g u)
  let R2 :=
    radialCLM (I := I) (M := M) g (show (0 : ℝ) ≤ 2 by norm_num) ρ
      (incl32 (I := I) (M := M) g u)
  let J := incl32 (I := I) (M := M) g
  let A2 := lowerScaleSecondOrderActionThirdToFirstOrder (I := I) (M := M) g hρ hδ0 hδ_le hreal
    (incl32 (I := I) (M := M) g u)
  let A1 := lowerScaleFirstOrderActionSecondToFirstOrder (I := I) (M := M) g hρ hδ0 hδ_le hreal u
  have hR3 : ‖R3‖ ≤ 1 :=
    radialCLM_norm (I := I) (M := M) g (by norm_num) hρ _
  have hR2 : ‖R2‖ ≤ 1 :=
    radialCLM_norm (I := I) (M := M) g (by norm_num) hρ _
  have hJ : ‖J‖ ≤ 1 :=
    tensorHsInclusion_opNorm_le_one (I := I) (M := M)
      (g := g) (r := 0) (s := 2) (by norm_num)
  have hR2J : ‖R2.comp J‖ ≤ 1 := by
    calc
      ‖R2.comp J‖ ≤ ‖R2‖ * ‖J‖ :=
        ContinuousLinearMap.opNorm_comp_le R2 J
      _ ≤ 1 * 1 :=
        mul_le_mul hR2 hJ (norm_nonneg J) zero_le_one
      _ = 1 := one_mul 1
  change ‖A2.comp R3 + A1.comp (R2.comp J)‖ ≤ ‖A2‖ + ‖A1‖
  calc
    ‖A2.comp R3 + A1.comp (R2.comp J)‖ ≤
        ‖A2.comp R3‖ + ‖A1.comp (R2.comp J)‖ :=
      norm_add_le (A2.comp R3) (A1.comp (R2.comp J))
    _ ≤ ‖A2‖ * ‖R3‖ + ‖A1‖ * ‖R2.comp J‖ :=
      add_le_add
        (ContinuousLinearMap.opNorm_comp_le A2 R3)
        (ContinuousLinearMap.opNorm_comp_le A1 (R2.comp J))
    _ ≤ ‖A2‖ * 1 + ‖A1‖ * 1 :=
      add_le_add
        (mul_le_mul_of_nonneg_left hR3 (norm_nonneg A2))
        (mul_le_mul_of_nonneg_left hR2J (norm_nonneg A1))
    _ = ‖A2‖ + ‖A1‖ := by ring

theorem lowerScaleA_aemeas
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (g : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    {u : Ω → metricThirdOrderSobolev (I := I) (M := M) g}
    (hu : AEStronglyMeasurable u μ)
    (hA2 : AEStronglyMeasurable
      (fun x => lowerScaleSecondOrderActionThirdToFirstOrder (I := I) (M := M) g hρ hδ0 hδ_le hreal
        (incl32 (I := I) (M := M) g (u x))) μ)
    (hA1 : AEStronglyMeasurable
      (fun x => lowerScaleFirstOrderActionSecondToFirstOrder (I := I) (M := M) g hρ hδ0 hδ_le hreal
        (u x)) μ) :
    AEStronglyMeasurable
      (fun x => lowerScaleA (I := I) (M := M)
        g hρ hδ0 hδ_le hreal (u x)) μ := by
  have hv :
      AEStronglyMeasurable
        (fun x => incl32 (I := I) (M := M) g (u x)) μ :=
    (incl32 (I := I) (M := M) g).continuous.comp_aestronglyMeasurable hu
  have hR3 :
      AEStronglyMeasurable
        (fun x => radialCLM (I := I) (M := M) g
          (show (0 : ℝ) ≤ 3 by norm_num) ρ
            (incl32 (I := I) (M := M) g (u x))) μ :=
    radialCLM_aemeas (I := I) (M := M) g (by norm_num) hv
  have hR2 :
      AEStronglyMeasurable
        (fun x => radialCLM (I := I) (M := M) g
          (show (0 : ℝ) ≤ 2 by norm_num) ρ
            (incl32 (I := I) (M := M) g (u x))) μ :=
    radialCLM_aemeas (I := I) (M := M) g (by norm_num) hv
  have hJ :
      AEStronglyMeasurable
        (fun _ : Ω => incl32 (I := I) (M := M) g) μ :=
    aestronglyMeasurable_const
  have hR2J :
      AEStronglyMeasurable
        (fun x =>
          (radialCLM (I := I) (M := M) g
            (show (0 : ℝ) ≤ 2 by norm_num) ρ
              (incl32 (I := I) (M := M) g (u x))).comp
            (incl32 (I := I) (M := M) g)) μ :=
    (ContinuousLinearMap.compL ℝ
      (metricThirdOrderSobolev (I := I) (M := M) g)
      (metricH2 (I := I) (M := M) g)
      (metricH2 (I := I) (M := M) g)).continuous₂
        |>.comp_aestronglyMeasurable₂ hR2 hJ
  have h2 :
      AEStronglyMeasurable
        (fun x =>
          (lowerScaleSecondOrderActionThirdToFirstOrder (I := I) (M := M) g hρ hδ0 hδ_le hreal
            (incl32 (I := I) (M := M) g (u x))).comp
            (radialCLM (I := I) (M := M) g
              (show (0 : ℝ) ≤ 3 by norm_num) ρ
                (incl32 (I := I) (M := M) g (u x)))) μ :=
    (ContinuousLinearMap.compL ℝ
      (metricThirdOrderSobolev (I := I) (M := M) g)
      (metricThirdOrderSobolev (I := I) (M := M) g)
      (metricH1 (I := I) (M := M) g)).continuous₂
        |>.comp_aestronglyMeasurable₂ hA2 hR3
  have h1 :
      AEStronglyMeasurable
        (fun x =>
          (lowerScaleFirstOrderActionSecondToFirstOrder (I := I) (M := M) g hρ hδ0 hδ_le hreal
            (u x)).comp
            ((radialCLM (I := I) (M := M) g
              (show (0 : ℝ) ≤ 2 by norm_num) ρ
                (incl32 (I := I) (M := M) g (u x))).comp
                  (incl32 (I := I) (M := M) g))) μ :=
    (ContinuousLinearMap.compL ℝ
      (metricThirdOrderSobolev (I := I) (M := M) g)
      (metricH2 (I := I) (M := M) g)
      (metricH1 (I := I) (M := M) g)).continuous₂
        |>.comp_aestronglyMeasurable₂ hA1 hR2J
  refine (h2.add h1).congr ?_
  exact Filter.Eventually.of_forall fun x => by
    unfold lowerScaleA
    congr 5

private theorem lowerScaleN_sub_eq
    (g : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (u v : metricThirdOrderSobolev (I := I) (M := M) g) :
    let A2 := lowerScaleSecondOrderActionThirdToFirstOrder (I := I) (M := M) g hρ hδ0 hδ_le hreal
    let A1 := lowerScaleFirstOrderActionSecondToFirstOrder (I := I) (M := M) g hρ hδ0 hδ_le hreal
    let Ru := lowRadialH3 (I := I) (M := M) g ρ u
    let Rv := lowRadialH3 (I := I) (M := M) g ρ v
    let Su := lowRadialHs (I := I) (M := M) g ρ
      (incl32 (I := I) (M := M) g u)
    let Sv := lowRadialHs (I := I) (M := M) g ρ
      (incl32 (I := I) (M := M) g v)
    lowerScaleN (I := I) (M := M) g hρ hδ0 hδ_le hreal u -
        lowerScaleN (I := I) (M := M) g hρ hδ0 hδ_le hreal v =
      (A2 (incl32 (I := I) (M := M) g u) -
          A2 (incl32 (I := I) (M := M) g v)) Ru +
        A2 (incl32 (I := I) (M := M) g v) (Ru - Rv) +
        (A1 u - A1 v) Su + A1 v (Su - Sv) := by
  dsimp only
  simp only [lowerScaleN, sub_apply, map_sub]
  module

private theorem lowerScaleN_sub_le
    (g : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (u v : metricThirdOrderSobolev (I := I) (M := M) g) :
    let A2 := lowerScaleSecondOrderActionThirdToFirstOrder (I := I) (M := M) g hρ hδ0 hδ_le hreal
    let A1 := lowerScaleFirstOrderActionSecondToFirstOrder (I := I) (M := M) g hρ hδ0 hδ_le hreal
    let Ru := lowRadialH3 (I := I) (M := M) g ρ u
    let Rv := lowRadialH3 (I := I) (M := M) g ρ v
    let Su := lowRadialHs (I := I) (M := M) g ρ
      (incl32 (I := I) (M := M) g u)
    let Sv := lowRadialHs (I := I) (M := M) g ρ
      (incl32 (I := I) (M := M) g v)
    ‖lowerScaleN (I := I) (M := M) g hρ hδ0 hδ_le hreal u -
        lowerScaleN (I := I) (M := M) g hρ hδ0 hδ_le hreal v‖ ≤
      (‖A2 (incl32 (I := I) (M := M) g u) -
          A2 (incl32 (I := I) (M := M) g v)‖ * ‖Ru‖ +
        ‖A2 (incl32 (I := I) (M := M) g v)‖ * ‖Ru - Rv‖) +
      (‖A1 u - A1 v‖ * ‖Su‖ + ‖A1 v‖ * ‖Su - Sv‖) := by
  dsimp only
  rw [show
    lowerScaleN (I := I) (M := M) g hρ hδ0 hδ_le hreal u -
        lowerScaleN (I := I) (M := M) g hρ hδ0 hδ_le hreal v =
      (lowerScaleSecondOrderActionThirdToFirstOrder (I := I) (M := M) g hρ hδ0 hδ_le hreal
          (incl32 (I := I) (M := M) g u)
            (lowRadialH3 (I := I) (M := M) g ρ u) -
        lowerScaleSecondOrderActionThirdToFirstOrder (I := I) (M := M) g hρ hδ0 hδ_le hreal
          (incl32 (I := I) (M := M) g v)
            (lowRadialH3 (I := I) (M := M) g ρ v)) +
      (lowerScaleFirstOrderActionSecondToFirstOrder (I := I) (M := M) g hρ hδ0 hδ_le hreal u
          (lowRadialHs (I := I) (M := M) g ρ
            (incl32 (I := I) (M := M) g u)) -
        lowerScaleFirstOrderActionSecondToFirstOrder (I := I) (M := M) g hρ hδ0 hδ_le hreal v
          (lowRadialHs (I := I) (M := M) g ρ
            (incl32 (I := I) (M := M) g v))) by
      simp only [lowerScaleN]
      module]
  exact (norm_add_le _ _).trans
    (add_le_add
      (clm_apply_sub_le
        (lowerScaleSecondOrderActionThirdToFirstOrder (I := I) (M := M) g hρ hδ0 hδ_le hreal
          (incl32 (I := I) (M := M) g u))
        (lowerScaleSecondOrderActionThirdToFirstOrder (I := I) (M := M) g hρ hδ0 hδ_le hreal
          (incl32 (I := I) (M := M) g v))
        (lowRadialH3 (I := I) (M := M) g ρ u)
        (lowRadialH3 (I := I) (M := M) g ρ v))
      (clm_apply_sub_le
        (lowerScaleFirstOrderActionSecondToFirstOrder (I := I) (M := M) g hρ hδ0 hδ_le hreal u)
        (lowerScaleFirstOrderActionSecondToFirstOrder (I := I) (M := M) g hρ hδ0 hδ_le hreal v)
        (lowRadialHs (I := I) (M := M) g ρ
          (incl32 (I := I) (M := M) g u))
        (lowRadialHs (I := I) (M := M) g ρ
          (incl32 (I := I) (M := M) g v))))

private theorem lowerScaleN_radial_le
    (g : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 < ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (u v : metricThirdOrderSobolev (I := I) (M := M) g) :
    let A2 := lowerScaleSecondOrderActionThirdToFirstOrder (I := I) (M := M) g hρ.le hδ0 hδ_le hreal
    let A1 := lowerScaleFirstOrderActionSecondToFirstOrder (I := I) (M := M) g hρ.le hδ0 hδ_le hreal
    ‖lowerScaleN (I := I) (M := M) g hρ.le hδ0 hδ_le hreal u -
        lowerScaleN (I := I) (M := M) g hρ.le hδ0 hδ_le hreal v‖ ≤
      (‖A2 (incl32 (I := I) (M := M) g u) -
          A2 (incl32 (I := I) (M := M) g v)‖ * ‖u‖ +
        ‖A2 (incl32 (I := I) (M := M) g v)‖ *
          (‖u - v‖ + (1 / ρ) * max ‖u‖ ‖v‖ *
            ‖incl32 (I := I) (M := M) g u -
              incl32 (I := I) (M := M) g v‖)) +
      (‖A1 u - A1 v‖ * ρ +
        ‖A1 v‖ * ‖incl32 (I := I) (M := M) g u -
          incl32 (I := I) (M := M) g v‖) := by
  dsimp only
  have htel := lowerScaleN_sub_le (I := I) (M := M)
    g hρ.le hδ0 hδ_le hreal u v
  dsimp only at htel
  have hRu := lowRadialH3_le (I := I) (M := M) g hρ u
  have hRsub := lowRadialH3_sub (I := I) (M := M) g hρ u v
  have hSu := lowRadialHs_norm (I := I) (M := M) g hρ.le
    (incl32 (I := I) (M := M) g u)
  have hSsub :=
    (lowRadialHs_lip (I := I) (M := M) g hρ.le).dist_le_mul
      (incl32 (I := I) (M := M) g u)
      (incl32 (I := I) (M := M) g v)
  rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm] at hSsub
  refine htel.trans ?_
  gcongr

noncomputable def lowerScaleNBall
    (g : SmoothRiemannianMetric I M)
    {ρ δ R : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ) :
  lowerState (I := I) (M := M) g 1 R →
      metricH1 (I := I) (M := M) g :=
  fun u =>
    lowerScaleN (I := I) (M := M) g hρ hδ0 hδ_le hreal
      (by
        have hu := u.1
        norm_num at hu ⊢
        exact hu)

@[simp] theorem lowerScaleN_zero
    (g : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 < ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ) :
    lowerScaleN (I := I) (M := M) g hρ.le hδ0 hδ_le hreal 0 =
      lowerScaleForce (I := I) (M := M) g := by
  simp only [lowerScaleN, map_zero, lowRadialH3_zero (I := I) (M := M) g hρ,
    lowRadialHs_zero (I := I) (M := M) g hρ.le, add_zero]

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
