import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.RicciDeTurckPairing.BackgroundDifferenceFirstDerivativePairingBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Background.Forcing.GalerkinTerms
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.Principal.H2H3FirstOrder
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.Embedding.H2PointwiseUniform
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Pairing.FiniteSpectral
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Pairing.CrossScaleCauchySchwarz
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Remainder.Symmetry

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped Manifold Topology ContDiff ENNReal NNReal InnerProductSpace BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.HCGCompactness
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral hiding TensorEigenIdx
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Spectral.MetricRealization

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

def galerkinFirstOrderActionFixedVectorBackground
    (g gBase : SmoothRiemannianMetric I M) {R δ : ℝ}
    (hR : 0 ≤ R) (hδ : δ < 1)
    (hreal : ∀ T : SmoothCcTensor g 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g
        (((1 : ℕ) : ℝ) + 1) T‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
    (F : Finset (TensorEigenIdx (I := I) (M := M) g 0 2))
    (c : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ) :
    TensorHs (I := I) (M := M) g 0 2 ((1 : ℕ) : ℝ) :=
  let T : SmoothCcTensor g 0 2 :=
    ccTensor02Symm (I := I) (M := M) g
      (galCoreRep (I := I) (M := M) g R F c)
  let hT := galRepFib (I := I) (M := M) g hR hreal F c
  let hZ := zeroMetricPerturbation_fibre_bound (I := I) (M := M) g hR hreal
  smoothCcToTensorHs (I := I) (M := M) g ((1 : ℕ) : ℝ)
    (operatorFieldApply (I := I) (M := M) g 3 2
      (lowerScaleFirstOrderCoefficientBackgroundDifference (I := I) (M := M) g gBase T hδ hT hZ)
      (iteratedCovGrad (I := I) g 0 2 1 T))

def galerkinFirstOrderActionFixedPairingBackground
    (g gBase : SmoothRiemannianMetric I M) {R δ : ℝ}
    (hR : 0 ≤ R) (hδ : δ < 1)
    (hreal : ∀ T : SmoothCcTensor g 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g
        (((1 : ℕ) : ℝ) + 1) T‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
    (F : Finset (TensorEigenIdx (I := I) (M := M) g 0 2))
    (c : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ)
    (σ : ℝ) : ℝ :=
  ∑ i ∈ F, tensorSobolevWeight (I := I) (M := M) i σ *
    (c i * (galerkinFirstOrderActionFixedVectorBackground (I := I) (M := M) g gBase
      hR hδ hreal F c).coeff i)

def galerkinFirstOrderActionRemainderVectorBackground
    (g gBase : SmoothRiemannianMetric I M) {R δ : ℝ}
    (hR : 0 ≤ R) (hδ : δ < 1)
    (hreal : ∀ T : SmoothCcTensor g 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g
        (((1 : ℕ) : ℝ) + 1) T‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
    (F : Finset (TensorEigenIdx (I := I) (M := M) g 0 2))
    (c : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ) :
    TensorHs (I := I) (M := M) g 0 2 ((1 : ℕ) : ℝ) :=
  let T : SmoothCcTensor g 0 2 :=
    ccTensor02Symm (I := I) (M := M) g
      (galCoreRep (I := I) (M := M) g R F c)
  let hT := galRepFib (I := I) (M := M) g hR hreal F c
  let hZ := zeroMetricPerturbation_fibre_bound (I := I) (M := M) g hR hreal
  let AB := lowerScaleActionCoefficients (I := I) (M := M) g gBase T hδ hT hZ
  let AS := lowerScaleActionCoefficients (I := I) (M := M) g g T hδ hT hZ
  smoothCcToTensorHs (I := I) (M := M) g ((1 : ℕ) : ℝ)
    (AB.secondOrderAction (I := I) (M := M) T +
      operatorFieldApply (I := I) (M := M) g 2 2 AB.zeroOrderCoefficient T +
      operatorFieldApply (I := I) (M := M) g 3 2 AS.firstOrderCoefficient
        (iteratedCovGrad (I := I) g 0 2 1 T))

theorem galTermVecBackground_split
    (g gBase : SmoothRiemannianMetric I M) {R δ : ℝ}
    (hR : 0 ≤ R) (hδ : δ < 1)
    (hreal : ∀ T : SmoothCcTensor g 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g
        (((1 : ℕ) : ℝ) + 1) T‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
    (F : Finset (TensorEigenIdx (I := I) (M := M) g 0 2))
    (c : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ) :
    galerkinActionVectorBackground (I := I) (M := M) g gBase hR hδ hreal F c =
      galerkinFirstOrderActionRemainderVectorBackground (I := I) (M := M) g gBase hR hδ hreal F c +
        galerkinFirstOrderActionFixedVectorBackground (I := I) (M := M) g gBase hR hδ hreal F c := by
  simp only [galerkinActionVectorBackground, galerkinFirstOrderActionRemainderVectorBackground, galerkinFirstOrderActionFixedVectorBackground, lowerScaleFirstOrderCoefficientBackgroundDifference]
  rw [← smoothCcToTensorHs_add]
  apply congrArg
  simp only [LowerScaleActionCoefficients.firstOrderAction, operatorFieldApplication_sub_left]
  abel

def galerkinFirstOrderActionRemainderPairingBackground
    (g gBase : SmoothRiemannianMetric I M) {R δ : ℝ}
    (hR : 0 ≤ R) (hδ : δ < 1)
    (hreal : ∀ T : SmoothCcTensor g 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g
        (((1 : ℕ) : ℝ) + 1) T‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
    (F : Finset (TensorEigenIdx (I := I) (M := M) g 0 2))
    (c : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ)
    (σ : ℝ) : ℝ :=
  ∑ i ∈ F, tensorSobolevWeight (I := I) (M := M) i σ *
    (c i * (galerkinFirstOrderActionRemainderVectorBackground (I := I) (M := M) g gBase
      hR hδ hreal F c).coeff i)

theorem galTermPair3_split
    (g gBase : SmoothRiemannianMetric I M) {R δ : ℝ}
    (hR : 0 ≤ R) (hδ : δ < 1)
    (hreal : ∀ T : SmoothCcTensor g 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g
        (((1 : ℕ) : ℝ) + 1) T‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
    (F : Finset (TensorEigenIdx (I := I) (M := M) g 0 2))
    (c : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ) :
    (∑ i ∈ F, tensorSobolevWeight (I := I) (M := M) i (3 : ℝ) *
      (c i * (galerkinActionVectorBackground (I := I) (M := M) g gBase
        hR hδ hreal F c).coeff i)) =
      galerkinFirstOrderActionRemainderPairingBackground (I := I) (M := M) g gBase
          hR hδ hreal F c 3 +
        galerkinFirstOrderActionFixedPairingBackground (I := I) (M := M) g gBase
          hR hδ hreal F c 3 := by
  rw [galTermVecBackground_split (I := I) (M := M) g gBase hR hδ hreal F c]
  simp only [TensorHs.add_coeff, mul_add, Finset.sum_add_distrib,
    galerkinFirstOrderActionRemainderPairingBackground, galerkinFirstOrderActionFixedPairingBackground]

private theorem lowTerm_symm
    (g gBase : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (hTsymm : ccTensor02Symm (I := I) (M := M) g T = T)
    {δ : ℝ} (hδ : δ < 1) (hδ0 : 0 ≤ δ) (hδ3 : δ ≤ 1 / 3)
    (hT : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) δ) :
    let A := lowerScaleActionCoefficients (I := I) (M := M) g gBase T hδ hT hZ
    ccTensor02Symm (I := I) (M := M) g
        (A.secondOrderAction (I := I) (M := M) T + A.firstOrderAction (I := I) (M := M) T) =
      A.secondOrderAction (I := I) (M := M) T + A.firstOrderAction (I := I) (M := M) T := by
  dsimp only
  obtain ⟨_, _, hsplit⟩ := lowData_split (I := I) (M := M) g gBase
  have hsplitT := (hsplit T
    (bilin_symm_of_ccTensor02Symm (I := I) (M := M) g hTsymm)
    hδ3 hδ0 hT hZ).1
  have hzero : ccTensor02Symm (I := I) (M := M) g
      (0 : SmoothCcTensor g 0 2) = 0 := by
    simpa only [zero_smul] using
      (ccTensor02Symm_smul (I := I) (M := M) g (0 : ℝ)
        (0 : SmoothCcTensor g 0 2))
  have hsT :=
    ccTensor02Symm_smoothRem (I := I) (M := M) g gBase T hδ hT hTsymm
  change ccTensor02Symm (I := I) (M := M) g
      (deTurckSmoothRemainder (I := I) g gBase T hδ hT) = _ at hsT
  have hsZ :=
    ccTensor02Symm_smoothRem (I := I) (M := M) g gBase
      (0 : SmoothCcTensor g 0 2) hδ hZ hzero
  change ccTensor02Symm (I := I) (M := M) g
      (deTurckSmoothRemainder (I := I) g gBase
        (0 : SmoothCcTensor g 0 2) hδ hZ) = _ at hsZ
  rw [← hsplitT]
  change ccTensor02Symm (I := I) (M := M) g
      (deTurckSmoothRemainder (I := I) g gBase T hδ hT -
        deTurckSmoothRemainder (I := I) g gBase
          (0 : SmoothCcTensor g 0 2) hδ hZ) = _
  rw [ccTensor02Symm_sub, hsT, hsZ]

theorem galTermPair3_diag
    (g gBase : SmoothRiemannianMetric I M) {R δ : ℝ}
    (hR : 0 ≤ R) (hδ : δ < 1) (hδ0 : 0 ≤ δ) (hδ3 : δ ≤ 1 / 3)
    (hreal : ∀ T : SmoothCcTensor g 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g
        (((1 : ℕ) : ℝ) + 1) T‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
    (F : Finset (TensorEigenIdx (I := I) (M := M) g 0 2))
    (c : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ) :
    let θ : ℝ := min 1 (R / ‖galLowView (I := I) (M := M) g 1
      (finiteEigenComboHs (I := I) (M := M) g F c (((1 : ℕ) : ℝ) + 2))‖)
    let T : SmoothCcTensor g 0 2 :=
      ccTensor02Symm (I := I) (M := M) g
        (galCoreRep (I := I) (M := M) g R F c)
    let hT := galRepFib (I := I) (M := M) g hR hreal F c
    let hZ := zeroMetricPerturbation_fibre_bound (I := I) (M := M) g hR hreal
    let A := lowerScaleActionCoefficients (I := I) (M := M) g gBase T hδ hT hZ
    θ * (∑ i ∈ F, tensorSobolevWeight (I := I) (M := M) i (3 : ℝ) *
        (c i * (galerkinActionVectorBackground (I := I) (M := M) g gBase
          hR hδ hreal F c).coeff i)) =
      tensorL2Inner (I := I) (M := M) g 0 2
        (oneMinusConnLapSmoothIter (I := I) g 0 2 2 T).toFun
        (oneMinusConnLapSmoothIter (I := I) g 0 2 1
          (A.secondOrderAction (I := I) (M := M) T +
            A.firstOrderAction (I := I) (M := M) T)).toFun := by
  classical
  let θ : ℝ := min 1 (R / ‖galLowView (I := I) (M := M) g 1
    (finiteEigenComboHs (I := I) (M := M) g F c (((1 : ℕ) : ℝ) + 2))‖)
  let T : SmoothCcTensor g 0 2 :=
    ccTensor02Symm (I := I) (M := M) g
      (galCoreRep (I := I) (M := M) g R F c)
  let hT := galRepFib (I := I) (M := M) g hR hreal F c
  let hZ := zeroMetricPerturbation_fibre_bound (I := I) (M := M) g hR hreal
  let A := lowerScaleActionCoefficients (I := I) (M := M) g gBase T hδ hT hZ
  have hTfix : ccTensor02Symm (I := I) (M := M) g T = T := by
    dsimp only [T]
    exact ccTensor02Symm_idem (I := I) (M := M) g _
  have hA : ccTensor02Symm (I := I) (M := M) g
      (A.secondOrderAction (I := I) (M := M) T + A.firstOrderAction (I := I) (M := M) T) =
        A.secondOrderAction (I := I) (M := M) T + A.firstOrderAction (I := I) (M := M) T := by
    exact lowTerm_symm (I := I) (M := M) g gBase T hTfix hδ hδ0 hδ3 hT hZ
  have hrep : T = θ • ccTensor02Symm (I := I) (M := M) g
      (finiteEigenCombo (I := I) (M := M) g F c) := by
    dsimp only [T, θ]
    rw [galCoreRep]
    rw [ccTensor02Symm_smul]
  have hpair := finite_symm_scale (I := I) (M := M) g F c
    (A.secondOrderAction (I := I) (M := M) T + A.firstOrderAction (I := I) (M := M) T)
    1 2 θ hA
  rw [← hrep] at hpair
  have hgal :
      galerkinActionVectorBackground (I := I) (M := M) g gBase hR hδ hreal F c =
        smoothCcToTensorHs (I := I) (M := M) g ((1 : ℕ) : ℝ)
          (A.secondOrderAction (I := I) (M := M) T +
            A.firstOrderAction (I := I) (M := M) T) := by
    dsimp only [galerkinActionVectorBackground, A, T, hT, hZ]
  rw [hgal]
  have hcoeff (i : TensorEigenIdx (I := I) (M := M) g 0 2) :
      (smoothCcToTensorHs (I := I) (M := M) g ((1 : ℕ) : ℝ)
        (A.secondOrderAction (I := I) (M := M) T +
          A.firstOrderAction (I := I) (M := M) T)).coeff i =
        tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
          (SmoothCcTensor.toL2
            (A.secondOrderAction (I := I) (M := M) T +
              A.firstOrderAction (I := I) (M := M) T)) i :=
    smoothCcToTensorHs_coeff (I := I) (M := M) g _ _ i
  simp_rw [hcoeff]
  have hthree : (((1 + 2 : ℕ) : ℝ)) = (3 : ℝ) := by norm_num
  rw [hthree] at hpair
  have hTfold : ccTensor02Symm (I := I) (M := M) g
      (galCoreRep (I := I) (M := M) g R F c) = T := rfl
  simp only [hTfold]
  have hAfold : lowerScaleActionCoefficients (I := I) (M := M)
      g gBase T hδ hT hZ = A := rfl
  rw [hAfold]
  exact hpair

theorem galTermPair4_diag
    (g gBase : SmoothRiemannianMetric I M) {R δ : ℝ}
    (hR : 0 ≤ R) (hδ : δ < 1) (hδ0 : 0 ≤ δ) (hδ3 : δ ≤ 1 / 3)
    (hreal : ∀ T : SmoothCcTensor g 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g
        (((1 : ℕ) : ℝ) + 1) T‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
    (F : Finset (TensorEigenIdx (I := I) (M := M) g 0 2))
    (c : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ) :
    let θ : ℝ := min 1 (R / ‖galLowView (I := I) (M := M) g 1
      (finiteEigenComboHs (I := I) (M := M) g F c (((1 : ℕ) : ℝ) + 2))‖)
    let T : SmoothCcTensor g 0 2 :=
      ccTensor02Symm (I := I) (M := M) g
        (galCoreRep (I := I) (M := M) g R F c)
    let hT := galRepFib (I := I) (M := M) g hR hreal F c
    let hZ := zeroMetricPerturbation_fibre_bound (I := I) (M := M) g hR hreal
    let A := lowerScaleActionCoefficients (I := I) (M := M) g gBase T hδ hT hZ
    θ * (∑ i ∈ F, tensorSobolevWeight (I := I) (M := M) i (4 : ℝ) *
        (c i * (galerkinActionVectorBackground (I := I) (M := M) g gBase
          hR hδ hreal F c).coeff i)) =
      tensorL2Inner (I := I) (M := M) g 0 2
        (oneMinusConnLapSmoothIter (I := I) g 0 2 3 T).toFun
        (oneMinusConnLapSmoothIter (I := I) g 0 2 1
          (A.secondOrderAction (I := I) (M := M) T +
            A.firstOrderAction (I := I) (M := M) T)).toFun := by
  classical
  let θ : ℝ := min 1 (R / ‖galLowView (I := I) (M := M) g 1
    (finiteEigenComboHs (I := I) (M := M) g F c (((1 : ℕ) : ℝ) + 2))‖)
  let T : SmoothCcTensor g 0 2 :=
    ccTensor02Symm (I := I) (M := M) g
      (galCoreRep (I := I) (M := M) g R F c)
  let hT := galRepFib (I := I) (M := M) g hR hreal F c
  let hZ := zeroMetricPerturbation_fibre_bound (I := I) (M := M) g hR hreal
  let A := lowerScaleActionCoefficients (I := I) (M := M) g gBase T hδ hT hZ
  have hTfix : ccTensor02Symm (I := I) (M := M) g T = T := by
    dsimp only [T]
    exact ccTensor02Symm_idem (I := I) (M := M) g _
  have hA : ccTensor02Symm (I := I) (M := M) g
      (A.secondOrderAction (I := I) (M := M) T + A.firstOrderAction (I := I) (M := M) T) =
        A.secondOrderAction (I := I) (M := M) T + A.firstOrderAction (I := I) (M := M) T := by
    exact lowTerm_symm (I := I) (M := M) g gBase T hTfix hδ hδ0 hδ3 hT hZ
  have hrep : T = θ • ccTensor02Symm (I := I) (M := M) g
      (finiteEigenCombo (I := I) (M := M) g F c) := by
    dsimp only [T, θ]
    rw [galCoreRep]
    rw [ccTensor02Symm_smul]
  have hpair := finite_symm_scale (I := I) (M := M) g F c
    (A.secondOrderAction (I := I) (M := M) T + A.firstOrderAction (I := I) (M := M) T)
    1 3 θ hA
  rw [← hrep] at hpair
  have hgal :
      galerkinActionVectorBackground (I := I) (M := M) g gBase hR hδ hreal F c =
        smoothCcToTensorHs (I := I) (M := M) g ((1 : ℕ) : ℝ)
          (A.secondOrderAction (I := I) (M := M) T +
            A.firstOrderAction (I := I) (M := M) T) := by
    dsimp only [galerkinActionVectorBackground, A, T, hT, hZ]
  rw [hgal]
  have hcoeff (i : TensorEigenIdx (I := I) (M := M) g 0 2) :
      (smoothCcToTensorHs (I := I) (M := M) g ((1 : ℕ) : ℝ)
        (A.secondOrderAction (I := I) (M := M) T +
          A.firstOrderAction (I := I) (M := M) T)).coeff i =
        tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
          (SmoothCcTensor.toL2
            (A.secondOrderAction (I := I) (M := M) T +
              A.firstOrderAction (I := I) (M := M) T)) i :=
    smoothCcToTensorHs_coeff (I := I) (M := M) g _ _ i
  simp_rw [hcoeff]
  have hfour : (((1 + 3 : ℕ) : ℝ)) = (4 : ℝ) := by norm_num
  rw [hfour] at hpair
  have hTfold : ccTensor02Symm (I := I) (M := M) g
      (galCoreRep (I := I) (M := M) g R F c) = T := rfl
  simp only [hTfold]
  have hAfold : lowerScaleActionCoefficients (I := I) (M := M)
      g gBase T hδ hT hZ = A := rfl
  rw [hAfold]
  exact hpair


theorem galerkinFirstOrderActionFixedPairing_h3_bound
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∀ {η : ℝ}, 0 < η →
      ∀ g : SmoothRiemannianMetric I M,
        MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
        (∀ a : ℕ, a ≤ 3 →
          MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ) →
        ∃ G : ℝ, 0 ≤ G ∧
          ∀ {R δ : ℝ}, (hR : 0 ≤ R) → (hRcap : R ≤ 1) →
          (hδ_le : δ ≤ δ₀) → 0 ≤ δ →
          (hreal : ∀ T : SmoothCcTensor g 0 2,
            ‖smoothCcToTensorHs (I := I) (M := M) g
              (((1 : ℕ) : ℝ) + 1) T‖ ≤ R →
              gFibreOpBound (I := I) (M := M) g
                (ccTensorBilinSymm (I := I) g T) δ) →
          ∀ (F : Finset (TensorEigenIdx (I := I) (M := M) g 0 2))
            (c : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ),
            2 * |galerkinFirstOrderActionFixedPairingBackground (I := I) (M := M) g gBase
              hR (lt_of_le_of_lt hδ_le hδ₀) hreal F c 3| ≤
              η * (∑ i ∈ F,
                tensorSobolevWeight (I := I) (M := M) i (4 : ℝ) *
                  (c i) ^ 2) +
              G * (∑ i ∈ F,
                tensorSobolevWeight (I := I) (M := M) i (3 : ℝ) *
                  (c i) ^ 2) := by
  obtain ⟨Bc, hBc, hcorr⟩ :=
    exists_lowerScaleFirstOrderCoefficient_backgroundDifference_covariantJetNormSq_two_uniform_bound (I := I) (M := M) hDim gBase hΛ hδ₀
  intro η hη g hEq hjet
  obtain ⟨Capp, hCapp, happ⟩ :=
    operatorFieldApplication_h2_h3_h2 (I := I) (M := M) hDim g 2 2
  let K : ℝ := Capp * Bc 1
  let G : ℝ := η⁻¹ * K ^ 2
  have hK : 0 ≤ K := mul_nonneg hCapp (hBc 1 zero_le_one)
  have hG : 0 ≤ G := mul_nonneg (inv_nonneg.mpr hη.le) (sq_nonneg K)
  refine ⟨G, hG, ?_⟩
  intro R δ hR hRcap hδ_le hδ_nonneg hreal F c
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  let T : SmoothCcTensor g 0 2 :=
    ccTensor02Symm (I := I) (M := M) g
      (galCoreRep (I := I) (M := M) g R F c)
  let hT := galRepFib (I := I) (M := M) g hR hreal F c
  let hZ := zeroMetricPerturbation_fibre_bound (I := I) (M := M) g hR hreal
  let Corr : SmoothCcTensor g 3 2 :=
    lowerScaleFirstOrderCoefficientBackgroundDifference (I := I) (M := M) g gBase T hδ_lt hT hZ
  let Y : SmoothCcTensor g 0 2 :=
    operatorFieldApply (I := I) (M := M) g 3 2 Corr
      (iteratedCovGrad (I := I) g 0 2 1 T)
  have hT2smooth :
      ‖smoothCcToTensorHs (I := I) (M := M) g (2 : ℝ) T‖ ≤ R := by
    have hraw := symm_h2_of_state (I := I) (M := M) g
        (galCoreRep (I := I) (M := M) g R F c)
        (galCoreRep_ball (I := I) (M := M) g hR F c)
    rw [show (2 : ℝ) = (((1 : ℕ) : ℝ) + 1) by norm_num]
    simpa only [T] using hraw
  have hT2 :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ 1 := by
    rw [norm_ccHs_eq_smoothHs]
    exact hT2smooth.trans hRcap
  have hCorr : covariantJetNormSq (I := I) (M := M) g 2 Corr ≤ (Bc 1) ^ 2 := by
    simpa only [Corr] using
      hcorr g hEq hjet T hδ_le hδ_nonneg hT hZ 1 zero_le_one hT2
  let E3 : ℝ := ∑ i ∈ F,
    tensorSobolevWeight (I := I) (M := M) i (3 : ℝ) * (c i) ^ 2
  have hE3 : 0 ≤ E3 := by
    dsimp only [E3]
    exact Finset.sum_nonneg fun i _ =>
      mul_nonneg
        (tensorSobolevWeight_nonneg (I := I) (M := M) i (3 : ℝ))
        (sq_nonneg (c i))
  have hT3 :
      ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ ≤ Real.sqrt E3 := by
    rw [norm_ccHs_eq_smoothHs]
    simpa only [T, E3] using
      galRepHs_le (I := I) (M := M) g (3 : ℝ) hR F c
  have hY :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) Y‖ ≤
        K * Real.sqrt E3 := by
    have hact := happ Corr T (Bc 1) (hBc 1 zero_le_one)
      (by simpa only [covariantJetNormSq, Nat.reduceAdd] using hCorr)
    have hmul := mul_le_mul_of_nonneg_left hT3
      (mul_nonneg hCapp (hBc 1 zero_le_one))
    exact hact.trans (by simpa only [K] using hmul)
  have hvec :
      galerkinFirstOrderActionFixedVectorBackground (I := I) (M := M) g gBase hR hδ_lt hreal F c =
        smoothCcToTensorHs (I := I) (M := M) g ((1 : ℕ) : ℝ) Y := by
    rfl
  have hmass :
      (∑ i ∈ F, tensorSobolevWeight (I := I) (M := M) i (2 : ℝ) *
          ((galerkinFirstOrderActionFixedVectorBackground (I := I) (M := M) g gBase
            hR hδ_lt hreal F c).coeff i) ^ 2) ≤
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) Y‖ ^ 2 := by
    simpa only [hvec, smoothCcToTensorHs_coeff] using
      cc_partial_le_norm (I := I) (M := M) g 2 (2 : ℝ) Y F
  have hmassK :
      (∑ i ∈ F, tensorSobolevWeight (I := I) (M := M) i (2 : ℝ) *
          ((galerkinFirstOrderActionFixedVectorBackground (I := I) (M := M) g gBase
            hR hδ_lt hreal F c).coeff i) ^ 2) ≤ K ^ 2 * E3 := by
    calc
      _ ≤ ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) Y‖ ^ 2 := hmass
      _ ≤ (K * Real.sqrt E3) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hY 2
      _ = K ^ 2 * (Real.sqrt E3) ^ 2 := by ring
      _ = K ^ 2 * E3 := by rw [Real.sq_sqrt hE3]
  have hcross := two_abs_cross_le_eps (I := I) (M := M)
    F (3 : ℝ) c
      (fun i => (galerkinFirstOrderActionFixedVectorBackground (I := I) (M := M) g gBase
        hR hδ_lt hreal F c).coeff i) hη
  norm_num at hcross
  calc
    2 * |galerkinFirstOrderActionFixedPairingBackground (I := I) (M := M) g gBase
        hR hδ_lt hreal F c 3| ≤
        η * (∑ i ∈ F,
          tensorSobolevWeight (I := I) (M := M) i (4 : ℝ) * (c i) ^ 2) +
        η⁻¹ * (∑ i ∈ F,
          tensorSobolevWeight (I := I) (M := M) i (2 : ℝ) *
            ((galerkinFirstOrderActionFixedVectorBackground (I := I) (M := M) g gBase
              hR hδ_lt hreal F c).coeff i) ^ 2) := by
          simpa only [galerkinFirstOrderActionFixedPairingBackground] using hcross
    _ ≤ η * (∑ i ∈ F,
          tensorSobolevWeight (I := I) (M := M) i (4 : ℝ) * (c i) ^ 2) +
        η⁻¹ * (K ^ 2 * E3) := by
          exact add_le_add (le_refl _)
            (mul_le_mul_of_nonneg_left hmassK (inv_nonneg.mpr hη.le))
    _ = η * (∑ i ∈ F,
          tensorSobolevWeight (I := I) (M := M) i (4 : ℝ) * (c i) ^ 2) +
        G * (∑ i ∈ F,
          tensorSobolevWeight (I := I) (M := M) i (3 : ℝ) * (c i) ^ 2) := by
          simp only [G, E3]
          ring

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
