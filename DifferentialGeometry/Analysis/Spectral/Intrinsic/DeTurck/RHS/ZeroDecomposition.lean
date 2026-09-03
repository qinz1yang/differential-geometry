import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.PalatiniDecomposition.RicciContractionKernel
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.Pairing.TopOrder.Decomposition
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.RHSLowCoeff

noncomputable section


open Bundle Manifold DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open scoped BigOperators Manifold ContDiff

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Analysis.Spectral.DeTurck
open DifferentialGeometry.PDE.DeTurck.RicciLinearization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

def ricciDecompositionQA : Fin 4 → Equiv.Perm (Fin 4) :=
  ![Equiv.swap (0 : Fin 4) 2, Equiv.swap (1 : Fin 4) 3,
    Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3, 1]

def ricciDecompositionQB : Fin 4 → Equiv.Perm (Fin 4) :=
  fun k => Equiv.swap (0 : Fin 4) 1 * ricciDecompositionQA k

def lieDecompositionQ : Fin 3 → Equiv.Perm (Fin 4) :=
  ![Equiv.swap (0 : Fin 4) 1 * Equiv.swap (0 : Fin 4) 2,
    Equiv.swap (2 : Fin 4) 3 * Equiv.swap (1 : Fin 4) 2 *
      Equiv.swap (0 : Fin 4) 1,
    Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3]

def lieDecompositionEps : Fin 3 → ℝ := ![(-1 : ℝ), -1, 1]

def ricciDecomposition0
    (g g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g 0 2) :
    SmoothCcTensor g 2 2 :=
  ricciArmOrder0RiemannCoeff (I := I) (M := M) g g +
    (2 : ℝ) •
      (ricciArmOrder0AACommCoeffField (I := I) (M := M) g g₁ +
        (ccOperatorFieldComp (I := I) (M := M) g 2 2 2
            (ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g g₁ -
              ricciArmOrder0BackgroundCurvatureCoeffField (I := I) (M := M) g g)
            (ccInputSlotSwapField (I := I) (M := M) g) +
          (1 / 2 : ℝ) •
            ricciArmSharpGradKoszulResidualField (I := I) (M := M) g g₁ P -
          ricciArmRicciFoldRemainderField (I := I) (M := M) g g₁ P))

def ricciDecomposition2
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2) {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) δ)
    (s : ℝ) : SmoothCcTensor g 4 2 :=
  (2 : ℝ) • riemannPalatiniDecompositionC2Family
    (I := I) (M := M) g T hδ hδZ ricciDecompositionQA ricciDecompositionQB s

def lieDecomposition0
    (g g₁ g_bg : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) δ)
    (s : ℝ) : SmoothCcTensor g 2 2 :=
  deTurckLieCovariantDerivativeArmField (I := I) (M := M) g g₁ g_bg -
    deTurckLieTopOrderPairingFamily (I := I) (M := M) g T hδ hδZ
      lieDecompositionQ lieDecompositionEps s

def lieDecomposition2
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2) {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) δ)
    (s : ℝ) : SmoothCcTensor g 4 2 :=
  deTurckLieCovariantDerivativeDecompositionC2Family
    (I := I) (M := M) g T hδ hδZ lieDecompositionQ lieDecompositionEps s

def rhsDecomposition0
    (g g_bg : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) δ)
    (s : ℝ) : SmoothCcTensor g 2 2 :=
  let g₁ := metricPerturbationPath (I := I) g T 0 hδ hδZ s
  (-2 : ℝ) • ricciPalatiniHalfCoefficient (I := I) (M := M) g g₁ +
    ricciDecomposition0 (I := I) (M := M) g g₁ (s • T) +
    (lieDecomposition0 (I := I) (M := M) g g₁ g_bg T hδ hδZ s +
      deTurckLieEndoArmField (I := I) (M := M) g g₁ g_bg +
      lieCorrectionZeroField (I := I) (M := M) g g₁ g_bg)

def rhsDecomposition2
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2) {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) δ)
    (s : ℝ) : SmoothCcTensor g 4 2 :=
  ricciDecomposition2 (I := I) (M := M) g T hδ hδZ s +
    lieDecomposition2 (I := I) (M := M) g T hδ hδZ s

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma bilin_smul
    (g : SmoothRiemannianMetric I M) (c : ℝ) (S : SmoothCcTensor g 0 2)
    (x : M) (v w : TangentSpace I x) :
    ccTensorBilin (I := I) g (c • S) x v w =
      c * ccTensorBilin (I := I) g S x v w := by
  rw [ccTensorBilin_apply, ccTensorBilin_apply, ccTensorModel_smul,
    smul_apply, smul_eq_mul]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma symmS_eq_self
    (g : SmoothRiemannianMetric I M) (S : SmoothCcTensor g 0 2)
    (hS : ∀ (x : M) (v w : TangentSpace I x),
      ccTensorBilin (I := I) g S x v w =
        ccTensorBilin (I := I) g S x w v) :
    symmS (I := I) (M := M) g S = S := by
  exact foldSymmS_eq_self (I := I) (M := M) g S hS

omit [BoundarylessManifold I M] in
omit [I.Boundaryless] in
omit [SigmaCompactSpace M] in
private lemma ricciDecomposition2_eq
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (hT : ∀ (x : M) (v w : TangentSpace I x),
      ccTensorBilin (I := I) g T x v w =
        ccTensorBilin (I := I) g T x w v)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) δ)
    (s : ℝ) :
    ricciDecomposition2 (I := I) (M := M) g T hδ hδZ s =
      (2 * s : ℝ) • curvatureDecompositionKernelCoeffField
        (I := I) (M := M) g
        (metricPerturbationPath (I := I) g T 0 hδ hδZ s)
        (ccTensorUnitValueSection (I := I) (M := M) g T)
        (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g T)
        (Equiv.swap (0 : Fin 4) 2) (Equiv.swap (1 : Fin 4) 3)
        (Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3) 1 := by
  have hsymm : ccTensor02Symm (I := I) (M := M) g T = T :=
    symmS_eq_self (I := I) (M := M) g T hT
  rw [ricciDecomposition2,
    riemannPalatiniDecompositionC2Family_eq_symmS_kernel
      (I := I) (M := M) g T hδ hδZ
      ricciDecompositionQA ricciDecompositionQB (fun _ => rfl) s,
    hsymm, smul_smul]
  rfl

omit [SigmaCompactSpace M] in
theorem ricciDecomposition_app
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (hT : ∀ (x : M) (v w : TangentSpace I x),
      ccTensorBilin (I := I) g T x v w =
        ccTensorBilin (I := I) g T x w v)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) δ)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    operatorFieldApply (I := I) (M := M) g 2 2
        (ricciArmOrder0RiemannCoeff (I := I) (M := M) g
          (metricPerturbationPath (I := I) g T 0 hδ hδZ s)) T =
      operatorFieldApply (I := I) (M := M) g 2 2
          (ricciDecomposition0 (I := I) (M := M) g
            (metricPerturbationPath (I := I) g T 0 hδ hδZ s) (s • T)) T +
        operatorFieldApply (I := I) (M := M) g 4 2
          (ricciDecomposition2 (I := I) (M := M) g T hδ hδZ s)
          (iteratedCovGrad (I := I) g 0 2 2 T) := by
  have hs_mem : s ∈ metricPerturbationPathDomain (δ := δ) (δ' := δ) :=
    Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt hs
  have htie : ∀ (y : M) (v w : TangentSpace I y),
      (metricPerturbationPath (I := I) g T 0 hδ hδZ s).inner y v w =
        g.inner y v w + ccTensorBilinSymm (I := I) g (s • T) y v w := by
    intro y v w
    rw [← show convexPerturbation (I := I) g T 0 s = s • T by
      rw [convexPerturbation, smul_zero, zero_add]]
    exact metricPerturbationPath_inner_of_mem (I := I) g T 0 hδ hδZ hs_mem y v w
  have hPsymm : ∀ (x : M) (v w : TangentSpace I x),
      ccTensorBilin (I := I) g (s • T) x v w =
        ccTensorBilin (I := I) g (s • T) x w v := by
    intro x v w
    rw [bilin_smul (I := I) (M := M), bilin_smul (I := I) (M := M), hT x v w]
  have hprim :=
    ricciArmOrder0RiemannHalfBackgroundDiff_operatorFieldApplication_eq_residualFieldSum_add_decompositionKernelSecondGrad
      (I := I) (M := M) g
      (metricPerturbationPath (I := I) g T 0 hδ hδZ s) (s • T) htie hPsymm T
  have hC2 := ricciDecomposition2_eq (I := I) (M := M) g T hT hδ hδZ s
  rw [ricciDecomposition0, hC2, operatorFieldApplication_add_left, operatorFieldApplication_smul_left,
    operatorFieldApplication_smul_left]
  rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.iteratedCovGrad_smul_real,
    operatorFieldApplication_smul_right] at hprim
  have htwice :
      operatorFieldApply (I := I) (M := M) g 2 2
          (ricciArmOrder0RiemannCoeff (I := I) (M := M) g
            (metricPerturbationPath (I := I) g T 0 hδ hδZ s)) T -
        operatorFieldApply (I := I) (M := M) g 2 2
          (ricciArmOrder0RiemannCoeff (I := I) (M := M) g g) T =
      (2 : ℝ) • ((1 / 2 : ℝ) •
        (operatorFieldApply (I := I) (M := M) g 2 2
            (ricciArmOrder0RiemannCoeff (I := I) (M := M) g
              (metricPerturbationPath (I := I) g T 0 hδ hδZ s)) T -
          operatorFieldApply (I := I) (M := M) g 2 2
            (ricciArmOrder0RiemannCoeff (I := I) (M := M) g g) T)) := by
    rw [smul_smul, show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_smul]
  rw [hprim] at htwice
  rw [sub_eq_iff_eq_add] at htwice
  rw [htwice]
  module

omit [SigmaCompactSpace M] in
theorem lieDecomposition_app
    (g g₁ g_bg : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g 0 2) {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) δ)
    (s : ℝ) :
    operatorFieldApply (I := I) (M := M) g 2 2
        (deTurckLieCovariantDerivativeArmField (I := I) (M := M) g g₁ g_bg) T =
      operatorFieldApply (I := I) (M := M) g 2 2
          (lieDecomposition0 (I := I) (M := M) g g₁ g_bg T hδ hδZ s) T +
        operatorFieldApply (I := I) (M := M) g 4 2
          (lieDecomposition2 (I := I) (M := M) g T hδ hδZ s)
          (iteratedCovGrad (I := I) g 0 2 2 T) := by
  rw [lieDecomposition0, lieDecomposition2, foldOperatorFieldApplication_sub_left,
    deTurckLieTopOrderPairing_apply (I := I) (M := M) g T hδ hδZ lieDecompositionQ lieDecompositionEps s]
  abel

omit [SigmaCompactSpace M] in
theorem rhsLow0_decomposition
    (g g_bg : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (hT : ∀ (x : M) (v w : TangentSpace I x),
      ccTensorBilin (I := I) g T x v w =
        ccTensorBilin (I := I) g T x w v)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) δ)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    operatorFieldApply (I := I) (M := M) g 2 2
        (DeTurckCoefficients.ricciDeTurckRemainderZeroOrderCoefficient
          (I := I) (M := M) g g_bg T 0 hδ hδZ s) T =
      operatorFieldApply (I := I) (M := M) g 2 2
          (rhsDecomposition0 (I := I) (M := M) g g_bg T hδ hδZ s) T +
        operatorFieldApply (I := I) (M := M) g 4 2
          (rhsDecomposition2 (I := I) (M := M) g T hδ hδZ s)
          (iteratedCovGrad (I := I) g 0 2 2 T) := by
  have hRic := ricciDecomposition_app (I := I) (M := M) g T hT hδ_lt hδ hδZ hs
  have hLie := lieDecomposition_app (I := I) (M := M) g
    (metricPerturbationPath (I := I) g T 0 hδ hδZ s) g_bg T hδ hδZ s
  rw [DeTurckCoefficients.ricciDeTurckRemainderZeroOrderCoefficient, rhsDecomposition0, rhsDecomposition2,
    deTurckLieCoeffField_eq_covDerivArm_add_endoArm,
    ricciPalatiniHalfCoefficient]
  change
    operatorFieldApply (I := I) (M := M) g 2 2
        ((-2 : ℝ) •
            linearizedRicciConnectionDifferenceOrder0CoeffField (I := I) (M := M) g
              (metricPerturbationPath (I := I) g T 0 hδ hδZ s) +
          (deTurckLieCovariantDerivativeArmField (I := I) (M := M) g
              (metricPerturbationPath (I := I) g T 0 hδ hδZ s) g_bg +
            deTurckLieEndoArmField (I := I) (M := M) g
              (metricPerturbationPath (I := I) g T 0 hδ hδZ s) g_bg +
            lieCorrectionZeroField (I := I) (M := M) g
              (metricPerturbationPath (I := I) g T 0 hδ hδZ s) g_bg)) T =
      _
  simp only [operatorFieldApplication_add_left, operatorFieldApplication_smul_left]
  rw [hRic, hLie]
  module

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
