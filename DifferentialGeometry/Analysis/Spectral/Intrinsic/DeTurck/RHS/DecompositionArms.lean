import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.RHS.ZeroDecomposition
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.RHSThreeArmCancel
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.RHSPathIntegral
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.ThreeArm.JointAlgebra

noncomputable section


open Bundle Manifold Set DifferentialGeometry.Tensor0SBundle
open scoped BigOperators Manifold ContDiff

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Sobolev

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

def rhsDecompositionTop
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) δ)
    (s : ℝ) : SmoothCcTensor g 4 2 :=
  rhsDecomposition2 (I := I) (M := M) g T hδ hδZ s +
    deTurckMetricPrincipalDefectTotal (I := I) (M := M) g
      (metricPerturbationPath (I := I) g T 0 hδ hδZ s)

theorem lieDecomposition2_joint
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) δ) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g 4
      (lieDecomposition2 (I := I) (M := M) g T hδ hδZ)
      (δ := δ) (δ' := δ) := by
  classical
  let a := 2 * Module.finrank ℝ E + 10
  let R : ℝ :=
    Finset.sum (Finset.range (a + 3))
      (fun j => ‖iteratedCovGrad (I := I) g 0 2 j T‖)
  have ha : 2 * Module.finrank ℝ E + 10 ≤ a := by
    simp [a]
  have hR : 0 ≤ R := by
    dsimp [R]
    exact Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hball :
      ∀ j : ℕ, j ≤ a + 2 →
        ‖iteratedCovGrad (I := I) g 0 2 j T‖ ≤ R := by
    intro j hj
    dsimp [R]
    exact Finset.single_le_sum
      (fun k _ => norm_nonneg (iteratedCovGrad (I := I) g 0 2 k T))
      (Finset.mem_range.mpr (by omega))
  have hε : ∀ i, |lieDecompositionEps i| ≤ 1 := by
    intro i
    fin_cases i <;> norm_num [lieDecompositionEps]
  obtain ⟨K, hK, hmain⟩ :=
    exists_deTurckLieCovariantDerivativeDecompositionC2Family_cap_l2JetWindow
      (I := I) (M := M) g a ha hR hδ_lt lieDecompositionQ lieDecompositionEps hε
  simpa only [linearizedRicciThreeArmHjoint, lieDecomposition2] using
    (hmain T le_rfl hδ hδZ hball).1

theorem rhsDecompositionTop_joint
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) δ) :
    linearizedRicciThreeArmHjoint (I := I) (M := M) g 4
      (rhsDecompositionTop (I := I) (M := M) g T hδ hδZ)
      (δ := δ) (δ' := δ) := by
  have hRic0 :=
    riemannPalatiniDecompositionC2Family_threeArmHjoint
      (I := I) (M := M) g T hδ hδZ ricciDecompositionQA ricciDecompositionQB
  have hRic := threeArmJoint_smul (I := I) (M := M) g (2 : ℝ) _ hRic0
  have hLie := lieDecomposition2_joint (I := I) (M := M) g T hδ_lt hδ hδZ
  have hDecomposition := threeArmJoint_add (I := I) (M := M) g _ _ hRic hLie
  have hTop := rhs_top_path_joint (I := I) (M := M) g T 0 hδ hδZ
  have hAll := threeArmJoint_add (I := I) (M := M) g _ _ hDecomposition hTop
  simpa only [linearizedRicciThreeArmHjoint, rhsDecompositionTop, rhsDecomposition2,
    ricciDecomposition2, lieDecomposition2] using hAll

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private theorem zero_symm (g : SmoothRiemannianMetric I M) :
    ∀ (x : M) (v w : TangentSpace I x),
      ccTensorBilin (I := I) g (0 : SmoothCcTensor g 0 2) x v w =
        ccTensorBilin (I := I) g (0 : SmoothCcTensor g 0 2) x w v := by
  intro x v w
  have h0 : (0 : SmoothCcTensor g 0 2) =
      (0 : ℝ) • (0 : SmoothCcTensor g 0 2) := (zero_smul ℝ _).symm
  rw [h0]
  simp only [ccTensorBilin_apply, ccTensorModel_smul,
    smul_apply, smul_eq_mul, zero_mul]

omit [SigmaCompactSpace M] in
theorem rhsSlope_decomposition
    (g g_bg : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (hT : ∀ (x : M) (v w : TangentSpace I x),
      ccTensorBilin (I := I) g T x v w =
        ccTensorBilin (I := I) g T x w v)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) δ)
    (x : M) (v w : TangentSpace I x) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    rhsSumSlope (I := I) g g_bg T 0 hδ_lt hδ hδ_lt hδZ x v w s =
      unitModel (I := I) (M := M) g 2
        (operatorFieldApply (I := I) (M := M) g 2 2
            (rhsDecomposition0 (I := I) (M := M) g g_bg T hδ hδZ s) T +
          operatorFieldApply (I := I) (M := M) g 3 2
            (ricciDeTurckRemainderFirstOrderCoefficient (I := I) (M := M) g g_bg T 0 hδ hδZ s)
            (iteratedCovGrad (I := I) g 0 2 1 T) +
          operatorFieldApply (I := I) (M := M) g 4 2
            (rhsDecompositionTop (I := I) (M := M) g T hδ hδZ s)
            (iteratedCovGrad (I := I) g 0 2 2 T)) x
        ![tangentSpaceModelContinuousLinearEquiv (I := I) x v,
          tangentSpaceModelContinuousLinearEquiv (I := I) x w] := by
  rw [ricciDeTurckRemainderSlope_eq_arms (I := I) (M := M) g g_bg T 0 hT
    (zero_symm (I := I) (M := M) g) hδ_lt hδ hδ_lt hδZ x v w hs]
  simp only [sub_zero, iteratedCovGrad_zero]
  have hCoeff :
      DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.ricciDeTurckRemainderZeroOrderCoefficient
          (I := I) (M := M) g g_bg T 0 hδ hδZ s =
        DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients.ricciDeTurckRemainderZeroOrderCoefficient
          (I := I) (M := M) g g_bg T 0 hδ hδZ s := rfl
  rw [hCoeff]
  rw [rhsLow0_decomposition (I := I) (M := M) g g_bg T hT hδ_lt hδ hδZ
    ⟨le_of_lt hs.1, le_of_lt hs.2⟩]
  simp only [rhsDecompositionTop, operatorFieldApplication_add_left]
  apply congrArg (fun Z : SmoothCcTensor g 0 2 =>
    unitModel (I := I) (M := M) g 2 Z x
      ![tangentSpaceModelContinuousLinearEquiv (I := I) x v,
        tangentSpaceModelContinuousLinearEquiv (I := I) x w])
  abel

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
