import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RiemannCoefficientPalatiniRefoldLinearizedRefoldCoreIdentity
import DifferentialGeometry.Geometry.Connection.TensorNabla.OperatorFieldSecondGradientRefold
import DifferentialGeometry.Geometry.Flow.DeTurckVFConnDiffVariation
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciThreeArmCorrectionFieldBound
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciLinearizationArmFields
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciPathPalatiniLinearization
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckSectionDifference
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureCoefficientDifferenceJetTowerIntegral
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderDefs
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.DeTurckLieHigherOrderCoeffField
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLieKernelL2JetBound
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLieCoeffL2JetBound
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.CurvatureRefoldMonomialFibreNormBound
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciArmResidualCoefficientFields
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RicciArmResidualFieldGridWindow
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RiemannCoefficientPalatiniRefoldFamilyJointSmoothness
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RiemannCoefficientPalatiniRefoldLieCovDerivFamily
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RiemannCoefficientPalatiniRefoldEndoArmGridWindow
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RiemannCoefficientPalatiniRefoldCovDerivArmPairTrace
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Connection


noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Manifold Set Filter DifferentialGeometry.Tensor0SBundle MeasureTheory
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2

open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Analysis.Parabolic DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Analysis.Spectral.DeTurck
open DifferentialGeometry.PDE.DeTurck.RicciLinearization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M]

private local instance tensorRSNormedAddCommGroupOfRiemannianBundle
    (r s : ℕ) [Bundle.RiemannianBundle (fun y : M => Tensor0SBundle.TensorRSSpace r s I y)]
      (x : M) :
    NormedAddCommGroup (Tensor0SBundle.TensorRSSpace r s I x) :=
  Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal
    (E := fun y : M => Tensor0SBundle.TensorRSSpace r s I y) x

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E


private lemma lrSingle_b_le_grid (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) (q : ℕ) (hq : 1 ≤ q) :
    b q ≤ Combinatorics.antidiagonalTupleGrid b q := by
  have h := Combinatorics.single_factor_mul_antidiagonalTupleGrid_le b hb 0 q hq
  rw [Combinatorics.antidiagonalTupleGrid_zero, mul_one] at h
  rwa [zero_add] at h

private lemma lrBFGW_mono_of_le (b b' : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j)
    (hbb : ∀ j, b j ≤ b' j) (K w : ℕ) :
    Combinatorics.boundedFactorGridWindow b K w ≤
      Combinatorics.boundedFactorGridWindow b' K w := by
  rw [Combinatorics.boundedFactorGridWindow, Combinatorics.boundedFactorGridWindow]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [Combinatorics.boundedFactorGrid, Combinatorics.boundedFactorGrid]
  refine Finset.sum_le_sum fun n _ => ?_
  refine Finset.sum_le_sum fun e _ => ?_
  exact Finset.prod_le_prod (fun m _ => hb (e m)) (fun m _ => hbb (e m))


private lemma lrWindow_le_bFGW (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) {K W W' : ℕ}
    (hK : W ≤ K + 1) (hW : W ≤ W') (_hW1 : 1 ≤ W') :
    Combinatorics.antidiagonalTupleGridWindow b W ≤
      (W : ℝ) * Combinatorics.boundedFactorGridWindow b K W' := by
  rw [Combinatorics.antidiagonalTupleGridWindow]
  calc ∑ k ∈ Finset.range W, Combinatorics.antidiagonalTupleGrid b k
      ≤ ∑ _k ∈ Finset.range W, Combinatorics.boundedFactorGridWindow b K W' := by
        refine Finset.sum_le_sum fun k hk => ?_
        rw [Finset.mem_range] at hk
        exact Combinatorics.antidiagonalTupleGrid_le_boundedFactorGridWindow b hb
          (by omega) (by omega)
    _ = (W : ℝ) * Combinatorics.boundedFactorGridWindow b K W' := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]


private lemma lrTcell_bfgw (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) {Λ0 : ℝ} (hΛ0 : 0 ≤ Λ0)
    (h0 : b 0 ≤ Λ0) {n K W : ℕ} (hnK : n ≤ K) (hnW : n + 1 ≤ W) :
    b n ≤ (Λ0 + 1) * Combinatorics.boundedFactorGridWindow b K W := by
  have hone : (1 : ℝ) ≤ Combinatorics.boundedFactorGridWindow b K W :=
    Combinatorics.one_le_boundedFactorGridWindow b hb (by omega)
  have hW_nn : (0 : ℝ) ≤ Combinatorics.boundedFactorGridWindow b K W := by linarith
  rcases Nat.eq_zero_or_pos n with hn0 | hn1
  · subst hn0
    nlinarith [hΛ0, hone, h0, hb 0]
  · have hsingle : b n ≤ Combinatorics.antidiagonalTupleGrid b n :=
      lrSingle_b_le_grid b hb n hn1
    have hgw : Combinatorics.antidiagonalTupleGrid b n ≤
        Combinatorics.boundedFactorGridWindow b K W :=
      Combinatorics.antidiagonalTupleGrid_le_boundedFactorGridWindow b hb hnK (by omega)
    nlinarith [le_trans hsingle hgw, hΛ0, hW_nn]

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
omit [BoundarylessManifold I M] in
theorem exists_sobolev_pointwise_bound_zero_order (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) :
    ∃ Csob : ℝ, 0 ≤ Csob ∧
      ∀ (T : SmoothCcTensor g₀ 0 2) {R : ℝ} (_hR : 0 ≤ R),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (T.toSection x) ≤
            (Csob * R) ^ 2 := by
  classical
  obtain ⟨Csob, hCsob_nn, hCsob⟩ :=
    exists_Csob_convexPerturbation_pointwise_C2_le (I := I) (M := M) g₀ a ha_super
  refine ⟨Csob, hCsob_nn, ?_⟩
  intro T R hR hball x
  have hball0 : ∀ j : ℕ, j ≤ a + 2 →
      ‖iteratedCovGrad (I := I) g₀ 0 2 j (0 : SmoothCcTensor g₀ 0 2)‖ ≤ R := by
    intro j hj
    rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • T from (zero_smul ℝ T).symm,
      iteratedCovGrad_smul_real, norm_smul, Real.norm_eq_abs, abs_zero, zero_mul]
    exact hR
  have hsum := hCsob T 0 hR hball hball0 1 ⟨by norm_num, le_refl 1⟩ x
  have hterms : ∀ k ∈ Finset.range 3, 0 ≤
      (letI : Bundle.RiemannianBundle
          (fun b : M => Tensor0SBundle.TensorRSSpace 0 (2 + k) I b) :=
        Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + k)
      ‖(iteratedCovGrad (I := I) g₀ 0 2 k
          (convexPerturbation (I := I) g₀ T 0 1)).toSection x‖) := by
    intro k _
    letI : Bundle.RiemannianBundle
        (fun b : M => Tensor0SBundle.TensorRSSpace 0 (2 + k) I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + k)
    exact norm_nonneg _
  have h0 := le_trans (Finset.single_le_sum hterms
    (show (0 : ℕ) ∈ Finset.range 3 from Finset.mem_range.mpr (by norm_num))) hsum
  have hcp1 : convexPerturbation (I := I) g₀ T 0 1 = T := by
    rw [convexPerturbation, smul_zero, zero_add, one_smul]
  rw [hcp1, iteratedCovGrad_zero] at h0
  letI : Bundle.RiemannianBundle (fun b : M => Tensor0SBundle.TensorRSSpace 0 2 I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 2
  have h0' : ‖(T.toSection x : Tensor0SBundle.TensorRSSpace 0 2 I x)‖ ≤ Csob * R := h0
  have hb : riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (T.toSection x) =
      ‖(T.toSection x : Tensor0SBundle.TensorRSSpace 0 2 I x)‖ ^ 2 :=
    riemannianFiberNormSq_eq_bundle_norm_sq' (I := I) (M := M) g₀ 0 2 x (T.toSection x)
  have hnn : (0 : ℝ) ≤ ‖(T.toSection x : Tensor0SBundle.TensorRSSpace 0 2 I x)‖ :=
    norm_nonneg _
  nlinarith [h0', hb, hnn, mul_nonneg hCsob_nn hR]

attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
omit [BoundarylessManifold I M] in
theorem exists_sobolev_pointwise_bound_first_order (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) :
    ∃ Csob : ℝ, 0 ≤ Csob ∧
      ∀ (T : SmoothCcTensor g₀ 0 2) {R : ℝ} (_hR : 0 ≤ R),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 1) x
            ((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x) ≤
            (Csob * R) ^ 2 := by
  classical
  obtain ⟨Csob, hCsob_nn, hCsob⟩ :=
    exists_Csob_convexPerturbation_pointwise_C2_le (I := I) (M := M) g₀ a ha_super
  refine ⟨Csob, hCsob_nn, ?_⟩
  intro T R hR hball x
  have hball0 : ∀ j : ℕ, j ≤ a + 2 →
      ‖iteratedCovGrad (I := I) g₀ 0 2 j (0 : SmoothCcTensor g₀ 0 2)‖ ≤ R := by
    intro j hj
    rw [show (0 : SmoothCcTensor g₀ 0 2) = (0 : ℝ) • T from (zero_smul ℝ T).symm,
      iteratedCovGrad_smul_real, norm_smul, Real.norm_eq_abs, abs_zero, zero_mul]
    exact hR
  have hsum := hCsob T 0 hR hball hball0 1 ⟨by norm_num, le_refl 1⟩ x
  have hterms : ∀ k ∈ Finset.range 3, 0 ≤
      (letI : Bundle.RiemannianBundle
          (fun b : M => Tensor0SBundle.TensorRSSpace 0 (2 + k) I b) :=
        Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + k)
      ‖(iteratedCovGrad (I := I) g₀ 0 2 k
          (convexPerturbation (I := I) g₀ T 0 1)).toSection x‖) := by
    intro k _
    letI : Bundle.RiemannianBundle
        (fun b : M => Tensor0SBundle.TensorRSSpace 0 (2 + k) I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + k)
    exact norm_nonneg _
  have h1 := le_trans (Finset.single_le_sum hterms
    (show (1 : ℕ) ∈ Finset.range 3 from Finset.mem_range.mpr (by norm_num))) hsum
  have hcp1 : convexPerturbation (I := I) g₀ T 0 1 = T := by
    rw [convexPerturbation, smul_zero, zero_add, one_smul]
  rw [hcp1] at h1
  letI : Bundle.RiemannianBundle (fun b : M => Tensor0SBundle.TensorRSSpace 0 (2 + 1) I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 (2 + 1)
  have h1' : ‖((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x :
      Tensor0SBundle.TensorRSSpace 0 (2 + 1) I x)‖ ≤ Csob * R := h1
  have hb : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 1) x
      ((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x) =
      ‖((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x :
        Tensor0SBundle.TensorRSSpace 0 (2 + 1) I x)‖ ^ 2 :=
    riemannianFiberNormSq_eq_bundle_norm_sq' (I := I) (M := M) g₀ 0 (2 + 1) x _
  have hnn : (0 : ℝ) ≤ ‖((iteratedCovGrad (I := I) g₀ 0 2 1 T).toSection x :
      Tensor0SBundle.TensorRSSpace 0 (2 + 1) I x)‖ := norm_nonneg _
  nlinarith [h1', hb, hnn, mul_nonneg hCsob_nn hR]


private theorem riemannCurvatureCoeffFieldGridWindow (g₀ : SmoothRiemannianMetric I M) (Λ0 : ℝ)
    (hΛ0 : 0 ≤ Λ0) :
    ∃ C : ℕ → ℝ, (∀ w, 0 ≤ C w) ∧
      ∀ (T : SmoothCcTensor g₀ 0 2)
        (_hT0 : ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (T.toSection x) ≤ Λ0)
        (w K : ℕ) (_hwK : w ≤ K) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + w) x
            ((iteratedCovGrad (I := I) g₀ 0 4 w
              (riemannCurvatureCoeffField (I := I) (M := M) g₀ T)).toSection x) ≤
          C w * Combinatorics.boundedFactorGridWindow
            (fun l' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l') x
              ((iteratedCovGrad (I := I) g₀ 0 2 l' T).toSection x)) K (w + 2) := by
  classical
  obtain ⟨cW1, hcW1_nn, hcW1⟩ := bdExists_fixedField_rfns_jet (I := I) (M := M) g₀ 2 4
    (riemannLoweredContractionA (I := I) (M := M) g₀)
  obtain ⟨cW2, hcW2_nn, hcW2⟩ := bdExists_fixedField_rfns_jet (I := I) (M := M) g₀ 2 4
    (riemannLoweredContractionB (I := I) (M := M) g₀)
  refine ⟨fun w => 2 * (diagonalGridGrowthFactor (E := E) w * ∑ i' ∈ Finset.range (w + 1),
      cW1 i' * (((w + 1 - i' : ℕ) : ℝ) * (Λ0 + 1)))
    + 2 * (diagonalGridGrowthFactor (E := E) w * ∑ i' ∈ Finset.range (w + 1),
      cW2 i' * (((w + 1 - i' : ℕ) : ℝ) * (Λ0 + 1))),
    fun w => by
      have h1 : (0 : ℝ) ≤ diagonalGridGrowthFactor (E := E) w * ∑ i' ∈ Finset.range (w + 1),
          cW1 i' * (((w + 1 - i' : ℕ) : ℝ) * (Λ0 + 1)) :=
        mul_nonneg (appCcGdiag_nonneg (E := E) w)
          (Finset.sum_nonneg fun i' _ => mul_nonneg (hcW1_nn i')
            (mul_nonneg (Nat.cast_nonneg _) (by linarith)))
      have h2 : (0 : ℝ) ≤ diagonalGridGrowthFactor (E := E) w * ∑ i' ∈ Finset.range (w + 1),
          cW2 i' * (((w + 1 - i' : ℕ) : ℝ) * (Λ0 + 1)) :=
        mul_nonneg (appCcGdiag_nonneg (E := E) w)
          (Finset.sum_nonneg fun i' _ => mul_nonneg (hcW2_nn i')
            (mul_nonneg (Nat.cast_nonneg _) (by linarith)))
      linarith, ?_⟩
  intro T hT0 w K hwK x
  set b : ℕ → ℝ := fun l' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l') x
    ((iteratedCovGrad (I := I) g₀ 0 2 l' T).toSection x) with hb_def
  have hb : ∀ l', 0 ≤ b l' :=
    fun l' => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l') x _
  set W : ℝ := Combinatorics.boundedFactorGridWindow b K (w + 2) with hW_def
  have hW_nn : (0 : ℝ) ≤ W := Combinatorics.boundedFactorGridWindow_nonneg b hb K (w + 2)
  have hb0 : b 0 ≤ Λ0 := by
    have := hT0 x
    rw [hb_def]
    simpa [iteratedCovGrad_zero] using this
  have hcell : ∀ l' : ℕ, l' ≤ w → b l' ≤ (Λ0 + 1) * W := by
    intro l' hl'
    exact lrTcell_bfgw b hb hΛ0 hb0 (by omega) (by omega)
  have hpart : ∀ (F : SmoothCcTensor g₀ 2 4) (cF : ℕ → ℝ) (hcF_nn : ∀ j, 0 ≤ cF j)
      (hcF : ∀ (j : ℕ) (y : M), riemannianFiberNormSq (I := I) (M := M) g₀ 2 (4 + j) y
        ((iteratedCovGrad (I := I) g₀ 2 4 j F).toSection y) ≤ cF j),
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + w) x
          ((iteratedCovGrad (I := I) g₀ 0 4 w
            (ccOperatorFieldComp (I := I) (M := M) g₀ 0 2 4 F T)).toSection x) ≤
        (diagonalGridGrowthFactor (E := E) w * ∑ i' ∈ Finset.range (w + 1),
          cF i' * (((w + 1 - i' : ℕ) : ℝ) * (Λ0 + 1))) * W := by
    intro F cF hcF_nn hcF
    refine le_trans
      (riemannianFiberNormSq_iteratedCovGrad_ccTensorCompose_diagonalProductGrid_leftFactor_le
      (I := I) (M := M) g₀ w 0 2 4 F T x) ?_
    have hcell2 : ∀ i' ∈ Finset.range (w + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (4 + i') x
            ((iteratedCovGrad (I := I) g₀ 2 4 i' F).toSection x) *
          ∑ l ∈ Finset.range (w + 1 - i'),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x) ≤
        (cF i' * (((w + 1 - i' : ℕ) : ℝ) * (Λ0 + 1))) * W := by
      intro i' hi'
      rw [Finset.mem_range] at hi'
      have hA1 := hcF i' x
      have hA2 : (∑ l ∈ Finset.range (w + 1 - i'),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x)) ≤
          (((w + 1 - i' : ℕ) : ℝ) * (Λ0 + 1)) * W := by
        calc (∑ l ∈ Finset.range (w + 1 - i'), b l)
            ≤ ∑ _l ∈ Finset.range (w + 1 - i'), (Λ0 + 1) * W := by
              refine Finset.sum_le_sum fun l hl => ?_
              rw [Finset.mem_range] at hl
              exact hcell l (by omega)
          _ = (((w + 1 - i' : ℕ) : ℝ) * (Λ0 + 1)) * W := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
              ring
      have hsum_nn : (0 : ℝ) ≤ ∑ l ∈ Finset.range (w + 1 - i'), b l :=
        Finset.sum_nonneg fun l _ => hb l
      calc riemannianFiberNormSq (I := I) (M := M) g₀ 2 (4 + i') x
            ((iteratedCovGrad (I := I) g₀ 2 4 i' F).toSection x) *
          ∑ l ∈ Finset.range (w + 1 - i'), b l
          ≤ cF i' * ((((w + 1 - i' : ℕ) : ℝ) * (Λ0 + 1)) * W) :=
            mul_le_mul hA1 hA2 hsum_nn (hcF_nn i')
        _ = (cF i' * (((w + 1 - i' : ℕ) : ℝ) * (Λ0 + 1))) * W := by ring
    refine le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hcell2)
      (appCcGdiag_nonneg (E := E) w)) ?_
    rw [← Finset.sum_mul, ← mul_assoc]
  have hsplit : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + w) x
      ((iteratedCovGrad (I := I) g₀ 0 4 w
        (riemannCurvatureCoeffField (I := I) (M := M) g₀ T)).toSection x) ≤
      2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + w) x
          ((iteratedCovGrad (I := I) g₀ 0 4 w
            (ccOperatorFieldComp (I := I) (M := M) g₀ 0 2 4
              (riemannLoweredContractionA (I := I) (M := M) g₀)
              T)).toSection x)
        + 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + w) x
            ((iteratedCovGrad (I := I) g₀ 0 4 w
              (ccOperatorFieldComp (I := I) (M := M) g₀ 0 2 4
                (riemannLoweredContractionB (I := I) (M := M) g₀)
                T)).toSection x) := by
    rw [riemannCurvatureCoeffField]
    exact bdRfns_iCG_add_le (I := I) (M := M) g₀ 0 4 w _ _ x
  refine le_trans hsplit ?_
  have h1 := hpart (riemannLoweredContractionA (I := I) (M := M) g₀) cW1 hcW1_nn hcW1
  have h2 := hpart (riemannLoweredContractionB (I := I) (M := M) g₀) cW2 hcW2_nn hcW2
  nlinarith [h1, h2, hW_nn]


private theorem lrOmegaHat_gridWindow (g₀ : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ l, 0 ≤ C l) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P)
          δ)
        (l : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 3 l
              (connDiffGmLoweredTensor (I := I) (M := M) g₀ g₁)).toSection x) ≤
          C l * Combinatorics.antidiagonalTupleGridWindow
            (fun l' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l') x
              ((iteratedCovGrad (I := I) g₀ 0 2 l' P).toSection x)) (l + 2) := by
  classical
  obtain ⟨CΩ, hCΩ_nn, hCΩ⟩ := bdOmRecover_gridWindow (I := I) (M := M) g₀ hδ₀
  obtain ⟨CA, hCA_nn, hCA⟩ :=
    exists_rfns_iteratedCovGrad_connDiffSection_tgrid (I := I) (M := M) g₀ hδ₀
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr_nn : 0 ≤ fr := Nat.cast_nonneg _
  refine ⟨fun l => diagonalGridGrowthFactor (E := E) l *
      ∑ i' ∈ Finset.range (l + 1), (fr ^ 2 * CΩ i') *
        ∑ l' ∈ Finset.range (l + 1 - i'),
          CA l' * Combinatorics.antidiagonalTupleGridWindowMulConst i' (l' + 1),
    fun l => mul_nonneg (appCcGdiag_nonneg (E := E) l)
      (Finset.sum_nonneg fun i' _ => mul_nonneg
        (mul_nonneg (by positivity) (hCΩ_nn i'))
        (Finset.sum_nonneg fun l' _ => mul_nonneg (hCA_nn l')
          (Combinatorics.antidiagonalTupleGridWindowMulConst_nonneg _ _))), ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hbound l x
  set b : ℕ → ℝ := fun l' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l') x
    ((iteratedCovGrad (I := I) g₀ 0 2 l' P).toSection x) with hb_def
  have hb : ∀ l', 0 ≤ b l' :=
    fun l' => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l') x _
  set W : ℝ := Combinatorics.antidiagonalTupleGridWindow b (l + 2) with hW_def
  have hW_nn : (0 : ℝ) ≤ W := Combinatorics.antidiagonalTupleGridWindow_nonneg b hb (l + 2)
  rw [connDiffGmLoweredTensor]
  refine le_trans
    (riemannianFiberNormSq_iteratedCovGrad_ccTensorCompose_diagonalProductGrid_leftFactor_le
    (I := I) (M := M) g₀ l 0 3 3
    (endoSlotZeroCcTensor (I := I) (M := M) g₀ 2 (fullRaisedEndoField (I := I) (M := M) g₁ g₀))
    (domDomCongrSection (I := I) g₀ (finRotate 3) (connDiffLoweredCc (I := I) g₀ g₁)) x) ?_
  have hop : ∀ i' : ℕ,
      riemannianFiberNormSq (I := I) (M := M) g₀ 3 (3 + i') x
          ((iteratedCovGrad (I := I) g₀ 3 3 i'
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ 2
              (fullRaisedEndoField (I := I) (M := M) g₁ g₀))).toSection x) ≤
        (fr ^ 2 * CΩ i') * Combinatorics.antidiagonalTupleGridWindow b (i' + 1) := by
    intro i'
    refine le_trans (rfns_iteratedCovGrad_slotInsertEndoCc_le_endo (I := I) (M := M) g₀ 2
      (fullRaisedEndoField (I := I) (M := M) g₁ g₀) i' x) ?_
    rw [bdSlotInsertZero_fullRaisedRev_eq_omRecover (I := I) (M := M) g₀ g₁]
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (hCΩ g₁ P htie hδ_le hδ0 hbound i' x) (by positivity)
  have hsec : ∀ l' : ℕ,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l') x
          ((iteratedCovGrad (I := I) g₀ 0 3 l'
            (domDomCongrSection (I := I) g₀ (finRotate 3)
              (connDiffLoweredCc (I := I) g₀ g₁))).toSection x) ≤
        CA l' * Combinatorics.antidiagonalTupleGridWindow b (l' + 2) := by
    intro l'
    rw [riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
      (finRotate 3) (connDiffLoweredCc (I := I) g₀ g₁) l' x]
    rw [bdRfns_iCG_connDiffLoweredCc_eq_connDiffSection (I := I) (M := M) g₀ g₁ l' x]
    have h := hCA g₁ P htie hδ_le hδ0 hbound l' x
    rwa [show (∑ k ∈ Finset.range (l' + 2), Combinatorics.antidiagonalTupleGrid b k) =
      Combinatorics.antidiagonalTupleGridWindow b (l' + 2) from rfl] at h
  have hcell : ∀ i' ∈ Finset.range (l + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ 3 (3 + i') x
          ((iteratedCovGrad (I := I) g₀ 3 3 i'
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ 2
              (fullRaisedEndoField (I := I) (M := M) g₁ g₀))).toSection x) *
        ∑ l' ∈ Finset.range (l + 1 - i'),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l') x
            ((iteratedCovGrad (I := I) g₀ 0 3 l'
              (domDomCongrSection (I := I) g₀ (finRotate 3)
                (connDiffLoweredCc (I := I) g₀ g₁))).toSection x) ≤
        ((fr ^ 2 * CΩ i') * ∑ l' ∈ Finset.range (l + 1 - i'),
          CA l' * Combinatorics.antidiagonalTupleGridWindowMulConst i' (l' + 1)) * W := by
    intro i' hi'
    rw [Finset.mem_range] at hi'
    have hA2 : (∑ l' ∈ Finset.range (l + 1 - i'),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l') x
          ((iteratedCovGrad (I := I) g₀ 0 3 l'
            (domDomCongrSection (I := I) g₀ (finRotate 3)
              (connDiffLoweredCc (I := I) g₀ g₁))).toSection x)) ≤
        ∑ l' ∈ Finset.range (l + 1 - i'),
          CA l' * Combinatorics.antidiagonalTupleGridWindow b (l' + 2) :=
      Finset.sum_le_sum fun l' _ => hsec l'
    have hsum_nn : (0 : ℝ) ≤ ∑ l' ∈ Finset.range (l + 1 - i'),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + l') x
          ((iteratedCovGrad (I := I) g₀ 0 3 l'
            (domDomCongrSection (I := I) g₀ (finRotate 3)
              (connDiffLoweredCc (I := I) g₀ g₁))).toSection x) :=
      Finset.sum_nonneg fun l' _ =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (3 + l') x _
    have hA1_rhs_nn : (0 : ℝ) ≤ (fr ^ 2 * CΩ i') *
        Combinatorics.antidiagonalTupleGridWindow b (i' + 1) :=
      mul_nonneg (mul_nonneg (by positivity) (hCΩ_nn i'))
        (Combinatorics.antidiagonalTupleGridWindow_nonneg b hb (i' + 1))
    refine le_trans (mul_le_mul (hop i') hA2 hsum_nn hA1_rhs_nn) ?_
    rw [Finset.mul_sum]
    rw [show ((fr ^ 2 * CΩ i') * ∑ l' ∈ Finset.range (l + 1 - i'),
        CA l' * Combinatorics.antidiagonalTupleGridWindowMulConst i' (l' + 1)) * W =
        ∑ l' ∈ Finset.range (l + 1 - i'),
          ((fr ^ 2 * CΩ i') * (CA l' *
            Combinatorics.antidiagonalTupleGridWindowMulConst i' (l' + 1))) * W from by
      rw [Finset.mul_sum, Finset.sum_mul]]
    refine Finset.sum_le_sum fun l' hl' => ?_
    rw [Finset.mem_range] at hl'
    have hpair : Combinatorics.antidiagonalTupleGridWindow b (i' + 1) *
        Combinatorics.antidiagonalTupleGridWindow b (l' + 1 + 1) ≤
        Combinatorics.antidiagonalTupleGridWindowMulConst i' (l' + 1) *
          Combinatorics.antidiagonalTupleGridWindow b (i' + (l' + 1) + 1) :=
      Combinatorics.antidiagonalTupleGridWindow_mul_le b hb i' (l' + 1)
    have hmono : Combinatorics.antidiagonalTupleGridWindow b (i' + (l' + 1) + 1) ≤ W := by
      rw [hW_def]
      exact Combinatorics.antidiagonalTupleGridWindow_mono b hb (by omega)
    calc (fr ^ 2 * CΩ i') * Combinatorics.antidiagonalTupleGridWindow b (i' + 1) *
          (CA l' * Combinatorics.antidiagonalTupleGridWindow b (l' + 2))
        = ((fr ^ 2 * CΩ i') * CA l') *
            (Combinatorics.antidiagonalTupleGridWindow b (i' + 1) *
              Combinatorics.antidiagonalTupleGridWindow b (l' + 1 + 1)) := by
          rw [show l' + 2 = l' + 1 + 1 from rfl]
          ring
      _ ≤ ((fr ^ 2 * CΩ i') * CA l') *
            (Combinatorics.antidiagonalTupleGridWindowMulConst i' (l' + 1) *
              Combinatorics.antidiagonalTupleGridWindow b (i' + (l' + 1) + 1)) := by
          refine mul_le_mul_of_nonneg_left hpair ?_
          exact mul_nonneg (mul_nonneg (by positivity) (hCΩ_nn i')) (hCA_nn l')
      _ ≤ ((fr ^ 2 * CΩ i') * CA l') *
            (Combinatorics.antidiagonalTupleGridWindowMulConst i' (l' + 1) * W) := by
          refine mul_le_mul_of_nonneg_left ?_
            (mul_nonneg (mul_nonneg (by positivity) (hCΩ_nn i')) (hCA_nn l'))
          exact mul_le_mul_of_nonneg_left hmono
            (Combinatorics.antidiagonalTupleGridWindowMulConst_nonneg _ _)
      _ = ((fr ^ 2 * CΩ i') * (CA l' *
            Combinatorics.antidiagonalTupleGridWindowMulConst i' (l' + 1))) * W := by
          ring
  refine le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hcell)
    (appCcGdiag_nonneg (E := E) l)) ?_
  rw [← Finset.sum_mul, ← mul_assoc]


private theorem connDiffQuadraticCurvatureTermGridWindow (g₀ : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ w, 0 ≤ C w) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P)
          δ)
        (w K : ℕ) (_hwK : w + 1 ≤ K) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + w) x
            ((iteratedCovGrad (I := I) g₀ 0 4 w
              (connDiffQuadraticCurvatureTerm (I := I) (M := M) g₀ g₁)).toSection x) ≤
          C w * Combinatorics.boundedFactorGridWindow
            (fun l' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l') x
              ((iteratedCovGrad (I := I) g₀ 0 2 l' P).toSection x)) K (w + 3) := by
  classical
  obtain ⟨CA, hCA_nn, hCA⟩ :=
    exists_rfns_iteratedCovGrad_connDiffSection_tgrid (I := I) (M := M) g₀ hδ₀
  obtain ⟨CΩ, hCΩ_nn, hCΩ⟩ := lrOmegaHat_gridWindow (I := I) (M := M) g₀ hδ₀
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr_nn : 0 ≤ fr := Nat.cast_nonneg _
  set CQ : ℕ → ℝ := fun w => diagonalGridGrowthFactor (E := E) w *
    ∑ u' ∈ Finset.range (w + 1), (fr ^ 2 * CA u') *
      ∑ w' ∈ Finset.range (w + 1 - u'),
        CΩ w' * (((u' + 2 : ℕ) : ℝ) * ((w' + 2 : ℕ) : ℝ) *
          Combinatorics.windowPairCellCount (u' + 2) (w' + 2)) with hCQ_def
  have hCQ_nn : ∀ w, 0 ≤ CQ w := by
    intro w
    rw [hCQ_def]
    exact mul_nonneg (appCcGdiag_nonneg (E := E) w)
      (Finset.sum_nonneg fun u' _ => mul_nonneg
        (mul_nonneg (by positivity) (hCA_nn u'))
        (Finset.sum_nonneg fun w' _ => mul_nonneg (hCΩ_nn w')
          (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
            (Combinatorics.windowPairCellCount_nonneg _ _))))
  refine ⟨fun w => 94 * CQ w, fun w => by have := hCQ_nn w; linarith, ?_⟩
  intro g₁ P htie δ hδ_le hδ0 hbound w K hwK x
  set b : ℕ → ℝ := fun l' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l') x
    ((iteratedCovGrad (I := I) g₀ 0 2 l' P).toSection x) with hb_def
  have hb : ∀ l', 0 ≤ b l' :=
    fun l' => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l') x _
  set W : ℝ := Combinatorics.boundedFactorGridWindow b K (w + 3) with hW_def
  have hW_nn : (0 : ℝ) ≤ W := Combinatorics.boundedFactorGridWindow_nonneg b hb K (w + 3)
  have hbase : ∀ (S : SmoothCcTensor g₀ 0 3)
      (hS : ∀ (w' : ℕ) (y : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + w') y
            ((iteratedCovGrad (I := I) g₀ 0 3 w' S).toSection y) ≤
          CΩ w' * Combinatorics.antidiagonalTupleGridWindow
            (fun l' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l') y
              ((iteratedCovGrad (I := I) g₀ 0 2 l' P).toSection y)) (w' + 2)),
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + w) x
          ((iteratedCovGrad (I := I) g₀ 0 4 w
            (ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 4
              (armSlotEndoCc (I := I) (M := M) g₀ 2 (connDiffEndo (I := I) (M := M) g₀ g₁))
              S)).toSection x) ≤
        CQ w * W := by
    intro S hS
    refine le_trans
      (riemannianFiberNormSq_iteratedCovGrad_ccTensorCompose_diagonalProductGrid_leftFactor_le
      (I := I) (M := M) g₀ w 0 3 4
      (armSlotEndoCc (I := I) (M := M) g₀ 2 (connDiffEndo (I := I) (M := M) g₀ g₁)) S x) ?_
    have hcell : ∀ u' ∈ Finset.range (w + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + u') x
            ((iteratedCovGrad (I := I) g₀ 3 4 u'
              (armSlotEndoCc (I := I) (M := M) g₀ 2
                (connDiffEndo (I := I) (M := M) g₀ g₁))).toSection x) *
          ∑ w' ∈ Finset.range (w + 1 - u'),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + w') x
              ((iteratedCovGrad (I := I) g₀ 0 3 w' S).toSection x) ≤
        ((fr ^ 2 * CA u') * ∑ w' ∈ Finset.range (w + 1 - u'),
          CΩ w' * (((u' + 2 : ℕ) : ℝ) * ((w' + 2 : ℕ) : ℝ) *
            Combinatorics.windowPairCellCount (u' + 2) (w' + 2))) * W := by
      intro u' hu'
      rw [Finset.mem_range] at hu'
      have hA1 : riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + u') x
          ((iteratedCovGrad (I := I) g₀ 3 4 u'
            (armSlotEndoCc (I := I) (M := M) g₀ 2
              (connDiffEndo (I := I) (M := M) g₀ g₁))).toSection x) ≤
          (fr ^ 2 * CA u') * Combinatorics.antidiagonalTupleGridWindow b (u' + 2) := by
        refine le_trans (bdArmSlot2_rfns_le (I := I) (M := M) g₀ g₁ u' x) ?_
        rw [← hfr_def, mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have h2 := hCA g₁ P htie hδ_le hδ0 hbound u' x
        rwa [show (∑ k ∈ Finset.range (u' + 2), Combinatorics.antidiagonalTupleGrid b k) =
          Combinatorics.antidiagonalTupleGridWindow b (u' + 2) from rfl] at h2
      have hA2 : (∑ w' ∈ Finset.range (w + 1 - u'),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + w') x
            ((iteratedCovGrad (I := I) g₀ 0 3 w' S).toSection x)) ≤
          ∑ w' ∈ Finset.range (w + 1 - u'),
            CΩ w' * Combinatorics.antidiagonalTupleGridWindow b (w' + 2) :=
        Finset.sum_le_sum fun w' _ => hS w' x
      have hsum_nn : (0 : ℝ) ≤ ∑ w' ∈ Finset.range (w + 1 - u'),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + w') x
            ((iteratedCovGrad (I := I) g₀ 0 3 w' S).toSection x) :=
        Finset.sum_nonneg fun w' _ =>
          riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (3 + w') x _
      have hA1_rhs_nn : (0 : ℝ) ≤ (fr ^ 2 * CA u') *
          Combinatorics.antidiagonalTupleGridWindow b (u' + 2) :=
        mul_nonneg (mul_nonneg (by positivity) (hCA_nn u'))
          (Combinatorics.antidiagonalTupleGridWindow_nonneg b hb (u' + 2))
      refine le_trans (mul_le_mul hA1 hA2 hsum_nn hA1_rhs_nn) ?_
      rw [Finset.mul_sum]
      rw [show ((fr ^ 2 * CA u') * ∑ w' ∈ Finset.range (w + 1 - u'),
          CΩ w' * (((u' + 2 : ℕ) : ℝ) * ((w' + 2 : ℕ) : ℝ) *
            Combinatorics.windowPairCellCount (u' + 2) (w' + 2))) * W =
          ∑ w' ∈ Finset.range (w + 1 - u'),
            ((fr ^ 2 * CA u') * (CΩ w' * (((u' + 2 : ℕ) : ℝ) * ((w' + 2 : ℕ) : ℝ) *
              Combinatorics.windowPairCellCount (u' + 2) (w' + 2)))) * W from by
        rw [Finset.mul_sum, Finset.sum_mul]]
      refine Finset.sum_le_sum fun w' hw' => ?_
      rw [Finset.mem_range] at hw'
      have hbf1 : Combinatorics.antidiagonalTupleGridWindow b (u' + 2) ≤
          ((u' + 2 : ℕ) : ℝ) * Combinatorics.boundedFactorGridWindow b K (u' + 2) :=
        lrWindow_le_bFGW b hb (by omega) (le_refl _) (by omega)
      have hbf2 : Combinatorics.antidiagonalTupleGridWindow b (w' + 2) ≤
          ((w' + 2 : ℕ) : ℝ) * Combinatorics.boundedFactorGridWindow b K (w' + 2) :=
        lrWindow_le_bFGW b hb (by omega) (le_refl _) (by omega)
      have hmul : Combinatorics.boundedFactorGridWindow b K (u' + 2) *
          Combinatorics.boundedFactorGridWindow b K (w' + 2) ≤
          Combinatorics.windowPairCellCount (u' + 2) (w' + 2) *
            Combinatorics.boundedFactorGridWindow b K (u' + 2 + (w' + 2) - 1) :=
        Combinatorics.boundedFactorGridWindow_mul_le b hb K (u' + 2) (w' + 2)
          (by omega) (by omega)
      have hmono : Combinatorics.boundedFactorGridWindow b K (u' + 2 + (w' + 2) - 1) ≤ W := by
        rw [hW_def]
        exact Combinatorics.boundedFactorGridWindow_mono b hb (le_refl K) (by omega)
      have hbf_nn1 : (0 : ℝ) ≤ Combinatorics.boundedFactorGridWindow b K (u' + 2) :=
        Combinatorics.boundedFactorGridWindow_nonneg b hb K _
      have hbf_nn2 : (0 : ℝ) ≤ Combinatorics.boundedFactorGridWindow b K (w' + 2) :=
        Combinatorics.boundedFactorGridWindow_nonneg b hb K _
      have hcnt_nn : (0 : ℝ) ≤ Combinatorics.windowPairCellCount (u' + 2) (w' + 2) :=
        Combinatorics.windowPairCellCount_nonneg _ _
      have hwin1_nn : (0 : ℝ) ≤ Combinatorics.antidiagonalTupleGridWindow b (u' + 2) :=
        Combinatorics.antidiagonalTupleGridWindow_nonneg b hb _
      have hwin2_nn : (0 : ℝ) ≤ Combinatorics.antidiagonalTupleGridWindow b (w' + 2) :=
        Combinatorics.antidiagonalTupleGridWindow_nonneg b hb _
      calc (fr ^ 2 * CA u') * Combinatorics.antidiagonalTupleGridWindow b (u' + 2) *
            (CΩ w' * Combinatorics.antidiagonalTupleGridWindow b (w' + 2))
          = ((fr ^ 2 * CA u') * CΩ w') *
              (Combinatorics.antidiagonalTupleGridWindow b (u' + 2) *
                Combinatorics.antidiagonalTupleGridWindow b (w' + 2)) := by ring
        _ ≤ ((fr ^ 2 * CA u') * CΩ w') *
              ((((u' + 2 : ℕ) : ℝ) * Combinatorics.boundedFactorGridWindow b K (u' + 2)) *
                (((w' + 2 : ℕ) : ℝ) * Combinatorics.boundedFactorGridWindow b K (w' + 2))) := by
            refine mul_le_mul_of_nonneg_left ?_
              (mul_nonneg (mul_nonneg (by positivity) (hCA_nn u')) (hCΩ_nn w'))
            exact mul_le_mul hbf1 hbf2 hwin2_nn
              (mul_nonneg (Nat.cast_nonneg _) hbf_nn1)
        _ = ((fr ^ 2 * CA u') * CΩ w') * (((u' + 2 : ℕ) : ℝ) * ((w' + 2 : ℕ) : ℝ)) *
              (Combinatorics.boundedFactorGridWindow b K (u' + 2) *
                Combinatorics.boundedFactorGridWindow b K (w' + 2)) := by ring
        _ ≤ ((fr ^ 2 * CA u') * CΩ w') * (((u' + 2 : ℕ) : ℝ) * ((w' + 2 : ℕ) : ℝ)) *
              (Combinatorics.windowPairCellCount (u' + 2) (w' + 2) *
                Combinatorics.boundedFactorGridWindow b K (u' + 2 + (w' + 2) - 1)) := by
            refine mul_le_mul_of_nonneg_left hmul ?_
            exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (hCA_nn u'))
              (hCΩ_nn w')) (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
        _ ≤ ((fr ^ 2 * CA u') * CΩ w') * (((u' + 2 : ℕ) : ℝ) * ((w' + 2 : ℕ) : ℝ)) *
              (Combinatorics.windowPairCellCount (u' + 2) (w' + 2) * W) := by
            refine mul_le_mul_of_nonneg_left ?_
              (mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (hCA_nn u'))
                (hCΩ_nn w')) (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
            exact mul_le_mul_of_nonneg_left hmono hcnt_nn
        _ = ((fr ^ 2 * CA u') * (CΩ w' * (((u' + 2 : ℕ) : ℝ) * ((w' + 2 : ℕ) : ℝ) *
              Combinatorics.windowPairCellCount (u' + 2) (w' + 2)))) * W := by ring
    refine le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hcell)
      (appCcGdiag_nonneg (E := E) w)) ?_
    rw [← Finset.sum_mul, ← mul_assoc, hCQ_def]
  have hΩ : ∀ (w' : ℕ) (y : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + w') y
          ((iteratedCovGrad (I := I) g₀ 0 3 w'
            (connDiffGmLoweredTensor (I := I) (M := M) g₀ g₁)).toSection y) ≤
        CΩ w' * Combinatorics.antidiagonalTupleGridWindow
          (fun l' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l') y
            ((iteratedCovGrad (I := I) g₀ 0 2 l' P).toSection y)) (w' + 2) :=
    fun w' y => hCΩ g₁ P htie hδ_le hδ0 hbound w' y
  have hΩswap : ∀ (w' : ℕ) (y : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + w') y
          ((iteratedCovGrad (I := I) g₀ 0 3 w'
            (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 1)
              (connDiffGmLoweredTensor (I := I) (M := M) g₀ g₁))).toSection y) ≤
        CΩ w' * Combinatorics.antidiagonalTupleGridWindow
          (fun l' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l') y
            ((iteratedCovGrad (I := I) g₀ 0 2 l' P).toSection y)) (w' + 2) := by
    intro w' y
    rw [riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 3) 1) (connDiffGmLoweredTensor (I := I) (M := M) g₀ g₁) w' y]
    exact hΩ w' y
  have hQB := hbase (connDiffGmLoweredTensor (I := I) (M := M) g₀ g₁) hΩ
  have hQA := hbase (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 1)
    (connDiffGmLoweredTensor (I := I) (M := M) g₀ g₁)) hΩswap
  have hQB' : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + w) x
      ((iteratedCovGrad (I := I) g₀ 0 4 w
        (connDiffQuadraticPairedTensor (I := I) (M := M) g₀ g₁)).toSection x) ≤
      CQ w * W := by
    rw [connDiffQuadraticPairedTensor]
    exact hQB
  have hQA' : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + w) x
      ((iteratedCovGrad (I := I) g₀ 0 4 w
        (connDiffQuadraticComposedTensor (I := I) (M := M) g₀ g₁)).toSection x) ≤
      CQ w * W := by
    rw [connDiffQuadraticComposedTensor]
    exact hQA
  have hddcQ : ∀ (σ : Equiv.Perm (Fin 4)) (F : SmoothCcTensor g₀ 0 4)
      (hF : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + w) x
        ((iteratedCovGrad (I := I) g₀ 0 4 w F).toSection x) ≤ CQ w * W),
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + w) x
        ((iteratedCovGrad (I := I) g₀ 0 4 w
          (domDomCongrSection (I := I) g₀ σ F)).toSection x) ≤ CQ w * W := by
    intro σ F hF
    rw [riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
      σ F w x]
    exact hF
  rw [connDiffQuadraticCurvatureTerm]
  have hsum6 : ∀ (F1 F2 F3 F4 F5 F6 : SmoothCcTensor g₀ 0 4)
      (h1 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + w) x
        ((iteratedCovGrad (I := I) g₀ 0 4 w F1).toSection x) ≤ CQ w * W)
      (h2 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + w) x
        ((iteratedCovGrad (I := I) g₀ 0 4 w F2).toSection x) ≤ CQ w * W)
      (h3 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + w) x
        ((iteratedCovGrad (I := I) g₀ 0 4 w F3).toSection x) ≤ CQ w * W)
      (h4 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + w) x
        ((iteratedCovGrad (I := I) g₀ 0 4 w F4).toSection x) ≤ CQ w * W)
      (h5 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + w) x
        ((iteratedCovGrad (I := I) g₀ 0 4 w F5).toSection x) ≤ CQ w * W)
      (h6 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + w) x
        ((iteratedCovGrad (I := I) g₀ 0 4 w F6).toSection x) ≤ CQ w * W),
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + w) x
        ((iteratedCovGrad (I := I) g₀ 0 4 w
          (F1 + F2 + F3 + F4 + F5 + F6)).toSection x) ≤ 94 * (CQ w * W) := by
    intro F1 F2 F3 F4 F5 F6 h1 h2 h3 h4 h5 h6
    have ha1 := bdRfns_iCG_add_le (I := I) (M := M) g₀ 0 4 w (F1 + F2 + F3 + F4 + F5) F6 x
    have ha2 := bdRfns_iCG_add_le (I := I) (M := M) g₀ 0 4 w (F1 + F2 + F3 + F4) F5 x
    have ha3 := bdRfns_iCG_add_le (I := I) (M := M) g₀ 0 4 w (F1 + F2 + F3) F4 x
    have ha4 := bdRfns_iCG_add_le (I := I) (M := M) g₀ 0 4 w (F1 + F2) F3 x
    have ha5 := bdRfns_iCG_add_le (I := I) (M := M) g₀ 0 4 w F1 F2 x
    have hnn : (0 : ℝ) ≤ CQ w * W := mul_nonneg (hCQ_nn w) hW_nn
    nlinarith [ha1, ha2, ha3, ha4, ha5, h1, h2, h3, h4, h5, h6,
      riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (4 + w) x
        ((iteratedCovGrad (I := I) g₀ 0 4 w (F1 + F2 + F3 + F4 + F5)).toSection x),
      riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (4 + w) x
        ((iteratedCovGrad (I := I) g₀ 0 4 w (F1 + F2 + F3 + F4)).toSection x),
      riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (4 + w) x
        ((iteratedCovGrad (I := I) g₀ 0 4 w (F1 + F2 + F3)).toSection x),
      riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (4 + w) x
        ((iteratedCovGrad (I := I) g₀ 0 4 w (F1 + F2)).toSection x)]
  have h6 := hsum6
    (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
      (connDiffQuadraticPairedTensor (I := I) (M := M) g₀ g₁))
    (connDiffQuadraticPairedTensor (I := I) (M := M) g₀ g₁)
    (domDomCongrSection (I := I) g₀ lrPermA
      (connDiffQuadraticComposedTensor (I := I) (M := M) g₀ g₁))
    (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 2)
      (connDiffQuadraticComposedTensor (I := I) (M := M) g₀ g₁))
    (domDomCongrSection (I := I) g₀ lrPermB
      (connDiffQuadraticComposedTensor (I := I) (M := M) g₀ g₁))
    (domDomCongrSection (I := I) g₀ lrPermC
      (connDiffQuadraticComposedTensor (I := I) (M := M) g₀ g₁))
    (hddcQ _ _ hQB') hQB' (hddcQ _ _ hQA') (hddcQ _ _ hQA') (hddcQ _ _ hQA')
    (hddcQ _ _ hQA')
  refine le_trans h6 (le_of_eq ?_)
  ring

private lemma lrGridWindow_mono_of_le (b b' : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j)
    (hbb : ∀ j, b j ≤ b' j) (w : ℕ) :
    Combinatorics.antidiagonalTupleGridWindow b w ≤
      Combinatorics.antidiagonalTupleGridWindow b' w := by
  rw [Combinatorics.antidiagonalTupleGridWindow, Combinatorics.antidiagonalTupleGridWindow]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [Combinatorics.antidiagonalTupleGrid, Combinatorics.antidiagonalTupleGrid]
  refine Finset.sum_le_sum fun n _ => ?_
  refine Finset.sum_le_sum fun e _ => ?_
  exact Finset.prod_le_prod (fun m _ => hb (e m)) (fun m _ => hbb (e m))


private theorem riemannCurvatureRemainderGridWindow (g₀ : SmoothRiemannianMetric I M) (Λ0 : ℝ)
    (hΛ0 : 0 ≤ Λ0)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ w, 0 ≤ C w) ∧
      ∀ (T : SmoothCcTensor g₀ 0 2)
        (_hT0 : ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (T.toSection x) ≤ Λ0)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (hδZ : metricCauchySchwarzBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ)
        {s : ℝ} (_hs : s ∈ Set.Icc (0 : ℝ) 1)
        (w K : ℕ) (_hwK : w + 1 ≤ K) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + w) x
            ((iteratedCovGrad (I := I) g₀ 0 4 w
              (lrR4 (I := I) (M := M) g₀ T hδ hδZ s)).toSection x) ≤
          C w * Combinatorics.boundedFactorGridWindow
            (fun l' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l') x
              ((iteratedCovGrad (I := I) g₀ 0 2 l' T).toSection x)) K (w + 3) := by
  classical
  obtain ⟨CF, hCF_nn, hCF⟩ := riemannCurvatureCoeffFieldGridWindow (I := I) (M := M) g₀ Λ0 hΛ0
  obtain ⟨CQ, hCQ_nn, hCQ⟩ := connDiffQuadraticCurvatureTermGridWindow (I := I) (M := M) g₀ hδ₀
  refine ⟨fun w => 2 * CF w + 2 * CQ w,
    fun w => by have := hCF_nn w; have := hCQ_nn w; linarith, ?_⟩
  intro T hT0 δ hδ_le hδ0 hδ hδZ s hs w K hwK x
  set b : ℕ → ℝ := fun l' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l') x
    ((iteratedCovGrad (I := I) g₀ 0 2 l' T).toSection x) with hb_def
  have hb : ∀ l', 0 ≤ b l' :=
    fun l' => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l') x _
  set W : ℝ := Combinatorics.boundedFactorGridWindow b K (w + 3) with hW_def
  have hW_nn : (0 : ℝ) ≤ W := Combinatorics.boundedFactorGridWindow_nonneg b hb K (w + 3)
  obtain ⟨hs0, hs1⟩ := hs
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hs_mem : s ∈ realizedSmallSet (δ := δ) (δ' := δ) :=
    Icc_subset_realizedSmallSet hδ_lt hδ_lt ⟨hs0, hs1⟩
  have htie : ∀ (y : M) (v w' : TangentSpace I y),
      (realizedFam (I := I) g₀ T 0 hδ hδZ s).inner y v w' =
        g₀.inner y v w' +
          ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T 0 s) y v w' :=
    fun y v w' => realizedFam_inner_of_mem (I := I) g₀ T 0 hδ hδZ hs_mem y v w'
  have hδP : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T 0 s)) δ := by
    intro y v w'
    have hraw := convexPerturbation_gFibreOpBound_abs (I := I) g₀ T 0 hδ hδZ s y v w'
    have heq : |1 - s| * δ + |s| * δ = δ := by
      rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - s), abs_of_nonneg hs0]
      ring
    rwa [heq] at hraw
  have hcP : convexPerturbation (I := I) g₀ T 0 s = s • T := by
    rw [convexPerturbation, smul_zero, zero_add]
  have hss : 0 ≤ s * s := mul_nonneg hs0 hs0
  have hs2 : s * s ≤ 1 := by nlinarith
  have hPT : ∀ l', riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l') x
      ((iteratedCovGrad (I := I) g₀ 0 2 l'
        (convexPerturbation (I := I) g₀ T 0 s)).toSection x) ≤ b l' := by
    intro l'
    rw [hcP, iteratedCovGrad_smul_real]
    rw [show ((s • iteratedCovGrad (I := I) g₀ 0 2 l' T).toSection x) =
        s • ((iteratedCovGrad (I := I) g₀ 0 2 l' T).toSection x) from by
      rw [SmoothCcTensor.toSection_smul]
      rfl]
    rw [riemannianFiberNormSq_smul (I := I) (M := M) g₀ 0 (2 + l') x]
    nlinarith [hb l', hss, hs2]
  have hsub : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + w) x
      ((iteratedCovGrad (I := I) g₀ 0 4 w
        (lrR4 (I := I) (M := M) g₀ T hδ hδZ s)).toSection x) ≤
      2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + w) x
          ((iteratedCovGrad (I := I) g₀ 0 4 w
            ((-(s / 2) : ℝ) • riemannCurvatureCoeffField (I := I) (M := M) g₀ T)).toSection x)
        + 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + w) x
            ((iteratedCovGrad (I := I) g₀ 0 4 w
              (connDiffQuadraticCurvatureTerm (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T 0 hδ hδZ s))).toSection x) := by
    rw [lrR4]
    exact bdRfns_iCG_sub_le (I := I) (M := M) g₀ 0 4 w _ _ x
  have hA : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + w) x
      ((iteratedCovGrad (I := I) g₀ 0 4 w
        ((-(s / 2) : ℝ) • riemannCurvatureCoeffField (I := I) (M := M) g₀ T)).toSection x) ≤
      CF w * W := by
    rw [iteratedCovGrad_smul_real]
    rw [show (((-(s / 2) : ℝ) • iteratedCovGrad (I := I) g₀ 0 4 w
        (riemannCurvatureCoeffField (I := I) (M := M) g₀ T)).toSection x) =
        (-(s / 2) : ℝ) • ((iteratedCovGrad (I := I) g₀ 0 4 w
          (riemannCurvatureCoeffField (I := I) (M := M) g₀ T)).toSection x) from by
      rw [SmoothCcTensor.toSection_smul]
      rfl]
    rw [riemannianFiberNormSq_smul (I := I) (M := M) g₀ 0 (4 + w) x]
    have hbase := hCF T hT0 w K (by omega) x
    have hbase' : CF w * Combinatorics.boundedFactorGridWindow b K (w + 2) ≤ CF w * W := by
      refine mul_le_mul_of_nonneg_left ?_ (hCF_nn w)
      rw [hW_def]
      exact Combinatorics.boundedFactorGridWindow_mono b hb (le_refl K) (by omega)
    have hsq : (-(s / 2) : ℝ) * -(s / 2) ≤ 1 := by nlinarith
    have hsq0 : (0 : ℝ) ≤ (-(s / 2) : ℝ) * -(s / 2) := by nlinarith
    have hrfns_nn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (4 + w) x
      ((iteratedCovGrad (I := I) g₀ 0 4 w
        (riemannCurvatureCoeffField (I := I) (M := M) g₀ T)).toSection x)
    nlinarith [le_trans hbase hbase', hrfns_nn]
  have hB : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + w) x
      ((iteratedCovGrad (I := I) g₀ 0 4 w
        (connDiffQuadraticCurvatureTerm (I := I) (M := M) g₀
          (realizedFam (I := I) g₀ T 0 hδ hδZ s))).toSection x) ≤
      CQ w * W := by
    have hbase := hCQ (realizedFam (I := I) g₀ T 0 hδ hδZ s)
      (convexPerturbation (I := I) g₀ T 0 s) htie hδ_le hδ0 hδP w K hwK x
    refine le_trans hbase ?_
    refine mul_le_mul_of_nonneg_left ?_ (hCQ_nn w)
    rw [hW_def]
    exact lrBFGW_mono_of_le _ b
      (fun l' => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l') x _)
      (fun l' => hPT l') K (w + 3)
  linarith [hsub, hA, hB]


theorem deTurckLieCovDerivArmDifferenceGridWindow (g₀ : SmoothRiemannianMetric I M) (Λ0 : ℝ)
    (hΛ0 : 0 ≤ Λ0)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (T : SmoothCcTensor g₀ 0 2)
        (_hTsymm : ∀ (x : M) (v w : TangentSpace I x),
          smoothCcTensorBilinForm (I := I) g₀ T x v w = smoothCcTensorBilinForm (I := I) g₀ T x w v)
        (_hT0 : ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (T.toSection x) ≤ Λ0)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (hδZ : metricCauchySchwarzBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ (0 : SmoothCcTensor g₀ 0 2)) δ)
        {s : ℝ} (_hs : s ∈ Set.Icc (0 : ℝ) 1) (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (deTurckLieCovDerivArmField (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀
                - deTurckLieCovDerivRefoldPairTraceFamily (I := I) (M := M) g₀ T hδ hδZ
                  ![Equiv.swap (0 : Fin 4) 1 * Equiv.swap (0 : Fin 4) 2,
                    Equiv.swap (2 : Fin 4) 3 * Equiv.swap (1 : Fin 4) 2 *
                      Equiv.swap (0 : Fin 4) 1,
                    Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3]
                  ![(-1 : ℝ), -1, 1] s)).toSection x) ≤
          C i * Combinatorics.boundedFactorGridWindow
            (fun l' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l') x
              ((iteratedCovGrad (I := I) g₀ 0 2 l' T).toSection x)) (i + 1) (i + 3) := by
  classical
  obtain ⟨CP, hCP_nn, hCP⟩ := bdPairTraceOp_tgrid (I := I) (M := M) g₀ hδ₀
  obtain ⟨CR, hCR_nn, hCR⟩ := riemannCurvatureRemainderGridWindow (I := I) (M := M) g₀ Λ0 hΛ0 hδ₀
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr_nn : 0 ≤ fr := Nat.cast_nonneg _
  refine ⟨fun i => diagonalGridGrowthFactor (E := E) i *
      ∑ u ∈ Finset.range (i + 1), (((u + 1 : ℕ) : ℝ) * CP u) *
        ∑ w ∈ Finset.range (i + 1 - u),
          (fr * (fr * CR w)) * Combinatorics.windowPairCellCount (u + 1) (w + 3),
    fun i => mul_nonneg (appCcGdiag_nonneg (E := E) i)
      (Finset.sum_nonneg fun u _ => mul_nonneg
        (mul_nonneg (Nat.cast_nonneg _) (hCP_nn u))
        (Finset.sum_nonneg fun w _ => mul_nonneg
          (mul_nonneg hfr_nn (mul_nonneg hfr_nn (hCR_nn w)))
          (Combinatorics.windowPairCellCount_nonneg _ _))), ?_⟩
  intro T hTsymm hT0 δ hδ_le hδ0 hδ hδZ s hs i x
  set b : ℕ → ℝ := fun l' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l') x
    ((iteratedCovGrad (I := I) g₀ 0 2 l' T).toSection x) with hb_def
  have hb : ∀ l', 0 ≤ b l' :=
    fun l' => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l') x _
  set W : ℝ := Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) with hW_def
  have hW_nn : (0 : ℝ) ≤ W :=
    Combinatorics.boundedFactorGridWindow_nonneg b hb (i + 1) (i + 3)
  obtain ⟨hs0, hs1⟩ := hs
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hs_mem : s ∈ realizedSmallSet (δ := δ) (δ' := δ) :=
    Icc_subset_realizedSmallSet hδ_lt hδ_lt ⟨hs0, hs1⟩
  have htie : ∀ (y : M) (v w' : TangentSpace I y),
      (realizedFam (I := I) g₀ T 0 hδ hδZ s).inner y v w' =
        g₀.inner y v w' +
          ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T 0 s) y v w' :=
    fun y v w' => realizedFam_inner_of_mem (I := I) g₀ T 0 hδ hδZ hs_mem y v w'
  have hδP : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (convexPerturbation (I := I) g₀ T 0 s)) δ := by
    intro y v w'
    have hraw := convexPerturbation_gFibreOpBound_abs (I := I) g₀ T 0 hδ hδZ s y v w'
    have heq : |1 - s| * δ + |s| * δ = δ := by
      rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - s), abs_of_nonneg hs0]
      ring
    rwa [heq] at hraw
  have hcP : convexPerturbation (I := I) g₀ T 0 s = s • T := by
    rw [convexPerturbation, smul_zero, zero_add]
  have hss : 0 ≤ s * s := mul_nonneg hs0 hs0
  have hs2 : s * s ≤ 1 := by nlinarith
  have hPT : ∀ (l' : ℕ) (y : M), riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l') y
      ((iteratedCovGrad (I := I) g₀ 0 2 l'
        (convexPerturbation (I := I) g₀ T 0 s)).toSection y) ≤
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l') y
        ((iteratedCovGrad (I := I) g₀ 0 2 l' T).toSection y) := by
    intro l' y
    rw [hcP, iteratedCovGrad_smul_real]
    rw [show ((s • iteratedCovGrad (I := I) g₀ 0 2 l' T).toSection y) =
        s • ((iteratedCovGrad (I := I) g₀ 0 2 l' T).toSection y) from by
      rw [SmoothCcTensor.toSection_smul]
      rfl]
    rw [riemannianFiberNormSq_smul (I := I) (M := M) g₀ 0 (2 + l') y]
    nlinarith [riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l') y
      ((iteratedCovGrad (I := I) g₀ 0 2 l' T).toSection y), hss, hs2]
  have hlift : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
      ((iteratedCovGrad (I := I) g₀ 2 2 i
        (deTurckLieCovDerivArmField (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T 0 hδ hδZ s) g₀
          - deTurckLieCovDerivRefoldPairTraceFamily (I := I) (M := M) g₀ T hδ hδZ
            ![Equiv.swap (0 : Fin 4) 1 * Equiv.swap (0 : Fin 4) 2,
              Equiv.swap (2 : Fin 4) 3 * Equiv.swap (1 : Fin 4) 2 *
                Equiv.swap (0 : Fin 4) 1,
              Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3]
            ![(-1 : ℝ), -1, 1] s)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 2 2 i
          (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
            (armPairTraceOpCc (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ s))
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                (lrR4 (I := I) (M := M) g₀ T hδ hδZ s))))).toSection x) := by
    rw [lrArm_sub_family_eq_pairTrace (I := I) (M := M) g₀ T hδ_lt hδ hδZ hTsymm
      ⟨hs0, hs1⟩]
    rw [iteratedCovGrad_smul_real]
    rw [show (((-1 : ℝ) • iteratedCovGrad (I := I) g₀ 2 2 i
        (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
          (armPairTraceOpCc (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ s))
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (lrR4 (I := I) (M := M) g₀ T hδ hδZ s))))).toSection x) =
        (-1 : ℝ) • ((iteratedCovGrad (I := I) g₀ 2 2 i
          (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
            (armPairTraceOpCc (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ s))
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                (lrR4 (I := I) (M := M) g₀ T hδ hδZ s))))).toSection x) from by
      rw [SmoothCcTensor.toSection_smul]
      rfl]
    rw [riemannianFiberNormSq_smul]
    norm_num
  rw [hlift]
  refine le_trans
    (riemannianFiberNormSq_iteratedCovGrad_ccTensorCompose_diagonalProductGrid_leftFactor_le
    (I := I) (M := M) g₀ i 2 6 2
    (armPairTraceOpCc (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T 0 hδ hδZ s))
    (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
      (slotExtendIter (I := I) (M := M) g₀ 0 4 2
        (lrR4 (I := I) (M := M) g₀ T hδ hδZ s))) x) ?_
  have hWtower : ∀ w, w ≤ i →
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + w) x
        ((iteratedCovGrad (I := I) g₀ 2 6 w
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (lrR4 (I := I) (M := M) g₀ T hδ hδZ s)))).toSection x) ≤
      (fr * (fr * CR w)) * Combinatorics.boundedFactorGridWindow b (i + 1) (w + 3) := by
    intro w hw
    have hperm : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + w) x
        ((iteratedCovGrad (I := I) g₀ 2 6 w
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (lrR4 (I := I) (M := M) g₀ T hδ hδZ s)))).toSection x) =
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + w) x
          ((iteratedCovGrad (I := I) g₀ 2 6 w
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (lrR4 (I := I) (M := M) g₀ T hδ hδZ s))).toSection x) :=
      riemannianFiberNormSq_iteratedCovGrad_rs_eq_of_section_domDomCongr (I := I) (M := M) g₀ 2 6
        armPairTraceSlotPerm6
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2
          (lrR4 (I := I) (M := M) g₀ T hδ hδZ s))
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (lrR4 (I := I) (M := M) g₀ T hδ hδZ s)))
        (fun y d => by
          rw [rsDomDomCongrSection_toSection, toModel_rsDomDomCongr_apply]) w x
    rw [hperm]
    have h1 := rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 1 5
      (slotExtendIter (I := I) (M := M) g₀ 0 4 1
        (lrR4 (I := I) (M := M) g₀ T hδ hδZ s)) w x
    have h2 := rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 0 4
      (lrR4 (I := I) (M := M) g₀ T hδ hδZ s) w x
    have h3 := hCR T hT0 hδ_le hδ0 hδ hδZ ⟨hs0, hs1⟩ w (i + 1) (by omega) x
    calc riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + w) x
          ((iteratedCovGrad (I := I) g₀ 2 6 w
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (lrR4 (I := I) (M := M) g₀ T hδ hδZ s))).toSection x)
        ≤ fr * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (5 + w) x
            ((iteratedCovGrad (I := I) g₀ 1 5 w
              (slotExtendIter (I := I) (M := M) g₀ 0 4 1
                (lrR4 (I := I) (M := M) g₀ T hδ hδZ s))).toSection x) := h1
      _ ≤ fr * (fr * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + w) x
            ((iteratedCovGrad (I := I) g₀ 0 4 w
              (lrR4 (I := I) (M := M) g₀ T hδ hδZ s)).toSection x)) :=
          mul_le_mul_of_nonneg_left h2 hfr_nn
      _ ≤ fr * (fr * (CR w * Combinatorics.boundedFactorGridWindow b (i + 1) (w + 3))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 hfr_nn) hfr_nn
      _ = (fr * (fr * CR w)) * Combinatorics.boundedFactorGridWindow b (i + 1) (w + 3) := by
          ring
  have hcell : ∀ u ∈ Finset.range (i + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ 6 (2 + u) x
          ((iteratedCovGrad (I := I) g₀ 6 2 u
            (armPairTraceOpCc (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T 0 hδ hδZ s))).toSection x) *
        ∑ w ∈ Finset.range (i + 1 - u),
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + w) x
            ((iteratedCovGrad (I := I) g₀ 2 6 w
              (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
                (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                  (lrR4 (I := I) (M := M) g₀ T hδ hδZ s)))).toSection x) ≤
      ((((u + 1 : ℕ) : ℝ) * CP u) * ∑ w ∈ Finset.range (i + 1 - u),
        (fr * (fr * CR w)) * Combinatorics.windowPairCellCount (u + 1) (w + 3)) * W := by
    intro u hu
    rw [Finset.mem_range] at hu
    have hA1 : riemannianFiberNormSq (I := I) (M := M) g₀ 6 (2 + u) x
        ((iteratedCovGrad (I := I) g₀ 6 2 u
          (armPairTraceOpCc (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T 0 hδ hδZ s))).toSection x) ≤
        (((u + 1 : ℕ) : ℝ) * CP u) *
          Combinatorics.boundedFactorGridWindow b (i + 1) (u + 1) := by
      have h0 := hCP (realizedFam (I := I) g₀ T 0 hδ hδZ s)
        (convexPerturbation (I := I) g₀ T 0 s) htie hδ_le hδ0 hδP u x
      refine le_trans h0 ?_
      have hmono1 : Combinatorics.antidiagonalTupleGridWindow
          (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 2 l
              (convexPerturbation (I := I) g₀ T 0 s)).toSection x)) (u + 1) ≤
          Combinatorics.antidiagonalTupleGridWindow b (u + 1) :=
        lrGridWindow_mono_of_le _ b
          (fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _)
          (fun l => hPT l x) (u + 1)
      have hmono2 : Combinatorics.antidiagonalTupleGridWindow b (u + 1) ≤
          ((u + 1 : ℕ) : ℝ) * Combinatorics.boundedFactorGridWindow b (i + 1) (u + 1) :=
        lrWindow_le_bFGW b hb (by omega) (le_refl _) (by omega)
      calc CP u * Combinatorics.antidiagonalTupleGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l
                (convexPerturbation (I := I) g₀ T 0 s)).toSection x)) (u + 1)
          ≤ CP u * Combinatorics.antidiagonalTupleGridWindow b (u + 1) :=
            mul_le_mul_of_nonneg_left hmono1 (hCP_nn u)
        _ ≤ CP u * (((u + 1 : ℕ) : ℝ) *
              Combinatorics.boundedFactorGridWindow b (i + 1) (u + 1)) :=
            mul_le_mul_of_nonneg_left hmono2 (hCP_nn u)
        _ = (((u + 1 : ℕ) : ℝ) * CP u) *
              Combinatorics.boundedFactorGridWindow b (i + 1) (u + 1) := by ring
    have hA2 : (∑ w ∈ Finset.range (i + 1 - u),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + w) x
          ((iteratedCovGrad (I := I) g₀ 2 6 w
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                (lrR4 (I := I) (M := M) g₀ T hδ hδZ s)))).toSection x)) ≤
        ∑ w ∈ Finset.range (i + 1 - u),
          (fr * (fr * CR w)) * Combinatorics.boundedFactorGridWindow b (i + 1) (w + 3) := by
      refine Finset.sum_le_sum fun w hw => ?_
      rw [Finset.mem_range] at hw
      exact hWtower w (by omega)
    have hsum_nn : (0 : ℝ) ≤ ∑ w ∈ Finset.range (i + 1 - u),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + w) x
          ((iteratedCovGrad (I := I) g₀ 2 6 w
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 armPairTraceSlotPerm6
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                (lrR4 (I := I) (M := M) g₀ T hδ hδZ s)))).toSection x) :=
      Finset.sum_nonneg fun w _ =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (6 + w) x _
    have hA1_rhs_nn : (0 : ℝ) ≤ (((u + 1 : ℕ) : ℝ) * CP u) *
        Combinatorics.boundedFactorGridWindow b (i + 1) (u + 1) :=
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hCP_nn u))
        (Combinatorics.boundedFactorGridWindow_nonneg b hb _ _)
    refine le_trans (mul_le_mul hA1 hA2 hsum_nn hA1_rhs_nn) ?_
    rw [Finset.mul_sum]
    rw [show ((((u + 1 : ℕ) : ℝ) * CP u) * ∑ w ∈ Finset.range (i + 1 - u),
        (fr * (fr * CR w)) * Combinatorics.windowPairCellCount (u + 1) (w + 3)) * W =
        ∑ w ∈ Finset.range (i + 1 - u),
          ((((u + 1 : ℕ) : ℝ) * CP u) * ((fr * (fr * CR w)) *
            Combinatorics.windowPairCellCount (u + 1) (w + 3))) * W from by
      rw [Finset.mul_sum, Finset.sum_mul]]
    refine Finset.sum_le_sum fun w hw => ?_
    rw [Finset.mem_range] at hw
    have hpair : Combinatorics.boundedFactorGridWindow b (i + 1) (u + 1) *
        Combinatorics.boundedFactorGridWindow b (i + 1) (w + 3) ≤
        Combinatorics.windowPairCellCount (u + 1) (w + 3) *
          Combinatorics.boundedFactorGridWindow b (i + 1) (u + 1 + (w + 3) - 1) :=
      Combinatorics.boundedFactorGridWindow_mul_le b hb (i + 1) (u + 1) (w + 3)
        (by omega) (by omega)
    have hmono : Combinatorics.boundedFactorGridWindow b (i + 1) (u + 1 + (w + 3) - 1) ≤
        W := by
      rw [hW_def]
      exact Combinatorics.boundedFactorGridWindow_mono b hb (le_refl _) (by omega)
    have hcnt_nn : (0 : ℝ) ≤ Combinatorics.windowPairCellCount (u + 1) (w + 3) :=
      Combinatorics.windowPairCellCount_nonneg _ _
    calc (((u + 1 : ℕ) : ℝ) * CP u) *
          Combinatorics.boundedFactorGridWindow b (i + 1) (u + 1) *
          ((fr * (fr * CR w)) * Combinatorics.boundedFactorGridWindow b (i + 1) (w + 3))
        = ((((u + 1 : ℕ) : ℝ) * CP u) * (fr * (fr * CR w))) *
            (Combinatorics.boundedFactorGridWindow b (i + 1) (u + 1) *
              Combinatorics.boundedFactorGridWindow b (i + 1) (w + 3)) := by ring
      _ ≤ ((((u + 1 : ℕ) : ℝ) * CP u) * (fr * (fr * CR w))) *
            (Combinatorics.windowPairCellCount (u + 1) (w + 3) *
              Combinatorics.boundedFactorGridWindow b (i + 1) (u + 1 + (w + 3) - 1)) := by
          refine mul_le_mul_of_nonneg_left hpair ?_
          exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hCP_nn u))
            (mul_nonneg hfr_nn (mul_nonneg hfr_nn (hCR_nn w)))
      _ ≤ ((((u + 1 : ℕ) : ℝ) * CP u) * (fr * (fr * CR w))) *
            (Combinatorics.windowPairCellCount (u + 1) (w + 3) * W) := by
          refine mul_le_mul_of_nonneg_left ?_
            (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hCP_nn u))
              (mul_nonneg hfr_nn (mul_nonneg hfr_nn (hCR_nn w))))
          exact mul_le_mul_of_nonneg_left hmono hcnt_nn
      _ = ((((u + 1 : ℕ) : ℝ) * CP u) * ((fr * (fr * CR w)) *
            Combinatorics.windowPairCellCount (u + 1) (w + 3))) * W := by ring
  refine le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hcell)
    (appCcGdiag_nonneg (E := E) i)) ?_
  rw [← Finset.sum_mul, ← mul_assoc]


end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
