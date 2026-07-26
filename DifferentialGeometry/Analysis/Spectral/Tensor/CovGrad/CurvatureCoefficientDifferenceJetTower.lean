import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricArmCoeffJetTower
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckSectionDifference
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedCovGradLinear
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.InverseMetricRaisedEndomorphismJetBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CometricDoubleTraceField
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RecoveryEndomorphismJetBound
import DifferentialGeometry.Tensor.Multilinear.Basis
import DifferentialGeometry.Tensor.Mixed.Field
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqSmoothCcUniformBound
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.FiberNormSubadditivity
import DifferentialGeometry.Analysis.Sobolev.GagliardoNirenbergLpFiberNorm
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderHigherOrderTame
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifferenceJetTower
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RaisedKoszulCovariantJetTower
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RaisedKoszulParallelRaiseJetBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifferenceArmRfnsBound
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciConnDiffPalatini
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.AppCcDropIteratedGrid
import DifferentialGeometry.Analysis.Sobolev.BoundedFactorProductGrid
import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.Fin.Tuple.NatAntidiagonal

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization (gFibreOpBound ccTensorBilinSymm ccTensorBilin ccTensorBilin_apply ccTensorModel ccTensorMultilinear ccTensorBilinSymm_contMDiff ccTensorBilinSymm_apply ccTensorBilinSymm_symm)
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

set_option backward.isDefEq.respectTransparency false in
def ricEndoRaisedField (g : SmoothRiemannianMetric I M) :
    ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x) where
  toFun := fun x : M => ricEndoRaisedFib (I := I) g x
  contMDiff_toFun := ricEndoRaisedFib_contMDiff (I := I) g

set_option backward.isDefEq.respectTransparency false in
def ricEndoBackgroundDifferenceField (g₀ g₁ : SmoothRiemannianMetric I M) :
    ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x) :=
  ricEndoRaisedField (I := I) (M := M) g₁ - ricEndoRaisedField (I := I) (M := M) g₀

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
lemma ricEndoBackgroundDifferenceField_apply (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁ x =
      ricEndoRaisedFib (I := I) g₁ x - ricEndoRaisedFib (I := I) g₀ x := by
  rw [ricEndoBackgroundDifferenceField]
  rw [show ((ricEndoRaisedField (I := I) (M := M) g₁ -
        ricEndoRaisedField (I := I) (M := M) g₀) x) =
      ricEndoRaisedField (I := I) (M := M) g₁ x -
        ricEndoRaisedField (I := I) (M := M) g₀ x from by
    rw [ContMDiffSection.coe_sub]; rfl]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
private lemma curvCoeffSlot_zero_backgroundDifference_eq
    (g₀ g₁ : SmoothRiemannianMetric I M) :
    ricciArmOrder0CurvCoeffSlot (I := I) (M := M) g₀ g₁ 0 -
        ricciArmOrder0CurvCoeffSlot (I := I) (M := M) g₀ g₀ 0 =
      slotInsertEndoCc (I := I) (M := M) g₀ 1
        (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((ricciArmOrder0CurvCoeffSlot (I := I) (M := M) g₀ g₁ 0 -
        ricciArmOrder0CurvCoeffSlot (I := I) (M := M) g₀ g₀ 0).toSection x) =
      (ricciArmOrder0CurvCoeffSlot (I := I) (M := M) g₀ g₁ 0).toSection x -
        (ricciArmOrder0CurvCoeffSlot (I := I) (M := M) g₀ g₀ 0).toSection x from by
    rw [SmoothCcTensor.toSection_sub]; rfl]
  apply ContinuousLinearMap.ext
  intro D
  rw [ContinuousLinearMap.sub_apply]
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  simp only [Tensor0SSpace.toModel_sub, ContinuousMultilinearMap.sub_apply]
  rw [show ((ricciArmOrder0CurvCoeffSlot (I := I) (M := M) g₀ g₁ 0).toSection x) D =
      ricciArmOrder0CurvCoeffFibSlot (I := I) g₁ 0 x D from rfl]
  rw [show ((ricciArmOrder0CurvCoeffSlot (I := I) (M := M) g₀ g₀ 0).toSection x) D =
      ricciArmOrder0CurvCoeffFibSlot (I := I) g₀ 0 x D from rfl]
  rw [ricciArmOrder0CurvCoeffFibSlot_toModel, ricciArmOrder0CurvCoeffFibSlot_toModel]
  rw [show ((slotInsertEndoCc (I := I) (M := M) g₀ 1
        (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁)).toSection x) D =
      slotInsertEndoFib (I := I) (M := M) 2 0 x
        (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁ x) D from rfl]
  rw [slotInsertEndoFib_apply_eval]
  rw [ricEndoBackgroundDifferenceField_apply (I := I) (M := M) g₀ g₁ x]
  rw [ContinuousLinearMap.sub_apply, ContinuousMultilinearMap.map_update_sub]

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
private lemma curvCoeffSlot_one_backgroundDifference_eq
    (g₀ g₁ : SmoothRiemannianMetric I M) :
    ricciArmOrder0CurvCoeffSlot (I := I) (M := M) g₀ g₁ 1 -
        ricciArmOrder0CurvCoeffSlot (I := I) (M := M) g₀ g₀ 1 =
      reindexCoeffGen (I := I) (M := M) g₀ 2 2
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
          (slotInsertEndoCc (I := I) (M := M) g₀ 1
            (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁)))
        (Equiv.swap (0 : Fin 2) 1) := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((ricciArmOrder0CurvCoeffSlot (I := I) (M := M) g₀ g₁ 1 -
        ricciArmOrder0CurvCoeffSlot (I := I) (M := M) g₀ g₀ 1).toSection x) =
      (ricciArmOrder0CurvCoeffSlot (I := I) (M := M) g₀ g₁ 1).toSection x -
        (ricciArmOrder0CurvCoeffSlot (I := I) (M := M) g₀ g₀ 1).toSection x from by
    rw [SmoothCcTensor.toSection_sub]; rfl]
  apply ContinuousLinearMap.ext
  intro D
  rw [ContinuousLinearMap.sub_apply]
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  simp only [Tensor0SSpace.toModel_sub, ContinuousMultilinearMap.sub_apply]
  rw [show ((ricciArmOrder0CurvCoeffSlot (I := I) (M := M) g₀ g₁ 1).toSection x) D =
      ricciArmOrder0CurvCoeffFibSlot (I := I) g₁ 1 x D from rfl]
  rw [show ((ricciArmOrder0CurvCoeffSlot (I := I) (M := M) g₀ g₀ 1).toSection x) D =
      ricciArmOrder0CurvCoeffFibSlot (I := I) g₀ 1 x D from rfl]
  rw [ricciArmOrder0CurvCoeffFibSlot_toModel, ricciArmOrder0CurvCoeffFibSlot_toModel]
  rw [show ((reindexCoeffGen (I := I) (M := M) g₀ 2 2
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
          (slotInsertEndoCc (I := I) (M := M) g₀ 1
            (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁)))
        (Equiv.swap (0 : Fin 2) 1)).toSection x) D =
      reindexCoeffFibGen (I := I) 2 2 (Equiv.swap (0 : Fin 2) 1) x
        (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
            (slotInsertEndoCc (I := I) (M := M) g₀ 1
              (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁))).toSection x) D
      from rfl]
  rw [reindexCoeffFibGen_apply]
  rw [rsDomDomCongrSection_toSection, toModel_rsDomDomCongr_apply,
    ContinuousMultilinearMap.domDomCongr_apply, slotInsertEndoCc_toSection,
    slotInsertEndoFib_apply_eval, Tensor0SSpace.toModel_ofModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  rw [show (fun i : Fin 2 =>
        Function.update (fun i : Fin 2 => m ((Equiv.swap (0 : Fin 2) 1) i)) 0
          ((ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁ x)
            (m ((Equiv.swap (0 : Fin 2) 1) 0))) ((Equiv.swap (0 : Fin 2) 1) i)) =
      Function.update m 1
        ((ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁ x) (m 1)) from by
    funext j
    fin_cases j <;>
      simp [Function.update]]
  rw [ricEndoBackgroundDifferenceField_apply (I := I) (M := M) g₀ g₁ x]
  rw [ContinuousLinearMap.sub_apply, ContinuousMultilinearMap.map_update_sub]

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
theorem ricciArmOrder0CurvCoeff_backgroundDifference_decomp
    (g₀ g₁ : SmoothRiemannianMetric I M) :
    ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
        ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀ =
      slotInsertEndoCc (I := I) (M := M) g₀ 1
          (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁) +
        reindexCoeffGen (I := I) (M := M) g₀ 2 2
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
            (slotInsertEndoCc (I := I) (M := M) g₀ 1
              (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁)))
          (Equiv.swap (0 : Fin 2) 1) := by
  rw [← curvCoeffSlot_one_backgroundDifference_eq (I := I) (M := M) g₀ g₁,
    ← curvCoeffSlot_zero_backgroundDifference_eq (I := I) (M := M) g₀ g₁,
    ricciArmOrder0CurvCoeff, ricciArmOrder0CurvCoeff]
  abel

set_option linter.unusedVariables false in
private theorem curvDiffGrid_productTerm_integral_le
    (g₀ : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2)
    {R : ℝ} (hR : 0 ≤ R)
    (i : ℕ) (hi1 : 1 ≤ i)
    {Λ : ℝ} (hΛ_nn : 0 ≤ Λ)
    (hΛsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (P.toSection x) ≤ Λ ^ 2)
    (hNi : ‖iteratedCovGrad (I := I) g₀ 0 2 i P‖ ≤ R)
    {C : ℝ} (hC_nn : 0 ≤ C)
    (hGNP : ∀ j : ℕ, 0 < j → j < i →
      (∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
              ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) ^ ((i : ℝ) / (j : ℝ))
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ^ ((j : ℝ) / (i : ℝ)) ≤
        C * Λ ^ (2 * (1 - (j : ℝ) / (i : ℝ))) * R ^ (2 * (j : ℝ) / (i : ℝ)))
    (n : ℕ) (hn_le : n ≤ i) (e : Fin n → ℕ) (he : ∑ m, e m = i) :
    MeasureTheory.Integrable
        (fun x => ∏ m : Fin n,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
        (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
      (∫ x, ∏ m : Fin n,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
        (i : ℝ) * (max Λ (max R (max C 1))) ^ (7 * i) := by
  classical
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g₀
  set μ : MeasureTheory.Measure M := riemannianVolumeMeasure (I := I) (M := M) g₀ with hμ
  haveI : IsFiniteMeasure μ := by rw [hμ]; infer_instance
  have hi_pos : 0 < i := hi1
  have hiR_pos : (0 : ℝ) < (i : ℝ) := by exact_mod_cast hi_pos
  have hiR_ne : (i : ℝ) ≠ 0 := ne_of_gt hiR_pos
  have hnn : ∀ (j : ℕ) (x : M),
      0 ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x) :=
    fun j x => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + j) x _
  have hcont : ∀ j : ℕ, Continuous (fun x => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
      ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) := by
    intro j
    have hc := Integral.L2.SmoothCcTensor.continuous_inner_self (I := I) (M := M)
      (iteratedCovGrad (I := I) g₀ 0 2 j P)
    refine hc.congr (fun x => ?_)
    rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x),
      ← Integral.L2.SmoothCcTensor.toFun_apply (I := I) (M := M)
        (iteratedCovGrad (I := I) g₀ 0 2 j P) x]
  have hint : ∀ j : ℕ, MeasureTheory.Integrable
      (fun x => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) μ := by
    intro j
    rw [hμ]
    exact integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 0 (2 + j)
      (iteratedCovGrad (I := I) g₀ 0 2 j P)
  have hint_rpow : ∀ (j : ℕ) (p : ℝ), 0 ≤ p → MeasureTheory.Integrable
      (fun x => (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) ^ p) μ := by
    intro j p hp
    have hcp : Continuous (fun x => (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) ^ p) :=
      (hcont j).rpow_const (fun x => Or.inr hp)
    exact hcp.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hint_prod : MeasureTheory.Integrable
      (fun x => ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) μ := by
    have hcp : Continuous (fun x => ∏ m : Fin n,
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) :=
      continuous_finset_prod Finset.univ (fun m _ => hcont (e m))
    exact hcp.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  refine ⟨hint_prod, ?_⟩
  set Mbar : ℝ := max Λ (max R (max C 1)) with hMbar
  have hMbar1 : (1 : ℝ) ≤ Mbar :=
    le_trans (le_max_right C 1) (le_trans (le_max_right R _) (le_max_right Λ _))
  have hMbar_nn : 0 ≤ Mbar := le_trans zero_le_one hMbar1
  have hΛ_le : Λ ≤ Mbar := le_max_left _ _
  have hR_le : R ≤ Mbar := le_trans (le_max_left R _) (le_max_right Λ _)
  have hC_le : C ≤ Mbar :=
    le_trans (le_trans (le_max_left C 1) (le_max_right R _)) (le_max_right Λ _)
  set Sset : Finset (Fin n) := Finset.univ.filter (fun m => 0 < e m) with hSset
  set Zset : Finset (Fin n) := Finset.univ.filter (fun m => ¬ (0 < e m)) with hZset
  have hsplit : ∀ x : M,
      (∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) =
        (∏ m ∈ Sset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) *
          (∏ m ∈ Zset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) := by
    intro x
    rw [hSset, hZset]
    exact (Finset.prod_filter_mul_prod_filter_not Finset.univ (fun m => 0 < e m)
      (fun m => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))).symm
  have hZbound : ∀ x : M,
      (∏ m ∈ Zset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ≤ Λ ^ (2 * Zset.card) := by
    intro x
    calc (∏ m ∈ Zset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
        ≤ ∏ _m ∈ Zset, Λ ^ 2 := by
          apply Finset.prod_le_prod (fun m _ => hnn (e m) x)
          intro m hm
          have hem0 : e m = 0 := by have := (Finset.mem_filter.mp hm).2; omega
          rw [hem0]; exact hΛsup x
      _ = Λ ^ (2 * Zset.card) := by rw [Finset.prod_const, ← pow_mul]
  have hZsum0 : ∑ m ∈ Zset, e m = 0 := by
    apply Finset.sum_eq_zero
    intro m hm
    have := (Finset.mem_filter.mp hm).2; omega
  have hSsum : ∑ m ∈ Sset, e m = i := by
    have h := Finset.sum_filter_add_sum_filter_not Finset.univ (fun m => 0 < e m) e
    rw [← hSset, ← hZset, hZsum0, add_zero, he] at h
    exact h
  have hScard_pos : 1 ≤ Sset.card := by
    rcases Nat.eq_zero_or_pos Sset.card with h0 | hp
    · exfalso
      rw [Finset.card_eq_zero] at h0
      rw [h0, Finset.sum_empty] at hSsum
      omega
    · exact hp
  rcases Nat.lt_or_ge Sset.card 2 with hScard_lt2 | hScard_ge2
  · have hScard1 : Sset.card = 1 := by omega
    obtain ⟨m₀, hm₀⟩ := Finset.card_eq_one.mp hScard1
    have hem₀ : e m₀ = i := by
      have hss : ∑ m ∈ Sset, e m = e m₀ := by rw [hm₀, Finset.sum_singleton]
      rw [hss] at hSsum; exact hSsum
    have hSprod : ∀ x : M,
        (∏ m ∈ Sset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) =
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection x) := by
      intro x; rw [hm₀, Finset.prod_singleton, hem₀]
    have hpt : ∀ x : M,
        (∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ≤
          Λ ^ (2 * Zset.card) * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection x) := by
      intro x
      rw [hsplit x, hSprod x]
      calc (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
              ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection x)) *
            (∏ m ∈ Zset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
          ≤ (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
              ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection x)) * Λ ^ (2 * Zset.card) :=
            mul_le_mul_of_nonneg_left (hZbound x) (hnn i x)
        _ = Λ ^ (2 * Zset.card) * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
              ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection x) := mul_comm _ _
    have hintFi : (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection x) ∂μ) ≤ R ^ 2 := by
      have heq : (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection x) ∂μ) =
          ‖iteratedCovGrad (I := I) g₀ 0 2 i P‖ ^ 2 := by
        rw [SmoothCcTensor.norm_def (iteratedCovGrad (I := I) g₀ 0 2 i P), hμ]
        exact (tensorL2Norm_sq_eq_integral_riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i)
          ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection)).symm
      rw [heq]
      nlinarith [hNi, norm_nonneg (iteratedCovGrad (I := I) g₀ 0 2 i P), hR]
    have hΛZ_nn : 0 ≤ Λ ^ (2 * Zset.card) := pow_nonneg hΛ_nn _
    calc (∫ x, ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x) ∂μ)
        ≤ ∫ x, Λ ^ (2 * Zset.card) * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection x) ∂μ :=
          MeasureTheory.integral_mono hint_prod ((hint i).const_mul _) hpt
      _ = Λ ^ (2 * Zset.card) * ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection x) ∂μ :=
          MeasureTheory.integral_const_mul _ _
      _ ≤ Λ ^ (2 * Zset.card) * R ^ 2 := mul_le_mul_of_nonneg_left hintFi hΛZ_nn
      _ ≤ (i : ℝ) * Mbar ^ (7 * i) := by
          have hZle : Zset.card ≤ i := le_trans (Finset.card_le_univ _) (by simpa using hn_le)
          have e1 : Λ ^ (2 * Zset.card) ≤ Mbar ^ (2 * i) :=
            le_trans (pow_le_pow_left₀ hΛ_nn hΛ_le _)
              (pow_le_pow_right₀ hMbar1 (by omega))
          have e2 : R ^ 2 ≤ Mbar ^ 2 := pow_le_pow_left₀ hR hR_le 2
          have e3 : Mbar ^ (2 * i) * Mbar ^ 2 ≤ Mbar ^ (7 * i) := by
            rw [← pow_add]
            exact pow_le_pow_right₀ hMbar1 (by omega)
          have e4 : Λ ^ (2 * Zset.card) * R ^ 2 ≤ Mbar ^ (2 * i) * Mbar ^ 2 :=
            mul_le_mul e1 e2 (by positivity) (by positivity)
          have e5 : Mbar ^ (7 * i) ≤ (i : ℝ) * Mbar ^ (7 * i) := by
            have : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi1
            nlinarith [pow_nonneg hMbar_nn (7 * i)]
          calc Λ ^ (2 * Zset.card) * R ^ 2 ≤ Mbar ^ (2 * i) * Mbar ^ 2 := e4
            _ ≤ Mbar ^ (7 * i) := e3
            _ ≤ (i : ℝ) * Mbar ^ (7 * i) := e5
  · have hem_lt : ∀ m ∈ Sset, e m < i := by
      intro m hm
      have hmpos : 0 < e m := (Finset.mem_filter.mp hm).2
      have hadd : e m + ∑ m' ∈ Sset.erase m, e m' = ∑ m' ∈ Sset, e m' :=
        Finset.add_sum_erase Sset e hm
      rw [hSsum] at hadd
      have herase_ne : (Sset.erase m).Nonempty := by
        rw [← Finset.card_pos, Finset.card_erase_of_mem hm]; omega
      obtain ⟨m', hm'⟩ := herase_ne
      have hm'S : m' ∈ Sset := Finset.mem_of_mem_erase hm'
      have hm'pos : 1 ≤ e m' := (Finset.mem_filter.mp hm'S).2
      have hle : e m' ≤ ∑ m'' ∈ Sset.erase m, e m'' :=
        Finset.single_le_sum (fun k _ => Nat.zero_le _) hm'
      omega
    have hAMGM : ∀ x : M,
        (∏ m ∈ Sset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ≤
          ∑ m ∈ Sset, ((e m : ℝ) / i) *
            (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) := by
      intro x
      have hw_nn : ∀ m ∈ Sset, 0 ≤ (e m : ℝ) / i := fun m _ => by positivity
      have hw_sum : ∑ m ∈ Sset, (e m : ℝ) / i = 1 := by
        rw [← Finset.sum_div]
        rw [show (∑ m ∈ Sset, (e m : ℝ)) = ((i : ℕ) : ℝ) from by
          rw [← Nat.cast_sum]; exact_mod_cast hSsum]
        exact div_self hiR_ne
      have hz_nn : ∀ m ∈ Sset, 0 ≤ (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) :=
        fun m _ => Real.rpow_nonneg (hnn (e m) x) _
      have hAM := Real.geom_mean_le_arith_mean_weighted Sset (fun m => (e m : ℝ) / i)
        (fun m => (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)))
        hw_nn hw_sum hz_nn
      have hLHS : (∏ m ∈ Sset, ((riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)))
            ^ ((e m : ℝ) / i)) =
          ∏ m ∈ Sset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x) := by
        apply Finset.prod_congr rfl
        intro m hm
        have hmpos : 0 < e m := (Finset.mem_filter.mp hm).2
        have hemR_ne : (e m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hmpos.ne'
        rw [← Real.rpow_mul (hnn (e m) x)]
        rw [show ((i : ℝ) / (e m : ℝ)) * ((e m : ℝ) / i) = 1 by field_simp]
        rw [Real.rpow_one]
      rw [hLHS] at hAM
      exact hAM
    have hfactor : ∀ m ∈ Sset,
        (∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ) ≤
          Mbar ^ (5 * i) := by
      intro m hm
      have hmpos : 0 < e m := (Finset.mem_filter.mp hm).2
      have hem_lt_i : e m < i := hem_lt m hm
      have hemR_pos : (0 : ℝ) < (e m : ℝ) := by exact_mod_cast hmpos
      have hemR_ne : (e m : ℝ) ≠ 0 := ne_of_gt hemR_pos
      have hgn := hGNP (e m) hmpos hem_lt_i
      set Ival : ℝ := ∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ
        with hIval
      have hIval_nn : 0 ≤ Ival := by
        rw [hIval]; exact integral_nonneg (fun x => Real.rpow_nonneg (hnn (e m) x) _)
      have hθ_nn : 0 ≤ (e m : ℝ) / i := by positivity
      have hθ_le1 : (e m : ℝ) / i ≤ 1 := by
        rw [div_le_one hiR_pos]; exact_mod_cast Nat.le_of_lt hem_lt_i
      have hexp1_nn : 0 ≤ 2 * (1 - (e m : ℝ) / i) := by nlinarith
      have hexp1_le : 2 * (1 - (e m : ℝ) / i) ≤ 2 := by nlinarith
      have hexp2_nn : 0 ≤ 2 * (e m : ℝ) / i := by positivity
      have hexp2_le : 2 * (e m : ℝ) / i ≤ 2 := by
        rw [mul_div_assoc]; nlinarith
      have hΛpow : Λ ^ (2 * (1 - (e m : ℝ) / i)) ≤ Mbar ^ (2 : ℕ) := by
        calc Λ ^ (2 * (1 - (e m : ℝ) / i)) ≤ Mbar ^ (2 * (1 - (e m : ℝ) / i)) :=
              Real.rpow_le_rpow hΛ_nn hΛ_le hexp1_nn
          _ ≤ Mbar ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hMbar1 hexp1_le
          _ = Mbar ^ (2 : ℕ) := by rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      have hRpow : R ^ (2 * (e m : ℝ) / i) ≤ Mbar ^ (2 : ℕ) := by
        calc R ^ (2 * (e m : ℝ) / i) ≤ Mbar ^ (2 * (e m : ℝ) / i) :=
              Real.rpow_le_rpow hR hR_le hexp2_nn
          _ ≤ Mbar ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hMbar1 hexp2_le
          _ = Mbar ^ (2 : ℕ) := by rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      have hbase_le : C * Λ ^ (2 * (1 - (e m : ℝ) / i)) * R ^ (2 * (e m : ℝ) / i) ≤
          Mbar ^ (5 : ℕ) := by
        have h1 : C * Λ ^ (2 * (1 - (e m : ℝ) / i)) ≤ Mbar * Mbar ^ (2 : ℕ) :=
          mul_le_mul hC_le hΛpow (Real.rpow_nonneg hΛ_nn _) hMbar_nn
        have h2 : C * Λ ^ (2 * (1 - (e m : ℝ) / i)) * R ^ (2 * (e m : ℝ) / i) ≤
            Mbar * Mbar ^ (2 : ℕ) * Mbar ^ (2 : ℕ) :=
          mul_le_mul h1 hRpow (Real.rpow_nonneg hR _) (by positivity)
        calc C * Λ ^ (2 * (1 - (e m : ℝ) / i)) * R ^ (2 * (e m : ℝ) / i)
            ≤ Mbar * Mbar ^ (2 : ℕ) * Mbar ^ (2 : ℕ) := h2
          _ = Mbar ^ (5 : ℕ) := by ring
      have hbase_nn : 0 ≤ C * Λ ^ (2 * (1 - (e m : ℝ) / i)) * R ^ (2 * (e m : ℝ) / i) := by
        apply mul_nonneg (mul_nonneg hC_nn (Real.rpow_nonneg hΛ_nn _)) (Real.rpow_nonneg hR _)
      have hIval_eq : Ival = (Ival ^ ((e m : ℝ) / i)) ^ ((i : ℝ) / (e m : ℝ)) := by
        rw [← Real.rpow_mul hIval_nn]
        rw [show ((e m : ℝ) / i) * ((i : ℝ) / (e m : ℝ)) = 1 by field_simp]
        rw [Real.rpow_one]
      have hM5_one : (1 : ℝ) ≤ Mbar ^ (5 : ℕ) :=
        le_trans hMbar1 (le_self_pow₀ hMbar1 (by norm_num))
      have hidiv : (i : ℝ) / (e m : ℝ) ≤ (i : ℝ) :=
        div_le_self hiR_pos.le (by exact_mod_cast hmpos)
      calc Ival = (Ival ^ ((e m : ℝ) / i)) ^ ((i : ℝ) / (e m : ℝ)) := hIval_eq
        _ ≤ (C * Λ ^ (2 * (1 - (e m : ℝ) / i)) * R ^ (2 * (e m : ℝ) / i)) ^ ((i : ℝ) / (e m : ℝ)) :=
            Real.rpow_le_rpow (Real.rpow_nonneg hIval_nn _) hgn (by positivity)
        _ ≤ (Mbar ^ (5 : ℕ)) ^ ((i : ℝ) / (e m : ℝ)) :=
            Real.rpow_le_rpow hbase_nn hbase_le (by positivity)
        _ ≤ (Mbar ^ (5 : ℕ)) ^ ((i : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_le hM5_one hidiv
        _ = (Mbar ^ (5 : ℕ)) ^ (i : ℕ) := by rw [Real.rpow_natCast]
        _ = Mbar ^ (5 * i) := by rw [← pow_mul]
    have hSsum_factor : ∑ m ∈ Sset, ((e m : ℝ) / i) *
        (∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ) ≤
        Mbar ^ (5 * i) := by
      have hw_nn : ∀ m ∈ Sset, 0 ≤ (e m : ℝ) / i := fun m _ => by positivity
      have hw_sum : ∑ m ∈ Sset, (e m : ℝ) / i = 1 := by
        rw [← Finset.sum_div]
        rw [show (∑ m ∈ Sset, (e m : ℝ)) = ((i : ℕ) : ℝ) from by
          rw [← Nat.cast_sum]; exact_mod_cast hSsum]
        exact div_self hiR_ne
      calc ∑ m ∈ Sset, ((e m : ℝ) / i) *
            (∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ)
          ≤ ∑ m ∈ Sset, ((e m : ℝ) / i) * Mbar ^ (5 * i) := by
            apply Finset.sum_le_sum
            intro m hm
            exact mul_le_mul_of_nonneg_left (hfactor m hm) (hw_nn m hm)
        _ = (∑ m ∈ Sset, (e m : ℝ) / i) * Mbar ^ (5 * i) := by rw [Finset.sum_mul]
        _ = Mbar ^ (5 * i) := by rw [hw_sum, one_mul]
    have hpt2 : ∀ x : M,
        (∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ≤
          Λ ^ (2 * Zset.card) * ∑ m ∈ Sset, ((e m : ℝ) / i) *
            (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) := by
      intro x
      rw [hsplit x]
      have hZnn : 0 ≤ ∏ m ∈ Zset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x) :=
        Finset.prod_nonneg (fun m _ => hnn (e m) x)
      have hsum_nn : 0 ≤ ∑ m ∈ Sset, ((e m : ℝ) / i) *
          (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) :=
        Finset.sum_nonneg (fun m _ => mul_nonneg (by positivity) (Real.rpow_nonneg (hnn (e m) x) _))
      calc (∏ m ∈ Sset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) *
            (∏ m ∈ Zset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
          ≤ (∑ m ∈ Sset, ((e m : ℝ) / i) *
              (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ))) *
              Λ ^ (2 * Zset.card) :=
            mul_le_mul (hAMGM x) (hZbound x) hZnn hsum_nn
        _ = Λ ^ (2 * Zset.card) * ∑ m ∈ Sset, ((e m : ℝ) / i) *
              (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) :=
            mul_comm _ _
    have hsum_int : MeasureTheory.Integrable
        (fun x => ∑ m ∈ Sset, ((e m : ℝ) / i) *
          (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ))) μ := by
      apply MeasureTheory.integrable_finset_sum
      intro m _
      exact (hint_rpow (e m) ((i : ℝ) / (e m : ℝ)) (by positivity)).const_mul _
    have hint_eq : (∫ x, ∑ m ∈ Sset, ((e m : ℝ) / i) *
          (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ) =
        ∑ m ∈ Sset, ((e m : ℝ) / i) *
          (∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ) := by
      rw [MeasureTheory.integral_finset_sum]
      · apply Finset.sum_congr rfl
        intro m _; rw [MeasureTheory.integral_const_mul]
      · intro m _
        exact (hint_rpow (e m) ((i : ℝ) / (e m : ℝ)) (by positivity)).const_mul _
    have hΛZ_nn : 0 ≤ Λ ^ (2 * Zset.card) := pow_nonneg hΛ_nn _
    calc (∫ x, ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x) ∂μ)
        ≤ ∫ x, Λ ^ (2 * Zset.card) * ∑ m ∈ Sset, ((e m : ℝ) / i) *
            (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ :=
          MeasureTheory.integral_mono hint_prod (hsum_int.const_mul _) hpt2
      _ = Λ ^ (2 * Zset.card) * ∫ x, ∑ m ∈ Sset, ((e m : ℝ) / i) *
            (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ :=
          MeasureTheory.integral_const_mul _ _
      _ ≤ Λ ^ (2 * Zset.card) * Mbar ^ (5 * i) := by
          rw [hint_eq]
          exact mul_le_mul_of_nonneg_left hSsum_factor hΛZ_nn
      _ ≤ (i : ℝ) * Mbar ^ (7 * i) := by
          have hZle : Zset.card ≤ i := le_trans (Finset.card_le_univ _) (by simpa using hn_le)
          have e1 : Λ ^ (2 * Zset.card) ≤ Mbar ^ (2 * i) :=
            le_trans (pow_le_pow_left₀ hΛ_nn hΛ_le _) (pow_le_pow_right₀ hMbar1 (by omega))
          have e3 : Mbar ^ (2 * i) * Mbar ^ (5 * i) = Mbar ^ (7 * i) := by
            rw [← pow_add]; congr 1; ring
          have e4 : Λ ^ (2 * Zset.card) * Mbar ^ (5 * i) ≤ Mbar ^ (2 * i) * Mbar ^ (5 * i) :=
            mul_le_mul_of_nonneg_right e1 (by positivity)
          have e5 : Mbar ^ (7 * i) ≤ (i : ℝ) * Mbar ^ (7 * i) := by
            have : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi1
            nlinarith [pow_nonneg hMbar_nn (7 * i)]
          calc Λ ^ (2 * Zset.card) * Mbar ^ (5 * i) ≤ Mbar ^ (2 * i) * Mbar ^ (5 * i) := e4
            _ = Mbar ^ (7 * i) := e3
            _ ≤ (i : ℝ) * Mbar ^ (7 * i) := e5

set_option linter.unusedVariables false in
private theorem curvDiffGrid_integral_ballUniform_window
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (P : SmoothCcTensor g₀ 0 2),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a + 2 →
          MeasureTheory.Integrable
              (fun x => ∑ n ∈ Finset.range (i + 1),
                ∑ e ∈ Finset.Nat.antidiagonalTuple n i,
                  ∏ m : Fin n,
                    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                      ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
              (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
            (∫ x, ∑ n ∈ Finset.range (i + 1),
                  ∑ e ∈ Finset.Nat.antidiagonalTuple n i,
                    ∏ m : Fin n,
                      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                        ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)
                ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤ K i := by
  classical
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g₀
  obtain ⟨Cemb, hCemb_nn, hCemb⟩ :=
    DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.deTurckSmoothRemainderDiff_supercritical_pointwise_jet_le_fixedWindow
      (I := I) (M := M) g₀ a ha_super
  set Lam : ℝ := Cemb * Real.sqrt ((a + 1 + 1 : ℕ) : ℝ) * R with hLam
  have hLam_nn : 0 ≤ Lam := by rw [hLam]; positivity
  set Cgn : ℕ → ℝ := fun k =>
    if h : 1 ≤ k then
      (DifferentialGeometry.Analysis.Sobolev.Tensor.exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
        (I := I) (M := M) g₀ 0 2 k h).choose
    else 0 with hCgn
  have hCgn_nn : ∀ k, 0 ≤ Cgn k := by
    intro k
    simp only [hCgn]
    split_ifs with h
    · exact (DifferentialGeometry.Analysis.Sobolev.Tensor.exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
        (I := I) (M := M) g₀ 0 2 k h).choose_spec.1
    · exact le_refl 0
  set Gfun : ℕ → ℝ := fun k => (k : ℝ) * (max Lam (max R (max (Cgn k) 1))) ^ (7 * k) with hGfun
  have hGfun_nn : ∀ k, 0 ≤ Gfun k := by
    intro k
    rw [hGfun]
    apply mul_nonneg (Nat.cast_nonneg k)
    apply pow_nonneg
    exact le_trans zero_le_one
      (le_trans (le_max_right (Cgn k) 1) (le_trans (le_max_right R _) (le_max_right Lam _)))
  set vol : ℝ := ((riemannianVolumeMeasure (I := I) (M := M) g₀) Set.univ).toReal with hvol
  have hvol_nn : 0 ≤ vol := ENNReal.toReal_nonneg
  refine ⟨fun k => (∑ n ∈ Finset.range (k + 1),
      ((Finset.Nat.antidiagonalTuple n k).card : ℝ)) * Gfun k + vol, ?_, ?_⟩
  · intro k
    exact add_nonneg
      (mul_nonneg (Finset.sum_nonneg (fun n _ => Nat.cast_nonneg _)) (hGfun_nn k)) hvol_nn
  · intro P hPball i hi
    by_cases hi0 : i = 0
    · subst hi0
      have hgrid0 : (fun x => ∑ n ∈ Finset.range (0 + 1),
          ∑ e ∈ Finset.Nat.antidiagonalTuple n 0, ∏ m : Fin n,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) = (fun _ : M => (1 : ℝ)) := by
        funext x
        simp only [Nat.zero_add, Finset.sum_range_one, Finset.Nat.antidiagonalTuple_zero_zero,
          Finset.sum_singleton, Finset.univ_eq_empty, Finset.prod_empty]
      refine ⟨?_, ?_⟩
      · rw [hgrid0]; exact MeasureTheory.integrable_const 1
      · rw [hgrid0, MeasureTheory.integral_const, smul_eq_mul, mul_one,
          MeasureTheory.measureReal_def, ← hvol]
        exact le_add_of_nonneg_left
          (mul_nonneg (Finset.sum_nonneg (fun n _ => Nat.cast_nonneg _)) (hGfun_nn 0))
    · have hi1 : 1 ≤ i := Nat.one_le_iff_ne_zero.mpr hi0
      have hNi : ‖iteratedCovGrad (I := I) g₀ 0 2 i P‖ ≤ R := hPball i (by omega)
      have hΛsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (P.toSection x) ≤
          Lam ^ 2 := by
        intro x
        have hsum_le : ∑ j ∈ Finset.range (a + 1 + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 ≤ ((a + 1 + 1 : ℕ) : ℝ) * R ^ 2 := by
          calc ∑ j ∈ Finset.range (a + 1 + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2
              ≤ ∑ j ∈ Finset.range (a + 1 + 1), R ^ 2 := by
                apply Finset.sum_le_sum
                intro j hj
                have hjle : j ≤ a + 2 := by have := Finset.mem_range.mp hj; omega
                nlinarith [norm_nonneg (iteratedCovGrad (I := I) g₀ 0 2 j P), hPball j hjle, hR]
            _ = ((a + 1 + 1 : ℕ) : ℝ) * R ^ 2 := by
                rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        have hsingle : riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (P.toSection x) ≤
            ∑ m ∈ Finset.range 3, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 m P).toSection x) := by
          have h0mem : (0 : ℕ) ∈ Finset.range 3 := by norm_num
          have hsl := Finset.single_le_sum
            (f := fun m => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 m P).toSection x))
            (fun m _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + m) x _) h0mem
          simpa using hsl
        have hLam2 : Lam ^ 2 = Cemb ^ 2 * ((a + 1 + 1 : ℕ) : ℝ) * R ^ 2 := by
          rw [hLam, mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
        have hchain : ∑ m ∈ Finset.range 3, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 m P).toSection x) ≤ Lam ^ 2 := by
          refine le_trans (hCemb P x) ?_
          rw [hLam2]
          calc Cemb ^ 2 * ∑ j ∈ Finset.range (a + 1 + 1),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2
              ≤ Cemb ^ 2 * (((a + 1 + 1 : ℕ) : ℝ) * R ^ 2) :=
                mul_le_mul_of_nonneg_left hsum_le (by positivity)
            _ = Cemb ^ 2 * ((a + 1 + 1 : ℕ) : ℝ) * R ^ 2 := by ring
        exact le_trans hsingle hchain
      have hGNspec := (DifferentialGeometry.Analysis.Sobolev.Tensor.exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
        (I := I) (M := M) g₀ 0 2 i hi1).choose_spec.2
      have hGNP : ∀ j : ℕ, 0 < j → j < i →
          (∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) ^ ((i : ℝ) / (j : ℝ))
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ^ ((j : ℝ) / (i : ℝ)) ≤
            Cgn i * Lam ^ (2 * (1 - (j : ℝ) / (i : ℝ))) * R ^ (2 * (j : ℝ) / (i : ℝ)) := by
        intro j hj0 hji
        have hb := hGNspec P Lam hLam_nn hΛsup j hj0 hji
        have hchoose : (DifferentialGeometry.Analysis.Sobolev.Tensor.exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
            (I := I) (M := M) g₀ 0 2 i hi1).choose = Cgn i := by
          rw [hCgn]; simp only [dif_pos hi1]
        rw [hchoose] at hb
        refine le_trans hb ?_
        have hnorm : Integral.L2.tensorL2Norm (I := I) (M := M) g₀ 0 (2 + i)
            (iteratedCovGrad (I := I) g₀ 0 2 i P).toFun = ‖iteratedCovGrad (I := I) g₀ 0 2 i P‖ :=
          (SmoothCcTensor.norm_def (iteratedCovGrad (I := I) g₀ 0 2 i P)).symm
        rw [hnorm]
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (norm_nonneg _) hNi (by positivity))
          (mul_nonneg (hCgn_nn i) (Real.rpow_nonneg hLam_nn _))
      have hPT : ∀ n ∈ Finset.range (i + 1), ∀ e ∈ Finset.Nat.antidiagonalTuple n i,
          MeasureTheory.Integrable (fun x => ∏ m : Fin n,
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
            (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
          (∫ x, ∏ m : Fin n,
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤ Gfun i := by
        intro n hn e he
        have hn_le : n ≤ i := by have := Finset.mem_range.mp hn; omega
        have hsum_e : ∑ m, e m = i := Finset.Nat.mem_antidiagonalTuple.mp he
        have hres := curvDiffGrid_productTerm_integral_le (I := I) (M := M) g₀ P hR i hi1 hLam_nn hΛsup
          hNi (hCgn_nn i) hGNP n hn_le e hsum_e
        simpa only [hGfun] using hres
      have hgrid_int : MeasureTheory.Integrable (fun x => ∑ n ∈ Finset.range (i + 1),
          ∑ e ∈ Finset.Nat.antidiagonalTuple n i, ∏ m : Fin n,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
          (riemannianVolumeMeasure (I := I) (M := M) g₀) := by
        apply MeasureTheory.integrable_finset_sum
        intro n hn
        apply MeasureTheory.integrable_finset_sum
        intro e he
        exact (hPT n hn e he).1
      refine ⟨hgrid_int, ?_⟩
      rw [MeasureTheory.integral_finset_sum _
        (fun n hn => MeasureTheory.integrable_finset_sum _ (fun e he => (hPT n hn e he).1))]
      have hinner : ∀ n ∈ Finset.range (i + 1),
          (∫ x, ∑ e ∈ Finset.Nat.antidiagonalTuple n i, ∏ m : Fin n,
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) =
          ∑ e ∈ Finset.Nat.antidiagonalTuple n i, ∫ x, ∏ m : Fin n,
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀) := by
        intro n hn
        exact MeasureTheory.integral_finset_sum _ (fun e he => (hPT n hn e he).1)
      rw [Finset.sum_congr rfl hinner]
      have hle1 : ∑ n ∈ Finset.range (i + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n i,
            (∫ x, ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
          ∑ n ∈ Finset.range (i + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n i, Gfun i := by
        apply Finset.sum_le_sum; intro n hn
        apply Finset.sum_le_sum; intro e he
        exact (hPT n hn e he).2
      have heq2 : ∑ n ∈ Finset.range (i + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n i, Gfun i =
          (∑ n ∈ Finset.range (i + 1), ((Finset.Nat.antidiagonalTuple n i).card : ℝ)) * Gfun i := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl; intro n _
        rw [Finset.sum_const, nsmul_eq_mul]
      refine le_trans hle1 ?_
      rw [heq2]
      exact le_add_of_nonneg_right hvol_nn

private def tGridCount (j : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (j + 1), ((Finset.Nat.antidiagonalTuple n j).card : ℝ)

private lemma tGridCount_nonneg (j : ℕ) : 0 ≤ tGridCount j :=
  Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)

private lemma prodTerm_le_antidiagonalTupleGrid (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j)
    (k n : ℕ) (hn : n < k + 1) (e : Fin n → ℕ)
    (he : e ∈ Finset.Nat.antidiagonalTuple n k) :
    (∏ m : Fin n, b (e m)) ≤ Combinatorics.antidiagonalTupleGrid b k := by
  rw [Combinatorics.antidiagonalTupleGrid]
  have h1 : (∏ m : Fin n, b (e m)) ≤
      ∑ e' ∈ Finset.Nat.antidiagonalTuple n k, ∏ m : Fin n, b (e' m) :=
    Finset.single_le_sum (f := fun e' : Fin n → ℕ => ∏ m : Fin n, b (e' m))
      (fun e' _ => Finset.prod_nonneg (fun m _ => hb _)) he
  refine le_trans h1 ?_
  exact Finset.single_le_sum
    (f := fun n' : ℕ => ∑ e' ∈ Finset.Nat.antidiagonalTuple n' k, ∏ m : Fin n', b (e' m))
    (fun n' _ => Finset.sum_nonneg (fun e' _ => Finset.prod_nonneg (fun m _ => hb _)))
    (Finset.mem_range.mpr hn)

private lemma antidiagonalTupleGrid_mul_le (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) (j k : ℕ) :
    Combinatorics.antidiagonalTupleGrid b j * Combinatorics.antidiagonalTupleGrid b k ≤
      (tGridCount j * tGridCount k) * Combinatorics.antidiagonalTupleGrid b (j + k) := by
  classical
  have hpair : ∀ n ∈ Finset.range (j + 1), ∀ e ∈ Finset.Nat.antidiagonalTuple n j,
      ∀ n' ∈ Finset.range (k + 1), ∀ e' ∈ Finset.Nat.antidiagonalTuple n' k,
      (∏ m : Fin n, b (e m)) * (∏ m : Fin n', b (e' m)) ≤
        Combinatorics.antidiagonalTupleGrid b (j + k) := by
    intro n hn e he n' hn' e' he'
    have happend : (∏ m : Fin n, b (e m)) * (∏ m : Fin n', b (e' m)) =
        ∏ m : Fin (n + n'), b (Fin.append e e' m) := by
      rw [Fin.prod_univ_add]
      congr 1
      · exact Finset.prod_congr rfl (fun m _ => by rw [Fin.append_left])
      · exact Finset.prod_congr rfl (fun m _ => by rw [Fin.append_right])
    rw [happend]
    have hmem : Fin.append e e' ∈ Finset.Nat.antidiagonalTuple (n + n') (j + k) := by
      rw [Finset.Nat.mem_antidiagonalTuple] at he he' ⊢
      rw [Fin.sum_univ_add]
      have h1 : (∑ m : Fin n, Fin.append e e' (Fin.castAdd n' m)) = j := by
        rw [← he]
        exact Finset.sum_congr rfl (fun m _ => by rw [Fin.append_left])
      have h2 : (∑ m : Fin n', Fin.append e e' (Fin.natAdd n m)) = k := by
        rw [← he']
        exact Finset.sum_congr rfl (fun m _ => by rw [Fin.append_right])
      rw [h1, h2]
    have hnn' : n + n' < j + k + 1 := by
      rw [Finset.mem_range] at hn hn'
      omega
    exact prodTerm_le_antidiagonalTupleGrid b hb (j + k) (n + n') hnn' _ hmem
  calc Combinatorics.antidiagonalTupleGrid b j * Combinatorics.antidiagonalTupleGrid b k
      = ∑ n ∈ Finset.range (j + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n j,
          ((∏ m : Fin n, b (e m)) * Combinatorics.antidiagonalTupleGrid b k) := by
        rw [Combinatorics.antidiagonalTupleGrid, Finset.sum_mul]
        exact Finset.sum_congr rfl (fun n _ => by rw [Finset.sum_mul])
    _ ≤ ∑ n ∈ Finset.range (j + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n j,
          (tGridCount k * Combinatorics.antidiagonalTupleGrid b (j + k)) := by
        refine Finset.sum_le_sum (fun n hn => Finset.sum_le_sum (fun e he => ?_))
        calc (∏ m : Fin n, b (e m)) * Combinatorics.antidiagonalTupleGrid b k
            = ∑ n' ∈ Finset.range (k + 1), ∑ e' ∈ Finset.Nat.antidiagonalTuple n' k,
                ((∏ m : Fin n, b (e m)) * ∏ m : Fin n', b (e' m)) := by
              rw [Combinatorics.antidiagonalTupleGrid, Finset.mul_sum]
              exact Finset.sum_congr rfl (fun n' _ => by rw [Finset.mul_sum])
          _ ≤ ∑ n' ∈ Finset.range (k + 1), ∑ e' ∈ Finset.Nat.antidiagonalTuple n' k,
                Combinatorics.antidiagonalTupleGrid b (j + k) := by
              refine Finset.sum_le_sum (fun n' hn' => Finset.sum_le_sum (fun e' he' => ?_))
              exact hpair n hn e he n' hn' e' he'
          _ = tGridCount k * Combinatorics.antidiagonalTupleGrid b (j + k) := by
              rw [tGridCount, Finset.sum_mul]
              exact Finset.sum_congr rfl (fun n' _ => by
                rw [Finset.sum_const, nsmul_eq_mul])
    _ = ∑ n ∈ Finset.range (j + 1), ((Finset.Nat.antidiagonalTuple n j).card : ℝ) *
          (tGridCount k * Combinatorics.antidiagonalTupleGrid b (j + k)) := by
        exact Finset.sum_congr rfl (fun n _ => by rw [Finset.sum_const, nsmul_eq_mul])
    _ = (tGridCount j * tGridCount k) * Combinatorics.antidiagonalTupleGrid b (j + k) := by
        rw [show (tGridCount j * tGridCount k) * Combinatorics.antidiagonalTupleGrid b (j + k) =
            tGridCount j * (tGridCount k * Combinatorics.antidiagonalTupleGrid b (j + k)) from by
          ring]
        rw [show tGridCount j = ∑ n ∈ Finset.range (j + 1),
            ((Finset.Nat.antidiagonalTuple n j).card : ℝ) from rfl]
        rw [Finset.sum_mul]

private def tWindow (b : ℕ → ℝ) (i : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (i + 3), Combinatorics.antidiagonalTupleGrid b k

private lemma tWindow_nonneg (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) (i : ℕ) : 0 ≤ tWindow b i :=
  Finset.sum_nonneg (fun k _ => Combinatorics.antidiagonalTupleGrid_nonneg b hb k)

private lemma antidiagonalTupleGrid_le_tWindow (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j)
    {k i : ℕ} (hk : k < i + 3) :
    Combinatorics.antidiagonalTupleGrid b k ≤ tWindow b i :=
  Finset.single_le_sum (fun k' _ => Combinatorics.antidiagonalTupleGrid_nonneg b hb k')
    (Finset.mem_range.mpr hk)

private lemma tWindow_mono (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) {i i' : ℕ} (h : i ≤ i') :
    tWindow b i ≤ tWindow b i' := by
  refine Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_subset_range.mpr (show i + 3 ≤ i' + 3 by omega)) ?_
  intro k _ _
  exact Combinatorics.antidiagonalTupleGrid_nonneg b hb k

private lemma one_le_tWindow (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) (i : ℕ) : 1 ≤ tWindow b i := by
  rw [← Combinatorics.antidiagonalTupleGrid_zero b]
  exact antidiagonalTupleGrid_le_tWindow b hb (by omega)

private def tWindowMulConst (j l : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (j + 3), tGridCount k * tGridCount l

private lemma tWindowMulConst_nonneg (j l : ℕ) : 0 ≤ tWindowMulConst j l :=
  Finset.sum_nonneg (fun k _ => mul_nonneg (tGridCount_nonneg k) (tGridCount_nonneg l))

private lemma tWindow_mul_antidiagonalTupleGrid_le (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) (j l : ℕ) :
    tWindow b j * Combinatorics.antidiagonalTupleGrid b l ≤
      tWindowMulConst j l * tWindow b (j + l) := by
  calc tWindow b j * Combinatorics.antidiagonalTupleGrid b l
      = ∑ k ∈ Finset.range (j + 3),
          Combinatorics.antidiagonalTupleGrid b k * Combinatorics.antidiagonalTupleGrid b l := by
        rw [tWindow, Finset.sum_mul]
    _ ≤ ∑ k ∈ Finset.range (j + 3), (tGridCount k * tGridCount l) * tWindow b (j + l) := by
        refine Finset.sum_le_sum (fun k hk => ?_)
        refine le_trans (antidiagonalTupleGrid_mul_le b hb k l) ?_
        refine mul_le_mul_of_nonneg_left ?_
          (mul_nonneg (tGridCount_nonneg k) (tGridCount_nonneg l))
        refine antidiagonalTupleGrid_le_tWindow b hb ?_
        rw [Finset.mem_range] at hk
        omega
    _ = tWindowMulConst j l * tWindow b (j + l) := by
        rw [tWindowMulConst, ← Finset.sum_mul]

set_option linter.unusedSectionVars false in
private lemma tWindow_eq_tripleSum (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (x : M) (i : ℕ) :
    tWindow (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x)) i =
      ∑ k ∈ Finset.range (i + 3),
        ∑ n ∈ Finset.range (k + 1),
          ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
            ∏ m : Fin n,
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T).toSection x) := rfl

set_option linter.unusedSectionVars false in
private lemma antidiagonalTupleGrid_eq_doubleSum (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (x : M) (l : ℕ) :
    Combinatorics.antidiagonalTupleGrid
        (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x)) l =
      ∑ n ∈ Finset.range (l + 1),
        ∑ e ∈ Finset.Nat.antidiagonalTuple n l,
          ∏ m : Fin n,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T).toSection x) := rfl

set_option linter.unusedSectionVars false in
private theorem exists_backgroundJet_rfns_bound (g₀ : SmoothRiemannianMetric I M)
    (r s : ℕ) (S : SmoothCcTensor g₀ r s) :
    ∃ c : ℕ → ℝ, (∀ i, 0 ≤ c i) ∧ ∀ (i : ℕ) (x : M),
      riemannianFiberNormSq (I := I) (M := M) g₀ r (s + i) x
        ((iteratedCovGrad (I := I) g₀ r s i S).toSection x) ≤ c i := by
  have h : ∀ i : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ r (s + i) x
        ((iteratedCovGrad (I := I) g₀ r s i S).toSection x) ≤ c := fun i =>
    exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ r (s + i)
      (iteratedCovGrad (I := I) g₀ r s i S)
  choose c hc0 hcb using h
  exact ⟨c, hc0, hcb⟩

section MixedSharpRicci

open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert

set_option backward.isDefEq.respectTransparency false in
def ricMixedSharpEndoFib (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => metricSharp (I := I) g₀ x (ricciTensor (I := I) g₁ x v).toLinearMap
      map_add' := fun v v' => by
        have h : (ricciTensor (I := I) g₁ x (v + v')).toLinearMap =
            (ricciTensor (I := I) g₁ x v).toLinearMap +
              (ricciTensor (I := I) g₁ x v').toLinearMap := by
          ext w
          simp [map_add]
        rw [show metricSharp (I := I) g₀ x (ricciTensor (I := I) g₁ x (v + v')).toLinearMap =
            (metricFlatMap (I := I) g₀ x).symm
              (ricciTensor (I := I) g₁ x (v + v')).toLinearMap from rfl,
          h, map_add]
        rfl
      map_smul' := fun c v => by
        have h : (ricciTensor (I := I) g₁ x (c • v)).toLinearMap =
            c • (ricciTensor (I := I) g₁ x v).toLinearMap := by
          ext w
          simp [map_smul]
        rw [show metricSharp (I := I) g₀ x (ricciTensor (I := I) g₁ x (c • v)).toLinearMap =
            (metricFlatMap (I := I) g₀ x).symm
              (ricciTensor (I := I) g₁ x (c • v)).toLinearMap from rfl,
          h, map_smul]
        rfl }

set_option linter.unusedSectionVars false in
@[simp] lemma ricMixedSharpEndoFib_apply (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (v : TangentSpace I x) :
    ricMixedSharpEndoFib (I := I) (M := M) g₀ g₁ x v =
      metricSharp (I := I) g₀ x (ricciTensor (I := I) g₁ x v).toLinearMap := by
  rw [ricMixedSharpEndoFib, LinearMap.coe_toContinuousLinearMap']
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem ricMixedSharpEndoFib_contMDiff (g₀ g₁ : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y) x
        (ricMixedSharpEndoFib (I := I) (M := M) g₀ g₁ x)) := by
  apply cotangentCov_clmSection_smooth_aux (I := I) (M := M)
    (F₂ := E) (V₂ := fun y : M => TangentSpace I y)
    (φ := fun x : M => ricMixedSharpEndoFib (I := I) (M := M) g₀ g₁ x)
  intro Y
  have hcv : ∀ (α : M) (j : Fin (Module.finrank ℝ E)),
      ContMDiffOn I 𝓘(ℝ) ∞
        (fun b : M => (ricciTensor (I := I) g₁ b (Y b)).toLinearMap
          (chartBasisVecFiber (I := I) α j b))
        (chartAt H α).source := by
    intro α j
    have hRic : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
        (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
          (E := fun y => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) b
          (ricciTensor (I := I) g₁ b)) :=
      ricciTensor_contMDiff (I := I) g₁
    have hBasis : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
        (chartBasisVec (I := I) α j)
        (trivializationAt E (TangentSpace I) α).baseSet :=
      chartBasisVec_contMDiffOn (I := I) α j
    have happ : ContMDiffOn I (I.prod 𝓘(ℝ, ℝ)) ∞
        (fun b : M => (⟨b,
            ricciTensor (I := I) g₁ b (Y b) (chartBasisVecFiber (I := I) α j b)⟩ :
            TotalSpace ℝ (Bundle.Trivial M ℝ)))
        (trivializationAt E (TangentSpace I) α).baseSet :=
      ContMDiffOn.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := ℝ)
        (b := id) hRic.contMDiffOn Y.contMDiff.contMDiffOn hBasis
    have hbase_eq :
        (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source :=
      trivializationAt_baseSet_eq_chartAt_source (I := I) α
    rw [hbase_eq] at happ
    intro b hb
    have hpb := happ b hb
    rw [Bundle.contMDiffWithinAt_totalSpace] at hpb
    exact hpb.2
  have hsmooth := metricSharp_contMDiff_total (I := I) g₀
    (cv := fun b : M => (ricciTensor (I := I) g₁ b (Y b)).toLinearMap) hcv
  refine hsmooth.congr ?_
  intro x
  change TotalSpace.mk' E x
      (metricSharp (I := I) g₀ x (ricciTensor (I := I) g₁ x (Y x)).toLinearMap) =
    TotalSpace.mk' E x (ricMixedSharpEndoFib (I := I) (M := M) g₀ g₁ x (Y x))
  rw [ricMixedSharpEndoFib_apply]

set_option backward.isDefEq.respectTransparency false in
def ricMixedSharpEndoField (g₀ g₁ : SmoothRiemannianMetric I M) :
    ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x) where
  toFun := fun x : M => ricMixedSharpEndoFib (I := I) (M := M) g₀ g₁ x
  contMDiff_toFun := ricMixedSharpEndoFib_contMDiff (I := I) (M := M) g₀ g₁

set_option linter.unusedSectionVars false in
lemma ricMixedSharpEndoField_apply (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    ricMixedSharpEndoField (I := I) (M := M) g₀ g₁ x =
      ricMixedSharpEndoFib (I := I) (M := M) g₀ g₁ x := rfl

set_option linter.unusedSectionVars false in
private lemma ricEndoRaisedFib_eq_mixed_add_gInvDiffRaised
    (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) (v : TangentSpace I x) :
    ricEndoRaisedFib (I := I) g₁ x v =
      ricMixedSharpEndoFib (I := I) (M := M) g₀ g₁ x v +
        gInvDiffRaisedEndo (I := I) g₀ g₁ x
          (ricMixedSharpEndoFib (I := I) (M := M) g₀ g₁ x v) := by
  rw [gInvDiffRaisedEndo_apply]
  have hcollapse : ricMixedSharpEndoFib (I := I) (M := M) g₀ g₁ x v +
      (inverseMetricSharpFib (I := I) g₁ x
          (g0FlatCLM (I := I) g₀ x (ricMixedSharpEndoFib (I := I) (M := M) g₀ g₁ x v)) -
        ricMixedSharpEndoFib (I := I) (M := M) g₀ g₁ x v) =
      inverseMetricSharpFib (I := I) g₁ x
        (g0FlatCLM (I := I) g₀ x (ricMixedSharpEndoFib (I := I) (M := M) g₀ g₁ x v)) := by
    abel
  rw [hcollapse]
  rw [inverseMetricSharpFib_g0FlatCLM_eq_metricSharp (I := I) g₀ g₁ x
    (ricMixedSharpEndoFib (I := I) (M := M) g₀ g₁ x v)]
  have hβ : (g₀.inner x (ricMixedSharpEndoFib (I := I) (M := M) g₀ g₁ x v)).toLinearMap =
      (ricciTensor (I := I) g₁ x v).toLinearMap := by
    ext w
    rw [show ((g₀.inner x (ricMixedSharpEndoFib (I := I) (M := M) g₀ g₁ x v)).toLinearMap) w =
        g₀.inner x (ricMixedSharpEndoFib (I := I) (M := M) g₀ g₁ x v) w from rfl]
    rw [ricMixedSharpEndoFib_apply]
    exact inner_metricSharp (I := I) g₀ x (ricciTensor (I := I) g₁ x v).toLinearMap w
  rw [hβ, ricEndoRaisedFib_apply]

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
theorem slotInsertEndoCc_zero_ricEndoBackgroundDifference_telescope
    (g₀ g₁ : SmoothRiemannianMetric I M) :
    slotInsertEndoCc (I := I) (M := M) g₀ 0
        (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁) =
      (slotInsertEndoCc (I := I) (M := M) g₀ 0
          (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁) -
        slotInsertEndoCc (I := I) (M := M) g₀ 0
          (ricEndoRaisedField (I := I) (M := M) g₀)) +
      appCcRS (I := I) (M := M) g₀ 1 1 1
        (slotInsertEndoCc (I := I) (M := M) g₀ 0
          (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁))
        (slotInsertEndoCc (I := I) (M := M) g₀ 0
          (gInvDiffRaisedEndoField (I := I) g₀ g₁)) := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((((slotInsertEndoCc (I := I) (M := M) g₀ 0
          (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁) -
        slotInsertEndoCc (I := I) (M := M) g₀ 0
          (ricEndoRaisedField (I := I) (M := M) g₀)) +
      appCcRS (I := I) (M := M) g₀ 1 1 1
        (slotInsertEndoCc (I := I) (M := M) g₀ 0
          (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁))
        (slotInsertEndoCc (I := I) (M := M) g₀ 0
          (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection) x) =
      ((slotInsertEndoCc (I := I) (M := M) g₀ 0
          (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁)).toSection x -
        (slotInsertEndoCc (I := I) (M := M) g₀ 0
          (ricEndoRaisedField (I := I) (M := M) g₀)).toSection x) +
      (appCcRS (I := I) (M := M) g₀ 1 1 1
        (slotInsertEndoCc (I := I) (M := M) g₀ 0
          (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁))
        (slotInsertEndoCc (I := I) (M := M) g₀ 0
          (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection x from by
    rw [SmoothCcTensor.toSection_add, SmoothCcTensor.toSection_sub]
    rfl]
  apply ContinuousLinearMap.ext
  intro A
  rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply]
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  simp only [Tensor0SSpace.toModel_add, Tensor0SSpace.toModel_sub,
    ContinuousMultilinearMap.add_apply, ContinuousMultilinearMap.sub_apply]
  rw [show ((slotInsertEndoCc (I := I) (M := M) g₀ 0
        (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁)).toSection x) A =
      slotInsertEndoFib (I := I) (M := M) 1 0 x
        (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁ x) A from rfl]
  rw [show ((slotInsertEndoCc (I := I) (M := M) g₀ 0
        (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁)).toSection x) A =
      slotInsertEndoFib (I := I) (M := M) 1 0 x
        (ricMixedSharpEndoFib (I := I) (M := M) g₀ g₁ x) A from rfl]
  rw [show ((slotInsertEndoCc (I := I) (M := M) g₀ 0
        (ricEndoRaisedField (I := I) (M := M) g₀)).toSection x) A =
      slotInsertEndoFib (I := I) (M := M) 1 0 x
        (ricEndoRaisedFib (I := I) g₀ x) A from rfl]
  rw [show ((appCcRS (I := I) (M := M) g₀ 1 1 1
        (slotInsertEndoCc (I := I) (M := M) g₀ 0
          (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁))
        (slotInsertEndoCc (I := I) (M := M) g₀ 0
          (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection x) A =
      slotInsertEndoFib (I := I) (M := M) 1 0 x
        (ricMixedSharpEndoFib (I := I) (M := M) g₀ g₁ x)
        (slotInsertEndoFib (I := I) (M := M) 1 0 x
          (gInvDiffRaisedEndo (I := I) g₀ g₁ x) A) from rfl]
  rw [slotInsertEndoFib_apply_eval, slotInsertEndoFib_apply_eval,
    slotInsertEndoFib_apply_eval, slotInsertEndoFib_apply_eval,
    slotInsertEndoFib_apply_eval]
  rw [Function.update_self, Function.update_idem]
  rw [ricEndoBackgroundDifferenceField_apply (I := I) (M := M) g₀ g₁ x]
  rw [ContinuousLinearMap.sub_apply, ContinuousMultilinearMap.map_update_sub]
  rw [ricEndoRaisedFib_eq_mixed_add_gInvDiffRaised (I := I) (M := M) g₀ g₁ x (m 0)]
  rw [ContinuousMultilinearMap.map_update_add]
  ring

end MixedSharpRicci

section RiemannLoweredDifference

open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck

set_option backward.isDefEq.respectTransparency false

def riemannLoweredCovec (gm gc : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 4 I x :=
  (show ContinuousMultilinearMap ℝ (fun _ : Fin 4 => TangentSpace I x) ℝ from
    { toFun := fun m =>
        gm.inner x (riemannOp (LeviCivita (I := I) gc) x (m 0) (m 2) (m 3)) (m 1)
      map_update_add' := by
        have h01 : (0 : Fin 4) ≠ 1 := by decide
        have h02 : (0 : Fin 4) ≠ 2 := by decide
        have h03 : (0 : Fin 4) ≠ 3 := by decide
        have h10 : (1 : Fin 4) ≠ 0 := by decide
        have h12 : (1 : Fin 4) ≠ 2 := by decide
        have h13 : (1 : Fin 4) ≠ 3 := by decide
        have h20 : (2 : Fin 4) ≠ 0 := by decide
        have h21 : (2 : Fin 4) ≠ 1 := by decide
        have h23 : (2 : Fin 4) ≠ 3 := by decide
        have h30 : (3 : Fin 4) ≠ 0 := by decide
        have h31 : (3 : Fin 4) ≠ 1 := by decide
        have h32 : (3 : Fin 4) ≠ 2 := by decide
        intro _ m i a a'
        fin_cases i <;>
          simp only [Fin.reduceFinMk, Fin.isValue, Function.update_self, ne_eq,
            Function.update_of_ne, h01, h02, h03, h10, h12, h13, h20, h21, h23, h30, h31, h32,
            not_false_eq_true, map_add, ContinuousLinearMap.add_apply]
      map_update_smul' := by
        have h01 : (0 : Fin 4) ≠ 1 := by decide
        have h02 : (0 : Fin 4) ≠ 2 := by decide
        have h03 : (0 : Fin 4) ≠ 3 := by decide
        have h10 : (1 : Fin 4) ≠ 0 := by decide
        have h12 : (1 : Fin 4) ≠ 2 := by decide
        have h13 : (1 : Fin 4) ≠ 3 := by decide
        have h20 : (2 : Fin 4) ≠ 0 := by decide
        have h21 : (2 : Fin 4) ≠ 1 := by decide
        have h23 : (2 : Fin 4) ≠ 3 := by decide
        have h30 : (3 : Fin 4) ≠ 0 := by decide
        have h31 : (3 : Fin 4) ≠ 1 := by decide
        have h32 : (3 : Fin 4) ≠ 2 := by decide
        intro _ m i c a
        fin_cases i <;>
          simp only [Fin.reduceFinMk, Fin.isValue, Function.update_self, ne_eq,
            Function.update_of_ne, h01, h02, h03, h10, h12, h13, h20, h21, h23, h30, h31, h32,
            not_false_eq_true, map_smul, ContinuousLinearMap.smul_apply]
      cont := by
        have hR : Continuous (fun m : Fin 4 → TangentSpace I x =>
            riemannOp (LeviCivita (I := I) gc) x (m 0) (m 2) (m 3)) :=
          (((riemannOp (LeviCivita (I := I) gc) x).continuous.comp
            (continuous_apply 0)).clm_apply (continuous_apply 2)).clm_apply (continuous_apply 3)
        exact ((gm.inner x).continuous.comp hR).clm_apply (continuous_apply 1) }
    : Tensor0SSpace 4 I x)

set_option linter.unusedSectionVars false in
@[simp] lemma riemannLoweredCovec_apply (gm gc : SmoothRiemannianMetric I M) (x : M)
    (m : Fin 4 → TangentSpace I x) :
    riemannLoweredCovec (I := I) gm gc x m =
      gm.inner x (riemannOp (LeviCivita (I := I) gc) x (m 0) (m 2) (m 3)) (m 1) := rfl

set_option linter.unusedSectionVars false in
private lemma riemannLoweredScalar_global (gm gc : SmoothRiemannianMetric I M)
    {Y W p q : Π b : M, TangentSpace I b}
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y))
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W))
    (hp : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% p))
    (hq : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% q)) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => gm.inner x
        (riemannOp (LeviCivita (I := I) gc) x (Y x) (p x) (q x)) (W x)) := by
  classical
  have hRsec : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b : M => riemannSec (LeviCivita (I := I) gc) Y p q b)) :=
    riemannSec_contMDiff (cov := LeviCivita (I := I) gc) hY hp hq
  have hcongr : (fun x : M => gm.inner x
        (riemannOp (LeviCivita (I := I) gc) x (Y x) (p x) (q x)) (W x)) =
      (fun x : M => gm.inner x (riemannSec (LeviCivita (I := I) gc) Y p q x) (W x)) := by
    funext x
    rw [riemannOp_apply_smooth (cov := LeviCivita (I := I) gc) hY hp hq]
  rw [hcongr]
  exact contMDiff_g_inner_of_smooth_sections (I := I) gm
    ⟨fun b => riemannSec (LeviCivita (I := I) gc) Y p q b, hRsec⟩ ⟨fun b => W b, hW⟩

set_option linter.unusedSectionVars false in
private lemma riemannLoweredScalar_contMDiffAt (gm gc : SmoothRiemannianMetric I M)
    (V0 V1 V2 V3 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x₀ : M) :
    ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun x : M =>
        gm.inner x (riemannOp (LeviCivita (I := I) gc) x (V0 x) (V2 x) (V3 x)) (V1 x)) x₀ := by
  have hglob := riemannLoweredScalar_global (I := I) (M := M) gm gc
    (Y := fun b => V0 b) (W := fun b => V1 b) (p := fun b => V2 b) (q := fun b => V3 b)
    V0.contMDiff V1.contMDiff V2.contMDiff V3.contMDiff
  exact hglob.contMDiffAt

set_option backward.isDefEq.respectTransparency false in
theorem riemannLoweredCovec_section_contMDiff (gm gc : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 4 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 4 ℝ E)
        (E := fun z : M => Tensor0SSpace 4 I z) x (riemannLoweredCovec (I := I) gm gc x)) := by
  classical
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 4
  refine (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
      (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
      (fun x : M => (riemannLoweredCovec (I := I) gm gc x :
        Bundle.continuousMultilinearMap ℝ 4 E (TangentSpace I) x))).mpr ?_
  intro σ x₀
  set b := Module.finBasis ℝ E with hb
  set e₁ := trivializationAt E (TangentSpace I : M → Type _) x₀ with he₁def
  have he₁ : x₀ ∈ e₁.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) x₀
  have hframe := e₁.isLocalFrameOn_localFrame_baseSet I (⊤ : ℕ∞) b
  obtain ⟨Y, hY⟩ := hframe.exists_contMDiffSection_eqOn_nhd e₁.open_baseSet he₁
  have hscalar : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun x : M => gm.inner x
        (riemannOp (LeviCivita (I := I) gc) x (Y (σ 0) x) (Y (σ 2) x) (Y (σ 3) x))
        (Y (σ 1) x)) x₀ :=
    riemannLoweredScalar_contMDiffAt (I := I) gm gc (Y (σ 0)) (Y (σ 1)) (Y (σ 2)) (Y (σ 3)) x₀
  refine hscalar.congr_of_eventuallyEq ?_
  have h_base₁ : ∀ᶠ x in 𝓝 x₀, x ∈ e₁.baseSet := e₁.open_baseSet.mem_nhds he₁
  filter_upwards [h_base₁, hY] with x hx₁ hYx
  rw [continuousMultilinearMap_basis_repr]
  have hframeEq : ∀ k : Fin 4, e₁.symmL ℝ x (b (σ k)) = (Y (σ k)) x := by
    intro k
    rw [hYx (σ k), Trivialization.localFrame_apply_of_mem_baseSet (hx := hx₁)]
    simp [Trivialization.basisAt]
  change gm.inner x (riemannOp (LeviCivita (I := I) gc) x
      (e₁.symmL ℝ x (b (σ 0))) (e₁.symmL ℝ x (b (σ 2))) (e₁.symmL ℝ x (b (σ 3))))
      (e₁.symmL ℝ x (b (σ 1))) = _
  rw [hframeEq 0, hframeEq 1, hframeEq 2, hframeEq 3]

def riemannLoweredField (gm gc : SmoothRiemannianMetric I M) :
    Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) ∞ 4 :=
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 4
  ⟨fun x => riemannLoweredCovec (I := I) gm gc x,
    riemannLoweredCovec_section_contMDiff (I := I) gm gc⟩

def riemannLoweredCc (g₀ gm gc : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 0 4 where
  toSection :=
    MixedSection.fromMultilinearSection (𝕜 := ℝ) (F := E) (IB := I)
      (E := (TangentSpace I : M → Type _)) ∞ (riemannLoweredField (I := I) gm gc)
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
lemma riemannLoweredCc_unitModel (g₀ gm gc : SmoothRiemannianMetric I M) (x : M) :
    unitModel (I := I) (M := M) g₀ 4 (riemannLoweredCc (I := I) (M := M) g₀ gm gc) x =
      Tensor0SSpace.toModel (riemannLoweredCovec (I := I) gm gc x) := by
  rw [unitModel]
  rw [show (riemannLoweredCc (I := I) (M := M) g₀ gm gc).toSection x
        (unitTensor (I := I) (M := M) x) =
      (MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight
          (riemannLoweredField (I := I) gm gc x)
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))
      from rfl]
  rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
    ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
  rfl

set_option linter.unusedSectionVars false in
lemma riemannLoweredCc_unitModel_apply (g₀ gm gc : SmoothRiemannianMetric I M) (x : M)
    (m : Fin 4 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 4 (riemannLoweredCc (I := I) (M := M) g₀ gm gc) x m =
      gm.inner x (riemannOp (LeviCivita (I := I) gc) x (m 0) (m 2) (m 3)) (m 1) := by
  rw [riemannLoweredCc_unitModel]
  rfl

def riemannLoweredBackgroundDifference (g₀ g₁ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 0 4 :=
  riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁ - riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
lemma riemannLoweredBackgroundDifference_unitModel_apply
    (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) (m : Fin 4 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 4
        (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁) x m =
      g₀.inner x (riemannOp (LeviCivita (I := I) g₁) x (m 0) (m 2) (m 3)) (m 1) -
        g₀.inner x (riemannOp (LeviCivita (I := I) g₀) x (m 0) (m 2) (m 3)) (m 1) := by
  have hsub : unitModel (I := I) (M := M) g₀ 4
      (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁) x m =
      unitModel (I := I) (M := M) g₀ 4
          (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁) x m -
        unitModel (I := I) (M := M) g₀ 4
          (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀) x m := by
    simp only [riemannLoweredBackgroundDifference, unitModel]
    rw [show ((riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁ -
          riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀).toSection x) =
        (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁).toSection x -
          (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀).toSection x from by
      rw [SmoothCcTensor.toSection_sub]; rfl]
    rw [ContinuousLinearMap.sub_apply, Tensor0SSpace.toModel_sub,
      ContinuousMultilinearMap.sub_apply]
  rw [hsub, riemannLoweredCc_unitModel_apply, riemannLoweredCc_unitModel_apply]

private instance tensor0SModelNormedSpaceCC {s : ℕ} :
    NormedSpace ℝ (Tensor0SModel s ℝ E) :=
  Tensor0SBundle.tensor0SModel_normedSpace s

set_option linter.unusedSectionVars false in
private lemma interiorProduct_toModel_eval_pal (s : ℕ) (x : M) (vv : TangentSpace I x)
    (D : Tensor0SSpace (s + 1) I x) (w : Fin s → TangentSpace I x) :
    Tensor0SSpace.toModel
        (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) s x vv D) w =
      Tensor0SSpace.toModel D (Fin.cons (show E from vv) (fun k => (show E from w k))) := by
  have h1 : Tensor0SSpace.toModel
      (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) s x vv D) =
      Tensor0SBundle.model_interior_product (𝕜 := ℝ) (E := E) s (show E from vv)
        (Tensor0SSpace.toModel D) := rfl
  rw [h1]
  rfl

set_option linter.unusedSectionVars false in
private lemma toModel_om_single_eq_cotangentToDual (x : M) (om : Tensor0SSpace 1 I x)
    (m : Fin 1 → TangentSpace I x) :
    Tensor0SSpace.toModel om (fun k => (m k : E)) =
      cotangentToDual (I := I) (x := x) om (m 0) := by
  rw [show (fun k : Fin 1 => (m k : E)) = (fun _ : Fin 1 => (m 0 : E)) from by
    funext k; fin_cases k; rfl]
  rw [cotangentToDual_apply]
  rfl

set_option linter.unusedSectionVars false in
private lemma g1_inner_gInvRaisedEndo_left (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    g₁.inner x (gInvRaisedEndo (I := I) g₀ g₁ x v) w = g₀.inner x v w := by
  rw [gInvRaisedEndo_apply]
  rw [inverseMetricSharpFib_inner (I := I) g₁ x (g0FlatCLM (I := I) g₀ x v) w]
  rw [show cotangentToDualLinear (I := I) (x := x) (g0FlatCLM (I := I) g₀ x v) w =
      cotangentToDual (I := I) (x := x) (g0FlatCLM (I := I) g₀ x v) w from rfl]
  rw [cotangentToDual_g0FlatCLM]

set_option linter.unusedSectionVars false in
private lemma g0_inner_inverseMetricSharp_mixed (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (om : Tensor0SSpace 1 I x) (v : TangentSpace I x) :
    g₀.inner x (inverseMetricSharpFib (I := I) g₁ x om) v =
      cotangentToDual (I := I) (x := x) om (gInvRaisedEndo (I := I) g₀ g₁ x v) := by
  rw [show cotangentToDual (I := I) (x := x) om (gInvRaisedEndo (I := I) g₀ g₁ x v) =
      cotangentToDualLinear (I := I) (x := x) om (gInvRaisedEndo (I := I) g₀ g₁ x v) from rfl]
  rw [← inverseMetricSharpFib_inner (I := I) g₁ x om (gInvRaisedEndo (I := I) g₀ g₁ x v)]
  rw [g₁.symm x (inverseMetricSharpFib (I := I) g₁ x om) (gInvRaisedEndo (I := I) g₀ g₁ x v)]
  rw [g1_inner_gInvRaisedEndo_left (I := I) (M := M) g₀ g₁ x v
    (inverseMetricSharpFib (I := I) g₁ x om)]
  rw [g₀.symm x v (inverseMetricSharpFib (I := I) g₁ x om)]

set_option linter.unusedSectionVars false in
private lemma cotangentToDual_eq_inner_sharp (g₀ : SmoothRiemannianMetric I M) (x : M)
    (om : Tensor0SSpace 1 I x) (ww : TangentSpace I x) :
    cotangentToDual (I := I) (x := x) om ww =
      g₀.inner x ww (inverseMetricSharpFib (I := I) g₀ x om) := by
  rw [g₀.symm x ww (inverseMetricSharpFib (I := I) g₀ x om)]
  rw [g0_inner_inverseMetricSharp_mixed (I := I) (M := M) g₀ g₀ x om ww]
  rw [show gInvRaisedEndo (I := I) g₀ g₀ x ww = ww from by
    rw [gInvRaisedEndo_apply, inverseMetricSharpFib_g0FlatCLM]]

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
private lemma sharpFlatEndoCc_eq_slotInsert_fullRaised (g₀ g₁ : SmoothRiemannianMetric I M) :
    sharpFlatEndoCc (I := I) g₀ g₁ =
      slotInsertEndoCc (I := I) (M := M) g₀ 0 (fullRaisedEndoField (I := I) (M := M) g₀ g₁) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro om
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (sharpFlatEndoCc (I := I) g₀ g₁).toSection x) om) =
      (g0FlatCLM (I := I) g₀ x) (inverseMetricSharpFib (I := I) g₁ x om) from rfl]
  rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (slotInsertEndoCc (I := I) (M := M) g₀ 0
          (fullRaisedEndoField (I := I) (M := M) g₀ g₁)).toSection x) om) =
      slotInsertEndoFib (I := I) (M := M) 1 0 x
        (fullRaisedEndoField (I := I) (M := M) g₀ g₁ x) om from rfl]
  rw [slotInsertEndoFib_apply_eval]
  rw [toModel_om_single_eq_cotangentToDual (I := I) (M := M) x om
    (Function.update m 0 (fullRaisedEndoField (I := I) (M := M) g₀ g₁ x (m 0)))]
  rw [Function.update_self]
  rw [toModel_om_single_eq_cotangentToDual (I := I) (M := M) x
    ((g0FlatCLM (I := I) g₀ x) (inverseMetricSharpFib (I := I) g₁ x om)) m]
  rw [cotangentToDual_g0FlatCLM]
  rw [g0_inner_inverseMetricSharp_mixed (I := I) (M := M) g₀ g₁ x om (m 0)]
  rw [fullRaisedEndoField_apply]

set_option linter.unusedSectionVars false in
private lemma fullRaisedEndoField_diff_split (g₀ g₁ : SmoothRiemannianMetric I M) :
    fullRaisedEndoField (I := I) (M := M) g₀ g₁ =
      gInvDiffRaisedEndoField (I := I) g₀ g₁ +
        fullRaisedEndoField (I := I) (M := M) g₀ g₀ := by
  apply ContMDiffSection.ext
  intro x
  rw [show ((gInvDiffRaisedEndoField (I := I) g₀ g₁ +
        fullRaisedEndoField (I := I) (M := M) g₀ g₀) x) =
      gInvDiffRaisedEndoField (I := I) g₀ g₁ x +
        fullRaisedEndoField (I := I) (M := M) g₀ g₀ x from by
    rw [ContMDiffSection.coe_add]; rfl]
  apply ContinuousLinearMap.ext
  intro v
  rw [fullRaisedEndoField_apply, ContinuousLinearMap.add_apply]
  rw [show (gInvDiffRaisedEndoField (I := I) g₀ g₁ x) = gInvDiffRaisedEndo (I := I) g₀ g₁ x
    from rfl]
  rw [fullRaisedEndoField_apply]
  rw [gInvRaisedEndo_eq_diff_add_id (I := I) g₀ g₁ x v]
  rw [show gInvRaisedEndo (I := I) g₀ g₀ x v = v from by
    rw [gInvRaisedEndo_apply, inverseMetricSharpFib_g0FlatCLM]]

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
private lemma slotInsertEndoCc_add_endo (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (A B : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)) :
    slotInsertEndoCc (I := I) (M := M) g₀ s (A + B) =
      slotInsertEndoCc (I := I) (M := M) g₀ s A +
        slotInsertEndoCc (I := I) (M := M) g₀ s B := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  rw [show ((slotInsertEndoCc (I := I) (M := M) g₀ s A +
        slotInsertEndoCc (I := I) (M := M) g₀ s B).toSection x) =
      (slotInsertEndoCc (I := I) (M := M) g₀ s A).toSection x +
        (slotInsertEndoCc (I := I) (M := M) g₀ s B).toSection x from by
    rw [SmoothCcTensor.toSection_add]; rfl]
  rw [ContinuousLinearMap.add_apply]
  simp only [slotInsertEndoCc_toSection]
  rw [show ((A + B) x) = A x + B x from by rw [ContMDiffSection.coe_add]; rfl]
  rw [slotInsertEndoFib_add_left, ContinuousLinearMap.add_apply]

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
private lemma endoCovariantDerivative_fullRaised_id_eq_zero (g₀ : SmoothRiemannianMetric I M)
    (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) (v : TangentSpace I x) :
    ((endoCovariantDerivative (I := I) (M := M) g₀)
        (fullRaisedEndoField (I := I) (M := M) g₀ g₀) x v) (Y x) = 0 := by
  have hLeib := endoCovariantDerivative_apply (I := I) (M := M) g₀
    (fullRaisedEndoField (I := I) (M := M) g₀ g₀) Y x v
  have hΛapp : (fun y : M => (fullRaisedEndoField (I := I) (M := M) g₀ g₀ y) (Y y)) =
      (fun y : M => Y y) := by
    funext y
    rw [fullRaisedEndoField_apply]
    rw [show gInvRaisedEndo (I := I) g₀ g₀ y (Y y) = Y y from by
      rw [gInvRaisedEndo_apply, inverseMetricSharpFib_g0FlatCLM]]
  rw [hLeib, hΛapp]
  rw [fullRaisedEndoField_apply]
  rw [show gInvRaisedEndo (I := I) g₀ g₀ x
      ((LeviCivita (I := I) g₀).toFun (fun y : M => Y y) x v) =
      (LeviCivita (I := I) g₀).toFun (fun y : M => Y y) x v from by
    rw [gInvRaisedEndo_apply, inverseMetricSharpFib_g0FlatCLM]]
  rw [sub_self]

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
private lemma covGrad_slotInsert_fullRaised_id_eq_zero (g₀ : SmoothRiemannianMetric I M) :
    covGrad (I := I) (M := M) g₀ 1 1
        (slotInsertEndoCc (I := I) (M := M) g₀ 0
          (fullRaisedEndoField (I := I) (M := M) g₀ g₀)) = 0 := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun m => ?_)
  rw [covGrad_toSection_apply_eval (I := I) (M := M) g₀ 1 1
    (slotInsertEndoCc (I := I) (M := M) g₀ 0
      (fullRaisedEndoField (I := I) (M := M) g₀ g₀)) x D m]
  rw [tensorCovDerivAt_slotInsertEndoCc_eq (I := I) (M := M) g₀ 0
    (fullRaisedEndoField (I := I) (M := M) g₀ g₀) x (m 0)]
  rw [show ((endoCovariantDerivative (I := I) (M := M) g₀)
        (fullRaisedEndoField (I := I) (M := M) g₀ g₀) x (m 0)) =
      (0 : TangentSpace I x →L[ℝ] TangentSpace I x) from by
    apply ContinuousLinearMap.ext
    intro w
    rw [ContinuousLinearMap.zero_apply]
    obtain ⟨Y, hY⟩ := ContMDiffSection.exists_eq_at (I := I)
      (F := E) (V := fun y : M => TangentSpace I y) (n := (⊤ : ℕ∞)) x w
    rw [← hY]
    exact endoCovariantDerivative_fullRaised_id_eq_zero (I := I) (M := M) g₀ Y x (m 0)]
  rw [show slotInsertEndoFib (I := I) (M := M) (0 + 1) 0 x
        (0 : TangentSpace I x →L[ℝ] TangentSpace I x) = 0 from by
    rw [show (0 : TangentSpace I x →L[ℝ] TangentSpace I x) =
        (0 : ℝ) • (0 : TangentSpace I x →L[ℝ] TangentSpace I x) from (zero_smul ℝ _).symm,
      slotInsertEndoFib_smul_left, zero_smul]]
  simp [SmoothCcTensor.toSection_zero]

set_option linter.unusedSectionVars false in
private lemma iteratedCovGrad_slotInsert_fullRaised_id_succ_eq_zero
    (g₀ : SmoothRiemannianMetric I M) (m : ℕ) :
    iteratedCovGrad (I := I) g₀ 1 1 (m + 1)
        (slotInsertEndoCc (I := I) (M := M) g₀ 0
          (fullRaisedEndoField (I := I) (M := M) g₀ g₀)) = 0 := by
  induction m with
  | zero =>
      rw [iteratedCovGrad_succ, iteratedCovGrad_zero]
      exact covGrad_slotInsert_fullRaised_id_eq_zero (I := I) (M := M) g₀
  | succ m' ih =>
      rw [iteratedCovGrad_succ, ih, covGrad_zero]

set_option linter.unusedSectionVars false in
private lemma iteratedCovGrad_smul_pt (g : SmoothRiemannianMetric I M) (r s j : ℕ)
    (c : ℝ) (w : SmoothCcTensor g r s) :
    iteratedCovGrad (I := I) g r s j (c • w) = c • iteratedCovGrad (I := I) g r s j w := by
  induction j with
  | zero => simp only [iteratedCovGrad_zero]
  | succ j ih =>
    rw [iteratedCovGrad_succ, iteratedCovGrad_succ, ih, covGrad_smul]

set_option linter.unusedSectionVars false in
private lemma rfns_smul_pt (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (c : ℝ) (v : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (c • v) =
      c ^ 2 * riemannianFiberNormSq (I := I) (M := M) g r s x v := by
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x (c • v),
    riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x v]
  rw [TensorRSSpace.toModel_smul, tensorInnerPointwise_smul_left,
    tensorInnerPointwise_smul_right]
  ring

set_option linter.unusedSectionVars false in
private lemma rfns_neg_pt (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (v : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (-v) =
      riemannianFiberNormSq (I := I) (M := M) g r s x v := by
  have h := rfns_smul_pt (I := I) (M := M) g r s x (-1 : ℝ) v
  rw [neg_one_smul] at h
  rw [h]; norm_num

set_option linter.unusedSectionVars false in
private lemma rfns_iteratedCovGrad_symmS_pointwise (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (k : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + k) x
        ((iteratedCovGrad (I := I) g₀ 0 2 k (symmS (I := I) (M := M) g₀ T)).toSection x) ≤
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + k) x
        ((iteratedCovGrad (I := I) g₀ 0 2 k T).toSection x) := by
  have hswap : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + k) x
      ((iteratedCovGrad (I := I) g₀ 0 2 k
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) T)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + k) x
        ((iteratedCovGrad (I := I) g₀ 0 2 k T).toSection x) :=
    riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 2) 1) T k x
  set A := iteratedCovGrad (I := I) g₀ 0 2 k T with hA
  set B := iteratedCovGrad (I := I) g₀ 0 2 k
    (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) T) with hB
  have htoSec : ((iteratedCovGrad (I := I) g₀ 0 2 k
        (symmS (I := I) (M := M) g₀ T)).toSection x : TensorRSSpace 0 (2 + k) I x) =
      (1 / 2 : ℝ) • (A.toSection x) + (1 / 2 : ℝ) • (B.toSection x) := by
    rw [iteratedCovGrad_symmS_eq (I := I) (M := M) g₀ T k]
    rw [show (((1 / 2 : ℝ) • A + (1 / 2 : ℝ) • B).toSection x) =
        ((1 / 2 : ℝ) • A).toSection x + ((1 / 2 : ℝ) • B).toSection x from by
      rw [SmoothCcTensor.toSection_add]; rfl]
    rw [show (((1 / 2 : ℝ) • A).toSection x) = (1 / 2 : ℝ) • (A.toSection x) from by
        rw [SmoothCcTensor.toSection_smul]; rfl,
      show (((1 / 2 : ℝ) • B).toSection x) = (1 / 2 : ℝ) • (B.toSection x) from by
        rw [SmoothCcTensor.toSection_smul]; rfl]
  rw [htoSec]
  have hRB : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + k) x (B.toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + k) x (A.toSection x) := hswap
  calc riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + k) x
          ((1 / 2 : ℝ) • (A.toSection x) + (1 / 2 : ℝ) • (B.toSection x))
      ≤ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + k) x
            ((1 / 2 : ℝ) • (A.toSection x)) +
          2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + k) x
            ((1 / 2 : ℝ) • (B.toSection x)) :=
        riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 (2 + k) x _ _
    _ = (1 / 2 : ℝ) * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + k) x (A.toSection x) +
          (1 / 2 : ℝ) * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + k) x (B.toSection x) := by
        rw [rfns_smul_pt, rfns_smul_pt]; ring
    _ = riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + k) x (A.toSection x) := by
        rw [hRB]; ring

set_option linter.unusedSectionVars false in
private lemma rfns_iteratedCovGrad_koszulCovecCc_pointwise (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (i : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x
        ((iteratedCovGrad (I := I) g₀ 0 3 i (koszulCovecCc (I := I) g₀ T)).toSection x) ≤
      10 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 1)) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (i + 1) T).toSection x) := by
  classical
  set W : SmoothCcTensor g₀ 0 3 := symmSCovGrad3 (I := I) g₀ T with hW
  set DA : SmoothCcTensor g₀ 0 3 :=
    domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 2) W with hDA
  set DB : SmoothCcTensor g₀ 0 3 := domDomCongrSection (I := I) g₀ (finRotate 3) W with hDB
  set DC : SmoothCcTensor g₀ 0 3 :=
    domDomCongrSection (I := I) g₀ (Equiv.swap (1 : Fin 3) 2) W with hDC
  have hpermW : ∀ σ : Equiv.Perm (Fin 3),
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x
        ((iteratedCovGrad (I := I) g₀ 0 3 i
          (domDomCongrSection (I := I) g₀ σ W)).toSection x) ≤
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 1)) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (i + 1) T).toSection x) := by
    intro σ
    rw [riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀ σ W i x]
    rw [hW]
    rw [show symmSCovGrad3 (I := I) g₀ T =
        covGrad (I := I) (M := M) g₀ 0 2 (symmS (I := I) g₀ T) from rfl]
    have hcomm := rfns_iteratedCovGrad_covGrad_comm_rs (I := I) (M := M) g₀ 0 2 i
      (symmS (I := I) g₀ T) x
    rw [hcomm]
    exact rfns_iteratedCovGrad_symmS_pointwise (I := I) (M := M) g₀ T (i + 1) x
  have hkos : koszulCovecCc (I := I) g₀ T = (1 / 2 : ℝ) • (DA + DB - DC) := by
    rw [koszulCovecCc, hDA, hDB, hDC, hW]
  have hsub : iteratedCovGrad (I := I) g₀ 0 3 i (DA + DB - DC) =
      iteratedCovGrad (I := I) g₀ 0 3 i DA + iteratedCovGrad (I := I) g₀ 0 3 i DB -
        iteratedCovGrad (I := I) g₀ 0 3 i DC := by
    rw [sub_eq_add_neg, sub_eq_add_neg, iteratedCovGrad_add, iteratedCovGrad_add,
      iteratedCovGrad_neg]
  have htoSec : ((iteratedCovGrad (I := I) g₀ 0 3 i (koszulCovecCc (I := I) g₀ T)).toSection x :
        TensorRSSpace 0 (3 + i) I x) =
      (1 / 2 : ℝ) • ((iteratedCovGrad (I := I) g₀ 0 3 i DA).toSection x +
        (iteratedCovGrad (I := I) g₀ 0 3 i DB).toSection x -
        (iteratedCovGrad (I := I) g₀ 0 3 i DC).toSection x) := by
    rw [hkos, iteratedCovGrad_smul_pt, hsub]
    rw [show (((1 / 2 : ℝ) • (iteratedCovGrad (I := I) g₀ 0 3 i DA +
          iteratedCovGrad (I := I) g₀ 0 3 i DB -
          iteratedCovGrad (I := I) g₀ 0 3 i DC)).toSection x) =
        (1 / 2 : ℝ) • ((iteratedCovGrad (I := I) g₀ 0 3 i DA +
          iteratedCovGrad (I := I) g₀ 0 3 i DB -
          iteratedCovGrad (I := I) g₀ 0 3 i DC).toSection x) from by
      rw [SmoothCcTensor.toSection_smul]; rfl]
    rw [show ((iteratedCovGrad (I := I) g₀ 0 3 i DA +
          iteratedCovGrad (I := I) g₀ 0 3 i DB -
          iteratedCovGrad (I := I) g₀ 0 3 i DC).toSection x) =
        (iteratedCovGrad (I := I) g₀ 0 3 i DA).toSection x +
          (iteratedCovGrad (I := I) g₀ 0 3 i DB).toSection x -
          (iteratedCovGrad (I := I) g₀ 0 3 i DC).toSection x from by
      rw [SmoothCcTensor.toSection_sub, SmoothCcTensor.toSection_add]; rfl]
  set PA := (iteratedCovGrad (I := I) g₀ 0 3 i DA).toSection x with hPA
  set PB := (iteratedCovGrad (I := I) g₀ 0 3 i DB).toSection x with hPB
  set PC := (iteratedCovGrad (I := I) g₀ 0 3 i DC).toSection x with hPC
  set R2 : ℝ := riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 1)) x
    ((iteratedCovGrad (I := I) g₀ 0 2 (i + 1) T).toSection x) with hR2
  have hbA : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x PA ≤ R2 :=
    hpermW (Equiv.swap (0 : Fin 3) 2)
  have hbB : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x PB ≤ R2 :=
    hpermW (finRotate 3)
  have hbC : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x PC ≤ R2 :=
    hpermW (Equiv.swap (1 : Fin 3) 2)
  rw [htoSec, rfns_smul_pt]
  have hnegC : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x (-PC) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x PC :=
    rfns_neg_pt (I := I) (M := M) g₀ 0 (3 + i) x PC
  have hR2_nn : 0 ≤ R2 := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + (i + 1)) x _
  have hsum : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + i) x (PA + PB - PC) ≤
      10 * R2 := by
    have h1 := riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 (3 + i) x (PA + PB) (-PC)
    have h2 := riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 (3 + i) x PA PB
    rw [hnegC] at h1
    rw [show PA + PB - PC = (PA + PB) + (-PC) from sub_eq_add_neg _ _]
    nlinarith [h1, h2, hbA, hbB, hbC,
      riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (3 + i) x PA,
      riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (3 + i) x PB,
      riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (3 + i) x PC]
  nlinarith [hsum, hR2_nn,
    riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (3 + i) x (PA + PB - PC)]

set_option linter.unusedSectionVars false in
private lemma rfns_iteratedCovGrad_raisedKoszul_pointwise (g₀ g₁ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
    (i : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 2 i (raisedKoszul (I := I) g₀ g₁)).toSection x) ≤
      10 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 1)) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (i + 1) T).toSection x) := by
  rw [raisedKoszul_eq_cometricRaiseSlot0Field_koszulCovecCc (I := I) (M := M) g₀ g₁ T htie]
  rw [rfns_iteratedCovGrad_cometricRaiseSlot0Field_koszul_eq (I := I) (M := M) g₀ T i x]
  exact rfns_iteratedCovGrad_koszulCovecCc_pointwise (I := I) (M := M) g₀ T i x

set_option linter.unusedVariables false in
private theorem exists_rfns_iteratedCovGrad_sharpFlatEndoCc_tgrid
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ S : ℕ → ℝ, (∀ l, 0 ≤ S l) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (l : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
            ((iteratedCovGrad (I := I) g₀ 1 1 l (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x) ≤
          S l * Combinatorics.antidiagonalTupleGrid
            (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
              ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x)) l := by
  classical
  obtain ⟨CD, hCD_nn, hCD⟩ :=
    rfns_iteratedCovGrad_slotInsertEndoCc_zero_gInvDiffRaisedEndoField_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨cid, hcid_nn, hcid⟩ := exists_bound_riemannianFiberNormSq_smoothCcTensor
    (I := I) (M := M) g₀ 1 1
    (slotInsertEndoCc (I := I) (M := M) g₀ 0 (fullRaisedEndoField (I := I) (M := M) g₀ g₀))
  refine ⟨fun l => 2 * CD l + 2 * cid,
    fun l => by have := hCD_nn l; linarith, ?_⟩
  intro g₁ T htie δ hδ_le hδ0 hbound l x
  set b : ℕ → ℝ := fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
    ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x) with hb_def
  have hb : ∀ j, 0 ≤ b j :=
    fun j => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + j) x _
  have hgrid_nn : 0 ≤ Combinatorics.antidiagonalTupleGrid b l :=
    Combinatorics.antidiagonalTupleGrid_nonneg b hb l
  have hsplit : sharpFlatEndoCc (I := I) g₀ g₁ =
      slotInsertEndoCc (I := I) (M := M) g₀ 0 (gInvDiffRaisedEndoField (I := I) g₀ g₁) +
        slotInsertEndoCc (I := I) (M := M) g₀ 0
          (fullRaisedEndoField (I := I) (M := M) g₀ g₀) := by
    rw [sharpFlatEndoCc_eq_slotInsert_fullRaised (I := I) (M := M) g₀ g₁,
      fullRaisedEndoField_diff_split (I := I) (M := M) g₀ g₁,
      slotInsertEndoCc_add_endo (I := I) (M := M) g₀ 0]
  have hsec : (iteratedCovGrad (I := I) g₀ 1 1 l (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x =
      (iteratedCovGrad (I := I) g₀ 1 1 l
        (slotInsertEndoCc (I := I) (M := M) g₀ 0
          (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection x +
      (iteratedCovGrad (I := I) g₀ 1 1 l
        (slotInsertEndoCc (I := I) (M := M) g₀ 0
          (fullRaisedEndoField (I := I) (M := M) g₀ g₀))).toSection x := by
    rw [hsplit, iteratedCovGrad_add, SmoothCcTensor.toSection_add]
    rfl
  rw [hsec]
  refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 1 (1 + l) x _ _) ?_
  have hA : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
      ((iteratedCovGrad (I := I) g₀ 1 1 l
        (slotInsertEndoCc (I := I) (M := M) g₀ 0
          (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection x) ≤
      CD l * Combinatorics.antidiagonalTupleGrid b l :=
    hCD g₁ T htie hδ_le hδ0 hbound l x
  have hB : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
      ((iteratedCovGrad (I := I) g₀ 1 1 l
        (slotInsertEndoCc (I := I) (M := M) g₀ 0
          (fullRaisedEndoField (I := I) (M := M) g₀ g₀))).toSection x) ≤
      cid * Combinatorics.antidiagonalTupleGrid b l := by
    match l with
    | 0 =>
        rw [iteratedCovGrad_zero]
        rw [Combinatorics.antidiagonalTupleGrid_zero, mul_one]
        exact hcid x
    | (m + 1) =>
        rw [iteratedCovGrad_slotInsert_fullRaised_id_succ_eq_zero (I := I) (M := M) g₀ m]
        rw [show ((0 : SmoothCcTensor g₀ 1 (1 + (m + 1))).toSection x) =
            (0 : TensorRSSpace 1 (1 + (m + 1)) I x) from by
          rw [SmoothCcTensor.toSection_zero]; rfl]
        rw [riemannianFiberNormSq_zero (I := I) (M := M) g₀ 1 (1 + (m + 1)) x]
        exact mul_nonneg hcid_nn
          (Combinatorics.antidiagonalTupleGrid_nonneg b hb (m + 1))
  calc 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
          ((iteratedCovGrad (I := I) g₀ 1 1 l
            (slotInsertEndoCc (I := I) (M := M) g₀ 0
              (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection x) +
        2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
          ((iteratedCovGrad (I := I) g₀ 1 1 l
            (slotInsertEndoCc (I := I) (M := M) g₀ 0
              (fullRaisedEndoField (I := I) (M := M) g₀ g₀))).toSection x)
      ≤ 2 * (CD l * Combinatorics.antidiagonalTupleGrid b l) +
          2 * (cid * Combinatorics.antidiagonalTupleGrid b l) := by
        have h1 := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 (1 + l) x
          ((iteratedCovGrad (I := I) g₀ 1 1 l
            (slotInsertEndoCc (I := I) (M := M) g₀ 0
              (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection x)
        linarith
    _ = (2 * CD l + 2 * cid) * Combinatorics.antidiagonalTupleGrid b l := by ring

omit [BoundarylessManifold I M] in
private lemma rfns_iteratedCovGrad_order_congr_ts (g : SmoothRiemannianMetric I M)
    (r s : ℕ) {n n' : ℕ} (h : n = n') (S : SmoothCcTensor g r s) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g r (s + n) x
        ((iteratedCovGrad (I := I) g r s n S).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g r (s + n') x
        ((iteratedCovGrad (I := I) g r s n' S).toSection x) := by
  subst h; rfl

set_option linter.unusedVariables false in
theorem rfns_iteratedCovGrad_connDiffSection_topSeparated_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Ktop : ℝ, 0 ≤ Ktop ∧ ∃ Kc : ℕ → ℝ, (∀ j, 0 ≤ Kc j) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (j : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j) x
            ((appCcRS (I := I) (M := M) g₀ 1 1 (2 + j)
              (iteratedCovGrad (I := I) g₀ 1 2 j (raisedKoszul (I := I) g₀ g₁))
              (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x) ≤
          Ktop * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (j + 1)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (j + 1) T).toSection x) ∧
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j) x
            ((iteratedCovGrad (I := I) g₀ 1 2 j (connDiffSection (I := I) g₁ g₀) -
              appCcRS (I := I) (M := M) g₀ 1 1 (2 + j)
                (iteratedCovGrad (I := I) g₀ 1 2 j (raisedKoszul (I := I) g₀ g₁))
                (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x) ≤
          Kc j * ∑ k ∈ Finset.range j,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (j - k)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (j - k) T).toSection x) *
              Combinatorics.antidiagonalTupleGrid
                (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x)) (k + 1) := by
  classical
  obtain ⟨S, hS_nn, hS⟩ :=
    exists_rfns_iteratedCovGrad_sharpFlatEndoCc_tgrid (I := I) (M := M) g₀ hδ₀
  refine ⟨10 * S 0, mul_nonneg (by norm_num) (hS_nn 0), ?_⟩
  refine ⟨fun j => (j : ℝ) * appCcGdiag (E := E) j * (10 * ∑ l ∈ Finset.range (j + 1), S l),
    fun j => mul_nonneg (mul_nonneg (Nat.cast_nonneg j) (appCcGdiag_nonneg (E := E) j))
      (mul_nonneg (by norm_num) (Finset.sum_nonneg (fun l _ => hS_nn l))), ?_⟩
  intro g₁ T htie δ hδ_le hδ0 hbound j x
  set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
    ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x) with hb_def
  have hb : ∀ l, 0 ≤ b l :=
    fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
  constructor
  · rw [appCcRS_toSection (I := I) (M := M) g₀ 1 1 (2 + j)
      (iteratedCovGrad (I := I) g₀ 1 2 j (raisedKoszul (I := I) g₀ g₁))
      (sharpFlatEndoCc (I := I) g₀ g₁) x]
    refine le_trans (riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g₀ 1 1 (2 + j) x
      ((iteratedCovGrad (I := I) g₀ 1 2 j (raisedKoszul (I := I) g₀ g₁)).toSection x)
      ((sharpFlatEndoCc (I := I) g₀ g₁).toSection x)) ?_
    have hK := rfns_iteratedCovGrad_raisedKoszul_pointwise (I := I) (M := M) g₀ g₁ T htie j x
    have hF : riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x
        ((sharpFlatEndoCc (I := I) g₀ g₁).toSection x) ≤ S 0 := by
      have h0 := hS g₁ T htie hδ_le hδ0 hbound 0 x
      rw [Combinatorics.antidiagonalTupleGrid_zero, mul_one] at h0
      exact h0
    calc riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j) x
            ((iteratedCovGrad (I := I) g₀ 1 2 j (raisedKoszul (I := I) g₀ g₁)).toSection x) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x
            ((sharpFlatEndoCc (I := I) g₀ g₁).toSection x)
        ≤ (10 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (j + 1)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (j + 1) T).toSection x)) * S 0 :=
          mul_le_mul hK hF
            (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 1 x _)
            (mul_nonneg (by norm_num)
              (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + (j + 1)) x _))
      _ = (10 * S 0) * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (j + 1)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (j + 1) T).toSection x) := by ring
  · have hid : iteratedCovGrad (I := I) g₀ 1 2 j (connDiffSection (I := I) g₁ g₀) =
        appCcRS (I := I) (M := M) g₀ 1 1 (2 + j)
            (iteratedCovGrad (I := I) g₀ 1 2 j (raisedKoszul (I := I) g₀ g₁))
            (sharpFlatEndoCc (I := I) g₀ g₁) +
          ∑ k ∈ Finset.range j,
            appCcRS (I := I) (M := M) g₀ 1 (1 + (k + 1)) (2 + j)
              (appCcLeibnizPsi (I := I) (M := M) g₀ 1 2 (raisedKoszul (I := I) g₀ g₁) j (k + 1))
              (iteratedCovGrad (I := I) g₀ 1 1 (k + 1) (sharpFlatEndoCc (I := I) g₀ g₁)) := by
      rw [connDiffSection_eq_appCcRS_raisedKoszul_sharpFlatEndoCc (I := I) (M := M) g₀ g₁]
      rw [iteratedCovGrad_appCcRS_eq (I := I) (M := M) g₀ 1 1 2
        (raisedKoszul (I := I) g₀ g₁) (sharpFlatEndoCc (I := I) g₀ g₁) j]
      rw [Finset.sum_range_succ' (fun k =>
        appCcRS (I := I) (M := M) g₀ 1 (1 + k) (2 + j)
          (appCcLeibnizPsi (I := I) (M := M) g₀ 1 2 (raisedKoszul (I := I) g₀ g₁) j k)
          (iteratedCovGrad (I := I) g₀ 1 1 k (sharpFlatEndoCc (I := I) g₀ g₁))) j]
      have hf0 : appCcRS (I := I) (M := M) g₀ 1 (1 + 0) (2 + j)
          (appCcLeibnizPsi (I := I) (M := M) g₀ 1 2 (raisedKoszul (I := I) g₀ g₁) j 0)
          (iteratedCovGrad (I := I) g₀ 1 1 0 (sharpFlatEndoCc (I := I) g₀ g₁)) =
          appCcRS (I := I) (M := M) g₀ 1 1 (2 + j)
            (iteratedCovGrad (I := I) g₀ 1 2 j (raisedKoszul (I := I) g₀ g₁))
            (sharpFlatEndoCc (I := I) g₀ g₁) :=
        congrArg (fun Z : SmoothCcTensor g₀ 1 (2 + j) =>
          appCcRS (I := I) (M := M) g₀ 1 1 (2 + j) Z (sharpFlatEndoCc (I := I) g₀ g₁))
          (appCcLeibnizPsi_zero_right_eq (I := I) (M := M) g₀ 1 2
            (raisedKoszul (I := I) g₀ g₁) j)
      rw [hf0]
      exact add_comm _ _
    have hsub : iteratedCovGrad (I := I) g₀ 1 2 j (connDiffSection (I := I) g₁ g₀) -
        appCcRS (I := I) (M := M) g₀ 1 1 (2 + j)
          (iteratedCovGrad (I := I) g₀ 1 2 j (raisedKoszul (I := I) g₀ g₁))
          (sharpFlatEndoCc (I := I) g₀ g₁) =
        ∑ k ∈ Finset.range j,
          appCcRS (I := I) (M := M) g₀ 1 (1 + (k + 1)) (2 + j)
            (appCcLeibnizPsi (I := I) (M := M) g₀ 1 2 (raisedKoszul (I := I) g₀ g₁) j (k + 1))
            (iteratedCovGrad (I := I) g₀ 1 1 (k + 1) (sharpFlatEndoCc (I := I) g₀ g₁)) := by
      rw [hid]
      exact add_sub_cancel_left _ _
    rw [hsub]
    rw [SmoothCcTensor.toSection_sum_apply]
    refine le_trans (riemannianFiberNormSq_sum_le_card_mul (I := I) (M := M) g₀ 1 (2 + j) x
      (Finset.range j) (fun k =>
        (appCcRS (I := I) (M := M) g₀ 1 (1 + (k + 1)) (2 + j)
          (appCcLeibnizPsi (I := I) (M := M) g₀ 1 2 (raisedKoszul (I := I) g₀ g₁) j (k + 1))
          (iteratedCovGrad (I := I) g₀ 1 1 (k + 1)
            (sharpFlatEndoCc (I := I) g₀ g₁))).toSection x)) ?_
    rw [Finset.card_range]
    have hstep : (∑ k ∈ Finset.range j,
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j) x
          ((appCcRS (I := I) (M := M) g₀ 1 (1 + (k + 1)) (2 + j)
            (appCcLeibnizPsi (I := I) (M := M) g₀ 1 2 (raisedKoszul (I := I) g₀ g₁) j (k + 1))
            (iteratedCovGrad (I := I) g₀ 1 1 (k + 1)
              (sharpFlatEndoCc (I := I) g₀ g₁))).toSection x)) ≤
        ∑ k ∈ Finset.range j,
          appCcGdiag (E := E) j * (10 * ∑ l ∈ Finset.range (j + 1), S l) *
            (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (j - k)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (j - k) T).toSection x) *
              Combinatorics.antidiagonalTupleGrid b (k + 1)) := by
      refine Finset.sum_le_sum (fun k hk => ?_)
      have hk_lt : k < j := Finset.mem_range.mp hk
      rw [appCcRS_toSection (I := I) (M := M) g₀ 1 (1 + (k + 1)) (2 + j)
        (appCcLeibnizPsi (I := I) (M := M) g₀ 1 2 (raisedKoszul (I := I) g₀ g₁) j (k + 1))
        (iteratedCovGrad (I := I) g₀ 1 1 (k + 1) (sharpFlatEndoCc (I := I) g₀ g₁)) x]
      refine le_trans (riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g₀ 1 (1 + (k + 1))
        (2 + j) x
        ((appCcLeibnizPsi (I := I) (M := M) g₀ 1 2 (raisedKoszul (I := I) g₀ g₁) j
          (k + 1)).toSection x)
        ((iteratedCovGrad (I := I) g₀ 1 1 (k + 1)
          (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x)) ?_
      have hPsi : riemannianFiberNormSq (I := I) (M := M) g₀ (1 + (k + 1)) (2 + j) x
          ((appCcLeibnizPsi (I := I) (M := M) g₀ 1 2 (raisedKoszul (I := I) g₀ g₁) j
            (k + 1)).toSection x) ≤
          appCcGdiag (E := E) j * (10 * b (j - k)) := by
        have hE3 := rfns_iteratedCovGrad_appCcLeibnizPsi_window_le (I := I) (M := M) g₀ 1 2
          (raisedKoszul (I := I) g₀ g₁) j (k + 1) 0 (by omega : k + 1 ≤ j) x
        rw [rfns_iteratedCovGrad_order_congr_ts (I := I) (M := M) g₀ 1 2
          (show (j - (k + 1)) + 0 = j - (k + 1) from by omega)
          (raisedKoszul (I := I) g₀ g₁) x] at hE3
        refine le_trans hE3 (mul_le_mul_of_nonneg_left ?_ (appCcGdiag_nonneg (E := E) j))
        have hK := rfns_iteratedCovGrad_raisedKoszul_pointwise (I := I) (M := M) g₀ g₁ T htie
          (j - (k + 1)) x
        rw [rfns_iteratedCovGrad_order_congr_ts (I := I) (M := M) g₀ 0 2
          (show (j - (k + 1)) + 1 = j - k from by omega) T x] at hK
        exact hK
      have hF : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + (k + 1)) x
          ((iteratedCovGrad (I := I) g₀ 1 1 (k + 1)
            (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x) ≤
          S (k + 1) * Combinatorics.antidiagonalTupleGrid b (k + 1) :=
        hS g₁ T htie hδ_le hδ0 hbound (k + 1) x
      have hgrid_nn : 0 ≤ Combinatorics.antidiagonalTupleGrid b (k + 1) :=
        Combinatorics.antidiagonalTupleGrid_nonneg b hb (k + 1)
      have hSk_le : S (k + 1) ≤ ∑ l ∈ Finset.range (j + 1), S l :=
        Finset.single_le_sum (f := S) (fun l _ => hS_nn l)
          (Finset.mem_range.mpr (by omega : k + 1 < j + 1))
      calc riemannianFiberNormSq (I := I) (M := M) g₀ (1 + (k + 1)) (2 + j) x
              ((appCcLeibnizPsi (I := I) (M := M) g₀ 1 2 (raisedKoszul (I := I) g₀ g₁) j
                (k + 1)).toSection x) *
            riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + (k + 1)) x
              ((iteratedCovGrad (I := I) g₀ 1 1 (k + 1)
                (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x)
          ≤ (appCcGdiag (E := E) j * (10 * b (j - k))) *
              (S (k + 1) * Combinatorics.antidiagonalTupleGrid b (k + 1)) := by
            refine mul_le_mul hPsi hF
              (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 (1 + (k + 1)) x _) ?_
            have h10 : (0 : ℝ) ≤ 10 * b (j - k) := by
              have := hb (j - k); linarith
            exact mul_nonneg (appCcGdiag_nonneg (E := E) j) h10
        _ ≤ (appCcGdiag (E := E) j * (10 * b (j - k))) *
              ((∑ l ∈ Finset.range (j + 1), S l) *
                Combinatorics.antidiagonalTupleGrid b (k + 1)) := by
            refine mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hSk_le hgrid_nn) ?_
            have h10 : (0 : ℝ) ≤ 10 * b (j - k) := by
              have := hb (j - k); linarith
            exact mul_nonneg (appCcGdiag_nonneg (E := E) j) h10
        _ = appCcGdiag (E := E) j * (10 * ∑ l ∈ Finset.range (j + 1), S l) *
              (b (j - k) * Combinatorics.antidiagonalTupleGrid b (k + 1)) := by ring
    refine le_trans (mul_le_mul_of_nonneg_left hstep (Nat.cast_nonneg j)) (le_of_eq ?_)
    rw [← Finset.mul_sum]
    ring

private def connDiffArmFieldPt (g₀ g₁ : SmoothRiemannianMetric I M) :
    ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x)) :=
  ⟨fun x : M => PDE.DeTurck.connDiff (I := I) g₁ g₀ x,
    bilinEndoField_contMDiff (I := I) (M := M)
      (fun x : M => PDE.DeTurck.connDiff (I := I) g₁ g₀ x)
      (fun V0 W => PDE.DeTurck.connDiff_contMDiff (I := I) g₁ g₀ V0.contMDiff W.contMDiff)⟩

set_option linter.unusedSectionVars false in
private lemma connDiffArmFieldPt_apply (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    connDiffArmFieldPt (I := I) (M := M) g₀ g₁ x = PDE.DeTurck.connDiff (I := I) g₁ g₀ x := rfl

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
private lemma connDiffSection_eq_armSlotEndoCc_zero (g₀ g₁ : SmoothRiemannianMetric I M) :
    connDiffSection (I := I) g₁ g₀ =
      armSlotEndoCc (I := I) (M := M) g₀ 0 (connDiffArmFieldPt (I := I) (M := M) g₀ g₁) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro om
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        (armSlotEndoCc (I := I) (M := M) g₀ 0
          (connDiffArmFieldPt (I := I) (M := M) g₀ g₁)).toSection x) om) =
      armSlotFib (I := I) (M := M) 0 x (connDiffArmFieldPt (I := I) (M := M) g₀ g₁ x) om
      from rfl]
  rw [armSlotFib_apply_eval (I := I) (M := M) 0 x
    (connDiffArmFieldPt (I := I) (M := M) g₀ g₁ x) om v]
  rw [slotInsertEndoFib_apply_eval]
  rw [show (Function.update (Matrix.vecTail (fun k : Fin 2 => (v k : E))) 0
        (connDiffArmFieldPt (I := I) (M := M) g₀ g₁ x (v 0)
          (Matrix.vecTail (fun k : Fin 2 => (v k : E)) 0))) =
      (fun _ : Fin 1 => (show E from
        PDE.DeTurck.connDiff (I := I) g₁ g₀ x (v 0) (v 1))) from by
    funext k
    rw [show k = (0 : Fin 1) from Subsingleton.elim k 0]
    rw [Function.update_self]
    rfl]
  rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        (connDiffSection (I := I) g₁ g₀).toSection x) om) =
      connDiffPairing (I := I) g₁ g₀ x om from rfl]
  change connDiffPairing (I := I) g₁ g₀ x om v = _
  rw [connDiffPairing_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
private lemma armSlotEndoCc_one_eq_reindex_slotExtend (g₀ : SmoothRiemannianMetric I M)
    (Arm : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x))) :
    armSlotEndoCc (I := I) (M := M) g₀ 1 Arm =
      reindexCoeffGen (I := I) (M := M) g₀ 2 3
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 3 (finRotate 3).symm
          (slotExtend (I := I) (M := M) g₀ 1 2 (armSlotEndoCc (I := I) (M := M) g₀ 0 Arm)))
        (Equiv.swap (0 : Fin 2) 1) := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro w
  have hτ0 : (finRotate 3).symm (0 : Fin 3) = (2 : Fin 3) := by decide
  have hτ1 : (finRotate 3).symm (1 : Fin 3) = (0 : Fin 3) := by decide
  have hτ2 : (finRotate 3).symm (2 : Fin 3) = (1 : Fin 3) := by decide
  set D' : Tensor0SSpace 2 I x := Tensor0SSpace.ofModel
    (ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
      (Tensor0SSpace.toModel D)) with hD'_def
  have hLHS : Tensor0SSpace.toModel
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
        (armSlotEndoCc (I := I) (M := M) g₀ 1 Arm).toSection x) D) w =
      Tensor0SSpace.toModel D
        (Function.update (Matrix.vecTail w) 0 (Arm x (w 0) (Matrix.vecTail w 0))) := by
    rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
          (armSlotEndoCc (I := I) (M := M) g₀ 1 Arm).toSection x) D) =
        armSlotFib (I := I) (M := M) 1 x (Arm x) D from rfl]
    rw [armSlotFib_apply_eval (I := I) (M := M) 1 x (Arm x) D w]
    rw [slotInsertEndoFib_apply_eval]
  have e1 : Tensor0SSpace.toModel
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
        (reindexCoeffGen (I := I) (M := M) g₀ 2 3
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 3 (finRotate 3).symm
            (slotExtend (I := I) (M := M) g₀ 1 2 (armSlotEndoCc (I := I) (M := M) g₀ 0 Arm)))
          (Equiv.swap (0 : Fin 2) 1)).toSection x) D) w =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
          rsDomDomCongr (finRotate 3).symm
            ((slotExtend (I := I) (M := M) g₀ 1 2
              (armSlotEndoCc (I := I) (M := M) g₀ 0 Arm)).toSection x)) D') w := by
    have h1 : ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
        (reindexCoeffGen (I := I) (M := M) g₀ 2 3
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 3 (finRotate 3).symm
            (slotExtend (I := I) (M := M) g₀ 1 2 (armSlotEndoCc (I := I) (M := M) g₀ 0 Arm)))
          (Equiv.swap (0 : Fin 2) 1)).toSection x) D) =
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
          rsDomDomCongr (finRotate 3).symm
            ((slotExtend (I := I) (M := M) g₀ 1 2
              (armSlotEndoCc (I := I) (M := M) g₀ 0 Arm)).toSection x)) D') := by
      rw [reindexCoeffGen_toSection]
      rw [reindexCoeffFibGen_apply (I := I) 2 3 (Equiv.swap (0 : Fin 2) 1) x
        (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 3 (finRotate 3).symm
            (slotExtend (I := I) (M := M) g₀ 1 2
              (armSlotEndoCc (I := I) (M := M) g₀ 0 Arm))).toSection x) D]
      rw [← hD'_def]
      rw [rsDomDomCongrSection_toSection]
    exact congrArg (fun t : Tensor0SSpace 3 I x => Tensor0SSpace.toModel t w) h1
  have e2 : Tensor0SSpace.toModel
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
        rsDomDomCongr (finRotate 3).symm
          ((slotExtend (I := I) (M := M) g₀ 1 2
            (armSlotEndoCc (I := I) (M := M) g₀ 0 Arm)).toSection x)) D') w =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
          (slotExtend (I := I) (M := M) g₀ 1 2
            (armSlotEndoCc (I := I) (M := M) g₀ 0 Arm)).toSection x) D')
        (fun i => w ((finRotate 3).symm i)) := by
    rw [toModel_rsDomDomCongr_apply (I := I) (M := M) (finRotate 3).symm
      ((slotExtend (I := I) (M := M) g₀ 1 2
        (armSlotEndoCc (I := I) (M := M) g₀ 0 Arm)).toSection x) D']
    rw [ContinuousMultilinearMap.domDomCongr_apply]
  have e3 : Tensor0SSpace.toModel
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
        (slotExtend (I := I) (M := M) g₀ 1 2
          (armSlotEndoCc (I := I) (M := M) g₀ 0 Arm)).toSection x) D')
      (fun i => w ((finRotate 3).symm i)) =
      Tensor0SSpace.toModel
        (armSlotFib (I := I) (M := M) 0 x (Arm x)
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D' (w ((finRotate 3).symm 0))))
        (Matrix.vecTail (fun i => w ((finRotate 3).symm i))) := by
    rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
          (slotExtend (I := I) (M := M) g₀ 1 2
            (armSlotEndoCc (I := I) (M := M) g₀ 0 Arm)).toSection x) D') =
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x).symm
          ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
              (armSlotEndoCc (I := I) (M := M) g₀ 0 Arm).toSection x).comp
            (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D')) from rfl]
    rw [show (fun i => w ((finRotate 3).symm i)) =
        Fin.cons (w ((finRotate 3).symm 0))
          (Matrix.vecTail (fun i => w ((finRotate 3).symm i))) from by
      funext k
      refine Fin.cases rfl (fun j => rfl) k]
    have hkey := TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (n := 2)
      (T := (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 2 x).symm
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
            (armSlotEndoCc (I := I) (M := M) g₀ 0 Arm).toSection x).comp
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D')))
      (v0 := w ((finRotate 3).symm 0))
      (vs := Matrix.vecTail (fun i => w ((finRotate 3).symm i)))
    rw [ContinuousLinearEquiv.apply_symm_apply] at hkey
    rw [← hkey]
    rfl
  have e4 : Tensor0SSpace.toModel
      (armSlotFib (I := I) (M := M) 0 x (Arm x)
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D' (w ((finRotate 3).symm 0))))
      (Matrix.vecTail (fun i => w ((finRotate 3).symm i))) =
      Tensor0SSpace.toModel
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D' (w ((finRotate 3).symm 0)))
        (fun _ : Fin 1 => (show E from
          Arm x (w ((finRotate 3).symm 1)) (w ((finRotate 3).symm 2)))) := by
    rw [armSlotFib_apply_eval (I := I) (M := M) 0 x (Arm x)
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D' (w ((finRotate 3).symm 0)))
      (Matrix.vecTail (fun i => w ((finRotate 3).symm i)))]
    rw [slotInsertEndoFib_apply_eval]
    congr 1
    funext k
    refine Fin.cases ?_ (fun j => j.elim0) k
    rw [Function.update_self]
    rfl
  have e5 : Tensor0SSpace.toModel
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D' (w ((finRotate 3).symm 0)))
      (fun _ : Fin 1 => (show E from
        Arm x (w ((finRotate 3).symm 1)) (w ((finRotate 3).symm 2)))) =
      Tensor0SSpace.toModel D'
        (Fin.cons (w ((finRotate 3).symm 0))
          (fun _ : Fin 1 => (show E from
            Arm x (w ((finRotate 3).symm 1)) (w ((finRotate 3).symm 2))))) :=
    TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (n := 1)
      (T := D') (v0 := w ((finRotate 3).symm 0))
      (vs := fun _ : Fin 1 => (show E from
        Arm x (w ((finRotate 3).symm 1)) (w ((finRotate 3).symm 2))))
  have e6 : Tensor0SSpace.toModel D'
      (Fin.cons (w ((finRotate 3).symm 0))
        (fun _ : Fin 1 => (show E from
          Arm x (w ((finRotate 3).symm 1)) (w ((finRotate 3).symm 2))))) =
      Tensor0SSpace.toModel D
        (Function.update (Matrix.vecTail w) 0 (Arm x (w 0) (Matrix.vecTail w 0))) := by
    rw [hD'_def, Tensor0SSpace.toModel_ofModel, ContinuousMultilinearMap.domDomCongr_apply]
    rw [hτ0, hτ1, hτ2]
    congr 1
    funext k
    refine Fin.cases ?_ ?_ k
    · rw [show (Function.update (Matrix.vecTail w) 0
            (Arm x (w 0) (Matrix.vecTail w 0)) (0 : Fin 2)) =
          Arm x (w 0) (Matrix.vecTail w 0) from Function.update_self _ _ _]
      rfl
    · intro j
      refine Fin.cases ?_ (fun j2 => j2.elim0) j
      rw [show (Fin.succ (0 : Fin 1)) = (1 : Fin 2) from rfl]
      rw [Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0)]
      rfl
  rw [hLHS, e1, e2, e3, e4, e5, e6]

set_option linter.unusedSectionVars false in
private lemma rfns_iteratedCovGrad_armSlotPass_connDiffArm_le
    (g₀ g₁ : SmoothRiemannianMetric I M) (j : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 2 (3 + j) x
        ((iteratedCovGrad (I := I) g₀ 2 3 j
          (armSlotEndoPassZeroCc (I := I) (M := M) g₀
            (connDiffArmFieldPt (I := I) (M := M) g₀ g₁))).toSection x) ≤
      (Module.finrank ℝ E : ℝ) *
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 1 2 j (connDiffSection (I := I) g₁ g₀)).toSection x) := by
  rw [riemannianFiberNormSq_iteratedCovGrad_armSlotEndoPassZeroCc_eq (I := I) (M := M) g₀
    (connDiffArmFieldPt (I := I) (M := M) g₀ g₁) j x]
  rw [armSlotEndoCc_one_eq_reindex_slotExtend (I := I) (M := M) g₀
    (connDiffArmFieldPt (I := I) (M := M) g₀ g₁)]
  rw [rfns_iteratedCovGrad_rsDomDomCongr_both_eq (I := I) (M := M) g₀ 2 3
    (Equiv.swap (0 : Fin 2) 1) (finRotate 3).symm
    (slotExtend (I := I) (M := M) g₀ 1 2
      (armSlotEndoCc (I := I) (M := M) g₀ 0 (connDiffArmFieldPt (I := I) (M := M) g₀ g₁))) j x]
  refine le_trans (rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 1 2
    (armSlotEndoCc (I := I) (M := M) g₀ 0 (connDiffArmFieldPt (I := I) (M := M) g₀ g₁)) j x) ?_
  rw [← connDiffSection_eq_armSlotEndoCc_zero (I := I) (M := M) g₀ g₁]

set_option linter.unusedVariables false in
theorem exists_rfns_iteratedCovGrad_connDiffSection_tgrid
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ CA : ℕ → ℝ, (∀ j, 0 ≤ CA j) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (j : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j) x
            ((iteratedCovGrad (I := I) g₀ 1 2 j
              (connDiffSection (I := I) g₁ g₀)).toSection x) ≤
          CA j * ∑ k ∈ Finset.range (j + 2),
            Combinatorics.antidiagonalTupleGrid
              (fun j' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j') x
                ((iteratedCovGrad (I := I) g₀ 0 2 j' T).toSection x)) k := by
  classical
  obtain ⟨S, hS_nn, hS⟩ := exists_rfns_iteratedCovGrad_sharpFlatEndoCc_tgrid
    (I := I) (M := M) g₀ hδ₀
  refine ⟨fun j => appCcGdiag (E := E) j *
      ∑ i ∈ Finset.range (j + 1), 10 * ∑ l ∈ Finset.range (j + 1 - i), S l,
    fun j => mul_nonneg (appCcGdiag_nonneg (E := E) j)
      (Finset.sum_nonneg fun i _ => mul_nonneg (by norm_num)
        (Finset.sum_nonneg fun l _ => hS_nn l)), ?_⟩
  intro g₁ T htie δ hδ_le hδ0 hbound j x
  set b : ℕ → ℝ := fun j' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j') x
    ((iteratedCovGrad (I := I) g₀ 0 2 j' T).toSection x) with hb_def
  have hb : ∀ j', 0 ≤ b j' :=
    fun j' => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + j') x _
  set G : ℝ := ∑ k ∈ Finset.range (j + 2), Combinatorics.antidiagonalTupleGrid b k with hG_def
  clear_value G
  have hG_nn : 0 ≤ G := by
    rw [hG_def]
    exact Finset.sum_nonneg fun k _ => Combinatorics.antidiagonalTupleGrid_nonneg b hb k
  have hcell : ∀ i ∈ Finset.range (j + 1), ∀ l ∈ Finset.range (j + 1 - i),
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 1 2 i (raisedKoszul (I := I) g₀ g₁)).toSection x) *
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
          ((iteratedCovGrad (I := I) g₀ 1 1 l (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x) ≤
      (10 * S l) * G := by
    intro i hi l hl
    have h1 := rfns_iteratedCovGrad_raisedKoszul_pointwise (I := I) (M := M) g₀ g₁ T htie i x
    have h2 := hS g₁ T htie hδ_le hδ0 hbound l x
    have h1_nn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 (2 + i) x
      ((iteratedCovGrad (I := I) g₀ 1 2 i (raisedKoszul (I := I) g₀ g₁)).toSection x)
    have h2_nn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 (1 + l) x
      ((iteratedCovGrad (I := I) g₀ 1 1 l (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x)
    have hb_le_grid : b (i + 1) * Combinatorics.antidiagonalTupleGrid b l ≤
        Combinatorics.antidiagonalTupleGrid b (l + (i + 1)) :=
      Combinatorics.single_factor_mul_antidiagonalTupleGrid_le b hb l (i + 1) (by omega)
    have hgrid_le_G : Combinatorics.antidiagonalTupleGrid b (l + (i + 1)) ≤ G := by
      rw [hG_def]
      refine Finset.single_le_sum
        (f := fun k => Combinatorics.antidiagonalTupleGrid b k)
        (fun k _ => Combinatorics.antidiagonalTupleGrid_nonneg b hb k) ?_
      rw [Finset.mem_range] at hi hl ⊢
      omega
    calc riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 1 2 i (raisedKoszul (I := I) g₀ g₁)).toSection x) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
            ((iteratedCovGrad (I := I) g₀ 1 1 l (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x)
        ≤ (10 * b (i + 1)) * (S l * Combinatorics.antidiagonalTupleGrid b l) := by
          refine mul_le_mul ?_ h2 h2_nn (by
            have := hb (i + 1); linarith)
          exact h1
      _ = (10 * S l) * (b (i + 1) * Combinatorics.antidiagonalTupleGrid b l) := by ring
      _ ≤ (10 * S l) * Combinatorics.antidiagonalTupleGrid b (l + (i + 1)) := by
          refine mul_le_mul_of_nonneg_left hb_le_grid ?_
          have := hS_nn l; linarith
      _ ≤ (10 * S l) * G := by
          refine mul_le_mul_of_nonneg_left hgrid_le_G ?_
          have := hS_nn l; linarith
  refine le_trans (rfns_iteratedCovGrad_connDiffSection_diagonalProductGrid_le
    (I := I) (M := M) g₀ g₁ j x) ?_
  have hsum : (∑ i ∈ Finset.range (j + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 1 2 i (raisedKoszul (I := I) g₀ g₁)).toSection x) *
          ∑ l ∈ Finset.range (j + 1 - i),
            riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
              ((iteratedCovGrad (I := I) g₀ 1 1 l
                (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x)) ≤
      (∑ i ∈ Finset.range (j + 1), 10 * ∑ l ∈ Finset.range (j + 1 - i), S l) * G := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i hi => ?_
    rw [Finset.mul_sum]
    calc (∑ l ∈ Finset.range (j + 1 - i),
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
              ((iteratedCovGrad (I := I) g₀ 1 2 i (raisedKoszul (I := I) g₀ g₁)).toSection x) *
            riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
              ((iteratedCovGrad (I := I) g₀ 1 1 l
                (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x))
        ≤ ∑ l ∈ Finset.range (j + 1 - i), (10 * S l) * G :=
          Finset.sum_le_sum fun l hl => hcell i hi l hl
      _ = (10 * ∑ l ∈ Finset.range (j + 1 - i), S l) * G := by
          rw [Finset.mul_sum, Finset.sum_mul]
  calc appCcGdiag (E := E) j *
        ∑ i ∈ Finset.range (j + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
              ((iteratedCovGrad (I := I) g₀ 1 2 i (raisedKoszul (I := I) g₀ g₁)).toSection x) *
            ∑ l ∈ Finset.range (j + 1 - i),
              riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
                ((iteratedCovGrad (I := I) g₀ 1 1 l
                  (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x)
      ≤ appCcGdiag (E := E) j *
          ((∑ i ∈ Finset.range (j + 1), 10 * ∑ l ∈ Finset.range (j + 1 - i), S l) * G) :=
        mul_le_mul_of_nonneg_left hsum (appCcGdiag_nonneg (E := E) j)
    _ = (appCcGdiag (E := E) j *
          ∑ i ∈ Finset.range (j + 1), 10 * ∑ l ∈ Finset.range (j + 1 - i), S l) * G := by
        ring

private def quadraticConnDiffCc (g₀ g₁ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 1 3 :=
  appCcRS (I := I) (M := M) g₀ 1 2 3
    (armSlotEndoPassZeroCc (I := I) (M := M) g₀ (connDiffArmFieldPt (I := I) (M := M) g₀ g₁))
    (connDiffSection (I := I) g₁ g₀)

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
private lemma quadraticConnDiffCc_toModel (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (om : Tensor0SSpace 1 I x) (w : Fin 3 → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
          (quadraticConnDiffCc (I := I) (M := M) g₀ g₁).toSection x) om) w =
      cotangentToDual (I := I) (x := x) om
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (w 1) (w 2)) (w 0)) := by
  rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
        (quadraticConnDiffCc (I := I) (M := M) g₀ g₁).toSection x) om) =
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
        (appCcRS (I := I) (M := M) g₀ 1 2 3
          (armSlotEndoPassZeroCc (I := I) (M := M) g₀
            (connDiffArmFieldPt (I := I) (M := M) g₀ g₁))
          (connDiffSection (I := I) g₁ g₀)).toSection x) om) from rfl]
  rw [toModel_appCcRS_armSlotEndoPassZeroCc_eval (I := I) (M := M) g₀
    (connDiffArmFieldPt (I := I) (M := M) g₀ g₁) (connDiffSection (I := I) g₁ g₀) x om w]
  rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        (connDiffSection (I := I) g₁ g₀).toSection x) om) =
      connDiffPairing (I := I) g₁ g₀ x om from rfl]
  have hchg : Tensor0SSpace.toModel (connDiffPairing (I := I) g₁ g₀ x om)
      (fun j : Fin 2 => if j = 0 then
        connDiffArmFieldPt (I := I) (M := M) g₀ g₁ x (w 1) (w 2) else w 0) =
      connDiffPairing (I := I) g₁ g₀ x om
        (fun j : Fin 2 => if j = 0 then
          connDiffArmFieldPt (I := I) (M := M) g₀ g₁ x (w 1) (w 2) else w 0) := rfl
  rw [hchg]
  rw [show (fun j : Fin 2 => if j = 0 then
        connDiffArmFieldPt (I := I) (M := M) g₀ g₁ x (w 1) (w 2) else w 0) =
      (Fin.cons (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (w 1) (w 2))
        (fun _ : Fin 1 => w 0) : Fin 2 → TangentSpace I x) from by
    funext j
    refine Fin.cases ?_ ?_ j
    · rw [if_pos rfl]
      rfl
    · intro i
      rw [if_neg (Fin.succ_ne_zero i)]
      rfl]
  rw [connDiffPairing_apply]
  rw [cotangentToDual_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
private def covectorExtensionSection (g₀ : SmoothRiemannianMetric I M) (x : M)
    (om : Tensor0SSpace 1 I x) :
    Cₛ^∞⟮I; Tensor0SModel 1 ℝ E, (fun y : M => Tensor0SSpace 1 I y)⟯ :=
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 1
  ⟨fun b : M => g0FlatCLM (I := I) g₀ b
      (smoothExtensionTangent (I := I) x (inverseMetricSharpFib (I := I) g₀ x om) b),
   by
     have hU : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
         (fun b : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) b
           (smoothExtensionTangent (I := I) x (inverseMetricSharpFib (I := I) g₀ x om) b)) :=
       smoothExtensionTangent_contMDiff (I := I) x (inverseMetricSharpFib (I := I) g₀ x om)
     exact ContMDiff.clm_bundle_apply (b := id) (g0FlatField_contMDiff (I := I) g₀) hU⟩

set_option linter.unusedSectionVars false in
private lemma covectorExtensionSection_self (g₀ : SmoothRiemannianMetric I M) (x : M)
    (om : Tensor0SSpace 1 I x) :
    covectorExtensionSection (I := I) (M := M) g₀ x om x = om := by
  change g0FlatCLM (I := I) g₀ x
      (smoothExtensionTangent (I := I) x (inverseMetricSharpFib (I := I) g₀ x om) x) = om
  rw [smoothExtensionTangent_eq (I := I) x (inverseMetricSharpFib (I := I) g₀ x om)]
  exact g0FlatCLM_inverseMetricSharpFib (I := I) g₀ x om

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
set_option maxHeartbeats 12800000 in
private theorem riemannLoweredBackgroundDifference_palatini_repr
    (g₀ g₁ : SmoothRiemannianMetric I M) :
    cometricRaiseSlot0Field (I := I) (M := M) g₀ 2
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
          (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)) =
      rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (Equiv.swap (1 : Fin 3) 2)
          (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀) +
            quadraticConnDiffCc (I := I) (M := M) g₀ g₁) -
        rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (finRotate 3)
          (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀) +
            quadraticConnDiffCc (I := I) (M := M) g₀ g₁) := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro om
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  set X0 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    smoothExtensionTangentSection (I := I) (M := M) x (v 0) with hX0_def
  set X1 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    smoothExtensionTangentSection (I := I) (M := M) x (v 1) with hX1_def
  set X2 : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    smoothExtensionTangentSection (I := I) (M := M) x (v 2) with hX2_def
  have hX0x : X0 x = v 0 := smoothExtensionTangent_eq (I := I) x (v 0)
  have hX1x : X1 x = v 1 := smoothExtensionTangent_eq (I := I) x (v 1)
  have hX2x : X2 x = v 2 := smoothExtensionTangent_eq (I := I) x (v 2)
  set omSec : Cₛ^∞⟮I; Tensor0SModel 1 ℝ E, (fun y : M => Tensor0SSpace 1 I y)⟯ :=
    covectorExtensionSection (I := I) (M := M) g₀ x om with homSec_def
  have homx : omSec x = om := covectorExtensionSection_self (I := I) (M := M) g₀ x om
  set u : TangentSpace I x := inverseMetricSharpFib (I := I) g₀ x om with hu_def
  have hpair : ∀ ww : TangentSpace I x,
      g₀.inner x ww u = cotangentToDual (I := I) (x := x) om ww := by
    intro ww
    rw [hu_def]
    rw [g₀.symm x ww (inverseMetricSharpFib (I := I) g₀ x om)]
    rw [g0_inner_inverseMetricSharp_mixed (I := I) (M := M) g₀ g₀ x om ww]
    rw [show gInvRaisedEndo (I := I) g₀ g₀ x ww = ww from by
      rw [gInvRaisedEndo_apply, inverseMetricSharpFib_g0FlatCLM]]
  have hDQ : ∀ (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯),
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
          ((covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀) +
            quadraticConnDiffCc (I := I) (M := M) g₀ g₁)).toSection x) om)
        (Fin.cons (X x) (Fin.cons (Y x) ![Z x])) =
      cotangentToDual (I := I) (x := x) om
          (covDerivConnDiff (I := I) g₀ g₁ (fun b => X b) (fun b => Z b) (fun b => Y b) x) +
        cotangentToDual (I := I) (x := x) om
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Y x) (Z x)) (X x)) := by
    intro X Y Z
    have hsplit : ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
        ((covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀) +
          quadraticConnDiffCc (I := I) (M := M) g₀ g₁)).toSection x) om) =
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
          (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀)).toSection x) om) +
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
          (quadraticConnDiffCc (I := I) (M := M) g₀ g₁).toSection x) om) := by
      rw [SmoothCcTensor.toSection_add]
      rfl
    rw [hsplit, Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply]
    have hbridge : Tensor0SSpace.toModel
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
          (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀)).toSection x) om)
        (Fin.cons (X x) (Fin.cons (Y x) ![Z x])) =
        cotangentToDual (I := I) (x := x) om
          (covDerivConnDiff (I := I) g₀ g₁ (fun b => X b) (fun b => Z b) (fun b => Y b) x) := by
      rw [← homx]
      rw [connDiffSection_covGrad_eq_covDerivConnDiff (I := I) (M := M) g₁ g₀ omSec X Y Z x]
      rw [cotangentToDual_apply]
    rw [hbridge]
    rw [quadraticConnDiffCc_toModel (I := I) (M := M) g₀ g₁ x om
      (Fin.cons (X x) (Fin.cons (Y x) ![Z x]))]
    rfl
  have htor : (LeviCivita (I := I) g₀).torsion = 0 := LeviCivita_torsion_eq_zero (I := I) g₀
  have hpal := riemannSec_difference (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁)
    (X := fun b => X0 b) (Y := fun b => X1 b) (Z := fun b => X2 b)
    X0.contMDiff X1.contMDiff X2.contMDiff htor x
  have hop1 : riemannOp (LeviCivita (I := I) g₁) x (v 0) (v 1) (v 2) =
      riemannSec (LeviCivita (I := I) g₁) (fun b => X0 b) (fun b => X1 b) (fun b => X2 b) x := by
    rw [← hX0x, ← hX1x, ← hX2x]
    exact riemannOp_apply_smooth (cov := LeviCivita (I := I) g₁)
      X0.contMDiff X1.contMDiff X2.contMDiff
  have hop0 : riemannOp (LeviCivita (I := I) g₀) x (v 0) (v 1) (v 2) =
      riemannSec (LeviCivita (I := I) g₀) (fun b => X0 b) (fun b => X1 b) (fun b => X2 b) x := by
    rw [← hX0x, ← hX1x, ← hX2x]
    exact riemannOp_apply_smooth (cov := LeviCivita (I := I) g₀)
      X0.contMDiff X1.contMDiff X2.contMDiff
  have hLHS : Tensor0SSpace.toModel
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
        (cometricRaiseSlot0Field (I := I) (M := M) g₀ 2
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
            (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁))).toSection x) om) v =
      g₀.inner x (riemannOp (LeviCivita (I := I) g₁) x (v 0) (v 1) (v 2)) u -
        g₀.inner x (riemannOp (LeviCivita (I := I) g₀) x (v 0) (v 1) (v 2)) u := by
    rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
          (cometricRaiseSlot0Field (I := I) (M := M) g₀ 2
            (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
              (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁))).toSection x) om) =
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
          cometricRaiseSlot0Fib g₀ 2 x
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from
              (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
                (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)).toSection x)
              (unitTensor (I := I) (M := M) x))) om) from rfl]
    rw [cometricRaiseSlot0Fib_clm_apply (I := I) g₀ 2 x
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
          (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)).toSection x)
        (unitTensor (I := I) (M := M) x)) om]
    rw [interiorProduct_toModel_eval_pal (I := I) (M := M) 3 x
      (inverseMetricSharpFib (I := I) g₀ x om) _ v]
    rw [show Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
            (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)).toSection x)
          (unitTensor (I := I) (M := M) x)) =
        unitModel (I := I) (M := M) g₀ 4
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
            (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)) x from rfl]
    rw [domDomCongrSection_unitModel (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
      (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁) x]
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    rw [show (fun i : Fin 4 =>
        (Fin.cons (show E from inverseMetricSharpFib (I := I) g₀ x om)
          (fun k => (show E from v k)) : Fin 4 → E) ((Equiv.swap (0 : Fin 4) 1) i)) =
      (![v 0, (show E from u), v 1, v 2] : Fin 4 → E) from by
      funext i
      fin_cases i <;> rfl]
    rw [riemannLoweredBackgroundDifference_unitModel_apply (I := I) (M := M) g₀ g₁ x
      (![v 0, (show E from u), v 1, v 2] : Fin 4 → TangentSpace I x)]
    rfl
  rw [hLHS]
  have hRHSsub : Tensor0SSpace.toModel
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
        (rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (Equiv.swap (1 : Fin 3) 2)
            (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀) +
              quadraticConnDiffCc (I := I) (M := M) g₀ g₁) -
          rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (finRotate 3)
            (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀) +
              quadraticConnDiffCc (I := I) (M := M) g₀ g₁)).toSection x) om) v =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
          (rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (Equiv.swap (1 : Fin 3) 2)
            (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀) +
              quadraticConnDiffCc (I := I) (M := M) g₀ g₁)).toSection x) om) v -
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
          (rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (finRotate 3)
            (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀) +
              quadraticConnDiffCc (I := I) (M := M) g₀ g₁)).toSection x) om) v := by
    rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
        (rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (Equiv.swap (1 : Fin 3) 2)
            (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀) +
              quadraticConnDiffCc (I := I) (M := M) g₀ g₁) -
          rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (finRotate 3)
            (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀) +
              quadraticConnDiffCc (I := I) (M := M) g₀ g₁)).toSection x) om) =
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
          (rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (Equiv.swap (1 : Fin 3) 2)
            (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀) +
              quadraticConnDiffCc (I := I) (M := M) g₀ g₁)).toSection x) om) -
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
          (rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (finRotate 3)
            (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀) +
              quadraticConnDiffCc (I := I) (M := M) g₀ g₁)).toSection x) om) from by
      rw [SmoothCcTensor.toSection_sub]
      rfl]
    rw [Tensor0SSpace.toModel_sub, ContinuousMultilinearMap.sub_apply]
  rw [hRHSsub]
  have hterm : ∀ (σ : Equiv.Perm (Fin 3)) (X Y Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯),
      ((fun i => v (σ i)) : Fin 3 → E) = Fin.cons (X x) (Fin.cons (Y x) ![Z x]) →
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
          (rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 σ
            (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀) +
              quadraticConnDiffCc (I := I) (M := M) g₀ g₁)).toSection x) om) v =
      cotangentToDual (I := I) (x := x) om
          (covDerivConnDiff (I := I) g₀ g₁ (fun b => X b) (fun b => Z b) (fun b => Y b) x) +
        cotangentToDual (I := I) (x := x) om
          (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Y x) (Z x)) (X x)) := by
    intro σ X Y Z htup
    rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
        (rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 σ
          (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀) +
            quadraticConnDiffCc (I := I) (M := M) g₀ g₁)).toSection x) om) =
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
          rsDomDomCongr σ
            ((covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀) +
              quadraticConnDiffCc (I := I) (M := M) g₀ g₁).toSection x)) om) from by
      rw [rsDomDomCongrSection_toSection]]
    rw [toModel_rsDomDomCongr_apply (I := I) (M := M) σ
      ((covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀) +
        quadraticConnDiffCc (I := I) (M := M) g₀ g₁).toSection x) om]
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    rw [htup]
    exact hDQ X Y Z
  have htup1 : ((fun i => v ((Equiv.swap (1 : Fin 3) 2) i)) : Fin 3 → E) =
      Fin.cons (X0 x) (Fin.cons (X2 x) ![X1 x]) := by
    funext k
    refine Fin.cases ?_ ?_ k
    · rw [show ((Equiv.swap (1 : Fin 3) 2) 0) = (0 : Fin 3) from by decide]
      rw [show (Fin.cons (X0 x) (Fin.cons (X2 x) ![X1 x]) : Fin 3 → E) 0 = X0 x from rfl]
      rw [hX0x]
    · intro j
      refine Fin.cases ?_ ?_ j
      · rw [show (Fin.succ (0 : Fin 2)) = (1 : Fin 3) from rfl]
        rw [show ((Equiv.swap (1 : Fin 3) 2) 1) = (2 : Fin 3) from by decide]
        rw [show (Fin.cons (X0 x) (Fin.cons (X2 x) ![X1 x]) : Fin 3 → E) 1 = X2 x from rfl]
        rw [hX2x]
      · intro j2
        refine Fin.cases ?_ (fun j3 => j3.elim0) j2
        rw [show (Fin.succ (Fin.succ (0 : Fin 1))) = (2 : Fin 3) from rfl]
        rw [show ((Equiv.swap (1 : Fin 3) 2) 2) = (1 : Fin 3) from by decide]
        rw [show (Fin.cons (X0 x) (Fin.cons (X2 x) ![X1 x]) : Fin 3 → E) 2 = X1 x from rfl]
        rw [hX1x]
  have htup2 : ((fun i => v ((finRotate 3) i)) : Fin 3 → E) =
      Fin.cons (X1 x) (Fin.cons (X2 x) ![X0 x]) := by
    funext k
    refine Fin.cases ?_ ?_ k
    · rw [show ((finRotate 3) 0) = (1 : Fin 3) from by decide]
      rw [show (Fin.cons (X1 x) (Fin.cons (X2 x) ![X0 x]) : Fin 3 → E) 0 = X1 x from rfl]
      rw [hX1x]
    · intro j
      refine Fin.cases ?_ ?_ j
      · rw [show (Fin.succ (0 : Fin 2)) = (1 : Fin 3) from rfl]
        rw [show ((finRotate 3) 1) = (2 : Fin 3) from by decide]
        rw [show (Fin.cons (X1 x) (Fin.cons (X2 x) ![X0 x]) : Fin 3 → E) 1 = X2 x from rfl]
        rw [hX2x]
      · intro j2
        refine Fin.cases ?_ (fun j3 => j3.elim0) j2
        rw [show (Fin.succ (Fin.succ (0 : Fin 1))) = (2 : Fin 3) from rfl]
        rw [show ((finRotate 3) 2) = (0 : Fin 3) from by decide]
        rw [show (Fin.cons (X1 x) (Fin.cons (X2 x) ![X0 x]) : Fin 3 → E) 2 = X0 x from rfl]
        rw [hX0x]
  rw [hterm (Equiv.swap (1 : Fin 3) 2) X0 X2 X1 htup1]
  rw [hterm (finRotate 3) X1 X2 X0 htup2]
  rw [hop1, hop0]
  rw [hpal]
  rw [map_add (g₀.inner x), ContinuousLinearMap.add_apply]
  rw [map_add (g₀.inner x), ContinuousLinearMap.add_apply]
  rw [map_sub (g₀.inner x), ContinuousLinearMap.sub_apply]
  rw [map_sub (g₀.inner x), ContinuousLinearMap.sub_apply]
  simp only [hpair]
  have hc1 : covDerivConnDiff (I := I) g₀ g₁
      (fun b => X0 b) (fun b => X1 b) (fun b => X2 b) x =
      covDerivDiff (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁)
        (fun b => X0 b) (fun b => X1 b) (fun b => X2 b) x := rfl
  have hc2 : covDerivConnDiff (I := I) g₀ g₁
      (fun b => X1 b) (fun b => X0 b) (fun b => X2 b) x =
      covDerivDiff (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁)
        (fun b => X1 b) (fun b => X0 b) (fun b => X2 b) x := rfl
  have hq1 : PDE.DeTurck.connDiff (I := I) g₁ g₀ x
      (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (X2 x) (X1 x)) (X0 x) =
      CovariantDerivative.difference (LeviCivita (I := I) g₁) (LeviCivita (I := I) g₀) x
        (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁)
          (fun b => X1 b) (fun b => X2 b) x) ((fun b => X0 b) x) := rfl
  have hq2 : PDE.DeTurck.connDiff (I := I) g₁ g₀ x
      (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (X2 x) (X0 x)) (X1 x) =
      CovariantDerivative.difference (LeviCivita (I := I) g₁) (LeviCivita (I := I) g₀) x
        (diffSec (LeviCivita (I := I) g₀) (LeviCivita (I := I) g₁)
          (fun b => X0 b) (fun b => X2 b) x) ((fun b => X1 b) x) := rfl
  rw [← hc1, ← hc2, ← hq1, ← hq2]
  ring

private def gridSumPairCount (m1 m2 : ℕ) : ℝ :=
  ∑ k1 ∈ Finset.range m1, ∑ k2 ∈ Finset.range m2, tGridCount k1 * tGridCount k2

private lemma gridSumPairCount_nonneg (m1 m2 : ℕ) : 0 ≤ gridSumPairCount m1 m2 :=
  Finset.sum_nonneg fun k1 _ => Finset.sum_nonneg fun k2 _ =>
    mul_nonneg (tGridCount_nonneg k1) (tGridCount_nonneg k2)

private lemma gridSum_mul_gridSum_le (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) (m1 m2 m3 : ℕ)
    (h3 : m1 + m2 ≤ m3 + 1) :
    (∑ k ∈ Finset.range m1, Combinatorics.antidiagonalTupleGrid b k) *
      (∑ k ∈ Finset.range m2, Combinatorics.antidiagonalTupleGrid b k) ≤
    gridSumPairCount m1 m2 * ∑ k ∈ Finset.range m3, Combinatorics.antidiagonalTupleGrid b k := by
  classical
  have hG_nn : ∀ k, 0 ≤ Combinatorics.antidiagonalTupleGrid b k :=
    fun k => Combinatorics.antidiagonalTupleGrid_nonneg b hb k
  have hS3_nn : 0 ≤ ∑ k ∈ Finset.range m3, Combinatorics.antidiagonalTupleGrid b k :=
    Finset.sum_nonneg fun k _ => hG_nn k
  rw [Finset.sum_mul]
  rw [gridSumPairCount, Finset.sum_mul]
  refine Finset.sum_le_sum fun k1 hk1 => ?_
  calc Combinatorics.antidiagonalTupleGrid b k1 *
        ∑ k ∈ Finset.range m2, Combinatorics.antidiagonalTupleGrid b k
      = ∑ k2 ∈ Finset.range m2, Combinatorics.antidiagonalTupleGrid b k1 *
          Combinatorics.antidiagonalTupleGrid b k2 := by rw [Finset.mul_sum]
    _ ≤ ∑ k2 ∈ Finset.range m2, (tGridCount k1 * tGridCount k2) *
          (∑ k ∈ Finset.range m3, Combinatorics.antidiagonalTupleGrid b k) := by
        refine Finset.sum_le_sum fun k2 hk2 => ?_
        refine le_trans (antidiagonalTupleGrid_mul_le b hb k1 k2) ?_
        refine mul_le_mul_of_nonneg_left ?_
          (mul_nonneg (tGridCount_nonneg k1) (tGridCount_nonneg k2))
        refine Finset.single_le_sum (f := fun k => Combinatorics.antidiagonalTupleGrid b k)
          (fun k _ => hG_nn k) ?_
        rw [Finset.mem_range] at hk1 hk2 ⊢
        omega
    _ = (∑ k2 ∈ Finset.range m2, tGridCount k1 * tGridCount k2) *
          (∑ k ∈ Finset.range m3, Combinatorics.antidiagonalTupleGrid b k) := by
        rw [Finset.sum_mul]

set_option backward.isDefEq.respectTransparency false in
private def perturbationSharpEndoFib (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => metricSharp (I := I) g₀ x
        (ccTensorBilinSymm (I := I) g₀ T x v).toLinearMap
      map_add' := fun v v' => by
        have h : ((ccTensorBilinSymm (I := I) g₀ T x (v + v')).toLinearMap) =
            (ccTensorBilinSymm (I := I) g₀ T x v).toLinearMap +
              (ccTensorBilinSymm (I := I) g₀ T x v').toLinearMap := by
          ext w
          simp [map_add]
        rw [show metricSharp (I := I) g₀ x
            (ccTensorBilinSymm (I := I) g₀ T x (v + v')).toLinearMap =
            (metricFlatMap (I := I) g₀ x).symm
              (ccTensorBilinSymm (I := I) g₀ T x (v + v')).toLinearMap from rfl,
          h, map_add]
        rfl
      map_smul' := fun c v => by
        have h : ((ccTensorBilinSymm (I := I) g₀ T x (c • v)).toLinearMap) =
            c • (ccTensorBilinSymm (I := I) g₀ T x v).toLinearMap := by
          ext w
          simp [map_smul]
        rw [show metricSharp (I := I) g₀ x
            (ccTensorBilinSymm (I := I) g₀ T x (c • v)).toLinearMap =
            (metricFlatMap (I := I) g₀ x).symm
              (ccTensorBilinSymm (I := I) g₀ T x (c • v)).toLinearMap from rfl,
          h, map_smul]
        rfl }

set_option linter.unusedSectionVars false in
private lemma perturbationSharpEndoFib_apply (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (x : M) (v : TangentSpace I x) :
    perturbationSharpEndoFib (I := I) (M := M) g₀ T x v =
      metricSharp (I := I) g₀ x (ccTensorBilinSymm (I := I) g₀ T x v).toLinearMap := by
  rw [perturbationSharpEndoFib, LinearMap.coe_toContinuousLinearMap']
  rfl

set_option linter.unusedSectionVars false in
private lemma inner_perturbationSharpEndoFib (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (x : M) (v w : TangentSpace I x) :
    g₀.inner x (perturbationSharpEndoFib (I := I) (M := M) g₀ T x v) w =
      ccTensorBilinSymm (I := I) g₀ T x v w := by
  rw [perturbationSharpEndoFib_apply]
  exact inner_metricSharp (I := I) g₀ x
    (ccTensorBilinSymm (I := I) g₀ T x v).toLinearMap w

set_option backward.isDefEq.respectTransparency false in
private theorem perturbationSharpEndoFib_contMDiff (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y) x
        (perturbationSharpEndoFib (I := I) (M := M) g₀ T x)) := by
  apply cotangentCov_clmSection_smooth_aux (I := I) (M := M)
    (F₂ := E) (V₂ := fun y : M => TangentSpace I y)
    (φ := fun x : M => perturbationSharpEndoFib (I := I) (M := M) g₀ T x)
  intro Y
  have hcv : ∀ (α : M) (j : Fin (Module.finrank ℝ E)),
      ContMDiffOn I 𝓘(ℝ) ∞
        (fun b : M => (ccTensorBilinSymm (I := I) g₀ T b (Y b)).toLinearMap
          (chartBasisVecFiber (I := I) α j b))
        (chartAt H α).source := by
    intro α j
    have hB : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
        (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
          (E := fun y => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) b
          (ccTensorBilinSymm (I := I) g₀ T b)) :=
      ccTensorBilinSymm_contMDiff (I := I) g₀ T
    have hBasis : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
        (chartBasisVec (I := I) α j)
        (trivializationAt E (TangentSpace I) α).baseSet :=
      chartBasisVec_contMDiffOn (I := I) α j
    have happ : ContMDiffOn I (I.prod 𝓘(ℝ, ℝ)) ∞
        (fun b : M => (⟨b,
            ccTensorBilinSymm (I := I) g₀ T b (Y b) (chartBasisVecFiber (I := I) α j b)⟩ :
            TotalSpace ℝ (Bundle.Trivial M ℝ)))
        (trivializationAt E (TangentSpace I) α).baseSet :=
      ContMDiffOn.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := ℝ)
        (b := id) hB.contMDiffOn Y.contMDiff.contMDiffOn hBasis
    have hbase_eq :
        (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source :=
      trivializationAt_baseSet_eq_chartAt_source (I := I) α
    rw [hbase_eq] at happ
    intro b hb
    have hpb := happ b hb
    rw [Bundle.contMDiffWithinAt_totalSpace] at hpb
    exact hpb.2
  have hsmooth := metricSharp_contMDiff_total (I := I) g₀
    (cv := fun b : M => (ccTensorBilinSymm (I := I) g₀ T b (Y b)).toLinearMap) hcv
  refine hsmooth.congr ?_
  intro x
  change TotalSpace.mk' E x
      (metricSharp (I := I) g₀ x (ccTensorBilinSymm (I := I) g₀ T x (Y x)).toLinearMap) =
    TotalSpace.mk' E x (perturbationSharpEndoFib (I := I) (M := M) g₀ T x (Y x))
  rw [perturbationSharpEndoFib_apply]

private def perturbationSharpEndoField (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) :
    ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x) where
  toFun := fun x : M => perturbationSharpEndoFib (I := I) (M := M) g₀ T x
  contMDiff_toFun := perturbationSharpEndoFib_contMDiff (I := I) (M := M) g₀ T

set_option linter.unusedSectionVars false in
private lemma unitModel_eq_ccTensorBilin_pt (g₀ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) (b : M) (u w : TangentSpace I b) :
    unitModel (I := I) (M := M) g₀ 2 S b ![u, w] = ccTensorBilin (I := I) g₀ S b u w := by
  rw [ccTensorBilin_apply (I := I) g₀ S b u w, ccTensorModel]
  rw [show ccTensorMultilinear (I := I) g₀ S b =
      (show Tensor0SSpace 0 I b →L[ℝ] Tensor0SSpace 2 I b from S.toSection b)
        (unitZeroSec (I := I) (M := M) b) from rfl]
  rw [unitModel]
  refine congrArg _ ?_
  funext k
  fin_cases k <;> rfl

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
private lemma slotInsert_perturbationSharp_eq_raise_symmS (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) :
    slotInsertEndoCc (I := I) (M := M) g₀ 0 (perturbationSharpEndoField (I := I) (M := M) g₀ T) =
      cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1)
          (symmS (I := I) (M := M) g₀ T)) := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro om
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro w
  have hLHS : Tensor0SSpace.toModel
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (slotInsertEndoCc (I := I) (M := M) g₀ 0
          (perturbationSharpEndoField (I := I) (M := M) g₀ T)).toSection x) om) w =
      ccTensorBilinSymm (I := I) g₀ T x (w 0)
        (inverseMetricSharpFib (I := I) g₀ x om) := by
    rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
          (slotInsertEndoCc (I := I) (M := M) g₀ 0
            (perturbationSharpEndoField (I := I) (M := M) g₀ T)).toSection x) om) =
        slotInsertEndoFib (I := I) (M := M) 1 0 x
          (perturbationSharpEndoField (I := I) (M := M) g₀ T x) om from rfl]
    rw [slotInsertEndoFib_apply_eval]
    rw [toModel_om_single_eq_cotangentToDual (I := I) (M := M) x om
      (Function.update w 0 (perturbationSharpEndoField (I := I) (M := M) g₀ T x (w 0)))]
    rw [Function.update_self]
    rw [show (perturbationSharpEndoField (I := I) (M := M) g₀ T x) =
        perturbationSharpEndoFib (I := I) (M := M) g₀ T x from rfl]
    rw [cotangentToDual_eq_inner_sharp (I := I) (M := M) g₀ x om
      (perturbationSharpEndoFib (I := I) (M := M) g₀ T x (w 0))]
    rw [inner_perturbationSharpEndoFib]
  rw [hLHS]
  rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1)
            (symmS (I := I) (M := M) g₀ T))).toSection x) om) =
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        cometricRaiseSlot0Fib g₀ 0 x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
            (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1)
              (symmS (I := I) (M := M) g₀ T)).toSection x)
            (unitTensor (I := I) (M := M) x))) om) from rfl]
  rw [cometricRaiseSlot0Fib_clm_apply (I := I) g₀ 0 x _ om]
  rw [interiorProduct_toModel_eval_pal (I := I) (M := M) 1 x
    (inverseMetricSharpFib (I := I) g₀ x om) _ w]
  rw [show Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1)
          (symmS (I := I) (M := M) g₀ T)).toSection x)
        (unitTensor (I := I) (M := M) x)) =
      unitModel (I := I) (M := M) g₀ 2
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1)
          (symmS (I := I) (M := M) g₀ T)) x from rfl]
  rw [domDomCongrSection_unitModel (I := I) g₀ (Equiv.swap (0 : Fin 2) 1)
    (symmS (I := I) (M := M) g₀ T) x]
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  rw [show (fun i : Fin 2 =>
      (Fin.cons (show E from inverseMetricSharpFib (I := I) g₀ x om)
        (fun k => (show E from w k)) : Fin 2 → E) ((Equiv.swap (0 : Fin 2) 1) i)) =
      (![(w 0 : E), (show E from inverseMetricSharpFib (I := I) g₀ x om)] : Fin 2 → E) from by
    funext i
    fin_cases i <;> rfl]
  rw [unitModel_eq_ccTensorBilin_pt (I := I) (M := M) g₀ (symmS (I := I) (M := M) g₀ T) x
    (w 0) (inverseMetricSharpFib (I := I) g₀ x om)]
  rw [ccTensorBilin_symmS (I := I) (M := M) g₀ T x]

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
set_option maxHeartbeats 12800000 in
private lemma riemannG1LoweringDifference_slotInsert_repr (g₀ g₁ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w) :
    riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁ - riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁ =
      domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
        (appCcRS (I := I) (M := M) g₀ 0 4 4
          (slotInsertEndoCc (I := I) (M := M) g₀ 3
            (perturbationSharpEndoField (I := I) (M := M) g₀ T))
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
            (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁))) := by
  classical
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g₀
  intro x
  apply ContinuousMultilinearMap.ext
  intro m
  have hLHS : unitModel (I := I) (M := M) g₀ 4
      (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁ -
        riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁) x m =
      ccTensorBilinSymm (I := I) g₀ T x
        (riemannOp (LeviCivita (I := I) g₁) x (m 0) (m 2) (m 3)) (m 1) := by
    have hsub : unitModel (I := I) (M := M) g₀ 4
        (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁ -
          riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁) x m =
        unitModel (I := I) (M := M) g₀ 4
            (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁) x m -
          unitModel (I := I) (M := M) g₀ 4
            (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁) x m := by
      rw [unitModel, unitModel, unitModel]
      rw [show ((riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁ -
            riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁).toSection x) =
          (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁).toSection x -
            (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁).toSection x from by
        rw [SmoothCcTensor.toSection_sub]; rfl]
      rw [ContinuousLinearMap.sub_apply, Tensor0SSpace.toModel_sub,
        ContinuousMultilinearMap.sub_apply]
    rw [hsub]
    rw [riemannLoweredCc_unitModel_apply (I := I) (M := M) g₀ g₁ g₁ x m]
    rw [riemannLoweredCc_unitModel_apply (I := I) (M := M) g₀ g₀ g₁ x m]
    rw [htie x (riemannOp (LeviCivita (I := I) g₁) x (m 0) (m 2) (m 3)) (m 1)]
    ring
  rw [hLHS]
  rw [domDomCongrSection_unitModel (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
    (appCcRS (I := I) (M := M) g₀ 0 4 4
      (slotInsertEndoCc (I := I) (M := M) g₀ 3
        (perturbationSharpEndoField (I := I) (M := M) g₀ T))
      (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
        (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁))) x]
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  have happ : unitModel (I := I) (M := M) g₀ 4
      (appCcRS (I := I) (M := M) g₀ 0 4 4
        (slotInsertEndoCc (I := I) (M := M) g₀ 3
          (perturbationSharpEndoField (I := I) (M := M) g₀ T))
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
          (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁))) x
      (fun i => m ((Equiv.swap (0 : Fin 4) 1) i)) =
      unitModel (I := I) (M := M) g₀ 4
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
          (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁)) x
        (Function.update (fun i => m ((Equiv.swap (0 : Fin 4) 1) i)) 0
          (perturbationSharpEndoField (I := I) (M := M) g₀ T x
            ((fun i => m ((Equiv.swap (0 : Fin 4) 1) i)) 0))) := by
    rw [unitModel, unitModel]
    rw [show ((appCcRS (I := I) (M := M) g₀ 0 4 4
        (slotInsertEndoCc (I := I) (M := M) g₀ 3
          (perturbationSharpEndoField (I := I) (M := M) g₀ T))
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
          (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁))).toSection x)
        (unitTensor (I := I) (M := M) x) =
      slotInsertEndoFib (I := I) (M := M) 4 0 x
        (perturbationSharpEndoField (I := I) (M := M) g₀ T x)
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
            (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁)).toSection x)
          (unitTensor (I := I) (M := M) x)) from by
      rw [appCcRS_toSection]
      rfl]
    rw [slotInsertEndoFib_apply_eval]
  rw [happ]
  rw [domDomCongrSection_unitModel (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
    (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁) x]
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  rw [show (fun i : Fin 4 =>
      (Function.update (fun i' => m ((Equiv.swap (0 : Fin 4) 1) i')) 0
        (perturbationSharpEndoField (I := I) (M := M) g₀ T x
          ((fun i' => m ((Equiv.swap (0 : Fin 4) 1) i')) 0)))
        ((Equiv.swap (0 : Fin 4) 1) i)) =
      (![(m 0 : E),
        (show E from perturbationSharpEndoFib (I := I) (M := M) g₀ T x (m 1)),
        (m 2 : E), (m 3 : E)] : Fin 4 → E) from by
    funext i
    fin_cases i
    · change (Function.update (fun i' => m ((Equiv.swap (0 : Fin 4) 1) i')) 0
          (perturbationSharpEndoField (I := I) (M := M) g₀ T x
            (m ((Equiv.swap (0 : Fin 4) 1) 0)))) ((Equiv.swap (0 : Fin 4) 1) 0) = m 0
      rw [show ((Equiv.swap (0 : Fin 4) 1) 0) = (1 : Fin 4) from by decide]
      rw [Function.update_of_ne (by decide : (1 : Fin 4) ≠ 0)]
      rw [show ((Equiv.swap (0 : Fin 4) 1) 1) = (0 : Fin 4) from by decide]
    · change (Function.update (fun i' => m ((Equiv.swap (0 : Fin 4) 1) i')) 0
          (perturbationSharpEndoField (I := I) (M := M) g₀ T x
            (m ((Equiv.swap (0 : Fin 4) 1) 0)))) ((Equiv.swap (0 : Fin 4) 1) 1) =
        (show E from perturbationSharpEndoFib (I := I) (M := M) g₀ T x (m 1))
      rw [show ((Equiv.swap (0 : Fin 4) 1) 1) = (0 : Fin 4) from by decide]
      rw [Function.update_self]
      rw [show ((Equiv.swap (0 : Fin 4) 1) 0) = (1 : Fin 4) from by decide]
      rfl
    · change (Function.update (fun i' => m ((Equiv.swap (0 : Fin 4) 1) i')) 0
          (perturbationSharpEndoField (I := I) (M := M) g₀ T x
            (m ((Equiv.swap (0 : Fin 4) 1) 0)))) ((Equiv.swap (0 : Fin 4) 1) 2) = m 2
      rw [show ((Equiv.swap (0 : Fin 4) 1) 2) = (2 : Fin 4) from by decide]
      rw [Function.update_of_ne (by decide : (2 : Fin 4) ≠ 0)]
      rw [show ((Equiv.swap (0 : Fin 4) 1) 2) = (2 : Fin 4) from by decide]
    · change (Function.update (fun i' => m ((Equiv.swap (0 : Fin 4) 1) i')) 0
          (perturbationSharpEndoField (I := I) (M := M) g₀ T x
            (m ((Equiv.swap (0 : Fin 4) 1) 0)))) ((Equiv.swap (0 : Fin 4) 1) 3) = m 3
      rw [show ((Equiv.swap (0 : Fin 4) 1) 3) = (3 : Fin 4) from by decide]
      rw [Function.update_of_ne (by decide : (3 : Fin 4) ≠ 0)]
      rw [show ((Equiv.swap (0 : Fin 4) 1) 3) = (3 : Fin 4) from by decide]]
  rw [riemannLoweredCc_unitModel_apply (I := I) (M := M) g₀ g₀ g₁ x]
  rw [show (![(m 0 : E),
      (show E from perturbationSharpEndoFib (I := I) (M := M) g₀ T x (m 1)),
      (m 2 : E), (m 3 : E)] : Fin 4 → TangentSpace I x) 0 = m 0 from rfl]
  rw [show (![(m 0 : E),
      (show E from perturbationSharpEndoFib (I := I) (M := M) g₀ T x (m 1)),
      (m 2 : E), (m 3 : E)] : Fin 4 → TangentSpace I x) 1 =
    perturbationSharpEndoFib (I := I) (M := M) g₀ T x (m 1) from rfl]
  rw [show (![(m 0 : E),
      (show E from perturbationSharpEndoFib (I := I) (M := M) g₀ T x (m 1)),
      (m 2 : E), (m 3 : E)] : Fin 4 → TangentSpace I x) 2 = m 2 from rfl]
  rw [show (![(m 0 : E),
      (show E from perturbationSharpEndoFib (I := I) (M := M) g₀ T x (m 1)),
      (m 2 : E), (m 3 : E)] : Fin 4 → TangentSpace I x) 3 = m 3 from rfl]
  rw [g₀.symm x (riemannOp (LeviCivita (I := I) g₁) x (m 0) (m 2) (m 3))
    (perturbationSharpEndoFib (I := I) (M := M) g₀ T x (m 1))]
  rw [inner_perturbationSharpEndoFib (I := I) (M := M) g₀ T x (m 1)
    (riemannOp (LeviCivita (I := I) g₁) x (m 0) (m 2) (m 3))]
  rw [ccTensorBilinSymm_symm (I := I) g₀ T x (m 1)
    (riemannOp (LeviCivita (I := I) g₁) x (m 0) (m 2) (m 3))]

set_option linter.unusedSectionVars false in
private lemma rfns_eq_sum_componentSq_of_horth_pt
    (g₀ : SmoothRiemannianMetric I M) (r s : ℕ) (x : M) (S : TensorRSSpace r s I x)
    {n : ℕ} (e : Fin n → TangentSpace I x) (hn : n = Module.finrank ℝ E)
    (horth : ∀ a b : Fin n, g₀.inner x (e a) (e b) = if a = b then (1 : ℝ) else 0) :
    riemannianFiberNormSq (I := I) (M := M) g₀ r s x S =
      ∑ K : Fin r → Fin n, ∑ J : Fin s → Fin n,
        (fiberNormSqComponent (I := I) (M := M) g₀ x r s S n e K J) ^ 2 := by
  classical
  haveI : Nonempty (Fin n) := by
    rw [hn]
    exact ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E))⟩⟩
  have he_li : LinearIndependent ℝ e := by
    rw [linearIndependent_iff']
    intro fs c hsum k hk_mem
    have h_zero : g₀.inner x (e k) (∑ j ∈ fs, c j • e j) = 0 := by rw [hsum]; simp
    rw [map_sum] at h_zero
    have h_pull : ∀ j ∈ fs, g₀.inner x (e k) (c j • e j) =
        c j * (if k = j then (1 : ℝ) else 0) := by
      intro j _
      rw [map_smul, horth k j, smul_eq_mul]
    rw [Finset.sum_congr rfl h_pull] at h_zero
    rw [Finset.sum_eq_single k (fun j _ hj => by rw [if_neg (Ne.symm hj), mul_zero])
      (fun hk => absurd hk_mem hk)] at h_zero
    rwa [if_pos rfl, mul_one] at h_zero
  have hrank : Module.finrank ℝ (TangentSpace I x) = Module.finrank ℝ E := rfl
  have hcard : Fintype.card (Fin n) = Module.finrank ℝ (TangentSpace I x) := by
    rw [Fintype.card_fin, hrank]; exact hn
  set bse := basisOfLinearIndependentOfCardEqFinrank he_li hcard with hbse_def
  have hbse : ∀ i : Fin n, bse i = e i := by
    intro i; rw [hbse_def, coe_basisOfLinearIndependentOfCardEqFinrank]
  exact rfns_rs_eq_sum_componentSq_of_basis (I := I) (M := M) g₀ r s x S e bse hn hbse horth

set_option linter.unusedSectionVars false in
private lemma fiberNormSqComponent_zero_toModel_pt
    (g₀ : SmoothRiemannianMetric I M) (s : ℕ) (x : M) (S : SmoothCcTensor g₀ 0 s)
    {n : ℕ} (e : Fin n → TangentSpace I x) (K : Fin 0 → Fin n) (L : Fin s → Fin n) :
    fiberNormSqComponent (I := I) (M := M) g₀ x 0 s (S.toSection x) n e K L =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from S.toSection x)
          (unitTensor (I := I) (M := M) x))
        (fun k => (show E from e (L k))) := by
  rw [show fiberNormSqComponent (I := I) (M := M) g₀ x 0 s (S.toSection x) n e K L =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from S.toSection x)
        (coframeS (I := I) (M := M) g₀ x 0 e K) (fun k => e (L k)) from rfl]
  rw [coframeS_zero_eq_unitZeroSec (I := I) (M := M) g₀ x e K]
  rfl

set_option linter.unusedSectionVars false in
private lemma rfns_symmS_zero_le_of_ball (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
        ((symmS (I := I) (M := M) g₀ T).toSection x) ≤
      (Module.finrank ℝ E : ℝ) ^ 2 * δ ^ 2 := by
  classical
  obtain ⟨n, e, bse, hn, hbse, horth, _hpars, _hrepr, _hsum⟩ :=
    tangent_orthonormalBasis_witness (I := I) (M := M) g₀ x
  have hnE : n = Module.finrank ℝ E := by rw [hn]; rfl
  rw [rfns_eq_sum_componentSq_of_horth_pt (I := I) (M := M) g₀ 0 2 x
    ((symmS (I := I) (M := M) g₀ T).toSection x) e hnE horth]
  have hcomp : ∀ (K : Fin 0 → Fin n) (J : Fin 2 → Fin n),
      (fiberNormSqComponent (I := I) (M := M) g₀ x 0 2
        ((symmS (I := I) (M := M) g₀ T).toSection x) n e K J) ^ 2 ≤ δ ^ 2 := by
    intro K J
    have hval : fiberNormSqComponent (I := I) (M := M) g₀ x 0 2
        ((symmS (I := I) (M := M) g₀ T).toSection x) n e K J =
        ccTensorBilinSymm (I := I) g₀ T x (e (J 0)) (e (J 1)) := by
      rw [fiberNormSqComponent_zero_toModel_pt (I := I) (M := M) g₀ 2 x
        (symmS (I := I) (M := M) g₀ T) e K J]
      rw [show Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
            (symmS (I := I) (M := M) g₀ T).toSection x)
            (unitTensor (I := I) (M := M) x))
          (fun k => (show E from e (J k))) =
          unitModel (I := I) (M := M) g₀ 2 (symmS (I := I) (M := M) g₀ T) x
            ![e (J 0), e (J 1)] from by
        rw [unitModel]
        refine congrArg _ ?_
        funext k
        fin_cases k <;> rfl]
      rw [unitModel_eq_ccTensorBilin_pt (I := I) (M := M) g₀
        (symmS (I := I) (M := M) g₀ T) x (e (J 0)) (e (J 1))]
      rw [ccTensorBilin_symmS (I := I) (M := M) g₀ T x (e (J 0)) (e (J 1))]
    rw [hval]
    have habs := hbound x (e (J 0)) (e (J 1))
    have h00 : g₀.inner x (e (J 0)) (e (J 0)) = 1 := by
      rw [horth (J 0) (J 0), if_pos rfl]
    have h11 : g₀.inner x (e (J 1)) (e (J 1)) = 1 := by
      rw [horth (J 1) (J 1), if_pos rfl]
    rw [h00, h11, Real.sqrt_one, mul_one, mul_one] at habs
    have := abs_nonneg (ccTensorBilinSymm (I := I) g₀ T x (e (J 0)) (e (J 1)))
    nlinarith [habs, sq_abs (ccTensorBilinSymm (I := I) g₀ T x (e (J 0)) (e (J 1)))]
  calc (∑ K : Fin 0 → Fin n, ∑ J : Fin 2 → Fin n,
        (fiberNormSqComponent (I := I) (M := M) g₀ x 0 2
          ((symmS (I := I) (M := M) g₀ T).toSection x) n e K J) ^ 2)
      ≤ ∑ K : Fin 0 → Fin n, ∑ J : Fin 2 → Fin n, δ ^ 2 :=
        Finset.sum_le_sum fun K _ => Finset.sum_le_sum fun J _ => hcomp K J
    _ = (Fintype.card (Fin 0 → Fin n) : ℝ) * ((Fintype.card (Fin 2 → Fin n) : ℝ) * δ ^ 2) := by
        rw [Finset.sum_const, Finset.sum_const]
        simp only [Finset.card_univ, nsmul_eq_mul]
    _ ≤ (Module.finrank ℝ E : ℝ) ^ 2 * δ ^ 2 := by
        have hc0 : (Fintype.card (Fin 0 → Fin n) : ℝ) = 1 := by
          simp
        have hc2 : (Fintype.card (Fin 2 → Fin n) : ℝ) = (n : ℝ) ^ 2 := by
          simp only [Fintype.card_fun, Fintype.card_fin]
          push_cast
          ring
        rw [hc0, hc2, one_mul, hnE]

set_option linter.unusedSectionVars false in
private lemma rfns_iteratedCovGrad_slotInsert3_perturbationSharp_le
    (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2) (j : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 4 (4 + j) x
        ((iteratedCovGrad (I := I) g₀ 4 4 j
          (slotInsertEndoCc (I := I) (M := M) g₀ 3
            (perturbationSharpEndoField (I := I) (M := M) g₀ T))).toSection x) ≤
      (Module.finrank ℝ E : ℝ) ^ 3 *
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 0 2 j (symmS (I := I) (M := M) g₀ T)).toSection x) := by
  refine le_trans (rfns_iteratedCovGrad_slotInsertEndoCc_le_endo (I := I) (M := M) g₀ 3
    (perturbationSharpEndoField (I := I) (M := M) g₀ T) j x) ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [slotInsert_perturbationSharp_eq_raise_symmS (I := I) (M := M) g₀ T]
  rw [rfns_iteratedCovGrad_cometricRaiseSlot0Field_eq (I := I) (M := M) g₀ 0
    (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1)
      (symmS (I := I) (M := M) g₀ T)) j x]
  rw [riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
    (Equiv.swap (0 : Fin 2) 1) (symmS (I := I) (M := M) g₀ T) j x]

set_option linter.unusedVariables false in
theorem rfns_iteratedCovGrad_riemannLoweredBackgroundDifference_diagonalProductGrid_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 4 i
              (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)).toSection x) ≤
          C i * ∑ k ∈ Finset.range (i + 3),
            ∑ n ∈ Finset.range (k + 1),
              ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
                ∏ m : Fin n,
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T).toSection x) := by
  classical
  obtain ⟨CA, hCA_nn, hCA⟩ := exists_rfns_iteratedCovGrad_connDiffSection_tgrid
    (I := I) (M := M) g₀ hδ₀
  set AA : ℕ → ℕ → ℝ := fun i i' => ∑ l ∈ Finset.range (i + 1 - i'),
    CA i' * CA l * gridSumPairCount (i' + 2) (l + 2) with hAA_def
  have hAA_nn : ∀ i i', 0 ≤ AA i i' := by
    intro i i'
    rw [hAA_def]
    exact Finset.sum_nonneg fun l _ =>
      mul_nonneg (mul_nonneg (hCA_nn i') (hCA_nn l)) (gridSumPairCount_nonneg _ _)
  clear_value AA
  refine ⟨fun i => 8 * CA (i + 1) + 8 * (appCcGdiag (E := E) i *
      ∑ i' ∈ Finset.range (i + 1), (Module.finrank ℝ E : ℝ) * AA i i'),
    fun i => by
      have h1 : 0 ≤ ∑ i' ∈ Finset.range (i + 1), (Module.finrank ℝ E : ℝ) * AA i i' :=
        Finset.sum_nonneg fun i' _ => mul_nonneg (Nat.cast_nonneg _) (hAA_nn i i')
      have h2 := appCcGdiag_nonneg (E := E) i
      have h4 := hCA_nn (i + 1)
      positivity, ?_⟩
  intro g₁ T htie δ hδ_le hδ0 hbound i x
  set b : ℕ → ℝ := fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
    ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x) with hb_def
  have hb : ∀ j, 0 ≤ b j :=
    fun j => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + j) x _
  have hgoal_eq : (∑ k ∈ Finset.range (i + 3),
      ∑ n ∈ Finset.range (k + 1),
        ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
          ∏ m : Fin n, b (e m)) =
      ∑ k ∈ Finset.range (i + 3), Combinatorics.antidiagonalTupleGrid b k := rfl
  rw [hgoal_eq]
  set WW : ℝ := ∑ k ∈ Finset.range (i + 3), Combinatorics.antidiagonalTupleGrid b k
    with hWW_def
  have hWW_nn : 0 ≤ WW := by
    rw [hWW_def]
    exact Finset.sum_nonneg fun k _ => Combinatorics.antidiagonalTupleGrid_nonneg b hb k
  have hgsum_le_WW : ∀ m : ℕ, m ≤ i + 3 →
      (∑ k ∈ Finset.range m, Combinatorics.antidiagonalTupleGrid b k) ≤ WW := by
    intro m hm
    rw [hWW_def]
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hm) ?_
    intro k _ _
    exact Combinatorics.antidiagonalTupleGrid_nonneg b hb k
  clear_value WW
  have hstep1 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
      ((iteratedCovGrad (I := I) g₀ 0 4 i
        (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 3 i
          (cometricRaiseSlot0Field (I := I) (M := M) g₀ 2
            (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
              (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)))).toSection x) := by
    rw [rfns_iteratedCovGrad_cometricRaiseSlot0Field_eq (I := I) (M := M) g₀ 2
      (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
        (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)) i x]
    rw [riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 4) 1)
      (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁) i x]
  rw [hstep1]
  rw [riemannLoweredBackgroundDifference_palatini_repr (I := I) (M := M) g₀ g₁]
  set DQ : SmoothCcTensor g₀ 1 3 :=
    covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀) +
      quadraticConnDiffCc (I := I) (M := M) g₀ g₁ with hDQ_def
  have hrs_eq : ∀ σ : Equiv.Perm (Fin 3),
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 3 i
          (rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 σ DQ)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 3 i DQ).toSection x) := by
    intro σ
    exact rfns_iteratedCovGrad_rs_eq_of_section_domDomCongr (I := I) (M := M) g₀ 1 3 σ DQ
      (rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 σ DQ)
      (fun y d => by
        rw [rsDomDomCongrSection_toSection, toModel_rsDomDomCongr_apply]) i x
  have hsubsec : (iteratedCovGrad (I := I) g₀ 1 3 i
      (rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (Equiv.swap (1 : Fin 3) 2) DQ -
        rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (finRotate 3) DQ)).toSection x =
      (iteratedCovGrad (I := I) g₀ 1 3 i
        (rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (Equiv.swap (1 : Fin 3) 2) DQ)).toSection x +
      (- (iteratedCovGrad (I := I) g₀ 1 3 i
        (rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (finRotate 3) DQ)).toSection x) := by
    rw [sub_eq_add_neg, iteratedCovGrad_add, iteratedCovGrad_neg,
      SmoothCcTensor.toSection_add]
    rw [show ((iteratedCovGrad (I := I) g₀ 1 3 i
        (rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (Equiv.swap (1 : Fin 3) 2) DQ)).toSection +
        (- iteratedCovGrad (I := I) g₀ 1 3 i
          (rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (finRotate 3) DQ)).toSection) x =
      (iteratedCovGrad (I := I) g₀ 1 3 i
        (rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (Equiv.swap (1 : Fin 3) 2) DQ)).toSection x +
      (- iteratedCovGrad (I := I) g₀ 1 3 i
        (rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (finRotate 3) DQ)).toSection x from rfl]
    rw [SmoothCcTensor.toSection_neg]
    rfl
  rw [hsubsec]
  refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 1 (3 + i) x _ _) ?_
  rw [rfns_neg_pt (I := I) (M := M) g₀ 1 (3 + i) x]
  rw [hrs_eq (Equiv.swap (1 : Fin 3) 2), hrs_eq (finRotate 3)]
  have hDQsec : (iteratedCovGrad (I := I) g₀ 1 3 i DQ).toSection x =
      (iteratedCovGrad (I := I) g₀ 1 3 i
        (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀))).toSection x +
      (iteratedCovGrad (I := I) g₀ 1 3 i
        (quadraticConnDiffCc (I := I) (M := M) g₀ g₁)).toSection x := by
    rw [hDQ_def, iteratedCovGrad_add, SmoothCcTensor.toSection_add]
    rfl
  have hD_le : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
      ((iteratedCovGrad (I := I) g₀ 1 3 i
        (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀))).toSection x) ≤
      CA (i + 1) * WW := by
    rw [rfns_iteratedCovGrad_covGrad_comm_rs (I := I) (M := M) g₀ 1 2 i
      (connDiffSection (I := I) g₁ g₀) x]
    refine le_trans (hCA g₁ T htie hδ_le hδ0 hbound (i + 1) x) ?_
    exact mul_le_mul_of_nonneg_left (hgsum_le_WW (i + 3) (le_refl _)) (hCA_nn (i + 1))
  have hcell : ∀ i' ∈ Finset.range (i + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (3 + i') x
          ((iteratedCovGrad (I := I) g₀ 2 3 i'
            (armSlotEndoPassZeroCc (I := I) (M := M) g₀
              (connDiffArmFieldPt (I := I) (M := M) g₀ g₁))).toSection x) *
        ∑ l ∈ Finset.range (i + 1 - i'),
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + l) x
            ((iteratedCovGrad (I := I) g₀ 1 2 l
              (connDiffSection (I := I) g₁ g₀)).toSection x) ≤
      ((Module.finrank ℝ E : ℝ) * AA i i') * WW := by
    intro i' hi'
    have hi'le : i' ≤ i := by
      rw [Finset.mem_range] at hi'; omega
    have hA1 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (3 + i') x
        ((iteratedCovGrad (I := I) g₀ 2 3 i'
          (armSlotEndoPassZeroCc (I := I) (M := M) g₀
            (connDiffArmFieldPt (I := I) (M := M) g₀ g₁))).toSection x) ≤
        (Module.finrank ℝ E : ℝ) *
          (CA i' * ∑ k ∈ Finset.range (i' + 2), Combinatorics.antidiagonalTupleGrid b k) := by
      refine le_trans (rfns_iteratedCovGrad_armSlotPass_connDiffArm_le
        (I := I) (M := M) g₀ g₁ i' x) ?_
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
      exact hCA g₁ T htie hδ_le hδ0 hbound i' x
    have hA2 : (∑ l ∈ Finset.range (i + 1 - i'),
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + l) x
          ((iteratedCovGrad (I := I) g₀ 1 2 l
            (connDiffSection (I := I) g₁ g₀)).toSection x)) ≤
        ∑ l ∈ Finset.range (i + 1 - i'),
          CA l * ∑ k ∈ Finset.range (l + 2), Combinatorics.antidiagonalTupleGrid b k :=
      Finset.sum_le_sum fun l _ => hCA g₁ T htie hδ_le hδ0 hbound l x
    have hprod_nn1 : 0 ≤ ∑ l ∈ Finset.range (i + 1 - i'),
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + l) x
          ((iteratedCovGrad (I := I) g₀ 1 2 l
            (connDiffSection (I := I) g₁ g₀)).toSection x) :=
      Finset.sum_nonneg fun l _ =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 (2 + l) x _
    have hfr_nn : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
    have hgsA_nn : 0 ≤ CA i' * ∑ k ∈ Finset.range (i' + 2),
        Combinatorics.antidiagonalTupleGrid b k :=
      mul_nonneg (hCA_nn i') (Finset.sum_nonneg fun k _ =>
        Combinatorics.antidiagonalTupleGrid_nonneg b hb k)
    have hpairsum : ∀ l ∈ Finset.range (i + 1 - i'),
        (CA i' * ∑ k ∈ Finset.range (i' + 2), Combinatorics.antidiagonalTupleGrid b k) *
          (CA l * ∑ k ∈ Finset.range (l + 2), Combinatorics.antidiagonalTupleGrid b k) ≤
        (CA i' * CA l * gridSumPairCount (i' + 2) (l + 2)) * WW := by
      intro l hl
      have hl_le : l ≤ i - i' := by
        rw [Finset.mem_range] at hl; omega
      have hgs := gridSum_mul_gridSum_le b hb (i' + 2) (l + 2) (i + 3) (by omega)
      calc (CA i' * ∑ k ∈ Finset.range (i' + 2), Combinatorics.antidiagonalTupleGrid b k) *
            (CA l * ∑ k ∈ Finset.range (l + 2), Combinatorics.antidiagonalTupleGrid b k)
          = (CA i' * CA l) *
              ((∑ k ∈ Finset.range (i' + 2), Combinatorics.antidiagonalTupleGrid b k) *
                (∑ k ∈ Finset.range (l + 2), Combinatorics.antidiagonalTupleGrid b k)) := by
            ring
        _ ≤ (CA i' * CA l) * (gridSumPairCount (i' + 2) (l + 2) *
              (∑ k ∈ Finset.range (i + 3), Combinatorics.antidiagonalTupleGrid b k)) := by
            refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (hCA_nn i') (hCA_nn l))
            exact hgs
        _ ≤ (CA i' * CA l) * (gridSumPairCount (i' + 2) (l + 2) * WW) := by
            refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (hCA_nn i') (hCA_nn l))
            refine mul_le_mul_of_nonneg_left ?_ (gridSumPairCount_nonneg _ _)
            exact hgsum_le_WW (i + 3) (le_refl _)
        _ = (CA i' * CA l * gridSumPairCount (i' + 2) (l + 2)) * WW := by ring
    calc riemannianFiberNormSq (I := I) (M := M) g₀ 2 (3 + i') x
          ((iteratedCovGrad (I := I) g₀ 2 3 i'
            (armSlotEndoPassZeroCc (I := I) (M := M) g₀
              (connDiffArmFieldPt (I := I) (M := M) g₀ g₁))).toSection x) *
        ∑ l ∈ Finset.range (i + 1 - i'),
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + l) x
            ((iteratedCovGrad (I := I) g₀ 1 2 l
              (connDiffSection (I := I) g₁ g₀)).toSection x)
        ≤ ((Module.finrank ℝ E : ℝ) *
            (CA i' * ∑ k ∈ Finset.range (i' + 2), Combinatorics.antidiagonalTupleGrid b k)) *
          ∑ l ∈ Finset.range (i + 1 - i'),
            CA l * ∑ k ∈ Finset.range (l + 2), Combinatorics.antidiagonalTupleGrid b k :=
          mul_le_mul hA1 hA2 hprod_nn1 (mul_nonneg hfr_nn hgsA_nn)
      _ = (Module.finrank ℝ E : ℝ) *
          ∑ l ∈ Finset.range (i + 1 - i'),
            (CA i' * ∑ k ∈ Finset.range (i' + 2), Combinatorics.antidiagonalTupleGrid b k) *
              (CA l * ∑ k ∈ Finset.range (l + 2), Combinatorics.antidiagonalTupleGrid b k) := by
          rw [mul_assoc, Finset.mul_sum]
      _ ≤ (Module.finrank ℝ E : ℝ) *
          ∑ l ∈ Finset.range (i + 1 - i'),
            (CA i' * CA l * gridSumPairCount (i' + 2) (l + 2)) * WW := by
          exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum hpairsum) hfr_nn
      _ = ((Module.finrank ℝ E : ℝ) * AA i i') * WW := by
          have hAAval : AA i i' = ∑ l ∈ Finset.range (i + 1 - i'),
              CA i' * CA l * gridSumPairCount (i' + 2) (l + 2) := by rw [hAA_def]
          rw [hAAval, ← Finset.sum_mul]
          ring
  have hQ_le : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
      ((iteratedCovGrad (I := I) g₀ 1 3 i
        (quadraticConnDiffCc (I := I) (M := M) g₀ g₁)).toSection x) ≤
      (appCcGdiag (E := E) i *
        ∑ i' ∈ Finset.range (i + 1), (Module.finrank ℝ E : ℝ) * AA i i') * WW := by
    rw [show quadraticConnDiffCc (I := I) (M := M) g₀ g₁ =
        appCcRS (I := I) (M := M) g₀ 1 2 3
          (armSlotEndoPassZeroCc (I := I) (M := M) g₀
            (connDiffArmFieldPt (I := I) (M := M) g₀ g₁))
          (connDiffSection (I := I) g₁ g₀) from rfl]
    refine le_trans (rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le
      (I := I) (M := M) g₀ i 1 2 3
      (armSlotEndoPassZeroCc (I := I) (M := M) g₀
        (connDiffArmFieldPt (I := I) (M := M) g₀ g₁))
      (connDiffSection (I := I) g₁ g₀) x) ?_
    calc appCcGdiag (E := E) i *
          ∑ i' ∈ Finset.range (i + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 2 (3 + i') x
                ((iteratedCovGrad (I := I) g₀ 2 3 i'
                  (armSlotEndoPassZeroCc (I := I) (M := M) g₀
                    (connDiffArmFieldPt (I := I) (M := M) g₀ g₁))).toSection x) *
              ∑ l ∈ Finset.range (i + 1 - i'),
                riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + l) x
                  ((iteratedCovGrad (I := I) g₀ 1 2 l
                    (connDiffSection (I := I) g₁ g₀)).toSection x)
        ≤ appCcGdiag (E := E) i *
            ∑ i' ∈ Finset.range (i + 1), ((Module.finrank ℝ E : ℝ) * AA i i') * WW :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum hcell) (appCcGdiag_nonneg (E := E) i)
      _ = (appCcGdiag (E := E) i *
            ∑ i' ∈ Finset.range (i + 1), (Module.finrank ℝ E : ℝ) * AA i i') * WW := by
          rw [← Finset.sum_mul]
          ring
  rw [hDQsec]
  have hsum_le := riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 1 (3 + i) x
    ((iteratedCovGrad (I := I) g₀ 1 3 i
      (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀))).toSection x)
    ((iteratedCovGrad (I := I) g₀ 1 3 i
      (quadraticConnDiffCc (I := I) (M := M) g₀ g₁)).toSection x)
  have hDQfull : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
      ((iteratedCovGrad (I := I) g₀ 1 3 i
        (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀))).toSection x +
      (iteratedCovGrad (I := I) g₀ 1 3 i
        (quadraticConnDiffCc (I := I) (M := M) g₀ g₁)).toSection x) ≤
      2 * (CA (i + 1) * WW) +
        2 * ((appCcGdiag (E := E) i *
          ∑ i' ∈ Finset.range (i + 1), (Module.finrank ℝ E : ℝ) * AA i i') * WW) := by
    refine le_trans hsum_le ?_
    linarith [hD_le, hQ_le]
  calc 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 3 i
          (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀))).toSection x +
        (iteratedCovGrad (I := I) g₀ 1 3 i
          (quadraticConnDiffCc (I := I) (M := M) g₀ g₁)).toSection x) +
      2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 3 i
          (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀))).toSection x +
        (iteratedCovGrad (I := I) g₀ 1 3 i
          (quadraticConnDiffCc (I := I) (M := M) g₀ g₁)).toSection x)
      ≤ 2 * (2 * (CA (i + 1) * WW) +
          2 * ((appCcGdiag (E := E) i *
            ∑ i' ∈ Finset.range (i + 1), (Module.finrank ℝ E : ℝ) * AA i i') * WW)) +
        2 * (2 * (CA (i + 1) * WW) +
          2 * ((appCcGdiag (E := E) i *
            ∑ i' ∈ Finset.range (i + 1), (Module.finrank ℝ E : ℝ) * AA i i') * WW)) := by
        linarith [hDQfull]
    _ = (8 * CA (i + 1) + 8 * (appCcGdiag (E := E) i *
          ∑ i' ∈ Finset.range (i + 1), (Module.finrank ℝ E : ℝ) * AA i i')) * WW := by
        ring

omit [CompactSpace M] [I.Boundaryless] in
private lemma linearMap_trace_eq_orthoFrame_inner_sum (g₀ : SmoothRiemannianMetric I M)
    (x : M) (G : TangentSpace I x →ₗ[ℝ] TangentSpace I x) :
    LinearMap.trace ℝ (TangentSpace I x) G =
      ∑ i : Fin (Module.finrank ℝ E),
        g₀.inner x (G (smoothOrthoFrame (I := I) g₀ x i x))
          (smoothOrthoFrame (I := I) g₀ x i x) := by
  classical
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  haveI : Nonempty (Fin (Module.finrank ℝ E)) :=
    ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E))⟩⟩
  set B : Fin (Module.finrank ℝ E) → TangentSpace I x :=
    fun i => smoothOrthoFrame (I := I) g₀ x i x with hB_def
  have horth : ∀ i j, g₀.inner x (B i) (B j) = if i = j then (1 : ℝ) else 0 :=
    fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g₀ x i j
  have hlin : LinearIndependent ℝ B := by
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    have hpair : g₀.inner x (∑ i, c i • B i) (B j) = 0 := by
      rw [hc]
      simp
    rw [map_sum, ContinuousLinearMap.sum_apply] at hpair
    have hsimp : ∀ i, g₀.inner x (c i • B i) (B j) = c i * (if i = j then (1 : ℝ) else 0) := by
      intro i
      rw [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul, horth i j]
    rw [Finset.sum_congr rfl (fun i _ => hsimp i)] at hpair
    have hcol : (∑ i, c i * (if i = j then (1 : ℝ) else 0)) = c j := by simp
    rw [hcol] at hpair
    exact hpair
  have hcard : Fintype.card (Fin (Module.finrank ℝ E)) =
      Module.finrank ℝ (TangentSpace I x) := by
    rw [Fintype.card_fin]
    rfl
  set bB : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x) :=
    basisOfLinearIndependentOfCardEqFinrank hlin hcard with hbB_def
  have hbB_coe : ∀ i, bB i = B i := by
    intro i
    rw [hbB_def]
    change (basisOfLinearIndependentOfCardEqFinrank hlin hcard :
        Fin (Module.finrank ℝ E) → TangentSpace I x) i = B i
    rw [coe_basisOfLinearIndependentOfCardEqFinrank]
  have hrepr : ∀ (v : TangentSpace I x) (j : Fin (Module.finrank ℝ E)),
      bB.repr v j = g₀.inner x v (B j) := by
    intro v j
    conv_rhs => rw [← bB.sum_repr v]
    rw [map_sum, ContinuousLinearMap.sum_apply]
    have hsimp : ∀ i, g₀.inner x (bB.repr v i • bB i) (B j) =
        bB.repr v i * (if i = j then (1 : ℝ) else 0) := by
      intro i
      rw [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul, hbB_coe i, horth i j]
    rw [Finset.sum_congr rfl (fun i _ => hsimp i)]
    simp
  rw [LinearMap.trace_eq_matrix_trace ℝ bB G]
  unfold Matrix.trace
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [Matrix.diag_apply]
  rw [LinearMap.toMatrix_apply, hrepr (G (bB i)) i, hbB_coe i]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma interiorProduct_toModel_eval_lc (s : ℕ) (x : M) (v : TangentSpace I x)
    (D : Tensor0SSpace (s + 1) I x) (w : Fin s → TangentSpace I x) :
    Tensor0SSpace.toModel
        (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) s x v D) w =
      Tensor0SSpace.toModel D (Fin.cons (show E from v) (fun k => (show E from w k))) := by
  have h1 : Tensor0SSpace.toModel
      (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) s x v D) =
      Tensor0SBundle.model_interior_product (𝕜 := ℝ) (E := E) s (show E from v)
        (Tensor0SSpace.toModel D) := rfl
  rw [h1]
  rfl

set_option linter.unusedSectionVars false in
private lemma toModel_om_eval_lc (x : M) (om : Tensor0SSpace 1 I x) (V : TangentSpace I x) :
    Tensor0SSpace.toModel om (fun _ : Fin 1 => (V : E)) =
      cotangentToDual (I := I) om V := by
  rw [cotangentToDual_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
set_option maxHeartbeats 6400000 in
theorem slotInsert_ricMixedSharp_sub_ricEndoRaised_eq_raise_doubleTrace
    (g₀ g₁ : SmoothRiemannianMetric I M) :
    slotInsertEndoCc (I := I) (M := M) g₀ 0 (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁) -
        slotInsertEndoCc (I := I) (M := M) g₀ 0 (ricEndoRaisedField (I := I) (M := M) g₀) =
      cometricRaiseSlot0Field (I := I) (M := M) g₀ 0
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1)
          (appCcRS (I := I) (M := M) g₀ 0 4 2
            (cometricDoubleTraceField (I := I) g₀ 2)
            (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁))) := by
  classical
  set W2 : SmoothCcTensor g₀ 0 2 :=
    appCcRS (I := I) (M := M) g₀ 0 4 2
      (cometricDoubleTraceField (I := I) g₀ 2)
      (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁) with hW2_def
  have hW2unitModel : ∀ (x : M) (mm : Fin 2 → TangentSpace I x),
      unitModel (I := I) (M := M) g₀ 2 W2 x mm =
        ricciTensor (I := I) g₁ x (mm 0) (mm 1) - ricciTensor (I := I) g₀ x (mm 0) (mm 1) := by
    intro x mm
    have hsec : (W2.toSection x) =
        (show Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 2 I x from
            cometricDoubleTraceFib (I := I) g₀ 2 x).comp
          (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from
            (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁).toSection x) := by
      rw [hW2_def, appCcRS_toSection, cometricDoubleTraceField_toSection]
    rw [unitModel]
    rw [show (W2.toSection x) (unitTensor (I := I) (M := M) x) =
        cometricDoubleTraceFib (I := I) g₀ 2 x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from
            (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁).toSection x)
            (unitTensor (I := I) (M := M) x)) from by rw [hsec]; rfl]
    rw [cometricDoubleTraceFib_toModel]
    rw [modelDoubleTrace_apply]
    have hT : Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from
          (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁).toSection x)
          (unitTensor (I := I) (M := M) x)) =
        unitModel (I := I) (M := M) g₀ 4
          (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁) x := rfl
    rw [hT]
    rw [cometric_dualTrace_eq_orthoFrame_diag (I := I) g₀ x
      (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x)
      (unitModel (I := I) (M := M) g₀ 4
        (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁) x)
      (fun j => (mm j : E))]
    have hker : ∀ i : Fin (Module.finrank ℝ E),
        unitModel (I := I) (M := M) g₀ 4
          (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁) x
          (Fin.cons ((smoothOrthoFrame (I := I) g₀ x i x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x i x : TangentSpace I x) : E)
              (fun j => (mm j : E)))) =
        g₀.inner x (riemannOp (LeviCivita (I := I) g₁) x
            (smoothOrthoFrame (I := I) g₀ x i x) (mm 0) (mm 1))
            (smoothOrthoFrame (I := I) g₀ x i x) -
          g₀.inner x (riemannOp (LeviCivita (I := I) g₀) x
              (smoothOrthoFrame (I := I) g₀ x i x) (mm 0) (mm 1))
              (smoothOrthoFrame (I := I) g₀ x i x) := by
      intro i
      rw [riemannLoweredBackgroundDifference_unitModel_apply]
      rfl
    rw [Finset.sum_congr rfl (fun i _ => hker i), Finset.sum_sub_distrib]
    have htr1 : (∑ i : Fin (Module.finrank ℝ E),
        g₀.inner x (riemannOp (LeviCivita (I := I) g₁) x
            (smoothOrthoFrame (I := I) g₀ x i x) (mm 0) (mm 1))
            (smoothOrthoFrame (I := I) g₀ x i x)) =
        ricciTensor (I := I) g₁ x (mm 0) (mm 1) := by
      rw [ricciTensor_apply (I := I) g₁ x (mm 0) (mm 1),
        linearMap_trace_eq_orthoFrame_inner_sum (I := I) (M := M) g₀ x
          (ricciEndo (I := I) g₁ x (mm 0) (mm 1))]
      rfl
    have htr0 : (∑ i : Fin (Module.finrank ℝ E),
        g₀.inner x (riemannOp (LeviCivita (I := I) g₀) x
            (smoothOrthoFrame (I := I) g₀ x i x) (mm 0) (mm 1))
            (smoothOrthoFrame (I := I) g₀ x i x)) =
        ricciTensor (I := I) g₀ x (mm 0) (mm 1) := by
      rw [ricciTensor_apply (I := I) g₀ x (mm 0) (mm 1),
        linearMap_trace_eq_orthoFrame_inner_sum (I := I) (M := M) g₀ x
          (ricciEndo (I := I) g₀ x (mm 0) (mm 1))]
      rfl
    rw [htr1, htr0]
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((slotInsertEndoCc (I := I) (M := M) g₀ 0
          (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁) -
        slotInsertEndoCc (I := I) (M := M) g₀ 0
          (ricEndoRaisedField (I := I) (M := M) g₀)).toSection x) =
      (slotInsertEndoCc (I := I) (M := M) g₀ 0
          (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁)).toSection x -
        (slotInsertEndoCc (I := I) (M := M) g₀ 0
          (ricEndoRaisedField (I := I) (M := M) g₀)).toSection x from by
    rw [SmoothCcTensor.toSection_sub]; rfl]
  apply ContinuousLinearMap.ext
  intro om
  rw [ContinuousLinearMap.sub_apply]
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  beta_reduce
  rw [Tensor0SSpace.toModel_sub, ContinuousMultilinearMap.sub_apply]
  rw [show ((slotInsertEndoCc (I := I) (M := M) g₀ 0
        (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁)).toSection x) om =
      slotInsertEndoFib (I := I) (M := M) 1 0 x
        (ricMixedSharpEndoFib (I := I) (M := M) g₀ g₁ x) om from rfl]
  rw [show ((slotInsertEndoCc (I := I) (M := M) g₀ 0
        (ricEndoRaisedField (I := I) (M := M) g₀)).toSection x) om =
      slotInsertEndoFib (I := I) (M := M) 1 0 x (ricEndoRaisedFib (I := I) g₀ x) om from rfl]
  rw [slotInsertEndoFib_apply_eval, slotInsertEndoFib_apply_eval]
  set u : TangentSpace I x := inverseMetricSharpFib (I := I) g₀ x om with hu_def
  have hupd : ∀ V : TangentSpace I x,
      (Function.update m 0 (show E from V)) = fun _ : Fin 1 => (V : E) := by
    intro V
    funext j
    fin_cases j
    simp [Function.update]
  have hsharp_pair : ∀ α : TangentSpace I x →ₗ[ℝ] ℝ,
      cotangentToDual (I := I) om (metricSharp (I := I) g₀ x α) = α u := by
    intro α
    rw [show cotangentToDual (I := I) om (metricSharp (I := I) g₀ x α) =
        cotangentToDualLinear (I := I) (x := x) om (metricSharp (I := I) g₀ x α) from rfl]
    rw [← inverseMetricSharpFib_inner (I := I) g₀ x om (metricSharp (I := I) g₀ x α), ← hu_def]
    exact inner_metricSharp_right (I := I) g₀ x α u
  have hLmix : Tensor0SSpace.toModel om
      (Function.update m 0 (ricMixedSharpEndoFib (I := I) (M := M) g₀ g₁ x (m 0))) =
      (ricciTensor (I := I) g₁ x (m 0)).toLinearMap u := by
    rw [show (ricMixedSharpEndoFib (I := I) (M := M) g₀ g₁ x (m 0)) =
        (show E from metricSharp (I := I) g₀ x
          (ricciTensor (I := I) g₁ x (m 0)).toLinearMap) from
      ricMixedSharpEndoFib_apply (I := I) (M := M) g₀ g₁ x (m 0)]
    rw [hupd, toModel_om_eval_lc, hsharp_pair]
  have hLraised : Tensor0SSpace.toModel om
      (Function.update m 0 (ricEndoRaisedFib (I := I) g₀ x (m 0))) =
      (ricciTensor (I := I) g₀ x (m 0)).toLinearMap u := by
    rw [show (ricEndoRaisedFib (I := I) g₀ x (m 0)) =
        (show E from metricSharp (I := I) g₀ x
          (ricciTensor (I := I) g₀ x (m 0)).toLinearMap) from
      ricEndoRaisedFib_apply (I := I) g₀ x (m 0)]
    rw [hupd, toModel_om_eval_lc, hsharp_pair]
  rw [hLmix, hLraised]
  rw [cometricRaiseSlot0Field_toSection]
  rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 1 I x from
        cometricRaiseSlot0Fib g₀ 0 x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
            (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) W2).toSection x)
            (unitTensor (I := I) (M := M) x))) om) =
      Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) (0 + 1) x
        (inverseMetricSharpFib (I := I) g₀ x om)
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) W2).toSection x)
          (unitTensor (I := I) (M := M) x)) from
    cometricRaiseSlot0Fib_clm_apply (I := I) g₀ 0 x _ om]
  rw [interiorProduct_toModel_eval_lc (I := I) (M := M) (0 + 1) x
    (inverseMetricSharpFib (I := I) g₀ x om) _ m]
  rw [show Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) W2).toSection x)
          (unitTensor (I := I) (M := M) x)) =
      unitModel (I := I) (M := M) g₀ 2
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) W2) x from rfl]
  rw [domDomCongrSection_unitModel, ContinuousMultilinearMap.domDomCongr_apply]
  rw [show (fun i : Fin 2 =>
        (Fin.cons (show E from inverseMetricSharpFib (I := I) g₀ x om)
          (fun k : Fin 1 => (show E from m k)) : Fin 2 → TangentSpace I x)
          ((Equiv.swap (0 : Fin 2) 1) i)) =
      (![(m 0 : TangentSpace I x), u] : Fin 2 → TangentSpace I x) from by
    funext i
    fin_cases i <;>
      simp [hu_def]]
  rw [hW2unitModel x]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rfl

end RiemannLoweredDifference

set_option linter.unusedVariables false in
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck in
theorem rfns_iteratedCovGrad_ricciMixedSharpBackgroundDifference_diagonalProductGrid_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
            ((iteratedCovGrad (I := I) g₀ 1 1 i
              (slotInsertEndoCc (I := I) (M := M) g₀ 0
                  (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁) -
                slotInsertEndoCc (I := I) (M := M) g₀ 0
                  (ricEndoRaisedField (I := I) (M := M) g₀))).toSection x) ≤
          C i * ∑ k ∈ Finset.range (i + 3),
            ∑ n ∈ Finset.range (k + 1),
              ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
                ∏ m : Fin n,
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T).toSection x) := by
  classical
  obtain ⟨CA, hCA_nn, hCA⟩ :=
    rfns_iteratedCovGrad_riemannLoweredBackgroundDifference_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨cPhi, hcPhi_nn, hcPhi⟩ := exists_bound_riemannianFiberNormSq_smoothCcTensor
    (I := I) (M := M) g₀ 4 2 (cometricDoubleTraceField (I := I) g₀ 2)
  refine ⟨fun i => appCcGdiag (E := E) i * cPhi * (∑ l ∈ Finset.range (i + 1), CA l),
    fun i => mul_nonneg (mul_nonneg (appCcGdiag_nonneg (E := E) i) hcPhi_nn)
      (Finset.sum_nonneg fun l _ => hCA_nn l), ?_⟩
  intro g₁ T htie δ hδ_le hδ0 hbound i x
  have hb : ∀ j : ℕ, 0 ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
      ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x) :=
    fun j => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + j) x _
  rw [slotInsert_ricMixedSharp_sub_ricEndoRaised_eq_raise_doubleTrace (I := I) (M := M) g₀ g₁]
  rw [rfns_iteratedCovGrad_cometricRaiseSlot0Field_eq (I := I) (M := M) g₀ 0
    (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1)
      (appCcRS (I := I) (M := M) g₀ 0 4 2
        (cometricDoubleTraceField (I := I) g₀ 2)
        (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁))) i x]
  rw [riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
    (Equiv.swap (0 : Fin 2) 1)
    (appCcRS (I := I) (M := M) g₀ 0 4 2
      (cometricDoubleTraceField (I := I) g₀ 2)
      (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)) i x]
  refine le_trans (rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le
    (I := I) (M := M) g₀ i 0 4 2 (cometricDoubleTraceField (I := I) g₀ 2)
    (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁) x) ?_
  have hAzero : ∀ m : ℕ,
      riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + (m + 1)) x
        ((iteratedCovGrad (I := I) g₀ 4 2 (m + 1)
          (cometricDoubleTraceField (I := I) g₀ 2)).toSection x) = 0 := by
    intro m
    rw [← rfns_iteratedCovGrad_covGrad_comm_rs (I := I) (M := M) g₀ 4 2 m
      (cometricDoubleTraceField (I := I) g₀ 2) x]
    rw [show covGrad (I := I) (M := M) g₀ 4 2 (cometricDoubleTraceField (I := I) g₀ 2) =
        (0 : SmoothCcTensor g₀ 4 3) from
      cometricDoubleTraceField_covGrad_eq_zero (I := I) g₀ 2]
    rw [show iteratedCovGrad (I := I) g₀ 4 3 m (0 : SmoothCcTensor g₀ 4 3) =
        (0 : SmoothCcTensor g₀ 4 (3 + m)) from by
      induction m with
      | zero => rw [iteratedCovGrad_zero]
      | succ m' ih => rw [iteratedCovGrad_succ, ih, covGrad_zero]]
    rw [show ((0 : SmoothCcTensor g₀ 4 (3 + m)).toSection x) =
        (0 : TensorRSSpace 4 (3 + m) I x) from by
      rw [SmoothCcTensor.toSection_zero]; rfl]
    exact riemannianFiberNormSq_zero (I := I) (M := M) g₀ 4 (3 + m) x
  have hBmono : ∀ i' : ℕ,
      (∑ l ∈ Finset.range (i + 1 - i'),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
          ((iteratedCovGrad (I := I) g₀ 0 4 l
            (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)).toSection x)) ≤
      ∑ l ∈ Finset.range (i + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
          ((iteratedCovGrad (I := I) g₀ 0 4 l
            (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)).toSection x) := by
    intro i'
    refine Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_subset_range.mpr (by omega)) ?_
    intro l _ _
    exact riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (4 + l) x _
  have hterm : ∀ i' ∈ Finset.range (i + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + i') x
          ((iteratedCovGrad (I := I) g₀ 4 2 i'
            (cometricDoubleTraceField (I := I) g₀ 2)).toSection x) *
        (∑ l ∈ Finset.range (i + 1 - i'),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 4 l
              (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)).toSection x)) ≤
      (if i' = 0 then
        cPhi * ∑ l ∈ Finset.range (i + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 4 l
              (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)).toSection x)
      else 0) := by
    intro i' _
    match i' with
    | 0 =>
        rw [if_pos rfl]
        have hA0 : riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + 0) x
            ((iteratedCovGrad (I := I) g₀ 4 2 0
              (cometricDoubleTraceField (I := I) g₀ 2)).toSection x) ≤ cPhi := by
          rw [iteratedCovGrad_zero]
          exact hcPhi x
        refine mul_le_mul hA0 (hBmono 0) (Finset.sum_nonneg fun l _ =>
          riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (4 + l) x _) hcPhi_nn
    | (m + 1) =>
        rw [if_neg (by omega)]
        rw [hAzero m, zero_mul]
  refine le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm)
    (appCcGdiag_nonneg (E := E) i)) ?_
  rw [Finset.sum_ite_eq' (Finset.range (i + 1)) 0]
  rw [if_pos (Finset.mem_range.mpr (by omega))]
  have hBgrid : (∑ l ∈ Finset.range (i + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 4 l
          (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)).toSection x)) ≤
      (∑ l ∈ Finset.range (i + 1), CA l) *
        tWindow (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x)) i := by
    calc (∑ l ∈ Finset.range (i + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
          ((iteratedCovGrad (I := I) g₀ 0 4 l
            (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)).toSection x))
        ≤ ∑ l ∈ Finset.range (i + 1), CA l *
            tWindow (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
              ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x)) l := by
          refine Finset.sum_le_sum (fun l _ => ?_)
          have h := hCA g₁ T htie hδ_le hδ0 hbound l x
          rw [← tWindow_eq_tripleSum (I := I) (M := M) g₀ T x l] at h
          exact h
      _ ≤ ∑ l ∈ Finset.range (i + 1), CA l *
            tWindow (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
              ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x)) i := by
          refine Finset.sum_le_sum (fun l hl => ?_)
          refine mul_le_mul_of_nonneg_left ?_ (hCA_nn l)
          exact tWindow_mono _ hb (by
            have := Finset.mem_range.mp hl
            omega)
      _ = (∑ l ∈ Finset.range (i + 1), CA l) *
            tWindow (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
              ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x)) i := by
          rw [Finset.sum_mul]
  rw [← tWindow_eq_tripleSum (I := I) (M := M) g₀ T x i]
  calc appCcGdiag (E := E) i *
        (cPhi * ∑ l ∈ Finset.range (i + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 4 l
              (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)).toSection x))
      ≤ appCcGdiag (E := E) i * (cPhi * ((∑ l ∈ Finset.range (i + 1), CA l) *
          tWindow (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
            ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x)) i)) := by
        refine mul_le_mul_of_nonneg_left ?_ (appCcGdiag_nonneg (E := E) i)
        exact mul_le_mul_of_nonneg_left hBgrid hcPhi_nn
    _ = appCcGdiag (E := E) i * cPhi * (∑ l ∈ Finset.range (i + 1), CA l) *
          tWindow (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
            ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x)) i := by
        ring

set_option linter.unusedSectionVars false in
private lemma diagonalGrid_assembly_arith (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j)
    (i : ℕ) (G : ℝ) (hG : 0 ≤ G)
    (CL CD cbg : ℕ → ℝ) (hCL_nn : ∀ k, 0 ≤ CL k) (hCD_nn : ∀ k, 0 ≤ CD k)
    (hcbg_nn : ∀ k, 0 ≤ cbg k)
    (t u ap : ℝ) (wj vl : ℕ → ℝ)
    (ht : t ≤ 2 * u + 2 * ap)
    (hu : u ≤ CL i * tWindow b i)
    (hap : ap ≤ G * ∑ j ∈ Finset.range (i + 1), wj j * ∑ l ∈ Finset.range (i + 1 - j), vl l)
    (hwj : ∀ j, j ≤ i → wj j ≤ (2 * CL j + 2 * cbg j) * tWindow b j)
    (hvl_nn : ∀ l, 0 ≤ vl l)
    (hvl : ∀ l, l ≤ i → vl l ≤ CD l * Combinatorics.antidiagonalTupleGrid b l) :
    t ≤ (2 * CL i + 2 * (G * ∑ j ∈ Finset.range (i + 1), (2 * CL j + 2 * cbg j) *
        ∑ l ∈ Finset.range (i + 1 - j), CD l * tWindowMulConst j l)) * tWindow b i := by
  have hstep : ∀ j ∈ Finset.range (i + 1),
      wj j * ∑ l ∈ Finset.range (i + 1 - j), vl l ≤
        ((2 * CL j + 2 * cbg j) * ∑ l ∈ Finset.range (i + 1 - j),
          CD l * tWindowMulConst j l) * tWindow b i := by
    intro j hj
    rw [Finset.mem_range] at hj
    have hj_le : j ≤ i := by omega
    have hcj_nn : 0 ≤ 2 * CL j + 2 * cbg j := by
      have := hCL_nn j
      have := hcbg_nn j
      linarith
    have h1 : wj j * ∑ l ∈ Finset.range (i + 1 - j), vl l ≤
        ((2 * CL j + 2 * cbg j) * tWindow b j) * ∑ l ∈ Finset.range (i + 1 - j), vl l :=
      mul_le_mul_of_nonneg_right (hwj j hj_le) (Finset.sum_nonneg (fun l _ => hvl_nn l))
    refine le_trans h1 ?_
    have h2 : ∀ l ∈ Finset.range (i + 1 - j), tWindow b j * vl l ≤
        CD l * tWindowMulConst j l * tWindow b i := by
      intro l hl
      rw [Finset.mem_range] at hl
      have hl_le : l ≤ i := by omega
      have hjl : j + l ≤ i := by omega
      have h3 : tWindow b j * vl l ≤
          tWindow b j * (CD l * Combinatorics.antidiagonalTupleGrid b l) :=
        mul_le_mul_of_nonneg_left (hvl l hl_le) (tWindow_nonneg b hb j)
      refine le_trans h3 ?_
      rw [show tWindow b j * (CD l * Combinatorics.antidiagonalTupleGrid b l) =
          CD l * (tWindow b j * Combinatorics.antidiagonalTupleGrid b l) from by ring]
      calc CD l * (tWindow b j * Combinatorics.antidiagonalTupleGrid b l)
          ≤ CD l * (tWindowMulConst j l * tWindow b (j + l)) :=
            mul_le_mul_of_nonneg_left
              (tWindow_mul_antidiagonalTupleGrid_le b hb j l) (hCD_nn l)
        _ ≤ CD l * (tWindowMulConst j l * tWindow b i) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left (tWindow_mono b hb hjl)
                (tWindowMulConst_nonneg j l)) (hCD_nn l)
        _ = CD l * tWindowMulConst j l * tWindow b i := by ring
    calc ((2 * CL j + 2 * cbg j) * tWindow b j) * ∑ l ∈ Finset.range (i + 1 - j), vl l
        = (2 * CL j + 2 * cbg j) * ∑ l ∈ Finset.range (i + 1 - j), tWindow b j * vl l := by
          rw [mul_assoc, Finset.mul_sum]
      _ ≤ (2 * CL j + 2 * cbg j) * ∑ l ∈ Finset.range (i + 1 - j),
            CD l * tWindowMulConst j l * tWindow b i :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum h2) hcj_nn
      _ = ((2 * CL j + 2 * cbg j) * ∑ l ∈ Finset.range (i + 1 - j),
            CD l * tWindowMulConst j l) * tWindow b i := by
          rw [← Finset.sum_mul]
          ring
  have hW_nn : 0 ≤ tWindow b i := tWindow_nonneg b hb i
  have hap2 : ap ≤ G * ((∑ j ∈ Finset.range (i + 1), (2 * CL j + 2 * cbg j) *
      ∑ l ∈ Finset.range (i + 1 - j), CD l * tWindowMulConst j l) * tWindow b i) := by
    refine le_trans hap ?_
    refine mul_le_mul_of_nonneg_left ?_ hG
    refine le_trans (Finset.sum_le_sum hstep) (le_of_eq ?_)
    rw [← Finset.sum_mul]
  have hu2 : u ≤ CL i * tWindow b i := hu
  calc t ≤ 2 * u + 2 * ap := ht
    _ ≤ 2 * (CL i * tWindow b i) + 2 * (G * ((∑ j ∈ Finset.range (i + 1),
          (2 * CL j + 2 * cbg j) * ∑ l ∈ Finset.range (i + 1 - j),
            CD l * tWindowMulConst j l) * tWindow b i)) := by linarith
    _ = (2 * CL i + 2 * (G * ∑ j ∈ Finset.range (i + 1), (2 * CL j + 2 * cbg j) *
          ∑ l ∈ Finset.range (i + 1 - j), CD l * tWindowMulConst j l)) * tWindow b i := by
        ring

set_option linter.unusedVariables false in
theorem rfns_iteratedCovGrad_slotInsertEndoCc_zero_ricEndoBackgroundDifferenceField_diagonalProductGrid_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
            ((iteratedCovGrad (I := I) g₀ 1 1 i
              (slotInsertEndoCc (I := I) (M := M) g₀ 0
                (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁))).toSection x) ≤
          C i * ∑ k ∈ Finset.range (i + 3),
            ∑ n ∈ Finset.range (k + 1),
              ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
                ∏ m : Fin n,
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T).toSection x) := by
  classical
  obtain ⟨CL, hCL_nn, hCL⟩ :=
    rfns_iteratedCovGrad_ricciMixedSharpBackgroundDifference_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨CD, hCD_nn, hCD⟩ :=
    rfns_iteratedCovGrad_slotInsertEndoCc_zero_gInvDiffRaisedEndoField_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨cbg, hcbg_nn, hcbg⟩ := exists_backgroundJet_rfns_bound (I := I) (M := M) g₀ 1 1
    (slotInsertEndoCc (I := I) (M := M) g₀ 0 (ricEndoRaisedField (I := I) (M := M) g₀))
  refine ⟨fun i => 2 * CL i + 2 * (appCcGdiag (E := E) i *
      ∑ j ∈ Finset.range (i + 1), (2 * CL j + 2 * cbg j) *
        ∑ l ∈ Finset.range (i + 1 - j), CD l * tWindowMulConst j l),
    fun i => ?_, ?_⟩
  · have h1 : 0 ≤ appCcGdiag (E := E) i := appCcGdiag_nonneg (E := E) i
    have h2 : 0 ≤ ∑ j ∈ Finset.range (i + 1), (2 * CL j + 2 * cbg j) *
        ∑ l ∈ Finset.range (i + 1 - j), CD l * tWindowMulConst j l :=
      Finset.sum_nonneg (fun j _ => mul_nonneg
        (by have := hCL_nn j; have := hcbg_nn j; linarith)
        (Finset.sum_nonneg (fun l _ => mul_nonneg (hCD_nn l) (tWindowMulConst_nonneg j l))))
    have h3 := mul_nonneg h1 h2
    have h4 := hCL_nn i
    linarith
  · intro g₁ T htie δ hδ_le hδ0 hbound i x
    have hb : ∀ j : ℕ, 0 ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x) :=
      fun j => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + j) x _
    rw [← tWindow_eq_tripleSum (I := I) (M := M) g₀ T x i]
    have hsec : (iteratedCovGrad (I := I) g₀ 1 1 i
        (slotInsertEndoCc (I := I) (M := M) g₀ 0
          (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁))).toSection x =
        (iteratedCovGrad (I := I) g₀ 1 1 i
          (slotInsertEndoCc (I := I) (M := M) g₀ 0
              (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁) -
            slotInsertEndoCc (I := I) (M := M) g₀ 0
              (ricEndoRaisedField (I := I) (M := M) g₀))).toSection x +
          (iteratedCovGrad (I := I) g₀ 1 1 i
            (appCcRS (I := I) (M := M) g₀ 1 1 1
              (slotInsertEndoCc (I := I) (M := M) g₀ 0
                (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁))
              (slotInsertEndoCc (I := I) (M := M) g₀ 0
                (gInvDiffRaisedEndoField (I := I) g₀ g₁)))).toSection x := by
      rw [slotInsertEndoCc_zero_ricEndoBackgroundDifference_telescope (I := I) (M := M) g₀ g₁,
        iteratedCovGrad_add (I := I) g₀ 1 1 i _ _, SmoothCcTensor.toSection_add]
      rfl
    have hLHS : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 1 i
          (slotInsertEndoCc (I := I) (M := M) g₀ 0
            (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁))).toSection x) ≤
        2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
            ((iteratedCovGrad (I := I) g₀ 1 1 i
              (slotInsertEndoCc (I := I) (M := M) g₀ 0
                  (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁) -
                slotInsertEndoCc (I := I) (M := M) g₀ 0
                  (ricEndoRaisedField (I := I) (M := M) g₀))).toSection x) +
          2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
            ((iteratedCovGrad (I := I) g₀ 1 1 i
              (appCcRS (I := I) (M := M) g₀ 1 1 1
                (slotInsertEndoCc (I := I) (M := M) g₀ 0
                  (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁))
                (slotInsertEndoCc (I := I) (M := M) g₀ 0
                  (gInvDiffRaisedEndoField (I := I) g₀ g₁)))).toSection x) := by
      rw [hsec]
      exact riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 1 (1 + i) x _ _
    have hu : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 1 i
          (slotInsertEndoCc (I := I) (M := M) g₀ 0
              (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁) -
            slotInsertEndoCc (I := I) (M := M) g₀ 0
              (ricEndoRaisedField (I := I) (M := M) g₀))).toSection x) ≤
        CL i * tWindow (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x)) i := by
      rw [tWindow_eq_tripleSum (I := I) (M := M) g₀ T x i]
      exact hCL g₁ T htie hδ_le hδ0 hbound i x
    have hap := rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le
      (I := I) (M := M) g₀ i 1 1 1
      (slotInsertEndoCc (I := I) (M := M) g₀ 0 (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁))
      (slotInsertEndoCc (I := I) (M := M) g₀ 0 (gInvDiffRaisedEndoField (I := I) g₀ g₁)) x
    have hwj : ∀ j, j ≤ i → riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + j) x
        ((iteratedCovGrad (I := I) g₀ 1 1 j
          (slotInsertEndoCc (I := I) (M := M) g₀ 0
            (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁))).toSection x) ≤
        (2 * CL j + 2 * cbg j) *
          tWindow (fun j' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j') x
            ((iteratedCovGrad (I := I) g₀ 0 2 j' T).toSection x)) j := by
      intro j hj
      have hsplit : slotInsertEndoCc (I := I) (M := M) g₀ 0
          (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁) =
          (slotInsertEndoCc (I := I) (M := M) g₀ 0
              (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁) -
            slotInsertEndoCc (I := I) (M := M) g₀ 0
              (ricEndoRaisedField (I := I) (M := M) g₀)) +
          slotInsertEndoCc (I := I) (M := M) g₀ 0
            (ricEndoRaisedField (I := I) (M := M) g₀) := by
        rw [sub_add_cancel]
      have hsec2 : (iteratedCovGrad (I := I) g₀ 1 1 j
          (slotInsertEndoCc (I := I) (M := M) g₀ 0
            (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁))).toSection x =
          (iteratedCovGrad (I := I) g₀ 1 1 j
            (slotInsertEndoCc (I := I) (M := M) g₀ 0
                (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁) -
              slotInsertEndoCc (I := I) (M := M) g₀ 0
                (ricEndoRaisedField (I := I) (M := M) g₀))).toSection x +
            (iteratedCovGrad (I := I) g₀ 1 1 j
              (slotInsertEndoCc (I := I) (M := M) g₀ 0
                (ricEndoRaisedField (I := I) (M := M) g₀))).toSection x := by
        conv_lhs => rw [hsplit]
        rw [iteratedCovGrad_add (I := I) g₀ 1 1 j _ _, SmoothCcTensor.toSection_add]
        rfl
      rw [hsec2]
      refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 1 (1 + j) x _ _) ?_
      have hone : 1 ≤ tWindow (fun j' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j') x
          ((iteratedCovGrad (I := I) g₀ 0 2 j' T).toSection x)) j :=
        one_le_tWindow _ hb j
      have hb1 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + j) x
          ((iteratedCovGrad (I := I) g₀ 1 1 j
            (slotInsertEndoCc (I := I) (M := M) g₀ 0
                (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁) -
              slotInsertEndoCc (I := I) (M := M) g₀ 0
                (ricEndoRaisedField (I := I) (M := M) g₀))).toSection x) ≤
          CL j * tWindow (fun j' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j') x
            ((iteratedCovGrad (I := I) g₀ 0 2 j' T).toSection x)) j := by
        rw [tWindow_eq_tripleSum (I := I) (M := M) g₀ T x j]
        exact hCL g₁ T htie hδ_le hδ0 hbound j x
      have hb2 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + j) x
          ((iteratedCovGrad (I := I) g₀ 1 1 j
            (slotInsertEndoCc (I := I) (M := M) g₀ 0
              (ricEndoRaisedField (I := I) (M := M) g₀))).toSection x) ≤
          cbg j * tWindow (fun j' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j') x
            ((iteratedCovGrad (I := I) g₀ 0 2 j' T).toSection x)) j :=
        le_trans (hcbg j x) (le_mul_of_one_le_right (hcbg_nn j) hone)
      linarith
    have hvl : ∀ l, l ≤ i → riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
        ((iteratedCovGrad (I := I) g₀ 1 1 l
          (slotInsertEndoCc (I := I) (M := M) g₀ 0
            (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection x) ≤
        CD l * Combinatorics.antidiagonalTupleGrid
          (fun j' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j') x
            ((iteratedCovGrad (I := I) g₀ 0 2 j' T).toSection x)) l := by
      intro l _
      rw [antidiagonalTupleGrid_eq_doubleSum (I := I) (M := M) g₀ T x l]
      exact hCD g₁ T htie hδ_le hδ0 hbound l x
    exact diagonalGrid_assembly_arith
      (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x)) hb i
      (appCcGdiag (E := E) i) (appCcGdiag_nonneg (E := E) i)
      CL CD cbg hCL_nn hCD_nn hcbg_nn
      (riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 1 i
          (slotInsertEndoCc (I := I) (M := M) g₀ 0
            (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁))).toSection x))
      (riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 1 i
          (slotInsertEndoCc (I := I) (M := M) g₀ 0
              (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁) -
            slotInsertEndoCc (I := I) (M := M) g₀ 0
              (ricEndoRaisedField (I := I) (M := M) g₀))).toSection x))
      (riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 1 i
          (appCcRS (I := I) (M := M) g₀ 1 1 1
            (slotInsertEndoCc (I := I) (M := M) g₀ 0
              (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁))
            (slotInsertEndoCc (I := I) (M := M) g₀ 0
              (gInvDiffRaisedEndoField (I := I) g₀ g₁)))).toSection x))
      (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + j) x
        ((iteratedCovGrad (I := I) g₀ 1 1 j
          (slotInsertEndoCc (I := I) (M := M) g₀ 0
            (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁))).toSection x))
      (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
        ((iteratedCovGrad (I := I) g₀ 1 1 l
          (slotInsertEndoCc (I := I) (M := M) g₀ 0
            (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection x))
      hLHS hu hap hwj
      (fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 (1 + l) x _)
      hvl

section RiemannMixedBiContr

set_option backward.isDefEq.respectTransparency false

open DifferentialGeometry.Integral.DivergenceTheorem

def riemannMixedKernelBilin (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (p q : TangentSpace I x) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap
    { toFun := fun v0 => (g₀.inner x (riemannOp (LeviCivita (I := I) g₁) x v0 p q))
      map_add' := fun v0 v0' => by
        rw [(riemannOp (LeviCivita (I := I) g₁) x).map_add v0 v0',
          ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply, map_add]
      map_smul' := fun c v0 => by
        rw [(riemannOp (LeviCivita (I := I) g₁) x).map_smul c v0,
          ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, map_smul,
          RingHom.id_apply] }

set_option linter.unusedSectionVars false in
@[simp] theorem riemannMixedKernelBilin_apply (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (p q v0 v1 : TangentSpace I x) :
    riemannMixedKernelBilin (I := I) g₀ g₁ x p q v0 v1 =
      g₀.inner x (riemannOp (LeviCivita (I := I) g₁) x v0 p q) v1 := by
  rw [riemannMixedKernelBilin, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk,
    AddHom.coe_mk]

def riemannMixedSummandFib (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (p q : TangentSpace I x) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  haveI : FiniteDimensional ℝ (Tensor0SSpace 2 I x) := inferInstance
  LinearMap.toContinuousLinearMap
    { toFun := fun D =>
        (Tensor0SSpace.toModel D ![(p : E), (q : E)]) •
          Tensor0SSpace.ofModel (I := I) (x := x)
            (bilinFormToModel E (riemannMixedKernelBilin (I := I) g₀ g₁ x p q))
      map_add' := fun D D' => by
        rw [Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply, add_smul]
      map_smul' := fun c D => by
        rw [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul,
          RingHom.id_apply, mul_smul] }

set_option linter.unusedSectionVars false in
@[simp] theorem riemannMixedSummandFib_toModel (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (p q : TangentSpace I x) (D : Tensor0SSpace 2 I x) (v : Fin 2 → E) :
    Tensor0SSpace.toModel (riemannMixedSummandFib (I := I) g₀ g₁ x p q D) v =
      (Tensor0SSpace.toModel D ![(p : E), (q : E)]) *
        g₀.inner x (riemannOp (LeviCivita (I := I) g₁) x (v 0) p q) (v 1) := by
  rw [riemannMixedSummandFib, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk,
    AddHom.coe_mk, Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply,
    Tensor0SSpace.toModel_ofModel, bilinFormToModel_apply, smul_eq_mul]
  rfl

def riemannMixedBiContrFibFixedFrame (g₀ g₁ : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  (2 : ℝ) • ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
    riemannMixedSummandFib (I := I) g₀ g₁ x (B a x) (B b x)

set_option linter.unusedSectionVars false in
theorem riemannMixedBiContrFibFixedFrame_toModel (g₀ g₁ : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b) (x : M)
    (D : Tensor0SSpace 2 I x) (v : Fin 2 → E) :
    Tensor0SSpace.toModel (riemannMixedBiContrFibFixedFrame (I := I) g₀ g₁ B x D) v =
      2 * ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        g₀.inner x (riemannOp (LeviCivita (I := I) g₁) x (v 0) (B a x) (B b x)) (v 1) *
          Tensor0SSpace.toModel D ![(B a x : E), (B b x : E)] := by
  classical
  rw [riemannMixedBiContrFibFixedFrame, ContinuousLinearMap.smul_apply,
    Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  congr 1
  rw [ContinuousLinearMap.sum_apply, ← Tensor0SSpace.toModelL_apply, map_sum,
    ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [ContinuousLinearMap.sum_apply, Tensor0SSpace.toModelL_apply, ← Tensor0SSpace.toModelL_apply,
    map_sum, ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Tensor0SSpace.toModelL_apply, riemannMixedSummandFib_toModel]
  ring

set_option linter.unusedSectionVars false in
theorem mixedKernelScalar_global (g₀ g₁ : SmoothRiemannianMetric I M)
    {Y W p q : Π b : M, TangentSpace I b}
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Y))
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% W))
    (hp : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% p))
    (hq : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% q)) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x : M => g₀.inner x
        (riemannOp (LeviCivita (I := I) g₁) x (Y x) (p x) (q x)) (W x)) := by
  classical
  have hRsec : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b : M => riemannSec (LeviCivita (I := I) g₁) Y p q b)) :=
    riemannSec_contMDiff (cov := LeviCivita (I := I) g₁) hY hp hq
  have hcongr : (fun x : M => g₀.inner x
        (riemannOp (LeviCivita (I := I) g₁) x (Y x) (p x) (q x)) (W x)) =
      (fun x : M => g₀.inner x (riemannSec (LeviCivita (I := I) g₁) Y p q x) (W x)) := by
    funext x
    rw [riemannOp_apply_smooth (cov := LeviCivita (I := I) g₁) hY hp hq]
  rw [hcongr]
  exact contMDiff_g_inner_of_smooth_sections (I := I) g₀
    ⟨fun b => riemannSec (LeviCivita (I := I) g₁) Y p q b, hRsec⟩ ⟨fun b => W b, hW⟩

set_option linter.unusedSectionVars false in
theorem riemannMixedKernelBilin_homSection_contMDiff (g₀ g₁ : SmoothRiemannianMetric I M)
    {p q : Π b : M, TangentSpace I b}
    (hp : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% p))
    (hq : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% q)) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun b : M => TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ)
        x (riemannMixedKernelBilin (I := I) g₀ g₁ x (p x) (q x))) := by
  classical
  apply cotangentCov_clmSection_smooth_aux
    (V₂ := fun x : M => TangentSpace I x →L[ℝ] ℝ)
    (φ := fun x : M => riemannMixedKernelBilin (I := I) g₀ g₁ x (p x) (q x))
  intro Y
  apply cotangentCov_clmSection_smooth_aux
    (V₂ := fun _ : M => ℝ)
    (φ := fun x : M => riemannMixedKernelBilin (I := I) g₀ g₁ x (p x) (q x) (Y x))
  intro W
  have h_scalar := mixedKernelScalar_global (I := I) g₀ g₁ Y.contMDiff W.contMDiff hp hq
  intro x
  rw [contMDiffAt_section]
  refine (h_scalar.contMDiffAt).congr_of_eventuallyEq ?_
  filter_upwards with y
  change riemannMixedKernelBilin (I := I) g₀ g₁ y (p y) (q y) (Y y) (W y) =
    (trivializationAt ℝ (Bundle.Trivial M ℝ) x ⟨y, _⟩).2
  rw [riemannMixedKernelBilin_apply]
  rfl

set_option linter.unusedSectionVars false in
theorem riemannMixedBiContrFibFixedFrame_apply_section_contMDiff
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)))
    (Y : Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun x : M => Tensor0SSpace 2 I x⟯) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) x
        (riemannMixedBiContrFibFixedFrame (I := I) g₀ g₁ B x (Y x))) := by
  classical
  have hsummand : ∀ a b : Fin (Module.finrank ℝ E),
      ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
          (E := fun z : M => Tensor0SSpace 2 I z) x
          (riemannMixedSummandFib (I := I) g₀ g₁ x (B a x) (B b x) (Y x))) := by
    intro a b
    have hscalar : ContMDiff I 𝓘(ℝ, ℝ) ∞
        (fun x : M => Tensor0SSpace.toModel (Y x) ![(B a x : E), (B b x : E)]) := by
      have h := TensorMultilinear.contMDiff_section_apply (n := 2)
        (fun b => Y b) Y.contMDiff
        (![fun z => B a z, fun z => B b z])
        (by
          intro i
          fin_cases i
          · exact hB a
          · exact hB b)
      refine h.congr ?_
      intro x
      congr 1
      funext i
      fin_cases i <;> rfl
    have hbilin := contMDiff_bilinSection_of_homSection (I := I)
      (fun x => riemannMixedKernelBilin (I := I) g₀ g₁ x (B a x) (B b x))
      (riemannMixedKernelBilin_homSection_contMDiff (I := I) g₀ g₁ (hB a) (hB b))
    have hsmul := ContMDiff.smul_section (f := fun x => Tensor0SSpace.toModel (Y x)
        ![(B a x : E), (B b x : E)])
      (s := fun x => Tensor0SSpace.ofModel (I := I) (x := x)
        (bilinFormToModel (TangentSpace I x)
          (riemannMixedKernelBilin (I := I) g₀ g₁ x (B a x) (B b x))))
      hscalar hbilin
    refine hsmul.congr ?_
    intro x
    rfl
  set S : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯ :=
    fun a b =>
      { toFun := fun x : M => riemannMixedSummandFib (I := I) g₀ g₁ x (B a x) (B b x) (Y x)
        contMDiff_toFun := hsummand a b } with hS_def
  set Stot : Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯ :=
    (2 : ℝ) • ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), S a b
    with hStot_def
  have hStot := Stot.contMDiff
  refine hStot.congr ?_
  intro x
  refine congrArg (TotalSpace.mk' (Tensor0SModel 2 ℝ E)
    (E := fun z : M => Tensor0SSpace 2 I z) x) ?_
  rw [riemannMixedBiContrFibFixedFrame, hStot_def, ContMDiffSection.coe_smul, Pi.smul_apply]
  have hcoeOuter : ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), S a b :
      Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
        Π z : M, Tensor0SSpace 2 I z) =
      ∑ a : Fin (Module.finrank ℝ E),
        ((∑ b : Fin (Module.finrank ℝ E), S a b :
          Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
          Π z : M, Tensor0SSpace 2 I z) :=
    map_sum (ContMDiffSection.coeAddHom I (Tensor0SModel 2 ℝ E) ∞
      (fun z : M => Tensor0SSpace 2 I z))
      (fun a => ∑ b : Fin (Module.finrank ℝ E), S a b) Finset.univ
  have hcoeInner : ∀ a : Fin (Module.finrank ℝ E),
      ((∑ b : Fin (Module.finrank ℝ E), S a b :
        Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
        Π z : M, Tensor0SSpace 2 I z) =
      ∑ b : Fin (Module.finrank ℝ E), ((S a b : Π z : M, Tensor0SSpace 2 I z)) := fun a =>
    map_sum (ContMDiffSection.coeAddHom I (Tensor0SModel 2 ℝ E) ∞
      (fun z : M => Tensor0SSpace 2 I z)) (fun b => S a b) Finset.univ
  have hsum : ((∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E), S a b :
      Cₛ^∞⟮I; Tensor0SModel 2 ℝ E, fun z : M => Tensor0SSpace 2 I z⟯) :
        Π z : M, Tensor0SSpace 2 I z) x =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        (S a b : Π z : M, Tensor0SSpace 2 I z) x := by
    rw [hcoeOuter, Finset.sum_apply]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [hcoeInner a, Finset.sum_apply]
  rw [hsum, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply]
  congr 1
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [ContinuousLinearMap.sum_apply]
  rfl

set_option linter.unusedSectionVars false in
theorem riemannMixedBiContrFibFixedFrame_contMDiff (g₀ g₁ : SmoothRiemannianMetric I M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i))) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (riemannMixedBiContrFibFixedFrame (I := I) g₀ g₁ B x))) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I)
    (F₁ := Tensor0SModel 2 ℝ E) (V₁ := fun z : M => Tensor0SSpace 2 I z)
    (F₂ := Tensor0SModel 2 ℝ E) (V₂ := fun z : M => Tensor0SSpace 2 I z)
    (φ := fun x : M => riemannMixedBiContrFibFixedFrame (I := I) g₀ g₁ B x)
  intro Y
  exact riemannMixedBiContrFibFixedFrame_apply_section_contMDiff (I := I) g₀ g₁ B hB Y

def frameRiemannMixedKernel (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (v0 v1 : TangentSpace I x) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap
    { toFun := fun p => (g₀.inner x).flip v1 |>.comp
        ((riemannOp (LeviCivita (I := I) g₁) x v0 p))
      map_add' := fun p p' => by
        ext q
        simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
          (riemannOp (LeviCivita (I := I) g₁) x v0).map_add p p', map_add]
      map_smul' := fun c p => by
        ext q
        simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
          RingHom.id_apply, (riemannOp (LeviCivita (I := I) g₁) x v0).map_smul c p, map_smul] }

set_option linter.unusedSectionVars false in
theorem frameRiemannMixedKernel_apply (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (v0 v1 p q : TangentSpace I x) :
    frameRiemannMixedKernel (I := I) g₀ g₁ x v0 v1 p q =
      g₀.inner x (riemannOp (LeviCivita (I := I) g₁) x v0 p q) v1 := by
  rw [frameRiemannMixedKernel, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk,
    AddHom.coe_mk, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply]

def riemannMixedBiContrFib (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x :=
  riemannMixedBiContrFibFixedFrame (I := I) g₀ g₁ (smoothOrthoFrame (I := I) g₀ x) x

set_option linter.unusedSectionVars false in
theorem riemannMixedBiContrFib_eq_fixedFrame_on_nbhd (g₀ g₁ : SmoothRiemannianMetric I M)
    (x₀ : M) {y : M} (hy : y ∈ smoothOrthoFrameNbhd (I := I) (M := M) x₀) :
    riemannMixedBiContrFib (I := I) (M := M) g₀ g₁ y =
      riemannMixedBiContrFibFixedFrame (I := I) g₀ g₁ (smoothOrthoFrame (I := I) g₀ x₀) y := by
  classical
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  rw [riemannMixedBiContrFib, riemannMixedBiContrFibFixedFrame_toModel,
    riemannMixedBiContrFibFixedFrame_toModel]
  apply congrArg (fun z : ℝ => 2 * z)
  have hrewrite : ∀ (Bf : Fin (Module.finrank ℝ E) → TangentSpace I y),
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        g₀.inner y (riemannOp (LeviCivita (I := I) g₁) y (v 0) (Bf a) (Bf b)) (v 1) *
          Tensor0SSpace.toModel D ![(Bf a : E), (Bf b : E)] =
      ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        frameRiemannMixedKernel (I := I) g₀ g₁ y (v 0) (v 1) (Bf a) (Bf b) *
          (bilinFormToModel (TangentSpace I y)).symm (Tensor0SSpace.toModel D) (Bf a) (Bf b) := by
    intro Bf
    refine Finset.sum_congr rfl (fun a _ => ?_)
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [frameRiemannMixedKernel_apply (I := I) g₀ g₁ y (v 0) (v 1) (Bf a) (Bf b),
      bilinFormToModel_symm_apply (TangentSpace I y) (Tensor0SSpace.toModel D) (Bf a) (Bf b)]
    rfl
  rw [hrewrite (fun a => smoothOrthoFrame (I := I) g₀ y a y),
    hrewrite (fun a => smoothOrthoFrame (I := I) g₀ x₀ a y)]
  exact double_frame_bilin_trace_indep (I := I) g₀ y
    (frameRiemannMixedKernel (I := I) g₀ g₁ y (v 0) (v 1))
    ((bilinFormToModel (TangentSpace I y)).symm (Tensor0SSpace.toModel D))
    (fun a => smoothOrthoFrame (I := I) g₀ y a y)
    (fun a => smoothOrthoFrame (I := I) g₀ x₀ a y)
    (fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g₀ y i j)
    (fun i j => smoothOrthoFrame_orthonormal (I := I) g₀ x₀ hy i j)

set_option linter.unusedSectionVars false in
theorem riemannMixedBiContrFib_contMDiff (g₀ g₁ : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (riemannMixedBiContrFib (I := I) (M := M) g₀ g₁ x))) := by
  classical
  intro x₀
  have h_fixed : ContMDiffAt I (I.prod 𝓘(ℝ, TensorRSModel 2 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
        (E := fun z : M => TensorRSSpace 2 2 I z) x
        (TensorRSSpace.ofCLM (riemannMixedBiContrFibFixedFrame (I := I) g₀ g₁
          (smoothOrthoFrame (I := I) g₀ x₀) x))) x₀ :=
    riemannMixedBiContrFibFixedFrame_contMDiff (I := I) g₀ g₁ (smoothOrthoFrame (I := I) g₀ x₀)
      (fun i => smoothOrthoFrame_smooth (I := I) g₀ x₀ i) x₀
  refine h_fixed.congr_of_eventuallyEq ?_
  filter_upwards [smoothOrthoFrameNbhd_mem_nhds (I := I) (M := M) x₀] with y hy
  exact congrArg (TotalSpace.mk' (TensorRSModel 2 2 ℝ E)
    (E := fun z : M => TensorRSSpace 2 2 I z) y)
    (congrArg TensorRSSpace.ofCLM
      (riemannMixedBiContrFib_eq_fixedFrame_on_nbhd (I := I) g₀ g₁ x₀ hy))

def ricciArmOrder0RiemannMixedCoeff (g₀ g₁ : SmoothRiemannianMetric I M) :
    SmoothCcTensor g₀ 2 2 where
  toSection :=
    { toFun := fun x : M =>
        (show TensorRSSpace 2 2 I x from
          TensorRSSpace.ofCLM (riemannMixedBiContrFib (I := I) (M := M) g₀ g₁ x))
      contMDiff_toFun := riemannMixedBiContrFib_contMDiff (I := I) (M := M) g₀ g₁ }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option linter.unusedSectionVars false in
theorem ricciArmOrder0RiemannMixedCoeff_toSection (g₀ g₁ : SmoothRiemannianMetric I M) (x : M) :
    (ricciArmOrder0RiemannMixedCoeff (I := I) (M := M) g₀ g₁).toSection x =
      (show TensorRSSpace 2 2 I x from
        TensorRSSpace.ofCLM (riemannMixedBiContrFib (I := I) (M := M) g₀ g₁ x)) := rfl

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
theorem ricciArmOrder0RiemannMixedCoeff_self (g₀ : SmoothRiemannianMetric I M) :
    ricciArmOrder0RiemannMixedCoeff (I := I) (M := M) g₀ g₀ =
      ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  rw [show ((ricciArmOrder0RiemannMixedCoeff (I := I) (M := M) g₀ g₀).toSection x) D =
      riemannMixedBiContrFib (I := I) (M := M) g₀ g₀ x D from rfl]
  rw [show ((ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀).toSection x) D =
      riemannBiContrFib (I := I) g₀ x D from rfl]
  rw [riemannMixedBiContrFib, riemannBiContrFib, riemannMixedBiContrFibFixedFrame_toModel,
    riemannBiContrFibFixedFrame_toModel]

end RiemannMixedBiContr

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
private lemma appCcRS_zero_left_cc (g₀ : SmoothRiemannianMetric I M) (a b c : ℕ)
    (W : SmoothCcTensor g₀ a b) :
    appCcRS (I := I) (M := M) g₀ a b c (0 : SmoothCcTensor g₀ b c) W = 0 := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  rw [show ((appCcRS (I := I) (M := M) g₀ a b c (0 : SmoothCcTensor g₀ b c) W).toSection x) D =
      ((show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from
        (0 : SmoothCcTensor g₀ b c).toSection x)
        ((show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from W.toSection x) D)) from by
    rw [appCcRS_toSection]
    rfl]
  rw [show ((0 : SmoothCcTensor g₀ b c).toSection x) = (0 : TensorRSSpace b c I x) from by
    rw [SmoothCcTensor.toSection_zero]; rfl]
  rw [show ((0 : SmoothCcTensor g₀ a c).toSection x) = (0 : TensorRSSpace a c I x) from by
    rw [SmoothCcTensor.toSection_zero]; rfl]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
private lemma appCcRS_right_zero_cc (g₀ : SmoothRiemannianMetric I M) (a b c : ℕ)
    (Φ : SmoothCcTensor g₀ b c) :
    appCcRS (I := I) (M := M) g₀ a b c Φ (0 : SmoothCcTensor g₀ a b) = 0 := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  rw [show ((appCcRS (I := I) (M := M) g₀ a b c Φ (0 : SmoothCcTensor g₀ a b)).toSection x) D =
      ((show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φ.toSection x)
        ((show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from
          (0 : SmoothCcTensor g₀ a b).toSection x) D)) from by
    rw [appCcRS_toSection]
    rfl]
  rw [show ((0 : SmoothCcTensor g₀ a b).toSection x) = (0 : TensorRSSpace a b I x) from by
    rw [SmoothCcTensor.toSection_zero]; rfl]
  rw [show ((0 : SmoothCcTensor g₀ a c).toSection x) = (0 : TensorRSSpace a c I x) from by
    rw [SmoothCcTensor.toSection_zero]; rfl]
  rw [show ((show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from
      (0 : TensorRSSpace a b I x)) D) = 0 from rfl]
  rw [map_zero]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
private lemma covGrad_slotExtend_toSection_rsDomDomCongr_b
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (Φ : SmoothCcTensor g r s) (x : M) :
    (covGrad (I := I) (M := M) g (r + 1) (s + 1)
        (slotExtend (I := I) (M := M) g r s Φ)).toSection x =
      rsDomDomCongr (I := I) (M := M) (r := r + 1) (Equiv.swap (0 : Fin (s + 1 + 1)) 1)
        ((slotExtend (I := I) (M := M) g r (s + 1)
          (covGrad (I := I) (M := M) g r s Φ)).toSection x) := by
  classical
  apply ContinuousLinearMap.ext
  intro d
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun m => ?_)
  have hfib : ∀ (y : Tensor0SSpace (s + 1 + 1) I x) (w : Fin (s + 1 + 1) → TangentSpace I x),
      Tensor0SSpace.toModel y w = (y : Tensor0SSpace (s + 1 + 1) I x) w := fun _ _ => rfl
  conv_rhs => rw [hfib, rsDomDomCongr_apply_eval (I := I) (M := M) (r := r + 1)
    (Equiv.swap (0 : Fin (s + 1 + 1)) 1)
    ((slotExtend (I := I) (M := M) g r (s + 1) (covGrad (I := I) (M := M) g r s Φ)).toSection x) d m]
  conv_rhs => rw [← hfib]
  rw [covGrad_toSection_apply_eval (I := I) (M := M) g (r + 1) (s + 1)
    (slotExtend (I := I) (M := M) g r s Φ) x d m]
  rw [DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurck.tensorCovDerivAt_slotExtend_eq
    (I := I) (M := M) g r s Φ x (m 0)]
  rw [show Matrix.vecTail m =
      Fin.cons (m 1) (fun k : Fin s => m (Fin.succ (Fin.succ k))) from by
    funext k
    refine Fin.cases ?_ (fun i => ?_) k
    · change m (Fin.succ 0) = _
      rw [Fin.cons_zero]; rfl
    · change m (Fin.succ (Fin.succ i)) = _
      rw [Fin.cons_succ]]
  rw [slotExtendFib_apply_eval (I := I) (M := M) g r s x
    (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
      tensorCovDerivAt (I := I) (M := M) g r s Φ x (m 0))
    d (m 1) (fun k : Fin s => m (Fin.succ (Fin.succ k)))]
  rw [slotExtend_toSection (I := I) (M := M) g r (s + 1) (covGrad (I := I) (M := M) g r s Φ) x]
  rw [show (fun k => m ((Equiv.swap (0 : Fin (s + 1 + 1)) 1) k)) =
      Fin.cons (m 1) (fun k : Fin (s + 1) => m ((Equiv.swap (0 : Fin (s + 1 + 1)) 1) (Fin.succ k)))
      from by
    funext k
    refine Fin.cases ?_ (fun i => ?_) k
    · simp only [Fin.cons_zero]
      rw [Equiv.swap_apply_left]
    · rw [Fin.cons_succ]]
  rw [slotExtendFib_apply_eval (I := I) (M := M) g r (s + 1) x
    (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (s + 1) I x from
      (covGrad (I := I) (M := M) g r s Φ).toSection x)
    d (m 1) (fun k : Fin (s + 1) => m ((Equiv.swap (0 : Fin (s + 1 + 1)) 1) (Fin.succ k)))]
  rw [covGrad_toSection_apply_eval (I := I) (M := M) g r s Φ x
    ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) r x) d (m 1))
    (fun k : Fin (s + 1) => m ((Equiv.swap (0 : Fin (s + 1 + 1)) 1) (Fin.succ k)))]
  have hdir : m ((Equiv.swap (0 : Fin (s + 1 + 1)) 1) (Fin.succ (0 : Fin (s + 1)))) = m 0 := by
    rw [show (Fin.succ (0 : Fin (s + 1)) : Fin (s + 1 + 1)) = 1 from rfl, Equiv.swap_apply_right]
  have htail : (Matrix.vecTail (fun k : Fin (s + 1) =>
        m ((Equiv.swap (0 : Fin (s + 1 + 1)) 1) (Fin.succ k)))) =
      (fun k : Fin s => m (Fin.succ (Fin.succ k))) := by
    funext k
    change m ((Equiv.swap (0 : Fin (s + 1 + 1)) 1) (Fin.succ (Fin.succ k))) =
      m (Fin.succ (Fin.succ k))
    rw [Equiv.swap_apply_of_ne_of_ne]
    · exact (Fin.succ_ne_zero _)
    · rw [show (1 : Fin (s + 1 + 1)) = Fin.succ (0 : Fin (s + 1)) from rfl]
      exact fun h => Fin.succ_ne_zero _ (Fin.succ_injective _ h)
  rw [hdir, htail]

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
private lemma slotExtend_zero_cc (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    slotExtend (I := I) (M := M) g r s (0 : SmoothCcTensor g r s) = 0 := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun m => ?_)
  rw [show ((show Tensor0SSpace (r + 1) I x →L[ℝ] Tensor0SSpace (s + 1) I x from
      (slotExtend (I := I) (M := M) g r s (0 : SmoothCcTensor g r s)).toSection x) D) =
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x).symm
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
          (0 : SmoothCcTensor g r s).toSection x).comp
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) r x D)) from rfl]
  rw [show ((0 : SmoothCcTensor g r s).toSection x) = (0 : TensorRSSpace r s I x) from by
    rw [SmoothCcTensor.toSection_zero]; rfl]
  rw [show ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
      (0 : TensorRSSpace r s I x)).comp
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) r x D)) =
      (0 : Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x).comp
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) r x D) from rfl]
  rw [ContinuousLinearMap.zero_comp, map_zero]
  rw [show ((0 : SmoothCcTensor g (r + 1) (s + 1)).toSection x) =
      (0 : TensorRSSpace (r + 1) (s + 1) I x) from by
    rw [SmoothCcTensor.toSection_zero]; rfl]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
private lemma rsDomDomCongrSection_zero_cc (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (σ : Equiv.Perm (Fin s)) :
    rsDomDomCongrSection (I := I) (M := M) g r s σ (0 : SmoothCcTensor g r s) = 0 := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  have h0 : ((0 : SmoothCcTensor g r s).toSection x) = (0 : TensorRSSpace r s I x) := by
    rw [SmoothCcTensor.toSection_zero]; rfl
  rw [rsDomDomCongrSection_toSection, h0]
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun m => ?_)
  have hfib : ∀ (y : Tensor0SSpace s I x) (w : Fin s → TangentSpace I x),
      Tensor0SSpace.toModel y w = (y : Tensor0SSpace s I x) w := fun _ _ => rfl
  rw [hfib, hfib]
  rw [rsDomDomCongr_apply_eval (I := I) (M := M) σ (0 : TensorRSSpace r s I x) D m]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
private lemma covGrad_slotExtend_parallel (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ : SmoothCcTensor g r s)
    (hΦ : covGrad (I := I) (M := M) g r s Φ = 0) :
    covGrad (I := I) (M := M) g (r + 1) (s + 1)
      (slotExtend (I := I) (M := M) g r s Φ) = 0 := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [covGrad_slotExtend_toSection_rsDomDomCongr_b (I := I) (M := M) g r s Φ x]
  rw [hΦ]
  rw [slotExtend_zero_cc (I := I) (M := M) g r (s + 1)]
  rw [show ((0 : SmoothCcTensor g (r + 1) (s + 1 + 1)).toSection x) =
      (0 : TensorRSSpace (r + 1) (s + 1 + 1) I x) from by
    rw [SmoothCcTensor.toSection_zero]; rfl]
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun m => ?_)
  have hfib : ∀ (y : Tensor0SSpace (s + 1 + 1) I x) (w : Fin (s + 1 + 1) → TangentSpace I x),
      Tensor0SSpace.toModel y w = (y : Tensor0SSpace (s + 1 + 1) I x) w := fun _ _ => rfl
  rw [hfib, hfib]
  rw [rsDomDomCongr_apply_eval (I := I) (M := M) (Equiv.swap (0 : Fin (s + 1 + 1)) 1)
    (0 : TensorRSSpace (r + 1) (s + 1 + 1) I x) D m]
  rfl

set_option linter.unusedSectionVars false in
private lemma slotExtendIter_parallel (g₀ : SmoothRiemannianMetric I M) (b c : ℕ)
    (Φ : SmoothCcTensor g₀ b c)
    (hΦ : covGrad (I := I) (M := M) g₀ b c Φ = 0) :
    ∀ j : ℕ, covGrad (I := I) (M := M) g₀ (b + j) (c + j)
      (slotExtendIter (I := I) (M := M) g₀ b c j Φ) = 0
  | 0 => hΦ
  | (j + 1) => by
      rw [show slotExtendIter (I := I) (M := M) g₀ b c (j + 1) Φ =
          slotExtend (I := I) (M := M) g₀ (b + j) (c + j)
            (slotExtendIter (I := I) (M := M) g₀ b c j Φ) from rfl]
      exact covGrad_slotExtend_parallel (I := I) (M := M) g₀ (b + j) (c + j)
        (slotExtendIter (I := I) (M := M) g₀ b c j Φ)
        (slotExtendIter_parallel g₀ b c Φ hΦ j)

set_option linter.unusedSectionVars false in
private lemma iteratedCovGrad_appCcRS_parallel (g₀ : SmoothRiemannianMetric I M)
    (a b c : ℕ) (Φ : SmoothCcTensor g₀ b c)
    (hΦ : covGrad (I := I) (M := M) g₀ b c Φ = 0) (W : SmoothCcTensor g₀ a b) :
    ∀ j : ℕ, iteratedCovGrad (I := I) g₀ a c j (appCcRS (I := I) (M := M) g₀ a b c Φ W) =
      appCcRS (I := I) (M := M) g₀ a (b + j) (c + j)
        (slotExtendIter (I := I) (M := M) g₀ b c j Φ)
        (iteratedCovGrad (I := I) g₀ a b j W)
  | 0 => by
      rw [iteratedCovGrad_zero, iteratedCovGrad_zero]
      rfl
  | (j + 1) => by
      rw [iteratedCovGrad_succ]
      rw [iteratedCovGrad_appCcRS_parallel g₀ a b c Φ hΦ W j]
      rw [covGrad_appCcRS_eq (I := I) (M := M) g₀ a (b + j) (c + j)
        (slotExtendIter (I := I) (M := M) g₀ b c j Φ)
        (iteratedCovGrad (I := I) g₀ a b j W)]
      rw [slotExtendIter_parallel (I := I) (M := M) g₀ b c Φ hΦ j]
      rw [appCcRS_zero_left_cc (I := I) (M := M) g₀ a (b + j) ((c + j) + 1)
        (iteratedCovGrad (I := I) g₀ a b j W)]
      rw [zero_add]
      rw [show covGrad (I := I) (M := M) g₀ a (b + j) (iteratedCovGrad (I := I) g₀ a b j W) =
          iteratedCovGrad (I := I) g₀ a b (j + 1) W from
        (iteratedCovGrad_succ (I := I) g₀ a b j W).symm]
      rfl

private def phiDtPair (g₀ : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 6 2 :=
  appCcRS (I := I) (M := M) g₀ 6 4 2
    (cometricDoubleTraceField (I := I) g₀ 2) (cometricDoubleTraceField (I := I) g₀ 4)

set_option linter.unusedSectionVars false in
private lemma phiDtPair_covGrad_zero (g₀ : SmoothRiemannianMetric I M) :
    covGrad (I := I) (M := M) g₀ 6 2 (phiDtPair (I := I) (M := M) g₀) = 0 := by
  rw [phiDtPair]
  rw [covGrad_appCcRS_eq (I := I) (M := M) g₀ 6 4 2
    (cometricDoubleTraceField (I := I) g₀ 2) (cometricDoubleTraceField (I := I) g₀ 4)]
  rw [cometricDoubleTraceField_covGrad_eq_zero (I := I) g₀ 2]
  rw [cometricDoubleTraceField_covGrad_eq_zero (I := I) g₀ 4]
  rw [appCcRS_zero_left_cc (I := I) (M := M) g₀ 6 4 3
    (cometricDoubleTraceField (I := I) g₀ 4)]
  rw [appCcRS_right_zero_cc (I := I) (M := M) g₀ 6 5 3
    (slotExtend (I := I) (M := M) g₀ 4 2 (cometricDoubleTraceField (I := I) g₀ 2))]
  rw [add_zero]

private def sigmaE0 : Equiv.Perm (Fin 6) :=
  ⟨fun i => (![1, 3, 4, 5, 0, 2] : Fin 6 → Fin 6) i,
   fun i => (![4, 0, 5, 1, 2, 3] : Fin 6 → Fin 6) i,
   by decide, by decide⟩

set_option linter.unusedSectionVars false in
private lemma tensor0S_zero_rank_decomp (x : M) (t : Tensor0SSpace 0 I x) :
    t = (Tensor0SSpace.toModel t (fun i : Fin 0 => i.elim0)) • unitTensor (I := I) (M := M) x := by
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun m => ?_)
  beta_reduce
  rw [show m = (fun i : Fin 0 => i.elim0 : Fin 0 → E) from by
    funext k
    exact k.elim0]
  rw [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply]
  rw [show Tensor0SSpace.toModel (unitTensor (I := I) (M := M) x)
      (fun i : Fin 0 => i.elim0) = 1 from by
    rw [unitTensor, Tensor0SSpace.toModel_ofModel]
    rfl]
  rw [smul_eq_mul, mul_one]

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
private lemma slotExtendIter_two_toModel (g₀ : SmoothRiemannianMetric I M)
    (X : SmoothCcTensor g₀ 0 4) (x : M) (D : Tensor0SSpace 2 I x)
    (u : Fin 6 → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2 X).toSection x) D) u =
      Tensor0SSpace.toModel D ![u 0, u 1] *
        unitModel (I := I) (M := M) g₀ 4 X x (fun k : Fin 4 => u (Fin.natAdd 2 k)) := by
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2 X).toSection x) D) =
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 5 x).symm
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 5 I x from
          (slotExtendIter (I := I) (M := M) g₀ 0 4 1 X).toSection x).comp
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D)) from rfl]
  have hkey1 := TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (n := 5)
    (T := (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 5 x).symm
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 5 I x from
        (slotExtendIter (I := I) (M := M) g₀ 0 4 1 X).toSection x).comp
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D)))
    (v0 := u 0) (vs := Matrix.vecTail u)
  rw [ContinuousLinearEquiv.apply_symm_apply] at hkey1
  rw [show (Fin.cons (u 0) (Matrix.vecTail u) : Fin 6 → TangentSpace I x) = u from by
    funext k
    refine Fin.cases rfl (fun i => rfl) k] at hkey1
  rw [← hkey1]
  rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 5 I x from
        (slotExtendIter (I := I) (M := M) g₀ 0 4 1 X).toSection x).comp
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D) (u 0)) =
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 4 x).symm
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from X.toSection x).comp
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 0 x
            (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D (u 0)))) from rfl]
  rw [show (Matrix.vecTail u : Fin 5 → TangentSpace I x) =
      Fin.cons (u 1) (fun k : Fin 4 => u (Fin.natAdd 2 k)) from by
    funext k
    refine Fin.cases ?_ (fun i => ?_) k
    · rfl
    · change u (Fin.succ (Fin.succ i)) = u (Fin.natAdd 2 i)
      congr 1
      exact Fin.ext (by simp [Fin.succ, Fin.natAdd]; omega)]
  have hkey2 := TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (n := 4)
    (T := (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 4 x).symm
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from X.toSection x).comp
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 0 x
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D (u 0)))))
    (v0 := u 1) (vs := fun k : Fin 4 => u (Fin.natAdd 2 k))
  rw [ContinuousLinearEquiv.apply_symm_apply] at hkey2
  rw [← hkey2]
  rw [show ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from X.toSection x).comp
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 0 x
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D (u 0))) (u 1)) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from X.toSection x)
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 0 x
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D (u 0)) (u 1)) from rfl]
  set t : Tensor0SSpace 0 I x :=
    tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 0 x
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D (u 0)) (u 1) with ht_def
  have htval : Tensor0SSpace.toModel t (fun i : Fin 0 => i.elim0) =
      Tensor0SSpace.toModel D ![u 0, u 1] := by
    rw [ht_def]
    have h1 := TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (n := 0)
      (T := tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x D (u 0)) (v0 := u 1)
      (vs := fun i : Fin 0 => i.elim0)
    rw [h1]
    have h2 := TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (n := 1)
      (T := D) (v0 := u 0) (vs := Fin.cons (u 1) (fun i : Fin 0 => i.elim0))
    rw [h2]
    refine congrArg _ ?_
    funext k
    refine Fin.cases rfl (fun i => ?_) k
    refine Fin.cases rfl (fun i2 => i2.elim0) i
  have hdecomp := tensor0S_zero_rank_decomp (I := I) (M := M) x t
  rw [htval] at hdecomp
  rw [hdecomp, map_smul]
  rw [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  rw [show ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from X.toSection x)
      (unitTensor (I := I) (M := M) x)) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from X.toSection x)
        (unitTensor (I := I) (M := M) x) from rfl]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
set_option maxHeartbeats 12800000 in
private theorem mixedCoeff_backgroundDifference_eq_pairTrace
    (g₀ g₁ : SmoothRiemannianMetric I M) :
    ricciArmOrder0RiemannMixedCoeff (I := I) (M := M) g₀ g₁ -
        ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ =
      (2 : ℝ) • appCcRS (I := I) (M := M) g₀ 2 6 2 (phiDtPair (I := I) (M := M) g₀)
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁))) := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  have hLHS : Tensor0SSpace.toModel
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (ricciArmOrder0RiemannMixedCoeff (I := I) (M := M) g₀ g₁ -
          ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀).toSection x) D) v =
      2 * ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        unitModel (I := I) (M := M) g₀ 4
            (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁) x
            ![v 0, v 1, (smoothOrthoFrame (I := I) g₀ x a x : E),
              (smoothOrthoFrame (I := I) g₀ x b x : E)] *
          Tensor0SSpace.toModel D
            ![(smoothOrthoFrame (I := I) g₀ x a x : E),
              (smoothOrthoFrame (I := I) g₀ x b x : E)] := by
    rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (ricciArmOrder0RiemannMixedCoeff (I := I) (M := M) g₀ g₁ -
          ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀).toSection x) D) =
        (riemannMixedBiContrFib (I := I) (M := M) g₀ g₁ x D -
          riemannBiContrFib (I := I) g₀ x D) from by
      rw [show ((ricciArmOrder0RiemannMixedCoeff (I := I) (M := M) g₀ g₁ -
          ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀).toSection x) =
        (ricciArmOrder0RiemannMixedCoeff (I := I) (M := M) g₀ g₁).toSection x -
          (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀).toSection x from by
        rw [SmoothCcTensor.toSection_sub]; rfl]
      rfl]
    rw [Tensor0SSpace.toModel_sub, ContinuousMultilinearMap.sub_apply]
    rw [show riemannMixedBiContrFib (I := I) (M := M) g₀ g₁ x =
        riemannMixedBiContrFibFixedFrame (I := I) g₀ g₁
          (smoothOrthoFrame (I := I) g₀ x) x from rfl]
    rw [show riemannBiContrFib (I := I) g₀ x =
        riemannBiContrFibFixedFrame (I := I) g₀ (smoothOrthoFrame (I := I) g₀ x) x from rfl]
    rw [riemannMixedBiContrFibFixedFrame_toModel (I := I) g₀ g₁
      (smoothOrthoFrame (I := I) g₀ x) x D v]
    rw [riemannBiContrFibFixedFrame_toModel (I := I) g₀ (smoothOrthoFrame (I := I) g₀ x) x D v]
    rw [← mul_sub]
    congr 1
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [riemannLoweredBackgroundDifference_unitModel_apply (I := I) (M := M) g₀ g₁ x
      (![v 0, v 1, (smoothOrthoFrame (I := I) g₀ x a x : E),
        (smoothOrthoFrame (I := I) g₀ x b x : E)] : Fin 4 → TangentSpace I x)]
    rw [show (![v 0, v 1, (smoothOrthoFrame (I := I) g₀ x a x : E),
        (smoothOrthoFrame (I := I) g₀ x b x : E)] : Fin 4 → TangentSpace I x) 0 = v 0 from rfl]
    rw [show (![v 0, v 1, (smoothOrthoFrame (I := I) g₀ x a x : E),
        (smoothOrthoFrame (I := I) g₀ x b x : E)] : Fin 4 → TangentSpace I x) 1 = v 1 from rfl]
    rw [show (![v 0, v 1, (smoothOrthoFrame (I := I) g₀ x a x : E),
        (smoothOrthoFrame (I := I) g₀ x b x : E)] : Fin 4 → TangentSpace I x) 2 =
      smoothOrthoFrame (I := I) g₀ x a x from rfl]
    rw [show (![v 0, v 1, (smoothOrthoFrame (I := I) g₀ x a x : E),
        (smoothOrthoFrame (I := I) g₀ x b x : E)] : Fin 4 → TangentSpace I x) 3 =
      smoothOrthoFrame (I := I) g₀ x b x from rfl]
    ring
  rw [hLHS]
  set X : SmoothCcTensor g₀ 0 4 :=
    riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁ with hX_def
  set Y : Tensor0SSpace 6 I x :=
    (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
      (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2 X)).toSection x) D with hY_def
  have hYval : ∀ w : Fin 6 → TangentSpace I x,
      Tensor0SSpace.toModel Y w =
        Tensor0SSpace.toModel D ![w 1, w 3] *
          unitModel (I := I) (M := M) g₀ 4 X x ![w 4, w 5, w 0, w 2] := by
    intro w
    rw [hY_def]
    rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2 X)).toSection x) D) =
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
          rsDomDomCongr sigmaE0
            ((slotExtendIter (I := I) (M := M) g₀ 0 4 2 X).toSection x)) D) from by
      rw [rsDomDomCongrSection_toSection]]
    rw [toModel_rsDomDomCongr_apply (I := I) (M := M) sigmaE0
      ((slotExtendIter (I := I) (M := M) g₀ 0 4 2 X).toSection x) D]
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    rw [slotExtendIter_two_toModel (I := I) (M := M) g₀ X x D
      (fun i => w (sigmaE0 i))]
    rfl
  have hRHS : Tensor0SSpace.toModel
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        ((2 : ℝ) • appCcRS (I := I) (M := M) g₀ 2 6 2 (phiDtPair (I := I) (M := M) g₀)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2 X))).toSection x) D) v =
      2 * ∑ b : Fin (Module.finrank ℝ E), ∑ a : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel D
            ![(smoothOrthoFrame (I := I) g₀ x a x : E),
              (smoothOrthoFrame (I := I) g₀ x b x : E)] *
          unitModel (I := I) (M := M) g₀ 4 X x
            ![v 0, v 1, (smoothOrthoFrame (I := I) g₀ x a x : E),
              (smoothOrthoFrame (I := I) g₀ x b x : E)] := by
    rw [show (((2 : ℝ) • appCcRS (I := I) (M := M) g₀ 2 6 2 (phiDtPair (I := I) (M := M) g₀)
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2 X))).toSection x) =
        (2 : ℝ) • ((appCcRS (I := I) (M := M) g₀ 2 6 2 (phiDtPair (I := I) (M := M) g₀)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2 X))).toSection x) from by
      rw [SmoothCcTensor.toSection_smul]; rfl]
    rw [show ((2 : ℝ) • ((appCcRS (I := I) (M := M) g₀ 2 6 2 (phiDtPair (I := I) (M := M) g₀)
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2 X))).toSection x) :
        TensorRSSpace 2 2 I x) D =
        (2 : ℝ) • (((appCcRS (I := I) (M := M) g₀ 2 6 2 (phiDtPair (I := I) (M := M) g₀)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2 X))).toSection x) D) from rfl]
    rw [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
    congr 1
    rw [show (((appCcRS (I := I) (M := M) g₀ 2 6 2 (phiDtPair (I := I) (M := M) g₀)
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2 X))).toSection x) D) =
        (show Tensor0SSpace 4 I x →L[ℝ] Tensor0SSpace 2 I x from
          cometricDoubleTraceFib (I := I) g₀ 2 x)
          ((show Tensor0SSpace 6 I x →L[ℝ] Tensor0SSpace 4 I x from
            cometricDoubleTraceFib (I := I) g₀ 4 x) Y) from by
      rw [hY_def]
      rw [appCcRS_toSection]
      rfl]
    rw [cometricDoubleTraceFib_toModel (I := I) g₀ 2 x]
    rw [modelDoubleTrace_apply (E := E) 2 (cometricLmodel (I := I) g₀ x)]
    rw [cometric_dualTrace_eq_orthoFrame_diag (I := I) g₀ x
      (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x)
      (Tensor0SSpace.toModel
        ((show Tensor0SSpace 6 I x →L[ℝ] Tensor0SSpace 4 I x from
          cometricDoubleTraceFib (I := I) g₀ 4 x) Y))
      (fun j => (v j : E))]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [cometricDoubleTraceFib_toModel (I := I) g₀ 4 x Y]
    rw [modelDoubleTrace_apply (E := E) 4 (cometricLmodel (I := I) g₀ x)]
    rw [cometric_dualTrace_eq_orthoFrame_diag (I := I) g₀ x
      (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x)
      (Tensor0SSpace.toModel Y)
      (Fin.cons ((smoothOrthoFrame (I := I) g₀ x b x : TangentSpace I x) : E)
        (Fin.cons ((smoothOrthoFrame (I := I) g₀ x b x : TangentSpace I x) : E)
          (fun j => (v j : E))))]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hYval]
    rfl
  rw [hRHS]
  rw [Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

set_option linter.unusedSectionVars false in
private lemma iteratedCovGrad_smul_b (g : SmoothRiemannianMetric I M) (r s j : ℕ)
    (c : ℝ) (w : SmoothCcTensor g r s) :
    iteratedCovGrad (I := I) g r s j (c • w) = c • iteratedCovGrad (I := I) g r s j w := by
  induction j with
  | zero => simp only [iteratedCovGrad_zero]
  | succ j ih =>
    rw [iteratedCovGrad_succ, iteratedCovGrad_succ, ih, covGrad_smul]

set_option linter.unusedSectionVars false in
private lemma rfns_smul_b (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (c : ℝ) (v : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (c • v) =
      c ^ 2 * riemannianFiberNormSq (I := I) (M := M) g r s x v := by
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x (c • v),
    riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x v]
  rw [TensorRSSpace.toModel_smul, tensorInnerPointwise_smul_left,
    tensorInnerPointwise_smul_right]
  ring

theorem rfns_iteratedCovGrad_riemannMixedCoeff_backgroundDifference_le_loweredDifference
    (g₀ : SmoothRiemannianMetric I M) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (ricciArmOrder0RiemannMixedCoeff (I := I) (M := M) g₀ g₁ -
                ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀)).toSection x) ≤
          C i * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 4 i
              (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)).toSection x) := by
  classical
  have hcB : ∀ j : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ (6 + j) (2 + j) x
        ((slotExtendIter (I := I) (M := M) g₀ 6 2 j
          (phiDtPair (I := I) (M := M) g₀)).toSection x) ≤ c := fun j =>
    exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ (6 + j) (2 + j)
      (slotExtendIter (I := I) (M := M) g₀ 6 2 j (phiDtPair (I := I) (M := M) g₀))
  choose cB hcB0 hcBb using hcB
  refine ⟨fun i => 4 * cB i * ((Module.finrank ℝ E : ℝ) * (Module.finrank ℝ E : ℝ)),
    fun i => by
      have := hcB0 i
      positivity, ?_⟩
  intro g₁ i x
  rw [mixedCoeff_backgroundDifference_eq_pairTrace (I := I) (M := M) g₀ g₁]
  set WB : SmoothCcTensor g₀ 2 6 :=
    rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
      (slotExtendIter (I := I) (M := M) g₀ 0 4 2
        (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)) with hWB_def
  have hsmul : (iteratedCovGrad (I := I) g₀ 2 2 i
      ((2 : ℝ) • appCcRS (I := I) (M := M) g₀ 2 6 2 (phiDtPair (I := I) (M := M) g₀)
        WB)).toSection x =
      (2 : ℝ) • ((iteratedCovGrad (I := I) g₀ 2 2 i
        (appCcRS (I := I) (M := M) g₀ 2 6 2 (phiDtPair (I := I) (M := M) g₀)
          WB)).toSection x) := by
    rw [iteratedCovGrad_smul_b]
    rw [SmoothCcTensor.toSection_smul]
    rfl
  rw [hsmul, rfns_smul_b]
  rw [iteratedCovGrad_appCcRS_parallel (I := I) (M := M) g₀ 2 6 2
    (phiDtPair (I := I) (M := M) g₀) (phiDtPair_covGrad_zero (I := I) (M := M) g₀) WB i]
  have hcomp : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
      ((appCcRS (I := I) (M := M) g₀ 2 (6 + i) (2 + i)
        (slotExtendIter (I := I) (M := M) g₀ 6 2 i (phiDtPair (I := I) (M := M) g₀))
        (iteratedCovGrad (I := I) g₀ 2 6 i WB)).toSection x) ≤
      riemannianFiberNormSq (I := I) (M := M) g₀ (6 + i) (2 + i) x
          ((slotExtendIter (I := I) (M := M) g₀ 6 2 i
            (phiDtPair (I := I) (M := M) g₀)).toSection x) *
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + i) x
          ((iteratedCovGrad (I := I) g₀ 2 6 i WB).toSection x) := by
    rw [appCcRS_toSection]
    exact riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g₀ 2 (6 + i) (2 + i) x
      ((slotExtendIter (I := I) (M := M) g₀ 6 2 i
        (phiDtPair (I := I) (M := M) g₀)).toSection x)
      ((iteratedCovGrad (I := I) g₀ 2 6 i WB).toSection x)
  have hWBjets : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + i) x
      ((iteratedCovGrad (I := I) g₀ 2 6 i WB).toSection x) ≤
      ((Module.finrank ℝ E : ℝ) * (Module.finrank ℝ E : ℝ)) *
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
          ((iteratedCovGrad (I := I) g₀ 0 4 i
            (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)).toSection x) := by
    have heq1 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + i) x
        ((iteratedCovGrad (I := I) g₀ 2 6 i WB).toSection x) =
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + i) x
          ((iteratedCovGrad (I := I) g₀ 2 6 i
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁))).toSection x) := by
      rw [hWB_def]
      exact rfns_iteratedCovGrad_rs_eq_of_section_domDomCongr (I := I) (M := M) g₀ 2 6 sigmaE0
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2
          (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁))
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)))
        (fun y d => by
          rw [rsDomDomCongrSection_toSection, toModel_rsDomDomCongr_apply]) i x
    rw [heq1]
    have hstep1 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + i) x
        ((iteratedCovGrad (I := I) g₀ 2 6 i
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁))).toSection x) ≤
        (Module.finrank ℝ E : ℝ) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (5 + i) x
            ((iteratedCovGrad (I := I) g₀ 1 5 i
              (slotExtend (I := I) (M := M) g₀ 0 4
                (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁))).toSection x) :=
      rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 1 5
        (slotExtend (I := I) (M := M) g₀ 0 4
          (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)) i x
    have hstep2 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (5 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 5 i
          (slotExtend (I := I) (M := M) g₀ 0 4
            (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁))).toSection x) ≤
        (Module.finrank ℝ E : ℝ) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 4 i
              (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)).toSection x) :=
      rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 0 4
        (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁) i x
    have hfr : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
    calc riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + i) x
          ((iteratedCovGrad (I := I) g₀ 2 6 i
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁))).toSection x)
        ≤ (Module.finrank ℝ E : ℝ) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (5 + i) x
            ((iteratedCovGrad (I := I) g₀ 1 5 i
              (slotExtend (I := I) (M := M) g₀ 0 4
                (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁))).toSection x) :=
          hstep1
      _ ≤ (Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 4 i
              (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)).toSection x)) :=
          mul_le_mul_of_nonneg_left hstep2 hfr
      _ = ((Module.finrank ℝ E : ℝ) * (Module.finrank ℝ E : ℝ)) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 4 i
              (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)).toSection x) := by
          ring
  have hrfns_nn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (6 + i) x
    ((iteratedCovGrad (I := I) g₀ 2 6 i WB).toSection x)
  have hCD_nn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (4 + i) x
    ((iteratedCovGrad (I := I) g₀ 0 4 i
      (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)).toSection x)
  calc (2 : ℝ) ^ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
        ((appCcRS (I := I) (M := M) g₀ 2 (6 + i) (2 + i)
          (slotExtendIter (I := I) (M := M) g₀ 6 2 i (phiDtPair (I := I) (M := M) g₀))
          (iteratedCovGrad (I := I) g₀ 2 6 i WB)).toSection x)
      ≤ (2 : ℝ) ^ 2 * (riemannianFiberNormSq (I := I) (M := M) g₀ (6 + i) (2 + i) x
          ((slotExtendIter (I := I) (M := M) g₀ 6 2 i
            (phiDtPair (I := I) (M := M) g₀)).toSection x) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 6 i WB).toSection x)) := by
        have := hcomp
        nlinarith
    _ ≤ (2 : ℝ) ^ 2 * (cB i *
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 6 i WB).toSection x)) := by
        have h1 := hcBb i x
        nlinarith
    _ ≤ (2 : ℝ) ^ 2 * (cB i * (((Module.finrank ℝ E : ℝ) * (Module.finrank ℝ E : ℝ)) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 4 i
              (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)).toSection x))) := by
        have := hcB0 i
        nlinarith [hWBjets]
    _ = (4 * cB i * ((Module.finrank ℝ E : ℝ) * (Module.finrank ℝ E : ℝ))) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 4 i
              (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)).toSection x) := by
        ring

set_option linter.unusedVariables false in
theorem rfns_iteratedCovGrad_riemannG1LoweringDifference_diagonalProductGrid_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 4 i
              (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁ -
                riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁)).toSection x) ≤
          C i * ∑ k ∈ Finset.range (i + 3),
            ∑ n ∈ Finset.range (k + 1),
              ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
                ∏ m : Fin n,
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T).toSection x) := by
  classical
  obtain ⟨CAd, hCAd_nn, hCAd⟩ :=
    rfns_iteratedCovGrad_riemannLoweredBackgroundDifference_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨cbg, hcbg_nn, hcbg⟩ := exists_backgroundJet_rfns_bound (I := I) (M := M) g₀ 0 4
    (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)
  set BB : ℕ → ℕ → ℝ := fun i i' => ((Module.finrank ℝ E : ℝ) ^ 2 * δ₀ ^ 2 + 1) *
    ∑ l ∈ Finset.range (i + 1 - i'),
      (2 * CAd l * gridSumPairCount (i' + 1) (l + 3) + 2 * cbg l) with hBB_def
  have hBBsum_nn : ∀ i i', 0 ≤ ∑ l ∈ Finset.range (i + 1 - i'),
      (2 * CAd l * gridSumPairCount (i' + 1) (l + 3) + 2 * cbg l) := by
    intro i i'
    refine Finset.sum_nonneg fun l _ => add_nonneg ?_ ?_
    · have := hCAd_nn l
      have := gridSumPairCount_nonneg (i' + 1) (l + 3)
      positivity
    · have := hcbg_nn l
      linarith
  have hc0fac_nn : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) ^ 2 * δ₀ ^ 2 + 1 := by positivity
  have hBB_nn : ∀ i i', 0 ≤ BB i i' := by
    intro i i'
    rw [hBB_def]
    exact mul_nonneg hc0fac_nn (hBBsum_nn i i')
  have hBBval : ∀ i i', BB i i' = ((Module.finrank ℝ E : ℝ) ^ 2 * δ₀ ^ 2 + 1) *
      ∑ l ∈ Finset.range (i + 1 - i'),
        (2 * CAd l * gridSumPairCount (i' + 1) (l + 3) + 2 * cbg l) := by
    intro i i'
    rw [hBB_def]
  clear_value BB
  refine ⟨fun i => appCcGdiag (E := E) i *
      ∑ i' ∈ Finset.range (i + 1), (Module.finrank ℝ E : ℝ) ^ 3 * BB i i',
    fun i => mul_nonneg (appCcGdiag_nonneg (E := E) i)
      (Finset.sum_nonneg fun i' _ => mul_nonneg (by positivity) (hBB_nn i i')), ?_⟩
  intro g₁ T htie δ hδ_le hδ0 hbound i x
  set b : ℕ → ℝ := fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
    ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x) with hb_def
  have hb : ∀ j, 0 ≤ b j :=
    fun j => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + j) x _
  have hgoal_eq : (∑ k ∈ Finset.range (i + 3),
      ∑ n ∈ Finset.range (k + 1),
        ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
          ∏ m : Fin n, b (e m)) =
      ∑ k ∈ Finset.range (i + 3), Combinatorics.antidiagonalTupleGrid b k := rfl
  rw [hgoal_eq]
  set WW : ℝ := ∑ k ∈ Finset.range (i + 3), Combinatorics.antidiagonalTupleGrid b k
    with hWW_def
  have hgsum_le_WW : ∀ m : ℕ, m ≤ i + 3 →
      (∑ k ∈ Finset.range m, Combinatorics.antidiagonalTupleGrid b k) ≤ WW := by
    intro m hm
    rw [hWW_def]
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hm) ?_
    intro k _ _
    exact Combinatorics.antidiagonalTupleGrid_nonneg b hb k
  have hWW_nn : 0 ≤ WW := by
    rw [hWW_def]
    exact Finset.sum_nonneg fun k _ => Combinatorics.antidiagonalTupleGrid_nonneg b hb k
  have hWW_ge1 : (1 : ℝ) ≤ WW := by
    rw [hWW_def]
    calc (1 : ℝ) = Combinatorics.antidiagonalTupleGrid b 0 :=
          (Combinatorics.antidiagonalTupleGrid_zero b).symm
      _ ≤ ∑ k ∈ Finset.range (i + 3), Combinatorics.antidiagonalTupleGrid b k :=
          Finset.single_le_sum
            (f := fun k => Combinatorics.antidiagonalTupleGrid b k)
            (fun k _ => Combinatorics.antidiagonalTupleGrid_nonneg b hb k)
            (Finset.mem_range.mpr (by omega))
  clear_value WW
  rw [riemannG1LoweringDifference_slotInsert_repr (I := I) (M := M) g₀ g₁ T htie]
  rw [riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
    (Equiv.swap (0 : Fin 4) 1)
    (appCcRS (I := I) (M := M) g₀ 0 4 4
      (slotInsertEndoCc (I := I) (M := M) g₀ 3
        (perturbationSharpEndoField (I := I) (M := M) g₀ T))
      (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
        (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁))) i x]
  refine le_trans (rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le
    (I := I) (M := M) g₀ i 0 4 4
    (slotInsertEndoCc (I := I) (M := M) g₀ 3
      (perturbationSharpEndoField (I := I) (M := M) g₀ T))
    (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
      (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁)) x) ?_
  have hL01 : ∀ l : ℕ,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 4 l
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
            (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁))).toSection x) ≤
      2 * CAd l * (∑ k ∈ Finset.range (l + 3), Combinatorics.antidiagonalTupleGrid b k) +
        2 * cbg l := by
    intro l
    rw [riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 4) 1) (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁) l x]
    have hsplit : riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁ =
        riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁ +
          riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀ := by
      rw [riemannLoweredBackgroundDifference, sub_add_cancel]
    have hsec : (iteratedCovGrad (I := I) g₀ 0 4 l
        (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁)).toSection x =
        (iteratedCovGrad (I := I) g₀ 0 4 l
          (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)).toSection x +
        (iteratedCovGrad (I := I) g₀ 0 4 l
          (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)).toSection x := by
      rw [hsplit, iteratedCovGrad_add, SmoothCcTensor.toSection_add]
      rfl
    rw [hsec]
    refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 (4 + l) x _ _) ?_
    have h1 := hCAd g₁ T htie hδ_le hδ0 hbound l x
    rw [show (∑ k ∈ Finset.range (l + 3),
        ∑ n ∈ Finset.range (k + 1),
          ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
            ∏ m : Fin n, b (e m)) =
        ∑ k ∈ Finset.range (l + 3), Combinatorics.antidiagonalTupleGrid b k from rfl] at h1
    have h2 := hcbg l x
    have h1nn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (4 + l) x
      ((iteratedCovGrad (I := I) g₀ 0 4 l
        (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)).toSection x)
    linarith
  have hcell : ∀ i' ∈ Finset.range (i + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ 4 (4 + i') x
          ((iteratedCovGrad (I := I) g₀ 4 4 i'
            (slotInsertEndoCc (I := I) (M := M) g₀ 3
              (perturbationSharpEndoField (I := I) (M := M) g₀ T))).toSection x) *
        ∑ l ∈ Finset.range (i + 1 - i'),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 4 l
              (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
                (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁))).toSection x) ≤
      ((Module.finrank ℝ E : ℝ) ^ 3 * BB i i') * WW := by
    intro i' hi'
    have hi'le : i' ≤ i := by
      rw [Finset.mem_range] at hi'; omega
    have hA2 : (∑ l ∈ Finset.range (i + 1 - i'),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
          ((iteratedCovGrad (I := I) g₀ 0 4 l
            (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
              (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁))).toSection x)) ≤
        ∑ l ∈ Finset.range (i + 1 - i'),
          (2 * CAd l * (∑ k ∈ Finset.range (l + 3), Combinatorics.antidiagonalTupleGrid b k) +
            2 * cbg l) :=
      Finset.sum_le_sum fun l _ => hL01 l
    have hprod_nn1 : 0 ≤ ∑ l ∈ Finset.range (i + 1 - i'),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
          ((iteratedCovGrad (I := I) g₀ 0 4 l
            (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
              (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁))).toSection x) :=
      Finset.sum_nonneg fun l _ =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (4 + l) x _
    have hsum2_nn : 0 ≤ ∑ l ∈ Finset.range (i + 1 - i'),
        (2 * CAd l * (∑ k ∈ Finset.range (l + 3), Combinatorics.antidiagonalTupleGrid b k) +
          2 * cbg l) := by
      refine Finset.sum_nonneg fun l _ => add_nonneg ?_ ?_
      · have := hCAd_nn l
        have : 0 ≤ ∑ k ∈ Finset.range (l + 3), Combinatorics.antidiagonalTupleGrid b k :=
          Finset.sum_nonneg fun k _ => Combinatorics.antidiagonalTupleGrid_nonneg b hb k
        positivity
      · have := hcbg_nn l
        linarith
    have hpairsum : ∀ gsA : ℝ, 0 ≤ gsA →
        (∀ m3ok : ∀ l ∈ Finset.range (i + 1 - i'),
          gsA * (∑ k ∈ Finset.range (l + 3), Combinatorics.antidiagonalTupleGrid b k) ≤
            gridSumPairCount (i' + 1) (l + 3) * WW, gsA ≤ WW →
        gsA * ∑ l ∈ Finset.range (i + 1 - i'),
          (2 * CAd l * (∑ k ∈ Finset.range (l + 3),
            Combinatorics.antidiagonalTupleGrid b k) + 2 * cbg l) ≤
        (∑ l ∈ Finset.range (i + 1 - i'),
          (2 * CAd l * gridSumPairCount (i' + 1) (l + 3) + 2 * cbg l)) * WW) := by
      intro gsA hgsA_nn hm3 hgsA_le
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_le_sum fun l hl => ?_
      have h1 : gsA * (2 * CAd l * (∑ k ∈ Finset.range (l + 3),
          Combinatorics.antidiagonalTupleGrid b k)) ≤
          2 * CAd l * gridSumPairCount (i' + 1) (l + 3) * WW := by
        calc gsA * (2 * CAd l * (∑ k ∈ Finset.range (l + 3),
            Combinatorics.antidiagonalTupleGrid b k))
            = (2 * CAd l) * (gsA * (∑ k ∈ Finset.range (l + 3),
              Combinatorics.antidiagonalTupleGrid b k)) := by ring
          _ ≤ (2 * CAd l) * (gridSumPairCount (i' + 1) (l + 3) * WW) := by
              refine mul_le_mul_of_nonneg_left (hm3 l hl) ?_
              have := hCAd_nn l
              linarith
          _ = 2 * CAd l * gridSumPairCount (i' + 1) (l + 3) * WW := by ring
      have h2 : gsA * (2 * cbg l) ≤ 2 * cbg l * WW := by
        calc gsA * (2 * cbg l) = (2 * cbg l) * gsA := by ring
          _ ≤ (2 * cbg l) * WW := by
              refine mul_le_mul_of_nonneg_left hgsA_le ?_
              have := hcbg_nn l
              linarith
          _ = 2 * cbg l * WW := by ring
      calc gsA * (2 * CAd l * (∑ k ∈ Finset.range (l + 3),
            Combinatorics.antidiagonalTupleGrid b k) + 2 * cbg l)
          = gsA * (2 * CAd l * (∑ k ∈ Finset.range (l + 3),
              Combinatorics.antidiagonalTupleGrid b k)) + gsA * (2 * cbg l) := by ring
        _ ≤ 2 * CAd l * gridSumPairCount (i' + 1) (l + 3) * WW + 2 * cbg l * WW :=
            add_le_add h1 h2
        _ = (2 * CAd l * gridSumPairCount (i' + 1) (l + 3) + 2 * cbg l) * WW := by ring
    have hSIsymm : riemannianFiberNormSq (I := I) (M := M) g₀ 4 (4 + i') x
        ((iteratedCovGrad (I := I) g₀ 4 4 i'
          (slotInsertEndoCc (I := I) (M := M) g₀ 3
            (perturbationSharpEndoField (I := I) (M := M) g₀ T))).toSection x) ≤
        (Module.finrank ℝ E : ℝ) ^ 3 *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i') x
            ((iteratedCovGrad (I := I) g₀ 0 2 i'
              (symmS (I := I) (M := M) g₀ T)).toSection x) :=
      rfns_iteratedCovGrad_slotInsert3_perturbationSharp_le (I := I) (M := M) g₀ T i' x
    match i' with
    | 0 =>
        have hsym0 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 0) x
            ((iteratedCovGrad (I := I) g₀ 0 2 0
              (symmS (I := I) (M := M) g₀ T)).toSection x) ≤
            (Module.finrank ℝ E : ℝ) ^ 2 * δ₀ ^ 2 := by
          rw [iteratedCovGrad_zero]
          refine le_trans (rfns_symmS_zero_le_of_ball (I := I) (M := M) g₀ T hδ0 hbound x) ?_
          have hδsq : δ ^ 2 ≤ δ₀ ^ 2 := by nlinarith [hδ_le, hδ0]
          have : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) ^ 2 := by positivity
          nlinarith
        have hm3 : ∀ l ∈ Finset.range (i + 1 - 0),
            ((Module.finrank ℝ E : ℝ) ^ 2 * δ₀ ^ 2) *
              (∑ k ∈ Finset.range (l + 3), Combinatorics.antidiagonalTupleGrid b k) ≤
            ((Module.finrank ℝ E : ℝ) ^ 2 * δ₀ ^ 2) *
              (gridSumPairCount (0 + 1) (l + 3) * WW) := by
          intro l hl
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have hl_le : l ≤ i := by
            rw [Finset.mem_range] at hl; omega
          have hgs := gridSum_mul_gridSum_le b hb (0 + 1) (l + 3) (i + 3) (by omega)
          have h1eq : (∑ k ∈ Finset.range (0 + 1),
              Combinatorics.antidiagonalTupleGrid b k) = 1 := by
            rw [Finset.sum_range_one, Combinatorics.antidiagonalTupleGrid_zero]
          rw [h1eq, one_mul] at hgs
          refine le_trans hgs ?_
          refine mul_le_mul_of_nonneg_left ?_ (gridSumPairCount_nonneg _ _)
          exact hgsum_le_WW (i + 3) (le_refl _)
        calc riemannianFiberNormSq (I := I) (M := M) g₀ 4 (4 + 0) x
              ((iteratedCovGrad (I := I) g₀ 4 4 0
                (slotInsertEndoCc (I := I) (M := M) g₀ 3
                  (perturbationSharpEndoField (I := I) (M := M) g₀ T))).toSection x) *
            ∑ l ∈ Finset.range (i + 1 - 0),
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
                ((iteratedCovGrad (I := I) g₀ 0 4 l
                  (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
                    (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁))).toSection x)
            ≤ ((Module.finrank ℝ E : ℝ) ^ 3 *
                ((Module.finrank ℝ E : ℝ) ^ 2 * δ₀ ^ 2)) *
              ∑ l ∈ Finset.range (i + 1 - 0),
                (2 * CAd l * (∑ k ∈ Finset.range (l + 3),
                  Combinatorics.antidiagonalTupleGrid b k) + 2 * cbg l) := by
              refine mul_le_mul (le_trans hSIsymm ?_) hA2 hprod_nn1 (by positivity)
              exact mul_le_mul_of_nonneg_left hsym0 (by positivity)
          _ = (Module.finrank ℝ E : ℝ) ^ 3 *
              (((Module.finrank ℝ E : ℝ) ^ 2 * δ₀ ^ 2) *
                ∑ l ∈ Finset.range (i + 1 - 0),
                  (2 * CAd l * (∑ k ∈ Finset.range (l + 3),
                    Combinatorics.antidiagonalTupleGrid b k) + 2 * cbg l)) := by ring
          _ ≤ (Module.finrank ℝ E : ℝ) ^ 3 *
              ((∑ l ∈ Finset.range (i + 1 - 0),
                (2 * CAd l * gridSumPairCount (0 + 1) (l + 3) + 2 * cbg l)) *
                (((Module.finrank ℝ E : ℝ) ^ 2 * δ₀ ^ 2) * WW)) := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              rw [Finset.mul_sum, Finset.sum_mul]
              refine Finset.sum_le_sum fun l hl => ?_
              have hc0nn : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) ^ 2 * δ₀ ^ 2 := by positivity
              have hCADl := hCAd_nn l
              have hcbgl := hcbg_nn l
              have hml := hm3 l hl
              have hgsl_nn : 0 ≤ ∑ k ∈ Finset.range (l + 3),
                  Combinatorics.antidiagonalTupleGrid b k :=
                Finset.sum_nonneg fun k _ =>
                  Combinatorics.antidiagonalTupleGrid_nonneg b hb k
              have hgspc_nn := gridSumPairCount_nonneg (0 + 1) (l + 3)
              nlinarith [mul_le_mul_of_nonneg_left hml (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hCADl),
                mul_nonneg hc0nn hcbgl, hWW_ge1, hWW_nn,
                mul_nonneg (mul_nonneg hc0nn hcbgl) (sub_nonneg.mpr hWW_ge1)]
          _ ≤ ((Module.finrank ℝ E : ℝ) ^ 3 * BB i 0) * WW := by
              rw [hBBval i 0]
              have hsum_nn := hBBsum_nn i 0
              have hc0nn : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) ^ 2 * δ₀ ^ 2 := by positivity
              have hfr3 : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) ^ 3 := by positivity
              have hstep : ((∑ l ∈ Finset.range (i + 1 - 0),
                  (2 * CAd l * gridSumPairCount (0 + 1) (l + 3) + 2 * cbg l)) *
                    (((Module.finrank ℝ E : ℝ) ^ 2 * δ₀ ^ 2) * WW)) ≤
                  (((Module.finrank ℝ E : ℝ) ^ 2 * δ₀ ^ 2 + 1) *
                    ∑ l ∈ Finset.range (i + 1 - 0),
                      (2 * CAd l * gridSumPairCount (0 + 1) (l + 3) + 2 * cbg l)) * WW := by
                have hsum_nn0 := hBBsum_nn i 0
                nlinarith [mul_nonneg hsum_nn0 hWW_nn]
              calc (Module.finrank ℝ E : ℝ) ^ 3 *
                    ((∑ l ∈ Finset.range (i + 1 - 0),
                      (2 * CAd l * gridSumPairCount (0 + 1) (l + 3) + 2 * cbg l)) *
                      (((Module.finrank ℝ E : ℝ) ^ 2 * δ₀ ^ 2) * WW))
                  ≤ (Module.finrank ℝ E : ℝ) ^ 3 *
                      ((((Module.finrank ℝ E : ℝ) ^ 2 * δ₀ ^ 2 + 1) *
                        ∑ l ∈ Finset.range (i + 1 - 0),
                          (2 * CAd l * gridSumPairCount (0 + 1) (l + 3) + 2 * cbg l)) * WW) :=
                    mul_le_mul_of_nonneg_left hstep hfr3
                _ = ((Module.finrank ℝ E : ℝ) ^ 3 *
                      (((Module.finrank ℝ E : ℝ) ^ 2 * δ₀ ^ 2 + 1) *
                        ∑ l ∈ Finset.range (i + 1 - 0),
                          (2 * CAd l * gridSumPairCount (0 + 1) (l + 3) + 2 * cbg l))) * WW := by
                    ring
    | (i'' + 1) =>
        have hb_le_grid : b (i'' + 1) ≤ Combinatorics.antidiagonalTupleGrid b (i'' + 1) := by
          have hmem : (fun _ : Fin 1 => (i'' + 1)) ∈
              Finset.Nat.antidiagonalTuple 1 (i'' + 1) := by
            rw [Finset.Nat.mem_antidiagonalTuple]
            rw [Fin.sum_univ_one]
          have := prodTerm_le_antidiagonalTupleGrid b hb (i'' + 1) 1
            (show (1 : ℕ) < (i'' + 1) + 1 by omega) (fun _ => (i'' + 1)) hmem
          simpa using this
        have hgrid_le_gsum : Combinatorics.antidiagonalTupleGrid b (i'' + 1) ≤
            ∑ k ∈ Finset.range ((i'' + 1) + 1), Combinatorics.antidiagonalTupleGrid b k :=
          Finset.single_le_sum
            (f := fun k => Combinatorics.antidiagonalTupleGrid b k)
            (fun k _ => Combinatorics.antidiagonalTupleGrid_nonneg b hb k)
            (Finset.mem_range.mpr (by omega))
        have hsym_le : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i'' + 1)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i'' + 1)
              (symmS (I := I) (M := M) g₀ T)).toSection x) ≤
            ∑ k ∈ Finset.range ((i'' + 1) + 1), Combinatorics.antidiagonalTupleGrid b k :=
          le_trans (rfns_iteratedCovGrad_symmS_pointwise (I := I) (M := M) g₀ T (i'' + 1) x)
            (le_trans hb_le_grid hgrid_le_gsum)
        have hm3 : ∀ l ∈ Finset.range (i + 1 - (i'' + 1)),
            (∑ k ∈ Finset.range ((i'' + 1) + 1), Combinatorics.antidiagonalTupleGrid b k) *
              (∑ k ∈ Finset.range (l + 3), Combinatorics.antidiagonalTupleGrid b k) ≤
            gridSumPairCount ((i'' + 1) + 1) (l + 3) * WW := by
          intro l hl
          have hl_le : l ≤ i - (i'' + 1) := by
            rw [Finset.mem_range] at hl
            omega
          have hii : i'' + 1 ≤ i := hi'le
          have hgs := gridSum_mul_gridSum_le b hb ((i'' + 1) + 1) (l + 3) (i + 3) (by omega)
          refine le_trans hgs ?_
          refine mul_le_mul_of_nonneg_left ?_ (gridSumPairCount_nonneg _ _)
          exact hgsum_le_WW (i + 3) (le_refl _)
        have hgsA_le : (∑ k ∈ Finset.range ((i'' + 1) + 1),
            Combinatorics.antidiagonalTupleGrid b k) ≤ WW :=
          hgsum_le_WW ((i'' + 1) + 1) (by omega)
        have hgsA_nn : 0 ≤ ∑ k ∈ Finset.range ((i'' + 1) + 1),
            Combinatorics.antidiagonalTupleGrid b k :=
          Finset.sum_nonneg fun k _ => Combinatorics.antidiagonalTupleGrid_nonneg b hb k
        have hmain := hpairsum (∑ k ∈ Finset.range ((i'' + 1) + 1),
          Combinatorics.antidiagonalTupleGrid b k) hgsA_nn
          (fun l hl => by
            calc (∑ k ∈ Finset.range ((i'' + 1) + 1),
                  Combinatorics.antidiagonalTupleGrid b k) *
                  (∑ k ∈ Finset.range (l + 3), Combinatorics.antidiagonalTupleGrid b k)
                ≤ gridSumPairCount ((i'' + 1) + 1) (l + 3) * WW := hm3 l hl)
          hgsA_le
        calc riemannianFiberNormSq (I := I) (M := M) g₀ 4 (4 + (i'' + 1)) x
              ((iteratedCovGrad (I := I) g₀ 4 4 (i'' + 1)
                (slotInsertEndoCc (I := I) (M := M) g₀ 3
                  (perturbationSharpEndoField (I := I) (M := M) g₀ T))).toSection x) *
            ∑ l ∈ Finset.range (i + 1 - (i'' + 1)),
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
                ((iteratedCovGrad (I := I) g₀ 0 4 l
                  (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
                    (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁))).toSection x)
            ≤ ((Module.finrank ℝ E : ℝ) ^ 3 *
                ∑ k ∈ Finset.range ((i'' + 1) + 1), Combinatorics.antidiagonalTupleGrid b k) *
              ∑ l ∈ Finset.range (i + 1 - (i'' + 1)),
                (2 * CAd l * (∑ k ∈ Finset.range (l + 3),
                  Combinatorics.antidiagonalTupleGrid b k) + 2 * cbg l) := by
              refine mul_le_mul (le_trans hSIsymm ?_) hA2 hprod_nn1 (by positivity)
              exact mul_le_mul_of_nonneg_left hsym_le (by positivity)
          _ = (Module.finrank ℝ E : ℝ) ^ 3 *
              ((∑ k ∈ Finset.range ((i'' + 1) + 1), Combinatorics.antidiagonalTupleGrid b k) *
                ∑ l ∈ Finset.range (i + 1 - (i'' + 1)),
                  (2 * CAd l * (∑ k ∈ Finset.range (l + 3),
                    Combinatorics.antidiagonalTupleGrid b k) + 2 * cbg l)) := by ring
          _ ≤ (Module.finrank ℝ E : ℝ) ^ 3 *
              ((∑ l ∈ Finset.range (i + 1 - (i'' + 1)),
                (2 * CAd l * gridSumPairCount ((i'' + 1) + 1) (l + 3) + 2 * cbg l)) * WW) := by
              exact mul_le_mul_of_nonneg_left hmain (by positivity)
          _ ≤ ((Module.finrank ℝ E : ℝ) ^ 3 * BB i (i'' + 1)) * WW := by
              rw [hBBval i (i'' + 1)]
              have hsum_nn := hBBsum_nn i (i'' + 1)
              have hc0nn : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) ^ 2 * δ₀ ^ 2 := by positivity
              have hfr3 : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) ^ 3 := by positivity
              have hstep : (∑ l ∈ Finset.range (i + 1 - (i'' + 1)),
                  (2 * CAd l * gridSumPairCount ((i'' + 1) + 1) (l + 3) + 2 * cbg l)) ≤
                  ((Module.finrank ℝ E : ℝ) ^ 2 * δ₀ ^ 2 + 1) *
                    ∑ l ∈ Finset.range (i + 1 - (i'' + 1)),
                      (2 * CAd l * gridSumPairCount ((i'' + 1) + 1) (l + 3) + 2 * cbg l) := by
                nlinarith [mul_nonneg hc0nn hsum_nn]
              calc (Module.finrank ℝ E : ℝ) ^ 3 *
                    ((∑ l ∈ Finset.range (i + 1 - (i'' + 1)),
                      (2 * CAd l * gridSumPairCount ((i'' + 1) + 1) (l + 3) + 2 * cbg l)) * WW)
                  = ((Module.finrank ℝ E : ℝ) ^ 3 *
                      ∑ l ∈ Finset.range (i + 1 - (i'' + 1)),
                        (2 * CAd l * gridSumPairCount ((i'' + 1) + 1) (l + 3) + 2 * cbg l)) *
                      WW := by ring
                _ ≤ ((Module.finrank ℝ E : ℝ) ^ 3 *
                      (((Module.finrank ℝ E : ℝ) ^ 2 * δ₀ ^ 2 + 1) *
                        ∑ l ∈ Finset.range (i + 1 - (i'' + 1)),
                          (2 * CAd l * gridSumPairCount ((i'' + 1) + 1) (l + 3) + 2 * cbg l))) *
                      WW := by
                    refine mul_le_mul_of_nonneg_right ?_ hWW_nn
                    exact mul_le_mul_of_nonneg_left hstep hfr3
  calc appCcGdiag (E := E) i *
        ∑ i' ∈ Finset.range (i + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 4 (4 + i') x
              ((iteratedCovGrad (I := I) g₀ 4 4 i'
                (slotInsertEndoCc (I := I) (M := M) g₀ 3
                  (perturbationSharpEndoField (I := I) (M := M) g₀ T))).toSection x) *
            ∑ l ∈ Finset.range (i + 1 - i'),
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
                ((iteratedCovGrad (I := I) g₀ 0 4 l
                  (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
                    (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁))).toSection x)
      ≤ appCcGdiag (E := E) i *
          ∑ i' ∈ Finset.range (i + 1), ((Module.finrank ℝ E : ℝ) ^ 3 * BB i i') * WW :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hcell) (appCcGdiag_nonneg (E := E) i)
    _ = (appCcGdiag (E := E) i *
          ∑ i' ∈ Finset.range (i + 1), (Module.finrank ℝ E : ℝ) ^ 3 * BB i i') * WW := by
        rw [← Finset.sum_mul]
        ring

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
private lemma slotInsertEndoCc_add_endo_c (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (A B : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)) :
    slotInsertEndoCc (I := I) (M := M) g₀ s (A + B) =
      slotInsertEndoCc (I := I) (M := M) g₀ s A +
        slotInsertEndoCc (I := I) (M := M) g₀ s B := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  rw [show ((slotInsertEndoCc (I := I) (M := M) g₀ s A +
        slotInsertEndoCc (I := I) (M := M) g₀ s B).toSection x) =
      (slotInsertEndoCc (I := I) (M := M) g₀ s A).toSection x +
        (slotInsertEndoCc (I := I) (M := M) g₀ s B).toSection x from by
    rw [SmoothCcTensor.toSection_add]; rfl]
  rw [ContinuousLinearMap.add_apply]
  simp only [slotInsertEndoCc_toSection]
  rw [show ((A + B) x) = A x + B x from by rw [ContMDiffSection.coe_add]; rfl]
  rw [slotInsertEndoFib_add_left, ContinuousLinearMap.add_apply]

set_option linter.unusedSectionVars false in
private lemma fullRaisedEndoField_diff_split_c (g₀ g₁ : SmoothRiemannianMetric I M) :
    fullRaisedEndoField (I := I) (M := M) g₀ g₁ =
      gInvDiffRaisedEndoField (I := I) g₀ g₁ +
        fullRaisedEndoField (I := I) (M := M) g₀ g₀ := by
  apply ContMDiffSection.ext
  intro x
  rw [show ((gInvDiffRaisedEndoField (I := I) g₀ g₁ +
        fullRaisedEndoField (I := I) (M := M) g₀ g₀) x) =
      gInvDiffRaisedEndoField (I := I) g₀ g₁ x +
        fullRaisedEndoField (I := I) (M := M) g₀ g₀ x from by
    rw [ContMDiffSection.coe_add]; rfl]
  apply ContinuousLinearMap.ext
  intro v
  rw [fullRaisedEndoField_apply, ContinuousLinearMap.add_apply]
  rw [show (gInvDiffRaisedEndoField (I := I) g₀ g₁ x) = gInvDiffRaisedEndo (I := I) g₀ g₁ x
    from rfl]
  rw [fullRaisedEndoField_apply]
  rw [gInvRaisedEndo_eq_diff_add_id (I := I) g₀ g₁ x v]
  rw [show gInvRaisedEndo (I := I) g₀ g₀ x v = v from by
    rw [gInvRaisedEndo_apply, inverseMetricSharpFib_g0FlatCLM]]

set_option linter.unusedSectionVars false in
private lemma g1_inner_gInvRaisedEndo_left_c (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    g₁.inner x (gInvRaisedEndo (I := I) g₀ g₁ x v) w = g₀.inner x v w := by
  rw [gInvRaisedEndo_apply]
  rw [inverseMetricSharpFib_inner (I := I) g₁ x (g0FlatCLM (I := I) g₀ x v) w]
  rw [show cotangentToDualLinear (I := I) (x := x) (g0FlatCLM (I := I) g₀ x v) w =
      cotangentToDual (I := I) (x := x) (g0FlatCLM (I := I) g₀ x v) w from rfl]
  rw [cotangentToDual_g0FlatCLM]

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
private lemma appCcRS_sub_left_cc (g₀ : SmoothRiemannianMetric I M) (a b c : ℕ)
    (Φ₁ Φ₂ : SmoothCcTensor g₀ b c) (W : SmoothCcTensor g₀ a b) :
    appCcRS (I := I) (M := M) g₀ a b c (Φ₁ - Φ₂) W =
      appCcRS (I := I) (M := M) g₀ a b c Φ₁ W - appCcRS (I := I) (M := M) g₀ a b c Φ₂ W := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  rw [show ((appCcRS (I := I) (M := M) g₀ a b c Φ₁ W -
        appCcRS (I := I) (M := M) g₀ a b c Φ₂ W).toSection x) =
      (appCcRS (I := I) (M := M) g₀ a b c Φ₁ W).toSection x -
        (appCcRS (I := I) (M := M) g₀ a b c Φ₂ W).toSection x from by
    rw [SmoothCcTensor.toSection_sub]; rfl]
  rw [ContinuousLinearMap.sub_apply]
  rw [show ((appCcRS (I := I) (M := M) g₀ a b c (Φ₁ - Φ₂) W).toSection x) D =
      ((show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from (Φ₁ - Φ₂).toSection x)
        ((show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from W.toSection x) D)) from by
    rw [appCcRS_toSection]
    rfl]
  rw [show ((appCcRS (I := I) (M := M) g₀ a b c Φ₁ W).toSection x) D =
      ((show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φ₁.toSection x)
        ((show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from W.toSection x) D)) from by
    rw [appCcRS_toSection]
    rfl]
  rw [show ((appCcRS (I := I) (M := M) g₀ a b c Φ₂ W).toSection x) D =
      ((show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φ₂.toSection x)
        ((show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from W.toSection x) D)) from by
    rw [appCcRS_toSection]
    rfl]
  rw [show ((Φ₁ - Φ₂).toSection x) = Φ₁.toSection x - Φ₂.toSection x from by
    rw [SmoothCcTensor.toSection_sub]; rfl]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
private lemma appCcRS_sub_right_cc (g₀ : SmoothRiemannianMetric I M) (a b c : ℕ)
    (Φ : SmoothCcTensor g₀ b c) (W₁ W₂ : SmoothCcTensor g₀ a b) :
    appCcRS (I := I) (M := M) g₀ a b c Φ (W₁ - W₂) =
      appCcRS (I := I) (M := M) g₀ a b c Φ W₁ - appCcRS (I := I) (M := M) g₀ a b c Φ W₂ := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  rw [show ((appCcRS (I := I) (M := M) g₀ a b c Φ W₁ -
        appCcRS (I := I) (M := M) g₀ a b c Φ W₂).toSection x) =
      (appCcRS (I := I) (M := M) g₀ a b c Φ W₁).toSection x -
        (appCcRS (I := I) (M := M) g₀ a b c Φ W₂).toSection x from by
    rw [SmoothCcTensor.toSection_sub]; rfl]
  rw [ContinuousLinearMap.sub_apply]
  rw [show ((appCcRS (I := I) (M := M) g₀ a b c Φ (W₁ - W₂)).toSection x) D =
      ((show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φ.toSection x)
        ((show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from (W₁ - W₂).toSection x) D))
      from by
    rw [appCcRS_toSection]
    rfl]
  rw [show ((appCcRS (I := I) (M := M) g₀ a b c Φ W₁).toSection x) D =
      ((show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φ.toSection x)
        ((show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from W₁.toSection x) D)) from by
    rw [appCcRS_toSection]
    rfl]
  rw [show ((appCcRS (I := I) (M := M) g₀ a b c Φ W₂).toSection x) D =
      ((show Tensor0SSpace b I x →L[ℝ] Tensor0SSpace c I x from Φ.toSection x)
        ((show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from W₂.toSection x) D)) from by
    rw [appCcRS_toSection]
    rfl]
  rw [show ((W₁ - W₂).toSection x) = W₁.toSection x - W₂.toSection x from by
    rw [SmoothCcTensor.toSection_sub]; rfl]
  rw [show ((show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from
      W₁.toSection x - W₂.toSection x) D) =
      (show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from W₁.toSection x) D -
        (show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace b I x from W₂.toSection x) D from rfl]
  rw [map_sub]

private instance tensorRSModelNormedSpaceCC {r s : ℕ} :
    NormedSpace ℝ (TensorRSModel r s ℝ E) :=
  Tensor0SBundle.tensorRSModel_normedSpace r s

set_option backward.isDefEq.respectTransparency false in
private def pureDoubleTraceField (g₀ g₁ : SmoothRiemannianMetric I M) (s : ℕ) :
    SmoothCcTensor g₀ (s + 2) s where
  toSection :=
    { toFun := fun x : M =>
        (show TensorRSSpace (s + 2) s I x from cometricDoubleTraceFib (I := I) g₁ s x)
      contMDiff_toFun := cometricDoubleTraceFib_contMDiff (I := I) g₁ s }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
private lemma appCcRS_slotInsert_id_eq (g₀ : SmoothRiemannianMetric I M) (s c : ℕ)
    (Φ : SmoothCcTensor g₀ (s + 1) c) :
    appCcRS (I := I) (M := M) g₀ (s + 1) (s + 1) c Φ
      (slotInsertEndoCc (I := I) (M := M) g₀ s
        (fullRaisedEndoField (I := I) (M := M) g₀ g₀)) = Φ := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  rw [show ((appCcRS (I := I) (M := M) g₀ (s + 1) (s + 1) c Φ
      (slotInsertEndoCc (I := I) (M := M) g₀ s
        (fullRaisedEndoField (I := I) (M := M) g₀ g₀))).toSection x) D =
      ((show Tensor0SSpace (s + 1) I x →L[ℝ] Tensor0SSpace c I x from Φ.toSection x)
        (slotInsertEndoFib (I := I) (M := M) (s + 1) 0 x
          (fullRaisedEndoField (I := I) (M := M) g₀ g₀ x) D)) from by
    rw [appCcRS_toSection]
    rfl]
  refine congrArg _ ?_
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun m => ?_)
  rw [slotInsertEndoFib_apply_eval]
  rw [show (fullRaisedEndoField (I := I) (M := M) g₀ g₀ x (m 0)) = m 0 from by
    rw [fullRaisedEndoField_apply, gInvRaisedEndo_apply, inverseMetricSharpFib_g0FlatCLM]]
  rw [Function.update_eq_self]

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
private lemma toModel_cons_sum_smul (x : M) {n : ℕ}
    (Zm : Tensor0SModel (n + 1) ℝ E) (d : ℕ) (t : Fin d → ℝ)
    (u : Fin d → E) (rest : Fin n → E) :
    Zm (Fin.cons (∑ c, t c • u c) rest) =
      ∑ c, t c * Zm (Fin.cons (u c) rest) := by
  classical
  have h1 : ∀ v : E, (Fin.cons v rest : Fin (n + 1) → E) =
      Function.update (Fin.cons (0 : E) rest) 0 v := by
    intro v
    rw [Fin.update_cons_zero]
  have hgen : ∀ ss : Finset (Fin d),
      Zm (Function.update (Fin.cons (0 : E) rest) 0 (∑ c ∈ ss, t c • u c)) =
        ∑ c ∈ ss, t c * Zm (Function.update (Fin.cons (0 : E) rest) 0 (u c)) := by
    intro ss
    induction ss using Finset.induction_on with
    | empty =>
        rw [Finset.sum_empty, Finset.sum_empty]
        rw [show (0 : E) = ((0 : ℝ) • (0 : E)) from (zero_smul ℝ (0 : E)).symm]
        rw [ContinuousMultilinearMap.map_update_smul]
        rw [zero_smul]
    | @insert a ss ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha]
        rw [ContinuousMultilinearMap.map_update_add]
        rw [ih]
        congr 1
        rw [ContinuousMultilinearMap.map_update_smul]
        rw [smul_eq_mul]
  have h2 := hgen Finset.univ
  rw [h1, h2]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← h1 (u c)]

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
private lemma toModel_cons_cons_sum_smul (x : M) {n : ℕ}
    (Zm : Tensor0SModel (n + 2) ℝ E) (aa : E) (d : ℕ) (t : Fin d → ℝ)
    (u : Fin d → E) (rest : Fin n → E) :
    Zm (Fin.cons aa (Fin.cons (∑ c, t c • u c) rest)) =
      ∑ c, t c * Zm (Fin.cons aa (Fin.cons (u c) rest)) := by
  classical
  have h1 : ∀ v : E, (Fin.cons aa (Fin.cons v rest) : Fin (n + 2) → E) =
      Function.update (Fin.cons aa (Fin.cons (0 : E) rest)) 1 v := by
    intro v
    rw [show (1 : Fin (n + 2)) = Fin.succ 0 from rfl]
    rw [← Fin.cons_update]
    rw [Fin.update_cons_zero]
  have hgen : ∀ ss : Finset (Fin d),
      Zm (Function.update (Fin.cons aa (Fin.cons (0 : E) rest)) 1 (∑ c ∈ ss, t c • u c)) =
        ∑ c ∈ ss, t c * Zm (Function.update (Fin.cons aa (Fin.cons (0 : E) rest)) 1 (u c)) := by
    intro ss
    induction ss using Finset.induction_on with
    | empty =>
        rw [Finset.sum_empty, Finset.sum_empty]
        rw [show (0 : E) = ((0 : ℝ) • (0 : E)) from (zero_smul ℝ (0 : E)).symm]
        rw [ContinuousMultilinearMap.map_update_smul]
        rw [zero_smul]
    | @insert a ss ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha]
        rw [ContinuousMultilinearMap.map_update_add]
        rw [ih]
        congr 1
        rw [ContinuousMultilinearMap.map_update_smul]
        rw [smul_eq_mul]
  have h2 := hgen Finset.univ
  rw [h1, h2]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← h1 (u c)]

set_option linter.unusedSectionVars false in
private lemma orthoFrame_center_repr (g : SmoothRiemannianMetric I M) (x : M)
    (v : TangentSpace I x) :
    v = ∑ i : Fin (Module.finrank ℝ E),
      g.inner x (smoothOrthoFrame (I := I) g x i x) v • smoothOrthoFrame (I := I) g x i x := by
  classical
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  haveI : Nonempty (Fin (Module.finrank ℝ E)) :=
    ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E))⟩⟩
  set B : Fin (Module.finrank ℝ E) → TangentSpace I x :=
    fun i => smoothOrthoFrame (I := I) g x i x with hB_def
  have horth : ∀ i j, g.inner x (B i) (B j) = if i = j then (1 : ℝ) else 0 :=
    fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g x i j
  have hlin : LinearIndependent ℝ B := by
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    have hpair : g.inner x (∑ i, c i • B i) (B j) = 0 := by
      rw [hc]
      simp
    rw [map_sum, ContinuousLinearMap.sum_apply] at hpair
    have hsimp : ∀ i, g.inner x (c i • B i) (B j) = c i * (if i = j then (1 : ℝ) else 0) := by
      intro i
      rw [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul, horth i j]
    rw [Finset.sum_congr rfl (fun i _ => hsimp i)] at hpair
    have hcol : (∑ i, c i * (if i = j then (1 : ℝ) else 0)) = c j := by simp
    rw [hcol] at hpair
    exact hpair
  have hcard : Fintype.card (Fin (Module.finrank ℝ E)) =
      Module.finrank ℝ (TangentSpace I x) := by
    rw [Fintype.card_fin]
    rfl
  set bB : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x) :=
    basisOfLinearIndependentOfCardEqFinrank hlin hcard with hbB_def
  have hbB_coe : ∀ i, bB i = B i := by
    intro i
    rw [hbB_def]
    change (basisOfLinearIndependentOfCardEqFinrank hlin hcard :
        Fin (Module.finrank ℝ E) → TangentSpace I x) i = B i
    rw [coe_basisOfLinearIndependentOfCardEqFinrank]
  have hrepr : ∀ (w : TangentSpace I x) (j : Fin (Module.finrank ℝ E)),
      bB.repr w j = g.inner x (B j) w := by
    intro w j
    conv_rhs => rw [← bB.sum_repr w]
    rw [map_sum]
    have hsimp : ∀ i, g.inner x (B j) (bB.repr w i • bB i) =
        bB.repr w i * (if j = i then (1 : ℝ) else 0) := by
      intro i
      rw [map_smul, smul_eq_mul, hbB_coe i, horth j i]
    rw [Finset.sum_congr rfl (fun i _ => hsimp i)]
    simp
  conv_lhs => rw [← bB.sum_repr v]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hrepr v i, hbB_coe i]

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
set_option maxHeartbeats 12800000 in
private lemma pureDoubleTraceField_eq_trace_fullRaised (g₀ g₁ : SmoothRiemannianMetric I M)
    (s : ℕ) :
    pureDoubleTraceField (I := I) (M := M) g₀ g₁ s =
      appCcRS (I := I) (M := M) g₀ (s + 2) (s + 2) s
        (cometricDoubleTraceField (I := I) g₀ s)
        (slotInsertEndoCc (I := I) (M := M) g₀ (s + 1)
          (fullRaisedEndoField (I := I) (M := M) g₀ g₁)) := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro Z
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro mm
  have hLHS : Tensor0SSpace.toModel
      ((show Tensor0SSpace (s + 2) I x →L[ℝ] Tensor0SSpace s I x from
        (pureDoubleTraceField (I := I) (M := M) g₀ g₁ s).toSection x) Z) mm =
      ∑ c : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel Z
          (Fin.cons ((smoothOrthoFrame (I := I) g₁ x c x : TangentSpace I x) : E)
            (Fin.cons ((smoothOrthoFrame (I := I) g₁ x c x : TangentSpace I x) : E) mm)) := by
    rw [show ((show Tensor0SSpace (s + 2) I x →L[ℝ] Tensor0SSpace s I x from
        (pureDoubleTraceField (I := I) (M := M) g₀ g₁ s).toSection x) Z) =
        cometricDoubleTraceFib (I := I) g₁ s x Z from rfl]
    rw [cometricDoubleTraceFib_toModel (I := I) g₁ s x Z]
    rw [modelDoubleTrace_apply (E := E) s (cometricLmodel (I := I) g₁ x)]
    rw [cometric_dualTrace_eq_orthoFrame_diag (I := I) g₁ x
      (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x) (Tensor0SSpace.toModel Z) mm]
  rw [hLHS]
  have hRHS : Tensor0SSpace.toModel
      ((show Tensor0SSpace (s + 2) I x →L[ℝ] Tensor0SSpace s I x from
        (appCcRS (I := I) (M := M) g₀ (s + 2) (s + 2) s
          (cometricDoubleTraceField (I := I) g₀ s)
          (slotInsertEndoCc (I := I) (M := M) g₀ (s + 1)
            (fullRaisedEndoField (I := I) (M := M) g₀ g₁))).toSection x) Z) mm =
      ∑ a : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel Z
          (Fin.cons (show E from gInvRaisedEndo (I := I) g₀ g₁ x
              (smoothOrthoFrame (I := I) g₀ x a x))
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x a x : TangentSpace I x) : E) mm)) := by
    rw [show ((show Tensor0SSpace (s + 2) I x →L[ℝ] Tensor0SSpace s I x from
        (appCcRS (I := I) (M := M) g₀ (s + 2) (s + 2) s
          (cometricDoubleTraceField (I := I) g₀ s)
          (slotInsertEndoCc (I := I) (M := M) g₀ (s + 1)
            (fullRaisedEndoField (I := I) (M := M) g₀ g₁))).toSection x) Z) =
        cometricDoubleTraceFib (I := I) g₀ s x
          (slotInsertEndoFib (I := I) (M := M) (s + 2) 0 x
            (fullRaisedEndoField (I := I) (M := M) g₀ g₁ x) Z) from by
      rw [appCcRS_toSection]
      rfl]
    rw [cometricDoubleTraceFib_toModel (I := I) g₀ s x]
    rw [modelDoubleTrace_apply (E := E) s (cometricLmodel (I := I) g₀ x)]
    rw [cometric_dualTrace_eq_orthoFrame_diag (I := I) g₀ x
      (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x)
      (Tensor0SSpace.toModel
        (slotInsertEndoFib (I := I) (M := M) (s + 2) 0 x
          (fullRaisedEndoField (I := I) (M := M) g₀ g₁ x) Z)) mm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [slotInsertEndoFib_apply_eval]
    rw [Fin.update_cons_zero]
    rfl
  rw [hRHS]
  have hGrep : ∀ a : Fin (Module.finrank ℝ E),
      (show E from gInvRaisedEndo (I := I) g₀ g₁ x (smoothOrthoFrame (I := I) g₀ x a x)) =
        ∑ c : Fin (Module.finrank ℝ E),
          (g₀.inner x (smoothOrthoFrame (I := I) g₀ x a x) (smoothOrthoFrame (I := I) g₁ x c x)) •
            (smoothOrthoFrame (I := I) g₁ x c x : E) := by
    intro a
    have h1 := orthoFrame_center_repr (I := I) (M := M) g₁ x
      (gInvRaisedEndo (I := I) g₀ g₁ x (smoothOrthoFrame (I := I) g₀ x a x))
    rw [show (show E from gInvRaisedEndo (I := I) g₀ g₁ x
        (smoothOrthoFrame (I := I) g₀ x a x)) =
        gInvRaisedEndo (I := I) g₀ g₁ x (smoothOrthoFrame (I := I) g₀ x a x) from rfl]
    conv_lhs => rw [h1]
    refine Finset.sum_congr rfl fun c _ => ?_
    congr 1
    rw [g₁.symm x (smoothOrthoFrame (I := I) g₁ x c x)
      (gInvRaisedEndo (I := I) g₀ g₁ x (smoothOrthoFrame (I := I) g₀ x a x))]
    rw [g1_inner_gInvRaisedEndo_left_c (I := I) (M := M) g₀ g₁ x
      (smoothOrthoFrame (I := I) g₀ x a x) (smoothOrthoFrame (I := I) g₁ x c x)]
  symm
  calc (∑ a : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel Z
          (Fin.cons (show E from gInvRaisedEndo (I := I) g₀ g₁ x
              (smoothOrthoFrame (I := I) g₀ x a x))
            (Fin.cons ((smoothOrthoFrame (I := I) g₀ x a x : TangentSpace I x) : E) mm)))
      = ∑ a : Fin (Module.finrank ℝ E), ∑ c : Fin (Module.finrank ℝ E),
          (g₀.inner x (smoothOrthoFrame (I := I) g₀ x a x)
            (smoothOrthoFrame (I := I) g₁ x c x)) *
          Tensor0SSpace.toModel Z
            (Fin.cons ((smoothOrthoFrame (I := I) g₁ x c x : TangentSpace I x) : E)
              (Fin.cons ((smoothOrthoFrame (I := I) g₀ x a x : TangentSpace I x) : E) mm)) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [hGrep a]
        exact toModel_cons_sum_smul (E := E) x (Tensor0SSpace.toModel Z)
          (Module.finrank ℝ E)
          (fun c => g₀.inner x (smoothOrthoFrame (I := I) g₀ x a x)
            (smoothOrthoFrame (I := I) g₁ x c x))
          (fun c => (smoothOrthoFrame (I := I) g₁ x c x : E))
          (Fin.cons ((smoothOrthoFrame (I := I) g₀ x a x : TangentSpace I x) : E) mm)
    _ = ∑ c : Fin (Module.finrank ℝ E), ∑ a : Fin (Module.finrank ℝ E),
          (g₀.inner x (smoothOrthoFrame (I := I) g₀ x a x)
            (smoothOrthoFrame (I := I) g₁ x c x)) *
          Tensor0SSpace.toModel Z
            (Fin.cons ((smoothOrthoFrame (I := I) g₁ x c x : TangentSpace I x) : E)
              (Fin.cons ((smoothOrthoFrame (I := I) g₀ x a x : TangentSpace I x) : E) mm)) :=
        Finset.sum_comm
    _ = ∑ c : Fin (Module.finrank ℝ E),
          Tensor0SSpace.toModel Z
            (Fin.cons ((smoothOrthoFrame (I := I) g₁ x c x : TangentSpace I x) : E)
              (Fin.cons ((smoothOrthoFrame (I := I) g₁ x c x : TangentSpace I x) : E) mm)) := by
        refine Finset.sum_congr rfl fun c _ => ?_
        have hsum := toModel_cons_cons_sum_smul (E := E) x (Tensor0SSpace.toModel Z)
          ((smoothOrthoFrame (I := I) g₁ x c x : TangentSpace I x) : E)
          (Module.finrank ℝ E)
          (fun a => g₀.inner x (smoothOrthoFrame (I := I) g₀ x a x)
            (smoothOrthoFrame (I := I) g₁ x c x))
          (fun a => (smoothOrthoFrame (I := I) g₀ x a x : E)) mm
        rw [← hsum]
        congr 2
        have hrep0 := orthoFrame_center_repr (I := I) (M := M) g₀ x
          (smoothOrthoFrame (I := I) g₁ x c x)
        rw [show (∑ a : Fin (Module.finrank ℝ E),
            g₀.inner x (smoothOrthoFrame (I := I) g₀ x a x)
              (smoothOrthoFrame (I := I) g₁ x c x) •
              (smoothOrthoFrame (I := I) g₀ x a x : E)) =
            ((∑ a : Fin (Module.finrank ℝ E),
              g₀.inner x (smoothOrthoFrame (I := I) g₀ x a x)
                (smoothOrthoFrame (I := I) g₁ x c x) •
                smoothOrthoFrame (I := I) g₀ x a x : TangentSpace I x) : E) from rfl]
        rw [← hrep0]

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
private lemma appCcRS_add_left_cc (g₀ : SmoothRiemannianMetric I M) (a b c : ℕ)
    (Φ₁ Φ₂ : SmoothCcTensor g₀ b c) (W : SmoothCcTensor g₀ a b) :
    appCcRS (I := I) (M := M) g₀ a b c (Φ₁ + Φ₂) W =
      appCcRS (I := I) (M := M) g₀ a b c Φ₁ W + appCcRS (I := I) (M := M) g₀ a b c Φ₂ W := by
  have h := appCcRS_sub_left_cc (I := I) (M := M) g₀ a b c (Φ₁ + Φ₂) Φ₂ W
  rw [add_sub_cancel_right] at h
  rw [h]
  abel

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
private lemma slotExtend_sub_cc (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (X Y : SmoothCcTensor g₀ r s) :
    slotExtend (I := I) (M := M) g₀ r s (X - Y) =
      slotExtend (I := I) (M := M) g₀ r s X - slotExtend (I := I) (M := M) g₀ r s Y := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  rw [show ((slotExtend (I := I) (M := M) g₀ r s X -
        slotExtend (I := I) (M := M) g₀ r s Y).toSection x) =
      (slotExtend (I := I) (M := M) g₀ r s X).toSection x -
        (slotExtend (I := I) (M := M) g₀ r s Y).toSection x from by
    rw [SmoothCcTensor.toSection_sub]; rfl]
  rw [ContinuousLinearMap.sub_apply]
  rw [show ((slotExtend (I := I) (M := M) g₀ r s (X - Y)).toSection x) D =
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x).symm
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
          (X - Y).toSection x).comp
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) r x D)) from rfl]
  rw [show ((slotExtend (I := I) (M := M) g₀ r s X).toSection x) D =
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x).symm
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from X.toSection x).comp
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) r x D)) from rfl]
  rw [show ((slotExtend (I := I) (M := M) g₀ r s Y).toSection x) D =
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x).symm
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Y.toSection x).comp
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) r x D)) from rfl]
  rw [show ((X - Y).toSection x) = X.toSection x - Y.toSection x from by
    rw [SmoothCcTensor.toSection_sub]; rfl]
  rw [show ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
      X.toSection x - Y.toSection x).comp
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) r x D)) =
      ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from X.toSection x).comp
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) r x D)) -
      ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Y.toSection x).comp
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) r x D)) from by
    apply ContinuousLinearMap.ext
    intro w
    rfl]
  rw [map_sub]

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
private lemma rsDomDomCongrSection_sub_cc (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (σ : Equiv.Perm (Fin s)) (X Y : SmoothCcTensor g₀ r s) :
    rsDomDomCongrSection (I := I) (M := M) g₀ r s σ (X - Y) =
      rsDomDomCongrSection (I := I) (M := M) g₀ r s σ X -
        rsDomDomCongrSection (I := I) (M := M) g₀ r s σ Y := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun m => ?_)
  have hsub : ((X - Y).toSection x) = X.toSection x - Y.toSection x := by
    rw [SmoothCcTensor.toSection_sub]; rfl
  have hsub2 : ((rsDomDomCongrSection (I := I) (M := M) g₀ r s σ X -
      rsDomDomCongrSection (I := I) (M := M) g₀ r s σ Y).toSection x) =
      (rsDomDomCongrSection (I := I) (M := M) g₀ r s σ X).toSection x -
        (rsDomDomCongrSection (I := I) (M := M) g₀ r s σ Y).toSection x := by
    rw [SmoothCcTensor.toSection_sub]; rfl
  rw [rsDomDomCongrSection_toSection, hsub, hsub2]
  rw [rsDomDomCongrSection_toSection, rsDomDomCongrSection_toSection]
  have hfib : ∀ (y : Tensor0SSpace s I x) (w : Fin s → TangentSpace I x),
      Tensor0SSpace.toModel y w = (y : Tensor0SSpace s I x) w := fun _ _ => rfl
  rw [hfib, hfib]
  rw [rsDomDomCongr_apply_eval (I := I) (M := M) σ (X.toSection x - Y.toSection x) D m]
  rw [show ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
      rsDomDomCongr σ (X.toSection x) - rsDomDomCongr σ (Y.toSection x)) D) =
      (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
        rsDomDomCongr σ (X.toSection x)) D -
      (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
        rsDomDomCongr σ (Y.toSection x)) D from rfl]
  rw [show ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
      (X.toSection x - Y.toSection x : TensorRSSpace r s I x)) D) =
      (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from X.toSection x) D -
      (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Y.toSection x) D from rfl]
  rw [show ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
        rsDomDomCongr σ (X.toSection x)) D -
      (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
        rsDomDomCongr σ (Y.toSection x)) D : Tensor0SSpace s I x) m =
      ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
        rsDomDomCongr σ (X.toSection x)) D : Tensor0SSpace s I x) m -
      ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
        rsDomDomCongr σ (Y.toSection x)) D : Tensor0SSpace s I x) m from rfl]
  rw [rsDomDomCongr_apply_eval (I := I) (M := M) σ (X.toSection x) D m]
  rw [rsDomDomCongr_apply_eval (I := I) (M := M) σ (Y.toSection x) D m]
  rfl

private def pairTraceOp (g₀ gm : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 6 2 :=
  appCcRS (I := I) (M := M) g₀ 6 4 2
    (pureDoubleTraceField (I := I) (M := M) g₀ gm 2)
    (pureDoubleTraceField (I := I) (M := M) g₀ gm 4)

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
set_option maxHeartbeats 12800000 in
private lemma pairTraceOp_apply_toModel (g₀ gm : SmoothRiemannianMetric I M)
    (X : SmoothCcTensor g₀ 0 4) (x : M) (D : Tensor0SSpace 2 I x) (v : Fin 2 → E) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
          (appCcRS (I := I) (M := M) g₀ 2 6 2 (pairTraceOp (I := I) (M := M) g₀ gm)
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2 X))).toSection x) D) v =
      ∑ b : Fin (Module.finrank ℝ E), ∑ a : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel D
            ![(smoothOrthoFrame (I := I) gm x a x : E),
              (smoothOrthoFrame (I := I) gm x b x : E)] *
          unitModel (I := I) (M := M) g₀ 4 X x
            ![v 0, v 1, (smoothOrthoFrame (I := I) gm x a x : E),
              (smoothOrthoFrame (I := I) gm x b x : E)] := by
  classical
  set Y : Tensor0SSpace 6 I x :=
    (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
      (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2 X)).toSection x) D with hY_def
  have hYval : ∀ w : Fin 6 → TangentSpace I x,
      Tensor0SSpace.toModel Y w =
        Tensor0SSpace.toModel D ![w 1, w 3] *
          unitModel (I := I) (M := M) g₀ 4 X x ![w 4, w 5, w 0, w 2] := by
    intro w
    rw [hY_def]
    rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2 X)).toSection x) D) =
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
          rsDomDomCongr sigmaE0
            ((slotExtendIter (I := I) (M := M) g₀ 0 4 2 X).toSection x)) D) from by
      rw [rsDomDomCongrSection_toSection]]
    rw [toModel_rsDomDomCongr_apply (I := I) (M := M) sigmaE0
      ((slotExtendIter (I := I) (M := M) g₀ 0 4 2 X).toSection x) D]
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    rw [slotExtendIter_two_toModel (I := I) (M := M) g₀ X x D
      (fun i => w (sigmaE0 i))]
    refine congrArg₂ (· * ·) ?_ ?_
    · refine congrArg _ ?_
      funext k
      fin_cases k <;> rfl
    · refine congrArg _ ?_
      funext k
      fin_cases k <;> rfl
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      (appCcRS (I := I) (M := M) g₀ 2 6 2 (pairTraceOp (I := I) (M := M) g₀ gm)
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2 X))).toSection x) D) =
      cometricDoubleTraceFib (I := I) gm 2 x
        (cometricDoubleTraceFib (I := I) gm 4 x Y) from by
    rw [hY_def]
    rw [appCcRS_toSection]
    rfl]
  rw [cometricDoubleTraceFib_toModel (I := I) gm 2 x]
  rw [modelDoubleTrace_apply (E := E) 2 (cometricLmodel (I := I) gm x)]
  rw [cometric_dualTrace_eq_orthoFrame_diag (I := I) gm x
    (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x)
    (Tensor0SSpace.toModel (cometricDoubleTraceFib (I := I) gm 4 x Y))
    (fun j => (v j : E))]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [cometricDoubleTraceFib_toModel (I := I) gm 4 x Y]
  rw [modelDoubleTrace_apply (E := E) 4 (cometricLmodel (I := I) gm x)]
  rw [cometric_dualTrace_eq_orthoFrame_diag (I := I) gm x
    (mem_smoothOrthoFrameNbhd_self (I := I) (M := M) x)
    (Tensor0SSpace.toModel Y)
    (Fin.cons ((smoothOrthoFrame (I := I) gm x b x : TangentSpace I x) : E)
      (Fin.cons ((smoothOrthoFrame (I := I) gm x b x : TangentSpace I x) : E)
        (fun j => (v j : E))))]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [hYval]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
set_option maxHeartbeats 12800000 in
private theorem riemannCoeff_eq_pairTrace_L11 (g₀ g₁ : SmoothRiemannianMetric I M) :
    ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ =
      (2 : ℝ) • appCcRS (I := I) (M := M) g₀ 2 6 2 (pairTraceOp (I := I) (M := M) g₀ g₁)
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁))) := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  have hsmul : ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      ((2 : ℝ) • appCcRS (I := I) (M := M) g₀ 2 6 2 (pairTraceOp (I := I) (M := M) g₀ g₁)
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁)))).toSection x) D) =
      (2 : ℝ) • ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (appCcRS (I := I) (M := M) g₀ 2 6 2 (pairTraceOp (I := I) (M := M) g₀ g₁)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁)))).toSection x) D) := by
    rw [show (((2 : ℝ) • appCcRS (I := I) (M := M) g₀ 2 6 2
        (pairTraceOp (I := I) (M := M) g₀ g₁)
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁)))).toSection x) =
        (2 : ℝ) • ((appCcRS (I := I) (M := M) g₀ 2 6 2 (pairTraceOp (I := I) (M := M) g₀ g₁)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁)))).toSection x) from by
      rw [SmoothCcTensor.toSection_smul]; rfl]
    rfl
  rw [hsmul]
  beta_reduce
  rw [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  rw [pairTraceOp_apply_toModel (I := I) (M := M) g₀ g₁
    (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁) x D v]
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁).toSection x) D) =
      riemannBiContrFib (I := I) g₁ x D from rfl]
  rw [show riemannBiContrFib (I := I) g₁ x =
      riemannBiContrFibFixedFrame (I := I) g₁ (smoothOrthoFrame (I := I) g₁ x) x from rfl]
  rw [riemannBiContrFibFixedFrame_toModel (I := I) g₁ (smoothOrthoFrame (I := I) g₁ x) x D v]
  rw [Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [riemannLoweredCc_unitModel_apply (I := I) (M := M) g₀ g₁ g₁ x
    (![v 0, v 1, (smoothOrthoFrame (I := I) g₁ x b x : E),
      (smoothOrthoFrame (I := I) g₁ x a x : E)] : Fin 4 → TangentSpace I x)]
  rw [show (![v 0, v 1, (smoothOrthoFrame (I := I) g₁ x b x : E),
      (smoothOrthoFrame (I := I) g₁ x a x : E)] : Fin 4 → TangentSpace I x) 0 = v 0 from rfl]
  rw [show (![v 0, v 1, (smoothOrthoFrame (I := I) g₁ x b x : E),
      (smoothOrthoFrame (I := I) g₁ x a x : E)] : Fin 4 → TangentSpace I x) 1 = v 1 from rfl]
  rw [show (![v 0, v 1, (smoothOrthoFrame (I := I) g₁ x b x : E),
      (smoothOrthoFrame (I := I) g₁ x a x : E)] : Fin 4 → TangentSpace I x) 2 =
    smoothOrthoFrame (I := I) g₁ x b x from rfl]
  rw [show (![v 0, v 1, (smoothOrthoFrame (I := I) g₁ x b x : E),
      (smoothOrthoFrame (I := I) g₁ x a x : E)] : Fin 4 → TangentSpace I x) 3 =
    smoothOrthoFrame (I := I) g₁ x a x from rfl]
  ring

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
set_option maxHeartbeats 12800000 in
private theorem riemannMixedCoeff_eq_pairTrace_L01 (g₀ g₁ : SmoothRiemannianMetric I M) :
    ricciArmOrder0RiemannMixedCoeff (I := I) (M := M) g₀ g₁ =
      (2 : ℝ) • appCcRS (I := I) (M := M) g₀ 2 6 2 (pairTraceOp (I := I) (M := M) g₀ g₀)
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁))) := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  have hsmul : ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      ((2 : ℝ) • appCcRS (I := I) (M := M) g₀ 2 6 2 (pairTraceOp (I := I) (M := M) g₀ g₀)
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁)))).toSection x) D) =
      (2 : ℝ) • ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (appCcRS (I := I) (M := M) g₀ 2 6 2 (pairTraceOp (I := I) (M := M) g₀ g₀)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁)))).toSection x) D) := by
    rw [show (((2 : ℝ) • appCcRS (I := I) (M := M) g₀ 2 6 2
        (pairTraceOp (I := I) (M := M) g₀ g₀)
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁)))).toSection x) =
        (2 : ℝ) • ((appCcRS (I := I) (M := M) g₀ 2 6 2 (pairTraceOp (I := I) (M := M) g₀ g₀)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁)))).toSection x) from by
      rw [SmoothCcTensor.toSection_smul]; rfl]
    rfl
  rw [hsmul]
  beta_reduce
  rw [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  rw [pairTraceOp_apply_toModel (I := I) (M := M) g₀ g₀
    (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁) x D v]
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      (ricciArmOrder0RiemannMixedCoeff (I := I) (M := M) g₀ g₁).toSection x) D) =
      riemannMixedBiContrFib (I := I) (M := M) g₀ g₁ x D from rfl]
  rw [show riemannMixedBiContrFib (I := I) (M := M) g₀ g₁ x =
      riemannMixedBiContrFibFixedFrame (I := I) g₀ g₁
        (smoothOrthoFrame (I := I) g₀ x) x from rfl]
  rw [riemannMixedBiContrFibFixedFrame_toModel (I := I) g₀ g₁
    (smoothOrthoFrame (I := I) g₀ x) x D v]
  rw [Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [riemannLoweredCc_unitModel_apply (I := I) (M := M) g₀ g₀ g₁ x
    (![v 0, v 1, (smoothOrthoFrame (I := I) g₀ x b x : E),
      (smoothOrthoFrame (I := I) g₀ x a x : E)] : Fin 4 → TangentSpace I x)]
  rw [show (![v 0, v 1, (smoothOrthoFrame (I := I) g₀ x b x : E),
      (smoothOrthoFrame (I := I) g₀ x a x : E)] : Fin 4 → TangentSpace I x) 0 = v 0 from rfl]
  rw [show (![v 0, v 1, (smoothOrthoFrame (I := I) g₀ x b x : E),
      (smoothOrthoFrame (I := I) g₀ x a x : E)] : Fin 4 → TangentSpace I x) 1 = v 1 from rfl]
  rw [show (![v 0, v 1, (smoothOrthoFrame (I := I) g₀ x b x : E),
      (smoothOrthoFrame (I := I) g₀ x a x : E)] : Fin 4 → TangentSpace I x) 2 =
    smoothOrthoFrame (I := I) g₀ x b x from rfl]
  rw [show (![v 0, v 1, (smoothOrthoFrame (I := I) g₀ x b x : E),
      (smoothOrthoFrame (I := I) g₀ x a x : E)] : Fin 4 → TangentSpace I x) 3 =
    smoothOrthoFrame (I := I) g₀ x a x from rfl]
  ring

set_option linter.unusedSectionVars false in
private lemma iteratedCovGrad_zero_of_covGrad_zero (g₀ : SmoothRiemannianMetric I M)
    (r s : ℕ) (Φ : SmoothCcTensor g₀ r s)
    (hΦ : covGrad (I := I) (M := M) g₀ r s Φ = 0) (m : ℕ) :
    iteratedCovGrad (I := I) g₀ r s (m + 1) Φ = 0 := by
  induction m with
  | zero =>
      rw [iteratedCovGrad_succ, iteratedCovGrad_zero]
      exact hΦ
  | succ m' ih =>
      rw [iteratedCovGrad_succ, ih, covGrad_zero]

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
private lemma pureDoubleTraceField_self_eq (g₀ : SmoothRiemannianMetric I M) (s : ℕ) :
    pureDoubleTraceField (I := I) (M := M) g₀ g₀ s = cometricDoubleTraceField (I := I) g₀ s := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [cometricDoubleTraceField_toSection]
  rfl

set_option linter.unusedSectionVars false in
private lemma pairTraceOp_self_eq (g₀ : SmoothRiemannianMetric I M) :
    pairTraceOp (I := I) (M := M) g₀ g₀ = phiDtPair (I := I) (M := M) g₀ := by
  rw [pairTraceOp, phiDtPair, pureDoubleTraceField_self_eq (I := I) (M := M) g₀ 2,
    pureDoubleTraceField_self_eq (I := I) (M := M) g₀ 4]

set_option linter.unusedSectionVars false in
private lemma pureDoubleTraceField_cross_split (g₀ g₁ : SmoothRiemannianMetric I M) (s : ℕ) :
    pureDoubleTraceField (I := I) (M := M) g₀ g₁ s =
      appCcRS (I := I) (M := M) g₀ (s + 2) (s + 2) s
        (cometricDoubleTraceField (I := I) g₀ s)
        (slotInsertEndoCc (I := I) (M := M) g₀ (s + 1)
          (gInvDiffRaisedEndoField (I := I) g₀ g₁)) +
      cometricDoubleTraceField (I := I) g₀ s := by
  rw [pureDoubleTraceField_eq_trace_fullRaised (I := I) (M := M) g₀ g₁ s]
  rw [fullRaisedEndoField_diff_split_c (I := I) (M := M) g₀ g₁]
  rw [slotInsertEndoCc_add_endo_c (I := I) (M := M) g₀ (s + 1)]
  rw [appCcRS_add_right (I := I) (M := M) g₀ (s + 2) (s + 2) s
    (cometricDoubleTraceField (I := I) g₀ s)]
  rw [appCcRS_slotInsert_id_eq (I := I) (M := M) g₀ (s + 1) s
    (cometricDoubleTraceField (I := I) g₀ s)]

/-- The moving cometric double-trace field, retagged to the frozen metric.

This short public name exposes the canonical field used internally by the
curvature coefficient tower.  Its fibre is the genuine `g₁⁻¹` double trace;
the frozen metric `g₀` only supplies the Hilbert-bundle tag. -/
noncomputable def pureTrace (g₀ g₁ : SmoothRiemannianMetric I M) (s : ℕ) :
    SmoothCcTensor g₀ (s + 2) s :=
  pureDoubleTraceField (I := I) (M := M) g₀ g₁ s

/-- Fibre readout of the moving cometric double trace. -/
@[simp] theorem pureTrace_toSection
    (g₀ g₁ : SmoothRiemannianMetric I M) (s : ℕ) (x : M) :
    (pureTrace (I := I) (M := M) g₀ g₁ s).toSection x =
      (show TensorRSSpace (s + 2) s I x from
        cometricDoubleTraceFib (I := I) g₁ s x) := rfl

/-- The moving double trace is the fixed parallel trace plus the exact
inverse-metric-difference correction. -/
theorem pureTrace_split (g₀ g₁ : SmoothRiemannianMetric I M) (s : ℕ) :
    pureTrace (I := I) (M := M) g₀ g₁ s =
      appCcRS (I := I) (M := M) g₀ (s + 2) (s + 2) s
        (cometricDoubleTraceField (I := I) g₀ s)
        (slotInsertEndoCc (I := I) (M := M) g₀ (s + 1)
          (gInvDiffRaisedEndoField (I := I) g₀ g₁)) +
      cometricDoubleTraceField (I := I) g₀ s := by
  exact pureDoubleTraceField_cross_split (I := I) (M := M) g₀ g₁ s

set_option linter.unusedVariables false in
private theorem exists_rfns_iteratedCovGrad_pairTraceOp_diff_grid
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ CΔ : ℕ → ℝ, (∀ j, 0 ≤ CΔ j) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (j : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 6 (2 + j) x
            ((iteratedCovGrad (I := I) g₀ 6 2 j
              (pairTraceOp (I := I) (M := M) g₀ g₁ -
                pairTraceOp (I := I) (M := M) g₀ g₀)).toSection x) ≤
          CΔ j * ∑ l ∈ Finset.range (j + 1),
            Combinatorics.antidiagonalTupleGrid
              (fun j' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j') x
                ((iteratedCovGrad (I := I) g₀ 0 2 j' T).toSection x)) l := by
  classical
  obtain ⟨CD, hCD_nn, hCD⟩ :=
    rfns_iteratedCovGrad_slotInsertEndoCc_zero_gInvDiffRaisedEndoField_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨c2, hc2_nn, hc2⟩ := exists_bound_riemannianFiberNormSq_smoothCcTensor
    (I := I) (M := M) g₀ 4 2 (cometricDoubleTraceField (I := I) g₀ 2)
  obtain ⟨c4, hc4_nn, hc4⟩ := exists_bound_riemannianFiberNormSq_smoothCcTensor
    (I := I) (M := M) g₀ 6 4 (cometricDoubleTraceField (I := I) g₀ 4)
  set dim : ℝ := (Module.finrank ℝ E : ℝ) with hdim_def
  have hdim_nn : 0 ≤ dim := Nat.cast_nonneg _
  set CDS : ℕ → ℝ := fun j => ∑ l ∈ Finset.range (j + 1), CD l with hCDS_def
  have hCDS_nn : ∀ j, 0 ≤ CDS j := by
    intro j
    rw [hCDS_def]
    exact Finset.sum_nonneg fun l _ => hCD_nn l
  have hCDS_mono : ∀ {j j' : ℕ}, j ≤ j' → CDS j ≤ CDS j' := by
    intro j j' hj
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_subset_range.mpr (by omega)) (fun l _ _ => hCD_nn l)
  have hCD_le_CDS : ∀ {l j : ℕ}, l ≤ j → CD l ≤ CDS j := by
    intro l j hl
    exact Finset.single_le_sum (f := fun l' => CD l') (fun l' _ => hCD_nn l')
      (Finset.mem_range.mpr (by omega))
  clear_value CDS
  set K2 : ℕ → ℝ := fun m => appCcGdiag (E := E) m * c2 * dim ^ (2 + 1) * CDS m with hK2_def
  set K4 : ℕ → ℝ := fun m => appCcGdiag (E := E) m * c4 * dim ^ (4 + 1) * CDS m with hK4_def
  have hK2_nn : ∀ m, 0 ≤ K2 m := by
    intro m
    rw [hK2_def]
    have := appCcGdiag_nonneg (E := E) m
    have := hCDS_nn m
    positivity
  have hK4_nn : ∀ m, 0 ≤ K4 m := by
    intro m
    rw [hK4_def]
    have := appCcGdiag_nonneg (E := E) m
    have := hCDS_nn m
    positivity
  have hK2val : ∀ m, K2 m = appCcGdiag (E := E) m * c2 * dim ^ (2 + 1) * CDS m := fun m => by
    rw [hK2_def]
  have hK4val : ∀ m, K4 m = appCcGdiag (E := E) m * c4 * dim ^ (4 + 1) * CDS m := fun m => by
    rw [hK4_def]
  clear_value K2 K4
  refine ⟨fun j => 2 * (appCcGdiag (E := E) j *
      ∑ m ∈ Finset.range (j + 1), ∑ l ∈ Finset.range (j + 1 - m),
        K2 m * (2 * K4 l + 2 * c4) * gridSumPairCount (m + 1) (l + 1)) +
    2 * (appCcGdiag (E := E) j *
      ∑ m ∈ Finset.range (j + 1), ∑ l ∈ Finset.range (j + 1 - m),
        c2 * K4 l * gridSumPairCount (m + 1) (l + 1)),
    fun j => by
      have h1 : 0 ≤ ∑ m ∈ Finset.range (j + 1), ∑ l ∈ Finset.range (j + 1 - m),
          K2 m * (2 * K4 l + 2 * c4) * gridSumPairCount (m + 1) (l + 1) :=
        Finset.sum_nonneg fun m _ => Finset.sum_nonneg fun l _ =>
          mul_nonneg (mul_nonneg (hK2_nn m) (by
            have := hK4_nn l
            linarith)) (gridSumPairCount_nonneg _ _)
      have h2 : 0 ≤ ∑ m ∈ Finset.range (j + 1), ∑ l ∈ Finset.range (j + 1 - m),
          c2 * K4 l * gridSumPairCount (m + 1) (l + 1) :=
        Finset.sum_nonneg fun m _ => Finset.sum_nonneg fun l _ =>
          mul_nonneg (mul_nonneg hc2_nn (hK4_nn l)) (gridSumPairCount_nonneg _ _)
      have h3 := appCcGdiag_nonneg (E := E) j
      positivity, ?_⟩
  intro g₁ T htie δ hδ_le hδ0 hbound j x
  set b : ℕ → ℝ := fun j' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j') x
    ((iteratedCovGrad (I := I) g₀ 0 2 j' T).toSection x) with hb_def
  have hb : ∀ j', 0 ≤ b j' :=
    fun j' => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + j') x _
  have hGg_nn : ∀ m, 0 ≤ ∑ l ∈ Finset.range (m + 1), Combinatorics.antidiagonalTupleGrid b l :=
    fun m => Finset.sum_nonneg fun l _ => Combinatorics.antidiagonalTupleGrid_nonneg b hb l
  have hGg_one : ∀ m : ℕ, (1 : ℝ) ≤ ∑ l ∈ Finset.range (m + 1),
      Combinatorics.antidiagonalTupleGrid b l := by
    intro m
    calc (1 : ℝ) = Combinatorics.antidiagonalTupleGrid b 0 :=
          (Combinatorics.antidiagonalTupleGrid_zero b).symm
      _ ≤ ∑ l ∈ Finset.range (m + 1), Combinatorics.antidiagonalTupleGrid b l :=
          Finset.single_le_sum
            (f := fun l => Combinatorics.antidiagonalTupleGrid b l)
            (fun l _ => Combinatorics.antidiagonalTupleGrid_nonneg b hb l)
            (Finset.mem_range.mpr (by omega))
  have hQjets : ∀ (ss : ℕ) (cS : ℝ), 0 ≤ cS →
      (∀ y : M, riemannianFiberNormSq (I := I) (M := M) g₀ (ss + 2) ss y
        ((cometricDoubleTraceField (I := I) g₀ ss).toSection y) ≤ cS) →
      ∀ m : ℕ,
      riemannianFiberNormSq (I := I) (M := M) g₀ (ss + 2) (ss + m) x
          ((iteratedCovGrad (I := I) g₀ (ss + 2) ss m
            (appCcRS (I := I) (M := M) g₀ (ss + 2) (ss + 2) ss
              (cometricDoubleTraceField (I := I) g₀ ss)
              (slotInsertEndoCc (I := I) (M := M) g₀ (ss + 1)
                (gInvDiffRaisedEndoField (I := I) g₀ g₁)))).toSection x) ≤
        (appCcGdiag (E := E) m * cS * dim ^ (ss + 1) * CDS m) *
          ∑ l ∈ Finset.range (m + 1), Combinatorics.antidiagonalTupleGrid b l := by
    intro ss cS hcS_nn hcS m
    refine le_trans (rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le
      (I := I) (M := M) g₀ m (ss + 2) (ss + 2) ss
      (cometricDoubleTraceField (I := I) g₀ ss)
      (slotInsertEndoCc (I := I) (M := M) g₀ (ss + 1)
        (gInvDiffRaisedEndoField (I := I) g₀ g₁)) x) ?_
    have hphi : ∀ m' ∈ Finset.range (m + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ (ss + 2) (ss + m') x
            ((iteratedCovGrad (I := I) g₀ (ss + 2) ss m'
              (cometricDoubleTraceField (I := I) g₀ ss)).toSection x) *
          ∑ l ∈ Finset.range (m + 1 - m'),
            riemannianFiberNormSq (I := I) (M := M) g₀ (ss + 2) ((ss + 2) + l) x
              ((iteratedCovGrad (I := I) g₀ (ss + 2) (ss + 2) l
                (slotInsertEndoCc (I := I) (M := M) g₀ (ss + 1)
                  (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection x) ≤
        (if m' = 0 then
          cS * ∑ l ∈ Finset.range (m + 1),
            dim ^ (ss + 1) * (CD l * Combinatorics.antidiagonalTupleGrid b l)
        else 0) := by
      intro m' hm'
      match m' with
      | 0 =>
          rw [if_pos rfl]
          have hphi0 : riemannianFiberNormSq (I := I) (M := M) g₀ (ss + 2) (ss + 0) x
              ((iteratedCovGrad (I := I) g₀ (ss + 2) ss 0
                (cometricDoubleTraceField (I := I) g₀ ss)).toSection x) ≤ cS := by
            rw [iteratedCovGrad_zero]
            exact hcS x
          have hSI : ∀ l ∈ Finset.range (m + 1 - 0),
              riemannianFiberNormSq (I := I) (M := M) g₀ (ss + 2) ((ss + 2) + l) x
                ((iteratedCovGrad (I := I) g₀ (ss + 2) (ss + 2) l
                  (slotInsertEndoCc (I := I) (M := M) g₀ (ss + 1)
                    (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection x) ≤
              dim ^ (ss + 1) * (CD l * Combinatorics.antidiagonalTupleGrid b l) := by
            intro l _
            refine le_trans (rfns_iteratedCovGrad_slotInsertEndoCc_le_endo
              (I := I) (M := M) g₀ (ss + 1) (gInvDiffRaisedEndoField (I := I) g₀ g₁) l x) ?_
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact hCD g₁ T htie hδ_le hδ0 hbound l x
          have hsum_le : (∑ l ∈ Finset.range (m + 1 - 0),
              riemannianFiberNormSq (I := I) (M := M) g₀ (ss + 2) ((ss + 2) + l) x
                ((iteratedCovGrad (I := I) g₀ (ss + 2) (ss + 2) l
                  (slotInsertEndoCc (I := I) (M := M) g₀ (ss + 1)
                    (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection x)) ≤
              ∑ l ∈ Finset.range (m + 1),
                dim ^ (ss + 1) * (CD l * Combinatorics.antidiagonalTupleGrid b l) := by
            refine le_trans (Finset.sum_le_sum hSI) ?_
            exact le_of_eq (by norm_num)
          have hsum_nn : 0 ≤ ∑ l ∈ Finset.range (m + 1 - 0),
              riemannianFiberNormSq (I := I) (M := M) g₀ (ss + 2) ((ss + 2) + l) x
                ((iteratedCovGrad (I := I) g₀ (ss + 2) (ss + 2) l
                  (slotInsertEndoCc (I := I) (M := M) g₀ (ss + 1)
                    (gInvDiffRaisedEndoField (I := I) g₀ g₁))).toSection x) :=
            Finset.sum_nonneg fun l _ =>
              riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ (ss + 2) ((ss + 2) + l) x _
          exact mul_le_mul hphi0 hsum_le hsum_nn hcS_nn
      | (m'' + 1) =>
          rw [if_neg (by omega)]
          rw [iteratedCovGrad_zero_of_covGrad_zero (I := I) (M := M) g₀ (ss + 2) ss
            (cometricDoubleTraceField (I := I) g₀ ss)
            (cometricDoubleTraceField_covGrad_eq_zero (I := I) g₀ ss) m'']
          rw [show ((0 : SmoothCcTensor g₀ (ss + 2) (ss + (m'' + 1))).toSection x) =
              (0 : TensorRSSpace (ss + 2) (ss + (m'' + 1)) I x) from by
            rw [SmoothCcTensor.toSection_zero]; rfl]
          rw [riemannianFiberNormSq_zero (I := I) (M := M) g₀ (ss + 2) (ss + (m'' + 1)) x]
          rw [zero_mul]
    refine le_trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hphi)
      (appCcGdiag_nonneg (E := E) m)) ?_
    rw [Finset.sum_ite_eq' (Finset.range (m + 1)) 0]
    rw [if_pos (Finset.mem_range.mpr (by omega))]
    have hinner : (∑ l ∈ Finset.range (m + 1),
        dim ^ (ss + 1) * (CD l * Combinatorics.antidiagonalTupleGrid b l)) ≤
        dim ^ (ss + 1) * CDS m *
          ∑ l ∈ Finset.range (m + 1), Combinatorics.antidiagonalTupleGrid b l := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun l hl => ?_
      have hl_le : l ≤ m := by
        rw [Finset.mem_range] at hl; omega
      have hgrid_nn := Combinatorics.antidiagonalTupleGrid_nonneg b hb l
      have hCDl := hCD_le_CDS hl_le
      have hd : (0 : ℝ) ≤ dim ^ (ss + 1) := by positivity
      have hkey : CD l * Combinatorics.antidiagonalTupleGrid b l ≤
          CDS m * Combinatorics.antidiagonalTupleGrid b l :=
        mul_le_mul_of_nonneg_right hCDl hgrid_nn
      nlinarith [hkey, hd]
    calc appCcGdiag (E := E) m *
          (cS * ∑ l ∈ Finset.range (m + 1),
            dim ^ (ss + 1) * (CD l * Combinatorics.antidiagonalTupleGrid b l))
        ≤ appCcGdiag (E := E) m *
            (cS * (dim ^ (ss + 1) * CDS m *
              ∑ l ∈ Finset.range (m + 1), Combinatorics.antidiagonalTupleGrid b l)) := by
          refine mul_le_mul_of_nonneg_left ?_ (appCcGdiag_nonneg (E := E) m)
          exact mul_le_mul_of_nonneg_left hinner hcS_nn
      _ = (appCcGdiag (E := E) m * cS * dim ^ (ss + 1) * CDS m) *
            ∑ l ∈ Finset.range (m + 1), Combinatorics.antidiagonalTupleGrid b l := by
          ring
  set Ggrid : ℕ → ℝ := fun m => ∑ l ∈ Finset.range (m + 1),
    Combinatorics.antidiagonalTupleGrid b l with hGgrid_def
  have hGgrid_nn : ∀ m, 0 ≤ Ggrid m := fun m => hGg_nn m
  have hGgrid_one : ∀ m, (1 : ℝ) ≤ Ggrid m := fun m => hGg_one m
  have hGgrid_pair : ∀ {m l : ℕ}, m + l ≤ j →
      Ggrid m * Ggrid l ≤ gridSumPairCount (m + 1) (l + 1) * Ggrid j := by
    intro m l hml
    have h := gridSum_mul_gridSum_le b hb (m + 1) (l + 1) (j + 1) (by omega)
    exact h
  have hQ2jets := hQjets 2 c2 hc2_nn hc2
  have hQ4jets := hQjets 4 c4 hc4_nn hc4
  have hPhi2jets : ∀ m : ℕ,
      riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + m) x
        ((iteratedCovGrad (I := I) g₀ 4 2 m
          (cometricDoubleTraceField (I := I) g₀ 2)).toSection x) ≤ c2 * Ggrid m := by
    intro m
    match m with
    | 0 =>
        rw [iteratedCovGrad_zero]
        refine le_trans (hc2 x) ?_
        nlinarith [hGgrid_one 0, hc2_nn]
    | (m' + 1) =>
        rw [iteratedCovGrad_zero_of_covGrad_zero (I := I) (M := M) g₀ 4 2
          (cometricDoubleTraceField (I := I) g₀ 2)
          (cometricDoubleTraceField_covGrad_eq_zero (I := I) g₀ 2) m']
        rw [show ((0 : SmoothCcTensor g₀ 4 (2 + (m' + 1))).toSection x) =
            (0 : TensorRSSpace 4 (2 + (m' + 1)) I x) from by
          rw [SmoothCcTensor.toSection_zero]; rfl]
        rw [riemannianFiberNormSq_zero (I := I) (M := M) g₀ 4 (2 + (m' + 1)) x]
        exact mul_nonneg hc2_nn (hGgrid_nn (m' + 1))
  have hP4jets : ∀ l : ℕ,
      riemannianFiberNormSq (I := I) (M := M) g₀ 6 (4 + l) x
        ((iteratedCovGrad (I := I) g₀ 6 4 l
          (pureDoubleTraceField (I := I) (M := M) g₀ g₁ 4)).toSection x) ≤
      (2 * K4 l + 2 * c4) * Ggrid l := by
    intro l
    have hsec : (iteratedCovGrad (I := I) g₀ 6 4 l
        (pureDoubleTraceField (I := I) (M := M) g₀ g₁ 4)).toSection x =
        (iteratedCovGrad (I := I) g₀ 6 4 l
          (appCcRS (I := I) (M := M) g₀ 6 6 4
            (cometricDoubleTraceField (I := I) g₀ 4)
            (slotInsertEndoCc (I := I) (M := M) g₀ 5
              (gInvDiffRaisedEndoField (I := I) g₀ g₁)))).toSection x +
        (iteratedCovGrad (I := I) g₀ 6 4 l
          (cometricDoubleTraceField (I := I) g₀ 4)).toSection x := by
      rw [show pureDoubleTraceField (I := I) (M := M) g₀ g₁ 4 =
          appCcRS (I := I) (M := M) g₀ 6 6 4
            (cometricDoubleTraceField (I := I) g₀ 4)
            (slotInsertEndoCc (I := I) (M := M) g₀ 5
              (gInvDiffRaisedEndoField (I := I) g₀ g₁)) +
          cometricDoubleTraceField (I := I) g₀ 4 from
        pureDoubleTraceField_cross_split (I := I) (M := M) g₀ g₁ 4]
      rw [iteratedCovGrad_add, SmoothCcTensor.toSection_add]
      rfl
    rw [hsec]
    refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 6 (4 + l) x _ _) ?_
    have h1 := hQ4jets l
    have h2 : riemannianFiberNormSq (I := I) (M := M) g₀ 6 (4 + l) x
        ((iteratedCovGrad (I := I) g₀ 6 4 l
          (cometricDoubleTraceField (I := I) g₀ 4)).toSection x) ≤ c4 * Ggrid l := by
      match l with
      | 0 =>
          rw [iteratedCovGrad_zero]
          refine le_trans (hc4 x) ?_
          nlinarith [hGgrid_one 0, hc4_nn]
      | (l' + 1) =>
          rw [iteratedCovGrad_zero_of_covGrad_zero (I := I) (M := M) g₀ 6 4
            (cometricDoubleTraceField (I := I) g₀ 4)
            (cometricDoubleTraceField_covGrad_eq_zero (I := I) g₀ 4) l']
          rw [show ((0 : SmoothCcTensor g₀ 6 (4 + (l' + 1))).toSection x) =
              (0 : TensorRSSpace 6 (4 + (l' + 1)) I x) from by
            rw [SmoothCcTensor.toSection_zero]; rfl]
          rw [riemannianFiberNormSq_zero (I := I) (M := M) g₀ 6 (4 + (l' + 1)) x]
          exact mul_nonneg hc4_nn (hGgrid_nn (l' + 1))
    rw [hK4val l]
    linarith [h1, h2]
  have hDelta : pairTraceOp (I := I) (M := M) g₀ g₁ - pairTraceOp (I := I) (M := M) g₀ g₀ =
      appCcRS (I := I) (M := M) g₀ 6 4 2
        (appCcRS (I := I) (M := M) g₀ 4 4 2
          (cometricDoubleTraceField (I := I) g₀ 2)
          (slotInsertEndoCc (I := I) (M := M) g₀ 3
            (gInvDiffRaisedEndoField (I := I) g₀ g₁)))
        (pureDoubleTraceField (I := I) (M := M) g₀ g₁ 4) +
      appCcRS (I := I) (M := M) g₀ 6 4 2
        (cometricDoubleTraceField (I := I) g₀ 2)
        (appCcRS (I := I) (M := M) g₀ 6 6 4
          (cometricDoubleTraceField (I := I) g₀ 4)
          (slotInsertEndoCc (I := I) (M := M) g₀ 5
            (gInvDiffRaisedEndoField (I := I) g₀ g₁))) := by
    rw [show pairTraceOp (I := I) (M := M) g₀ g₁ =
        appCcRS (I := I) (M := M) g₀ 6 4 2
          (pureDoubleTraceField (I := I) (M := M) g₀ g₁ 2)
          (pureDoubleTraceField (I := I) (M := M) g₀ g₁ 4) from rfl]
    rw [pureDoubleTraceField_cross_split (I := I) (M := M) g₀ g₁ 2]
    rw [appCcRS_add_left_cc (I := I) (M := M) g₀ 6 4 2]
    conv_lhs =>
      rw [show pureDoubleTraceField (I := I) (M := M) g₀ g₁ 4 =
          appCcRS (I := I) (M := M) g₀ 6 6 4
            (cometricDoubleTraceField (I := I) g₀ 4)
            (slotInsertEndoCc (I := I) (M := M) g₀ 5
              (gInvDiffRaisedEndoField (I := I) g₀ g₁)) +
          cometricDoubleTraceField (I := I) g₀ 4 from
        pureDoubleTraceField_cross_split (I := I) (M := M) g₀ g₁ 4]
    rw [appCcRS_add_right (I := I) (M := M) g₀ 6 4 2
      (cometricDoubleTraceField (I := I) g₀ 2)]
    rw [pairTraceOp_self_eq (I := I) (M := M) g₀]
    rw [phiDtPair]
    conv_rhs =>
      rw [show pureDoubleTraceField (I := I) (M := M) g₀ g₁ 4 =
          appCcRS (I := I) (M := M) g₀ 6 6 4
            (cometricDoubleTraceField (I := I) g₀ 4)
            (slotInsertEndoCc (I := I) (M := M) g₀ 5
              (gInvDiffRaisedEndoField (I := I) g₀ g₁)) +
          cometricDoubleTraceField (I := I) g₀ 4 from
        pureDoubleTraceField_cross_split (I := I) (M := M) g₀ g₁ 4]
    rw [appCcRS_add_right (I := I) (M := M) g₀ 6 4 2
      (appCcRS (I := I) (M := M) g₀ 4 4 2
        (cometricDoubleTraceField (I := I) g₀ 2)
        (slotInsertEndoCc (I := I) (M := M) g₀ 3
          (gInvDiffRaisedEndoField (I := I) g₀ g₁)))]
    abel
  rw [hDelta]
  have hsplitsec : (iteratedCovGrad (I := I) g₀ 6 2 j
      (appCcRS (I := I) (M := M) g₀ 6 4 2
        (appCcRS (I := I) (M := M) g₀ 4 4 2
          (cometricDoubleTraceField (I := I) g₀ 2)
          (slotInsertEndoCc (I := I) (M := M) g₀ 3
            (gInvDiffRaisedEndoField (I := I) g₀ g₁)))
        (pureDoubleTraceField (I := I) (M := M) g₀ g₁ 4) +
      appCcRS (I := I) (M := M) g₀ 6 4 2
        (cometricDoubleTraceField (I := I) g₀ 2)
        (appCcRS (I := I) (M := M) g₀ 6 6 4
          (cometricDoubleTraceField (I := I) g₀ 4)
          (slotInsertEndoCc (I := I) (M := M) g₀ 5
            (gInvDiffRaisedEndoField (I := I) g₀ g₁))))).toSection x =
      (iteratedCovGrad (I := I) g₀ 6 2 j
        (appCcRS (I := I) (M := M) g₀ 6 4 2
          (appCcRS (I := I) (M := M) g₀ 4 4 2
            (cometricDoubleTraceField (I := I) g₀ 2)
            (slotInsertEndoCc (I := I) (M := M) g₀ 3
              (gInvDiffRaisedEndoField (I := I) g₀ g₁)))
          (pureDoubleTraceField (I := I) (M := M) g₀ g₁ 4))).toSection x +
      (iteratedCovGrad (I := I) g₀ 6 2 j
        (appCcRS (I := I) (M := M) g₀ 6 4 2
          (cometricDoubleTraceField (I := I) g₀ 2)
          (appCcRS (I := I) (M := M) g₀ 6 6 4
            (cometricDoubleTraceField (I := I) g₀ 4)
            (slotInsertEndoCc (I := I) (M := M) g₀ 5
              (gInvDiffRaisedEndoField (I := I) g₀ g₁))))).toSection x := by
    rw [iteratedCovGrad_add, SmoothCcTensor.toSection_add]
    rfl
  rw [hsplitsec]
  refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 6 (2 + j) x _ _) ?_
  have hterm1 : riemannianFiberNormSq (I := I) (M := M) g₀ 6 (2 + j) x
      ((iteratedCovGrad (I := I) g₀ 6 2 j
        (appCcRS (I := I) (M := M) g₀ 6 4 2
          (appCcRS (I := I) (M := M) g₀ 4 4 2
            (cometricDoubleTraceField (I := I) g₀ 2)
            (slotInsertEndoCc (I := I) (M := M) g₀ 3
              (gInvDiffRaisedEndoField (I := I) g₀ g₁)))
          (pureDoubleTraceField (I := I) (M := M) g₀ g₁ 4))).toSection x) ≤
      (appCcGdiag (E := E) j *
        ∑ m ∈ Finset.range (j + 1), ∑ l ∈ Finset.range (j + 1 - m),
          K2 m * (2 * K4 l + 2 * c4) * gridSumPairCount (m + 1) (l + 1)) * Ggrid j := by
    refine le_trans (rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le
      (I := I) (M := M) g₀ j 6 4 2
      (appCcRS (I := I) (M := M) g₀ 4 4 2
        (cometricDoubleTraceField (I := I) g₀ 2)
        (slotInsertEndoCc (I := I) (M := M) g₀ 3
          (gInvDiffRaisedEndoField (I := I) g₀ g₁)))
      (pureDoubleTraceField (I := I) (M := M) g₀ g₁ 4) x) ?_
    have hcell : ∀ m ∈ Finset.range (j + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + m) x
            ((iteratedCovGrad (I := I) g₀ 4 2 m
              (appCcRS (I := I) (M := M) g₀ 4 4 2
                (cometricDoubleTraceField (I := I) g₀ 2)
                (slotInsertEndoCc (I := I) (M := M) g₀ 3
                  (gInvDiffRaisedEndoField (I := I) g₀ g₁)))).toSection x) *
          ∑ l ∈ Finset.range (j + 1 - m),
            riemannianFiberNormSq (I := I) (M := M) g₀ 6 (4 + l) x
              ((iteratedCovGrad (I := I) g₀ 6 4 l
                (pureDoubleTraceField (I := I) (M := M) g₀ g₁ 4)).toSection x) ≤
        (∑ l ∈ Finset.range (j + 1 - m),
          K2 m * (2 * K4 l + 2 * c4) * gridSumPairCount (m + 1) (l + 1)) * Ggrid j := by
      intro m hm
      have hm_le : m ≤ j := by
        rw [Finset.mem_range] at hm; omega
      have hA1 : riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + m) x
          ((iteratedCovGrad (I := I) g₀ 4 2 m
            (appCcRS (I := I) (M := M) g₀ 4 4 2
              (cometricDoubleTraceField (I := I) g₀ 2)
              (slotInsertEndoCc (I := I) (M := M) g₀ 3
                (gInvDiffRaisedEndoField (I := I) g₀ g₁)))).toSection x) ≤
          K2 m * Ggrid m := by
        rw [hK2val m]
        exact hQ2jets m
      have hA2 : (∑ l ∈ Finset.range (j + 1 - m),
          riemannianFiberNormSq (I := I) (M := M) g₀ 6 (4 + l) x
            ((iteratedCovGrad (I := I) g₀ 6 4 l
              (pureDoubleTraceField (I := I) (M := M) g₀ g₁ 4)).toSection x)) ≤
          ∑ l ∈ Finset.range (j + 1 - m), (2 * K4 l + 2 * c4) * Ggrid l :=
        Finset.sum_le_sum fun l _ => hP4jets l
      have hnn1 : 0 ≤ ∑ l ∈ Finset.range (j + 1 - m),
          riemannianFiberNormSq (I := I) (M := M) g₀ 6 (4 + l) x
            ((iteratedCovGrad (I := I) g₀ 6 4 l
              (pureDoubleTraceField (I := I) (M := M) g₀ g₁ 4)).toSection x) :=
        Finset.sum_nonneg fun l _ =>
          riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 6 (4 + l) x _
      have hK2G_nn : 0 ≤ K2 m * Ggrid m := mul_nonneg (hK2_nn m) (hGgrid_nn m)
      calc riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + m) x
            ((iteratedCovGrad (I := I) g₀ 4 2 m
              (appCcRS (I := I) (M := M) g₀ 4 4 2
                (cometricDoubleTraceField (I := I) g₀ 2)
                (slotInsertEndoCc (I := I) (M := M) g₀ 3
                  (gInvDiffRaisedEndoField (I := I) g₀ g₁)))).toSection x) *
          ∑ l ∈ Finset.range (j + 1 - m),
            riemannianFiberNormSq (I := I) (M := M) g₀ 6 (4 + l) x
              ((iteratedCovGrad (I := I) g₀ 6 4 l
                (pureDoubleTraceField (I := I) (M := M) g₀ g₁ 4)).toSection x)
          ≤ (K2 m * Ggrid m) *
            ∑ l ∈ Finset.range (j + 1 - m), (2 * K4 l + 2 * c4) * Ggrid l :=
            mul_le_mul hA1 hA2 hnn1 hK2G_nn
        _ = ∑ l ∈ Finset.range (j + 1 - m),
              (K2 m * (2 * K4 l + 2 * c4)) * (Ggrid m * Ggrid l) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun l _ => ?_
            ring
        _ ≤ ∑ l ∈ Finset.range (j + 1 - m),
              (K2 m * (2 * K4 l + 2 * c4)) * (gridSumPairCount (m + 1) (l + 1) * Ggrid j) := by
            refine Finset.sum_le_sum fun l hl => ?_
            refine mul_le_mul_of_nonneg_left ?_ ?_
            · refine hGgrid_pair ?_
              rw [Finset.mem_range] at hl
              omega
            · have := hK2_nn m
              have := hK4_nn l
              positivity
        _ = (∑ l ∈ Finset.range (j + 1 - m),
              K2 m * (2 * K4 l + 2 * c4) * gridSumPairCount (m + 1) (l + 1)) * Ggrid j := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun l _ => ?_
            ring
    calc appCcGdiag (E := E) j *
          ∑ m ∈ Finset.range (j + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + m) x
                ((iteratedCovGrad (I := I) g₀ 4 2 m
                  (appCcRS (I := I) (M := M) g₀ 4 4 2
                    (cometricDoubleTraceField (I := I) g₀ 2)
                    (slotInsertEndoCc (I := I) (M := M) g₀ 3
                      (gInvDiffRaisedEndoField (I := I) g₀ g₁)))).toSection x) *
              ∑ l ∈ Finset.range (j + 1 - m),
                riemannianFiberNormSq (I := I) (M := M) g₀ 6 (4 + l) x
                  ((iteratedCovGrad (I := I) g₀ 6 4 l
                    (pureDoubleTraceField (I := I) (M := M) g₀ g₁ 4)).toSection x)
        ≤ appCcGdiag (E := E) j *
            ∑ m ∈ Finset.range (j + 1),
              (∑ l ∈ Finset.range (j + 1 - m),
                K2 m * (2 * K4 l + 2 * c4) * gridSumPairCount (m + 1) (l + 1)) * Ggrid j :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum hcell) (appCcGdiag_nonneg (E := E) j)
      _ = (appCcGdiag (E := E) j *
            ∑ m ∈ Finset.range (j + 1), ∑ l ∈ Finset.range (j + 1 - m),
              K2 m * (2 * K4 l + 2 * c4) * gridSumPairCount (m + 1) (l + 1)) * Ggrid j := by
          rw [← Finset.sum_mul]
          ring
  have hterm2 : riemannianFiberNormSq (I := I) (M := M) g₀ 6 (2 + j) x
      ((iteratedCovGrad (I := I) g₀ 6 2 j
        (appCcRS (I := I) (M := M) g₀ 6 4 2
          (cometricDoubleTraceField (I := I) g₀ 2)
          (appCcRS (I := I) (M := M) g₀ 6 6 4
            (cometricDoubleTraceField (I := I) g₀ 4)
            (slotInsertEndoCc (I := I) (M := M) g₀ 5
              (gInvDiffRaisedEndoField (I := I) g₀ g₁))))).toSection x) ≤
      (appCcGdiag (E := E) j *
        ∑ m ∈ Finset.range (j + 1), ∑ l ∈ Finset.range (j + 1 - m),
          c2 * K4 l * gridSumPairCount (m + 1) (l + 1)) * Ggrid j := by
    refine le_trans (rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le
      (I := I) (M := M) g₀ j 6 4 2
      (cometricDoubleTraceField (I := I) g₀ 2)
      (appCcRS (I := I) (M := M) g₀ 6 6 4
        (cometricDoubleTraceField (I := I) g₀ 4)
        (slotInsertEndoCc (I := I) (M := M) g₀ 5
          (gInvDiffRaisedEndoField (I := I) g₀ g₁))) x) ?_
    have hcell : ∀ m ∈ Finset.range (j + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + m) x
            ((iteratedCovGrad (I := I) g₀ 4 2 m
              (cometricDoubleTraceField (I := I) g₀ 2)).toSection x) *
          ∑ l ∈ Finset.range (j + 1 - m),
            riemannianFiberNormSq (I := I) (M := M) g₀ 6 (4 + l) x
              ((iteratedCovGrad (I := I) g₀ 6 4 l
                (appCcRS (I := I) (M := M) g₀ 6 6 4
                  (cometricDoubleTraceField (I := I) g₀ 4)
                  (slotInsertEndoCc (I := I) (M := M) g₀ 5
                    (gInvDiffRaisedEndoField (I := I) g₀ g₁)))).toSection x) ≤
        (∑ l ∈ Finset.range (j + 1 - m),
          c2 * K4 l * gridSumPairCount (m + 1) (l + 1)) * Ggrid j := by
      intro m hm
      have hm_le : m ≤ j := by
        rw [Finset.mem_range] at hm; omega
      have hA1 := hPhi2jets m
      have hA2 : (∑ l ∈ Finset.range (j + 1 - m),
          riemannianFiberNormSq (I := I) (M := M) g₀ 6 (4 + l) x
            ((iteratedCovGrad (I := I) g₀ 6 4 l
              (appCcRS (I := I) (M := M) g₀ 6 6 4
                (cometricDoubleTraceField (I := I) g₀ 4)
                (slotInsertEndoCc (I := I) (M := M) g₀ 5
                  (gInvDiffRaisedEndoField (I := I) g₀ g₁)))).toSection x)) ≤
          ∑ l ∈ Finset.range (j + 1 - m), K4 l * Ggrid l := by
        refine Finset.sum_le_sum fun l _ => ?_
        rw [hK4val l]
        exact hQ4jets l
      have hnn1 : 0 ≤ ∑ l ∈ Finset.range (j + 1 - m),
          riemannianFiberNormSq (I := I) (M := M) g₀ 6 (4 + l) x
            ((iteratedCovGrad (I := I) g₀ 6 4 l
              (appCcRS (I := I) (M := M) g₀ 6 6 4
                (cometricDoubleTraceField (I := I) g₀ 4)
                (slotInsertEndoCc (I := I) (M := M) g₀ 5
                  (gInvDiffRaisedEndoField (I := I) g₀ g₁)))).toSection x) :=
        Finset.sum_nonneg fun l _ =>
          riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 6 (4 + l) x _
      have hc2G_nn : 0 ≤ c2 * Ggrid m := mul_nonneg hc2_nn (hGgrid_nn m)
      calc riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + m) x
            ((iteratedCovGrad (I := I) g₀ 4 2 m
              (cometricDoubleTraceField (I := I) g₀ 2)).toSection x) *
          ∑ l ∈ Finset.range (j + 1 - m),
            riemannianFiberNormSq (I := I) (M := M) g₀ 6 (4 + l) x
              ((iteratedCovGrad (I := I) g₀ 6 4 l
                (appCcRS (I := I) (M := M) g₀ 6 6 4
                  (cometricDoubleTraceField (I := I) g₀ 4)
                  (slotInsertEndoCc (I := I) (M := M) g₀ 5
                    (gInvDiffRaisedEndoField (I := I) g₀ g₁)))).toSection x)
          ≤ (c2 * Ggrid m) * ∑ l ∈ Finset.range (j + 1 - m), K4 l * Ggrid l :=
            mul_le_mul hA1 hA2 hnn1 hc2G_nn
        _ = ∑ l ∈ Finset.range (j + 1 - m), (c2 * K4 l) * (Ggrid m * Ggrid l) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun l _ => ?_
            ring
        _ ≤ ∑ l ∈ Finset.range (j + 1 - m),
              (c2 * K4 l) * (gridSumPairCount (m + 1) (l + 1) * Ggrid j) := by
            refine Finset.sum_le_sum fun l hl => ?_
            refine mul_le_mul_of_nonneg_left ?_ ?_
            · refine hGgrid_pair ?_
              rw [Finset.mem_range] at hl
              omega
            · have := hK4_nn l
              positivity
        _ = (∑ l ∈ Finset.range (j + 1 - m),
              c2 * K4 l * gridSumPairCount (m + 1) (l + 1)) * Ggrid j := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun l _ => ?_
            ring
    calc appCcGdiag (E := E) j *
          ∑ m ∈ Finset.range (j + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 4 (2 + m) x
                ((iteratedCovGrad (I := I) g₀ 4 2 m
                  (cometricDoubleTraceField (I := I) g₀ 2)).toSection x) *
              ∑ l ∈ Finset.range (j + 1 - m),
                riemannianFiberNormSq (I := I) (M := M) g₀ 6 (4 + l) x
                  ((iteratedCovGrad (I := I) g₀ 6 4 l
                    (appCcRS (I := I) (M := M) g₀ 6 6 4
                      (cometricDoubleTraceField (I := I) g₀ 4)
                      (slotInsertEndoCc (I := I) (M := M) g₀ 5
                        (gInvDiffRaisedEndoField (I := I) g₀ g₁)))).toSection x)
        ≤ appCcGdiag (E := E) j *
            ∑ m ∈ Finset.range (j + 1),
              (∑ l ∈ Finset.range (j + 1 - m),
                c2 * K4 l * gridSumPairCount (m + 1) (l + 1)) * Ggrid j :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum hcell) (appCcGdiag_nonneg (E := E) j)
      _ = (appCcGdiag (E := E) j *
            ∑ m ∈ Finset.range (j + 1), ∑ l ∈ Finset.range (j + 1 - m),
              c2 * K4 l * gridSumPairCount (m + 1) (l + 1)) * Ggrid j := by
          rw [← Finset.sum_mul]
          ring
  calc 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 6 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 6 2 j
          (appCcRS (I := I) (M := M) g₀ 6 4 2
            (appCcRS (I := I) (M := M) g₀ 4 4 2
              (cometricDoubleTraceField (I := I) g₀ 2)
              (slotInsertEndoCc (I := I) (M := M) g₀ 3
                (gInvDiffRaisedEndoField (I := I) g₀ g₁)))
            (pureDoubleTraceField (I := I) (M := M) g₀ g₁ 4))).toSection x) +
      2 * riemannianFiberNormSq (I := I) (M := M) g₀ 6 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 6 2 j
          (appCcRS (I := I) (M := M) g₀ 6 4 2
            (cometricDoubleTraceField (I := I) g₀ 2)
            (appCcRS (I := I) (M := M) g₀ 6 6 4
              (cometricDoubleTraceField (I := I) g₀ 4)
              (slotInsertEndoCc (I := I) (M := M) g₀ 5
                (gInvDiffRaisedEndoField (I := I) g₀ g₁))))).toSection x)
      ≤ 2 * ((appCcGdiag (E := E) j *
          ∑ m ∈ Finset.range (j + 1), ∑ l ∈ Finset.range (j + 1 - m),
            K2 m * (2 * K4 l + 2 * c4) * gridSumPairCount (m + 1) (l + 1)) * Ggrid j) +
        2 * ((appCcGdiag (E := E) j *
          ∑ m ∈ Finset.range (j + 1), ∑ l ∈ Finset.range (j + 1 - m),
            c2 * K4 l * gridSumPairCount (m + 1) (l + 1)) * Ggrid j) := by
        linarith [hterm1, hterm2]
    _ = (2 * (appCcGdiag (E := E) j *
          ∑ m ∈ Finset.range (j + 1), ∑ l ∈ Finset.range (j + 1 - m),
            K2 m * (2 * K4 l + 2 * c4) * gridSumPairCount (m + 1) (l + 1)) +
        2 * (appCcGdiag (E := E) j *
          ∑ m ∈ Finset.range (j + 1), ∑ l ∈ Finset.range (j + 1 - m),
            c2 * K4 l * gridSumPairCount (m + 1) (l + 1))) * Ggrid j := by
        ring

set_option linter.unusedSectionVars false in
private lemma rfns_iteratedCovGrad_WBform_le (g₀ : SmoothRiemannianMetric I M)
    (X : SmoothCcTensor g₀ 0 4) (l : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + l) x
        ((iteratedCovGrad (I := I) g₀ 2 6 l
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2 X))).toSection x) ≤
      ((Module.finrank ℝ E : ℝ) * (Module.finrank ℝ E : ℝ)) *
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
          ((iteratedCovGrad (I := I) g₀ 0 4 l X).toSection x) := by
  have heq1 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + l) x
      ((iteratedCovGrad (I := I) g₀ 2 6 l
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2 X))).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + l) x
        ((iteratedCovGrad (I := I) g₀ 2 6 l
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2 X)).toSection x) :=
    rfns_iteratedCovGrad_rs_eq_of_section_domDomCongr (I := I) (M := M) g₀ 2 6 sigmaE0
      (slotExtendIter (I := I) (M := M) g₀ 0 4 2 X)
      (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2 X))
      (fun y d => by
        rw [rsDomDomCongrSection_toSection, toModel_rsDomDomCongr_apply]) l x
  rw [heq1]
  have hfr : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
  calc riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + l) x
        ((iteratedCovGrad (I := I) g₀ 2 6 l
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2 X)).toSection x)
      ≤ (Module.finrank ℝ E : ℝ) *
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (5 + l) x
          ((iteratedCovGrad (I := I) g₀ 1 5 l
            (slotExtend (I := I) (M := M) g₀ 0 4 X)).toSection x) :=
        rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 1 5
          (slotExtend (I := I) (M := M) g₀ 0 4 X) l x
    _ ≤ (Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) *
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
          ((iteratedCovGrad (I := I) g₀ 0 4 l X).toSection x)) :=
        mul_le_mul_of_nonneg_left
          (rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 0 4 X l x) hfr
    _ = ((Module.finrank ℝ E : ℝ) * (Module.finrank ℝ E : ℝ)) *
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
          ((iteratedCovGrad (I := I) g₀ 0 4 l X).toSection x) := by ring

set_option linter.unusedVariables false in
set_option maxHeartbeats 12800000 in

set_option linter.unusedVariables false in
set_option maxHeartbeats 12800000 in
theorem rfns_iteratedCovGrad_riemannCoeff_metricFactorTelescope_traceConversion_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                ricciArmOrder0RiemannMixedCoeff (I := I) (M := M) g₀ g₁)).toSection x) ≤
          C i * ∑ j ∈ Finset.range (i + 1),
            (∑ n ∈ Finset.range (j + 1),
              ∑ e ∈ Finset.Nat.antidiagonalTuple n j,
                ∏ m : Fin n,
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T).toSection x)) *
            ∑ l ∈ Finset.range (i + 1 - j),
              (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
                  ((iteratedCovGrad (I := I) g₀ 0 4 l
                    (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁)).toSection x) +
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
                  ((iteratedCovGrad (I := I) g₀ 0 4 l
                    (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁ -
                      riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁)).toSection x)) := by
  classical
  obtain ⟨CΔ, hCΔ_nn, hCΔ⟩ := exists_rfns_iteratedCovGrad_pairTraceOp_diff_grid
    (I := I) (M := M) g₀ hδ₀
  have hcB : ∀ j : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ (6 + j) (2 + j) x
        ((slotExtendIter (I := I) (M := M) g₀ 6 2 j
          (phiDtPair (I := I) (M := M) g₀)).toSection x) ≤ c := fun j =>
    exists_bound_riemannianFiberNormSq_smoothCcTensor (I := I) (M := M) g₀ (6 + j) (2 + j)
      (slotExtendIter (I := I) (M := M) g₀ 6 2 j (phiDtPair (I := I) (M := M) g₀))
  choose cB hcB0 hcBb using hcB
  set dim : ℝ := (Module.finrank ℝ E : ℝ) with hdim_def
  have hdim_nn : 0 ≤ dim := Nat.cast_nonneg _
  refine ⟨fun i => 8 * (cB i * (dim * dim)) +
      8 * (appCcGdiag (E := E) i * (∑ j ∈ Finset.range (i + 1), CΔ j) * (dim * dim) * 2),
    fun i => by
      have h1 := hcB0 i
      have h2 : 0 ≤ ∑ j ∈ Finset.range (i + 1), CΔ j :=
        Finset.sum_nonneg fun j _ => hCΔ_nn j
      have h3 := appCcGdiag_nonneg (E := E) i
      positivity, ?_⟩
  intro g₁ T htie δ hδ_le hδ0 hbound i x
  set b : ℕ → ℝ := fun j' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j') x
    ((iteratedCovGrad (I := I) g₀ 0 2 j' T).toSection x) with hb_def
  have hb : ∀ j', 0 ≤ b j' :=
    fun j' => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + j') x _
  set L01 : SmoothCcTensor g₀ 0 4 := riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁ with hL01_def
  set Ldiff : SmoothCcTensor g₀ 0 4 :=
    riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁ -
      riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁ with hLdiff_def
  set Lterm : ℕ → ℝ := fun l =>
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 4 l L01).toSection x) +
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 4 l Ldiff).toSection x) with hLterm_def
  have hLterm_nn : ∀ l, 0 ≤ Lterm l := by
    intro l
    rw [hLterm_def]
    exact add_nonneg (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (4 + l) x _)
      (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (4 + l) x _)
  set RHS : ℝ := ∑ j ∈ Finset.range (i + 1),
    Combinatorics.antidiagonalTupleGrid b j * ∑ l ∈ Finset.range (i + 1 - j), Lterm l
    with hRHS_def
  have hRHS_cell_nn : ∀ j, 0 ≤ Combinatorics.antidiagonalTupleGrid b j *
      ∑ l ∈ Finset.range (i + 1 - j), Lterm l := fun j =>
    mul_nonneg (Combinatorics.antidiagonalTupleGrid_nonneg b hb j)
      (Finset.sum_nonneg fun l _ => hLterm_nn l)
  have hRHS_nn : 0 ≤ RHS := by
    rw [hRHS_def]
    exact Finset.sum_nonneg fun j _ => hRHS_cell_nn j
  have hgoal_eq : (∑ j ∈ Finset.range (i + 1),
      (∑ n ∈ Finset.range (j + 1),
        ∑ e ∈ Finset.Nat.antidiagonalTuple n j,
          ∏ m : Fin n, b (e m)) *
      ∑ l ∈ Finset.range (i + 1 - j),
        (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 4 l L01).toSection x) +
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 4 l Ldiff).toSection x))) = RHS := rfl
  rw [hgoal_eq]
  clear_value RHS
  have hdecomp : ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
      ricciArmOrder0RiemannMixedCoeff (I := I) (M := M) g₀ g₁ =
      (2 : ℝ) • (appCcRS (I := I) (M := M) g₀ 2 6 2
          (pairTraceOp (I := I) (M := M) g₀ g₁ - pairTraceOp (I := I) (M := M) g₀ g₀)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁))) +
        appCcRS (I := I) (M := M) g₀ 2 6 2 (pairTraceOp (I := I) (M := M) g₀ g₀)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2 Ldiff))) := by
    rw [riemannCoeff_eq_pairTrace_L11 (I := I) (M := M) g₀ g₁]
    rw [riemannMixedCoeff_eq_pairTrace_L01 (I := I) (M := M) g₀ g₁]
    rw [← smul_sub]
    congr 1
    rw [appCcRS_sub_left_cc (I := I) (M := M) g₀ 2 6 2]
    have hWsub : rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2 Ldiff) =
        rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁)) -
        rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁)) := by
      rw [hLdiff_def]
      rw [show slotExtendIter (I := I) (M := M) g₀ 0 4 2
          (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁ -
            riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁) =
          slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁) -
          slotExtendIter (I := I) (M := M) g₀ 0 4 2
            (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁) from by
        rw [show ∀ Y : SmoothCcTensor g₀ 0 4,
            slotExtendIter (I := I) (M := M) g₀ 0 4 2 Y =
            slotExtend (I := I) (M := M) g₀ 1 5
              (slotExtend (I := I) (M := M) g₀ 0 4 Y) from fun Y => rfl]
        rw [slotExtend_sub_cc (I := I) (M := M) g₀ 0 4]
        rw [slotExtend_sub_cc (I := I) (M := M) g₀ 1 5]
        rfl]
      rw [rsDomDomCongrSection_sub_cc (I := I) (M := M) g₀ 2 6 sigmaE0]
    rw [hWsub]
    rw [appCcRS_sub_right_cc (I := I) (M := M) g₀ 2 6 2 (pairTraceOp (I := I) (M := M) g₀ g₀)]
    abel
  rw [hdecomp]
  have hsmulsec : (iteratedCovGrad (I := I) g₀ 2 2 i
      ((2 : ℝ) • (appCcRS (I := I) (M := M) g₀ 2 6 2
          (pairTraceOp (I := I) (M := M) g₀ g₁ - pairTraceOp (I := I) (M := M) g₀ g₀)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁))) +
        appCcRS (I := I) (M := M) g₀ 2 6 2 (pairTraceOp (I := I) (M := M) g₀ g₀)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2 Ldiff))))).toSection x =
      (2 : ℝ) • ((iteratedCovGrad (I := I) g₀ 2 2 i
        (appCcRS (I := I) (M := M) g₀ 2 6 2
          (pairTraceOp (I := I) (M := M) g₀ g₁ - pairTraceOp (I := I) (M := M) g₀ g₀)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁))))).toSection x +
      (iteratedCovGrad (I := I) g₀ 2 2 i
        (appCcRS (I := I) (M := M) g₀ 2 6 2 (pairTraceOp (I := I) (M := M) g₀ g₀)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2 Ldiff)))).toSection x) := by
    rw [iteratedCovGrad_smul_b, iteratedCovGrad_add]
    rw [SmoothCcTensor.toSection_smul, SmoothCcTensor.toSection_add]
    rfl
  rw [hsmulsec, rfns_smul_b]
  have hT2 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
      ((iteratedCovGrad (I := I) g₀ 2 2 i
        (appCcRS (I := I) (M := M) g₀ 2 6 2 (pairTraceOp (I := I) (M := M) g₀ g₀)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2 Ldiff)))).toSection x) ≤
      (cB i * (dim * dim)) * RHS := by
    rw [pairTraceOp_self_eq (I := I) (M := M) g₀]
    rw [iteratedCovGrad_appCcRS_parallel (I := I) (M := M) g₀ 2 6 2
      (phiDtPair (I := I) (M := M) g₀) (phiDtPair_covGrad_zero (I := I) (M := M) g₀) _ i]
    have hcomp : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
        ((appCcRS (I := I) (M := M) g₀ 2 (6 + i) (2 + i)
          (slotExtendIter (I := I) (M := M) g₀ 6 2 i (phiDtPair (I := I) (M := M) g₀))
          (iteratedCovGrad (I := I) g₀ 2 6 i
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2 Ldiff)))).toSection x) ≤
        riemannianFiberNormSq (I := I) (M := M) g₀ (6 + i) (2 + i) x
            ((slotExtendIter (I := I) (M := M) g₀ 6 2 i
              (phiDtPair (I := I) (M := M) g₀)).toSection x) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 6 i
              (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
                (slotExtendIter (I := I) (M := M) g₀ 0 4 2 Ldiff))).toSection x) := by
      rw [appCcRS_toSection]
      exact riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g₀ 2 (6 + i) (2 + i) x _ _
    refine le_trans hcomp ?_
    have h1 := hcBb i x
    have h2 := rfns_iteratedCovGrad_WBform_le (I := I) (M := M) g₀ Ldiff i x
    rw [← hdim_def] at h2
    have hLd_le_RHS : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
        ((iteratedCovGrad (I := I) g₀ 0 4 i Ldiff).toSection x) ≤ RHS := by
      rw [hRHS_def]
      have hcell0 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
          ((iteratedCovGrad (I := I) g₀ 0 4 i Ldiff).toSection x) ≤
          Combinatorics.antidiagonalTupleGrid b 0 * ∑ l ∈ Finset.range (i + 1 - 0), Lterm l := by
        rw [Combinatorics.antidiagonalTupleGrid_zero, one_mul]
        have hLi : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 4 i Ldiff).toSection x) ≤ Lterm i := by
          rw [hLterm_def]
          have := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (4 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 4 i L01).toSection x)
          linarith
        refine le_trans hLi ?_
        exact Finset.single_le_sum (f := fun l => Lterm l) (fun l _ => hLterm_nn l)
          (Finset.mem_range.mpr (by omega))
      refine le_trans hcell0 ?_
      exact Finset.single_le_sum
        (f := fun j => Combinatorics.antidiagonalTupleGrid b j *
          ∑ l ∈ Finset.range (i + 1 - j), Lterm l)
        (fun j _ => hRHS_cell_nn j) (Finset.mem_range.mpr (by omega))
    have hWB_nn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (6 + i) x
      ((iteratedCovGrad (I := I) g₀ 2 6 i
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
          (slotExtendIter (I := I) (M := M) g₀ 0 4 2 Ldiff))).toSection x)
    have hLd_nn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (4 + i) x
      ((iteratedCovGrad (I := I) g₀ 0 4 i Ldiff).toSection x)
    calc riemannianFiberNormSq (I := I) (M := M) g₀ (6 + i) (2 + i) x
          ((slotExtendIter (I := I) (M := M) g₀ 6 2 i
            (phiDtPair (I := I) (M := M) g₀)).toSection x) *
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + i) x
          ((iteratedCovGrad (I := I) g₀ 2 6 i
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2 Ldiff))).toSection x)
        ≤ cB i * ((dim * dim) *
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
              ((iteratedCovGrad (I := I) g₀ 0 4 i Ldiff).toSection x)) := by
          have hdd : (0 : ℝ) ≤ dim * dim := by positivity
          nlinarith [mul_le_mul h1 h2 hWB_nn (hcB0 i), hcB0 i]
      _ ≤ cB i * ((dim * dim) * RHS) := by
          have hdd : (0 : ℝ) ≤ dim * dim := by positivity
          have hmono := mul_le_mul_of_nonneg_left hLd_le_RHS
            (mul_nonneg (hcB0 i) hdd)
          nlinarith [hmono]
      _ = (cB i * (dim * dim)) * RHS := by ring
  have hT1 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
      ((iteratedCovGrad (I := I) g₀ 2 2 i
        (appCcRS (I := I) (M := M) g₀ 2 6 2
          (pairTraceOp (I := I) (M := M) g₀ g₁ - pairTraceOp (I := I) (M := M) g₀ g₀)
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
            (slotExtendIter (I := I) (M := M) g₀ 0 4 2
              (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁))))).toSection x) ≤
      (appCcGdiag (E := E) i * (∑ j ∈ Finset.range (i + 1), CΔ j) * (dim * dim) * 2) * RHS := by
    refine le_trans (rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le
      (I := I) (M := M) g₀ i 2 6 2
      (pairTraceOp (I := I) (M := M) g₀ g₁ - pairTraceOp (I := I) (M := M) g₀ g₀)
      (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
        (slotExtendIter (I := I) (M := M) g₀ 0 4 2
          (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁))) x) ?_
    have hL11 : ∀ l : ℕ, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 4 l
          (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁)).toSection x) ≤ 2 * Lterm l := by
      intro l
      have hsec : (iteratedCovGrad (I := I) g₀ 0 4 l
          (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁)).toSection x =
          (iteratedCovGrad (I := I) g₀ 0 4 l L01).toSection x +
          (iteratedCovGrad (I := I) g₀ 0 4 l Ldiff).toSection x := by
        rw [show riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁ = L01 + Ldiff from by
          rw [hL01_def, hLdiff_def]
          abel]
        rw [iteratedCovGrad_add, SmoothCcTensor.toSection_add]
        rfl
      rw [hsec]
      refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 (4 + l) x _ _) ?_
      rw [hLterm_def]
      ring_nf
      rfl
    have hcell : ∀ j ∈ Finset.range (i + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 6 (2 + j) x
            ((iteratedCovGrad (I := I) g₀ 6 2 j
              (pairTraceOp (I := I) (M := M) g₀ g₁ -
                pairTraceOp (I := I) (M := M) g₀ g₀)).toSection x) *
          ∑ l ∈ Finset.range (i + 1 - j),
            riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + l) x
              ((iteratedCovGrad (I := I) g₀ 2 6 l
                (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
                  (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                    (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁)))).toSection x) ≤
        (CΔ j * (dim * dim) * 2) * RHS := by
      intro j hj
      have hj_le : j ≤ i := by
        rw [Finset.mem_range] at hj
        omega
      have hA1 := hCΔ g₁ T htie hδ_le hδ0 hbound j x
      have hA2 : (∑ l ∈ Finset.range (i + 1 - j),
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + l) x
            ((iteratedCovGrad (I := I) g₀ 2 6 l
              (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
                (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                  (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁)))).toSection x)) ≤
          ∑ l ∈ Finset.range (i + 1 - j), (dim * dim) * (2 * Lterm l) := by
        refine Finset.sum_le_sum fun l _ => ?_
        refine le_trans (rfns_iteratedCovGrad_WBform_le (I := I) (M := M) g₀
          (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁) l x) ?_
        exact mul_le_mul_of_nonneg_left (hL11 l) (by positivity)
      have hA1_nn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 6 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 6 2 j
          (pairTraceOp (I := I) (M := M) g₀ g₁ -
            pairTraceOp (I := I) (M := M) g₀ g₀)).toSection x)
      have hA2_nn : 0 ≤ ∑ l ∈ Finset.range (i + 1 - j),
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + l) x
            ((iteratedCovGrad (I := I) g₀ 2 6 l
              (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
                (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                  (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁)))).toSection x) :=
        Finset.sum_nonneg fun l _ =>
          riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (6 + l) x _
      have hgrid_nn : 0 ≤ CΔ j * ∑ l' ∈ Finset.range (j + 1),
          Combinatorics.antidiagonalTupleGrid b l' :=
        mul_nonneg (hCΔ_nn j) (Finset.sum_nonneg fun l' _ =>
          Combinatorics.antidiagonalTupleGrid_nonneg b hb l')
      have hkey : (CΔ j * ∑ l' ∈ Finset.range (j + 1),
          Combinatorics.antidiagonalTupleGrid b l') *
          ∑ l ∈ Finset.range (i + 1 - j), (dim * dim) * (2 * Lterm l) ≤
          (CΔ j * (dim * dim) * 2) * RHS := by
        have hexpand : (∑ l' ∈ Finset.range (j + 1),
            Combinatorics.antidiagonalTupleGrid b l') *
            (∑ l ∈ Finset.range (i + 1 - j), Lterm l) ≤ RHS := by
          rw [Finset.sum_mul]
          rw [hRHS_def]
          have hstep : ∀ l' ∈ Finset.range (j + 1),
              Combinatorics.antidiagonalTupleGrid b l' *
                (∑ l ∈ Finset.range (i + 1 - j), Lterm l) ≤
              Combinatorics.antidiagonalTupleGrid b l' *
                ∑ l ∈ Finset.range (i + 1 - l'), Lterm l := by
            intro l' hl'
            refine mul_le_mul_of_nonneg_left ?_
              (Combinatorics.antidiagonalTupleGrid_nonneg b hb l')
            refine Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.range_subset_range.mpr ?_) (fun l _ _ => hLterm_nn l)
            rw [Finset.mem_range] at hl'
            omega
          refine le_trans (Finset.sum_le_sum hstep) ?_
          refine Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.range_subset_range.mpr (by omega)) ?_
          intro j' _ _
          exact hRHS_cell_nn j'
        calc (CΔ j * ∑ l' ∈ Finset.range (j + 1),
              Combinatorics.antidiagonalTupleGrid b l') *
              ∑ l ∈ Finset.range (i + 1 - j), (dim * dim) * (2 * Lterm l)
            = (CΔ j * (dim * dim) * 2) *
              ((∑ l' ∈ Finset.range (j + 1), Combinatorics.antidiagonalTupleGrid b l') *
                (∑ l ∈ Finset.range (i + 1 - j), Lterm l)) := by
              have hfac : (∑ l ∈ Finset.range (i + 1 - j),
                  (dim * dim) * (2 * Lterm l)) =
                  (dim * dim * 2) * ∑ l ∈ Finset.range (i + 1 - j), Lterm l := by
                rw [Finset.mul_sum]
                exact Finset.sum_congr rfl fun l _ => by ring
              rw [hfac]
              ring
          _ ≤ (CΔ j * (dim * dim) * 2) * RHS := by
              refine mul_le_mul_of_nonneg_left hexpand ?_
              have := hCΔ_nn j
              positivity
      calc riemannianFiberNormSq (I := I) (M := M) g₀ 6 (2 + j) x
            ((iteratedCovGrad (I := I) g₀ 6 2 j
              (pairTraceOp (I := I) (M := M) g₀ g₁ -
                pairTraceOp (I := I) (M := M) g₀ g₀)).toSection x) *
          ∑ l ∈ Finset.range (i + 1 - j),
            riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + l) x
              ((iteratedCovGrad (I := I) g₀ 2 6 l
                (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
                  (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                    (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁)))).toSection x)
          ≤ (CΔ j * ∑ l' ∈ Finset.range (j + 1),
              Combinatorics.antidiagonalTupleGrid b l') *
            ∑ l ∈ Finset.range (i + 1 - j), (dim * dim) * (2 * Lterm l) :=
            mul_le_mul hA1 hA2 hA2_nn hgrid_nn
        _ ≤ (CΔ j * (dim * dim) * 2) * RHS := hkey
    calc appCcGdiag (E := E) i *
          ∑ j ∈ Finset.range (i + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 6 (2 + j) x
                ((iteratedCovGrad (I := I) g₀ 6 2 j
                  (pairTraceOp (I := I) (M := M) g₀ g₁ -
                    pairTraceOp (I := I) (M := M) g₀ g₀)).toSection x) *
              ∑ l ∈ Finset.range (i + 1 - j),
                riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + l) x
                  ((iteratedCovGrad (I := I) g₀ 2 6 l
                    (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
                      (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                        (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁)))).toSection x)
        ≤ appCcGdiag (E := E) i *
            ∑ j ∈ Finset.range (i + 1), (CΔ j * (dim * dim) * 2) * RHS :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum hcell) (appCcGdiag_nonneg (E := E) i)
      _ = (appCcGdiag (E := E) i * (∑ j ∈ Finset.range (i + 1), CΔ j) * (dim * dim) * 2) *
            RHS := by
          rw [← Finset.sum_mul]
          rw [← Finset.sum_mul]
          rw [← Finset.sum_mul]
          ring
  calc (2 : ℝ) ^ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 2 2 i
          (appCcRS (I := I) (M := M) g₀ 2 6 2
            (pairTraceOp (I := I) (M := M) g₀ g₁ - pairTraceOp (I := I) (M := M) g₀ g₀)
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁))))).toSection x +
        (iteratedCovGrad (I := I) g₀ 2 2 i
          (appCcRS (I := I) (M := M) g₀ 2 6 2 (pairTraceOp (I := I) (M := M) g₀ g₀)
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
              (slotExtendIter (I := I) (M := M) g₀ 0 4 2 Ldiff)))).toSection x)
      ≤ (2 : ℝ) ^ 2 * (2 * ((appCcGdiag (E := E) i * (∑ j ∈ Finset.range (i + 1), CΔ j) *
            (dim * dim) * 2) * RHS) + 2 * ((cB i * (dim * dim)) * RHS)) := by
        have hadd := riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 2 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 2 2 i
            (appCcRS (I := I) (M := M) g₀ 2 6 2
              (pairTraceOp (I := I) (M := M) g₀ g₁ - pairTraceOp (I := I) (M := M) g₀ g₀)
              (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
                (slotExtendIter (I := I) (M := M) g₀ 0 4 2
                  (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁))))).toSection x)
          ((iteratedCovGrad (I := I) g₀ 2 2 i
            (appCcRS (I := I) (M := M) g₀ 2 6 2 (pairTraceOp (I := I) (M := M) g₀ g₀)
              (rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
                (slotExtendIter (I := I) (M := M) g₀ 0 4 2 Ldiff)))).toSection x)
        nlinarith [hT1, hT2, hadd]
    _ ≤ (8 * (cB i * (dim * dim)) +
          8 * (appCcGdiag (E := E) i * (∑ j ∈ Finset.range (i + 1), CΔ j) *
            (dim * dim) * 2)) * RHS := by
        nlinarith [hRHS_nn]

set_option linter.unusedVariables false in
theorem rfns_iteratedCovGrad_riemannMixedCoeff_backgroundDifference_diagonalProductGrid_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (ricciArmOrder0RiemannMixedCoeff (I := I) (M := M) g₀ g₁ -
                ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀)).toSection x) ≤
          C i * ∑ k ∈ Finset.range (i + 3),
            ∑ n ∈ Finset.range (k + 1),
              ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
                ∏ m : Fin n,
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T).toSection x) := by
  classical
  obtain ⟨CB, hCB_nn, hCB⟩ :=
    rfns_iteratedCovGrad_riemannMixedCoeff_backgroundDifference_le_loweredDifference
      (I := I) (M := M) g₀
  obtain ⟨CA, hCA_nn, hCA⟩ :=
    rfns_iteratedCovGrad_riemannLoweredBackgroundDifference_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  refine ⟨fun i => CB i * CA i, fun i => mul_nonneg (hCB_nn i) (hCA_nn i), ?_⟩
  intro g₁ T htie δ hδ_le hδ0 hbound i x
  refine le_trans (hCB g₁ i x) ?_
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (hCA g₁ T htie hδ_le hδ0 hbound i x) (hCB_nn i)

set_option linter.unusedVariables false in
theorem rfns_iteratedCovGrad_riemannCoeff_metricFactorTelescope_diagonalProductGrid_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                ricciArmOrder0RiemannMixedCoeff (I := I) (M := M) g₀ g₁)).toSection x) ≤
          C i * ∑ k ∈ Finset.range (i + 3),
            ∑ n ∈ Finset.range (k + 1),
              ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
                ∏ m : Fin n,
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T).toSection x) := by
  classical
  obtain ⟨CC, hCC_nn, hCC⟩ :=
    rfns_iteratedCovGrad_riemannCoeff_metricFactorTelescope_traceConversion_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨C1, hC1_nn, hC1⟩ :=
    rfns_iteratedCovGrad_riemannG1LoweringDifference_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨CA, hCA_nn, hCA⟩ :=
    rfns_iteratedCovGrad_riemannLoweredBackgroundDifference_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨cbg, hcbg_nn, hcbg⟩ := exists_backgroundJet_rfns_bound (I := I) (M := M) g₀ 0 4
    (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)
  refine ⟨fun i => CC i * ∑ j ∈ Finset.range (i + 1), ∑ l ∈ Finset.range (i + 1),
      (2 * cbg l + (2 * CA l + C1 l) * tWindowMulConst l j),
    fun i => mul_nonneg (hCC_nn i) (Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun l _ =>
      add_nonneg (by have := hcbg_nn l; linarith)
        (mul_nonneg (by have := hCA_nn l; have := hC1_nn l; linarith)
          (tWindowMulConst_nonneg l j))), ?_⟩
  intro g₁ T htie δ hδ_le hδ0 hbound i x
  set b : ℕ → ℝ := fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
    ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x) with hb_def
  have hb : ∀ j, 0 ≤ b j :=
    fun j => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + j) x _
  have hP : ∀ l : ℕ,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 4 l
          (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁)).toSection x) ≤
      2 * cbg l + 2 * CA l * tWindow b l := by
    intro l
    have hsplit : riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁ =
        riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁ +
          riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀ := by
      rw [riemannLoweredBackgroundDifference, sub_add_cancel]
    have hsec : (iteratedCovGrad (I := I) g₀ 0 4 l
        (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁)).toSection x =
        (iteratedCovGrad (I := I) g₀ 0 4 l
          (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)).toSection x +
        (iteratedCovGrad (I := I) g₀ 0 4 l
          (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)).toSection x := by
      rw [hsplit, iteratedCovGrad_add, SmoothCcTensor.toSection_add]
      rfl
    rw [hsec]
    refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 (4 + l) x _ _) ?_
    have h1 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 4 l
          (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)).toSection x) ≤
        CA l * tWindow b l := by
      have h := hCA g₁ T htie hδ_le hδ0 hbound l x
      rw [← tWindow_eq_tripleSum (I := I) (M := M) g₀ T x l] at h
      exact h
    have h2 := hcbg l x
    linarith
  have hQ : ∀ l : ℕ,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 4 l
          (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁ -
            riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁)).toSection x) ≤
      C1 l * tWindow b l := by
    intro l
    have h := hC1 g₁ T htie hδ_le hδ0 hbound l x
    rw [← tWindow_eq_tripleSum (I := I) (M := M) g₀ T x l] at h
    exact h
  refine le_trans (hCC g₁ T htie hδ_le hδ0 hbound i x) ?_
  rw [← tWindow_eq_tripleSum (I := I) (M := M) g₀ T x i]
  have hjl : ∀ j ∈ Finset.range (i + 1),
      (∑ n ∈ Finset.range (j + 1),
        ∑ e ∈ Finset.Nat.antidiagonalTuple n j,
          ∏ m : Fin n, b (e m)) *
        (∑ l ∈ Finset.range (i + 1 - j),
          (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 4 l
                (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁)).toSection x) +
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 4 l
                (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁ -
                  riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁)).toSection x))) ≤
      (∑ l ∈ Finset.range (i + 1),
        (2 * cbg l + (2 * CA l + C1 l) * tWindowMulConst l j)) * tWindow b i := by
    intro j hj
    have hjle : j ≤ i := by
      have := Finset.mem_range.mp hj
      omega
    have hgrid_eq : (∑ n ∈ Finset.range (j + 1),
        ∑ e ∈ Finset.Nat.antidiagonalTuple n j, ∏ m : Fin n, b (e m)) =
        Combinatorics.antidiagonalTupleGrid b j := rfl
    rw [hgrid_eq, mul_comm (Combinatorics.antidiagonalTupleGrid b j)]
    rw [Finset.sum_mul]
    have hterm : ∀ l ∈ Finset.range (i + 1 - j),
        (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 4 l
              (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁)).toSection x) +
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 4 l
              (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁ -
                riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁)).toSection x)) *
          Combinatorics.antidiagonalTupleGrid b j ≤
        (2 * cbg l + (2 * CA l + C1 l) * tWindowMulConst l j) * tWindow b i := by
      intro l hl
      have hlle : l ≤ i - j := by
        have := Finset.mem_range.mp hl
        omega
      have hlj : l + j ≤ i := by omega
      have hgrid_nn : 0 ≤ Combinatorics.antidiagonalTupleGrid b j :=
        Combinatorics.antidiagonalTupleGrid_nonneg b hb j
      have hgrid_le : Combinatorics.antidiagonalTupleGrid b j ≤ tWindow b i :=
        antidiagonalTupleGrid_le_tWindow b hb (by omega)
      have hsum_le : (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 4 l
              (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁)).toSection x) +
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 4 l
              (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁ -
                riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁)).toSection x)) ≤
          2 * cbg l + (2 * CA l + C1 l) * tWindow b l := by
        have h1 := hP l
        have h2 := hQ l
        have hW_nn : 0 ≤ tWindow b l := tWindow_nonneg b hb l
        nlinarith [hCA_nn l, hC1_nn l]
      calc (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 4 l
                (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁)).toSection x) +
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 4 l
                (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁ -
                  riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁)).toSection x)) *
            Combinatorics.antidiagonalTupleGrid b j
          ≤ (2 * cbg l + (2 * CA l + C1 l) * tWindow b l) *
              Combinatorics.antidiagonalTupleGrid b j :=
            mul_le_mul_of_nonneg_right hsum_le hgrid_nn
        _ = 2 * cbg l * Combinatorics.antidiagonalTupleGrid b j +
              (2 * CA l + C1 l) * (tWindow b l * Combinatorics.antidiagonalTupleGrid b j) := by
            ring
        _ ≤ 2 * cbg l * tWindow b i +
              (2 * CA l + C1 l) * (tWindowMulConst l j * tWindow b (l + j)) := by
            have hmul := tWindow_mul_antidiagonalTupleGrid_le b hb l j
            have hnn1 : 0 ≤ 2 * cbg l := by have := hcbg_nn l; linarith
            have hnn2 : 0 ≤ 2 * CA l + C1 l := by
              have := hCA_nn l; have := hC1_nn l; linarith
            exact add_le_add (mul_le_mul_of_nonneg_left hgrid_le hnn1)
              (mul_le_mul_of_nonneg_left hmul hnn2)
        _ ≤ 2 * cbg l * tWindow b i +
              (2 * CA l + C1 l) * (tWindowMulConst l j * tWindow b i) := by
            have hnn2 : 0 ≤ 2 * CA l + C1 l := by
              have := hCA_nn l; have := hC1_nn l; linarith
            exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left (tWindow_mono b hb hlj)
                (tWindowMulConst_nonneg l j)) hnn2)
        _ = (2 * cbg l + (2 * CA l + C1 l) * tWindowMulConst l j) * tWindow b i := by
            ring
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.sum_mul]
    refine mul_le_mul_of_nonneg_right ?_ (tWindow_nonneg b hb i)
    refine Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_subset_range.mpr (by omega)) ?_
    intro l _ _
    exact add_nonneg (by have := hcbg_nn l; linarith)
      (mul_nonneg (by have := hCA_nn l; have := hC1_nn l; linarith)
        (tWindowMulConst_nonneg l j))
  calc CC i * ∑ j ∈ Finset.range (i + 1),
        (∑ n ∈ Finset.range (j + 1),
          ∑ e ∈ Finset.Nat.antidiagonalTuple n j,
            ∏ m : Fin n, b (e m)) *
          ∑ l ∈ Finset.range (i + 1 - j),
            (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
                ((iteratedCovGrad (I := I) g₀ 0 4 l
                  (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁)).toSection x) +
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
                ((iteratedCovGrad (I := I) g₀ 0 4 l
                  (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁ -
                    riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁)).toSection x))
      ≤ CC i * ∑ j ∈ Finset.range (i + 1),
          (∑ l ∈ Finset.range (i + 1),
            (2 * cbg l + (2 * CA l + C1 l) * tWindowMulConst l j)) * tWindow b i :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hjl) (hCC_nn i)
    _ = CC i * (∑ j ∈ Finset.range (i + 1), ∑ l ∈ Finset.range (i + 1),
          (2 * cbg l + (2 * CA l + C1 l) * tWindowMulConst l j)) * tWindow b i := by
        rw [← Finset.sum_mul]
        ring

set_option linter.unusedVariables false in
theorem rfns_iteratedCovGrad_ricciArmOrder0RiemannCoeff_backgroundDifference_diagonalProductGrid_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀)).toSection x) ≤
          C i * ∑ k ∈ Finset.range (i + 3),
            ∑ n ∈ Finset.range (k + 1),
              ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
                ∏ m : Fin n,
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 (e m) T).toSection x) := by
  classical
  obtain ⟨Ca, hCa_nn, hCa⟩ :=
    rfns_iteratedCovGrad_riemannMixedCoeff_backgroundDifference_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨Cb, hCb_nn, hCb⟩ :=
    rfns_iteratedCovGrad_riemannCoeff_metricFactorTelescope_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  refine ⟨fun i => 2 * Cb i + 2 * Ca i,
    fun i => by have := hCa_nn i; have := hCb_nn i; linarith, ?_⟩
  intro g₁ T htie δ hδ_le hδ0 hbound i x
  have hb : ∀ j : ℕ, 0 ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
      ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x) :=
    fun j => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + j) x _
  rw [← tWindow_eq_tripleSum (I := I) (M := M) g₀ T x i]
  have hsplit : ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
      ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ =
      (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
        ricciArmOrder0RiemannMixedCoeff (I := I) (M := M) g₀ g₁) +
      (ricciArmOrder0RiemannMixedCoeff (I := I) (M := M) g₀ g₁ -
        ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) := by
    rw [sub_add_sub_cancel]
  have hsec : (iteratedCovGrad (I := I) g₀ 2 2 i
      (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
        ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀)).toSection x =
      (iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
          ricciArmOrder0RiemannMixedCoeff (I := I) (M := M) g₀ g₁)).toSection x +
        (iteratedCovGrad (I := I) g₀ 2 2 i
          (ricciArmOrder0RiemannMixedCoeff (I := I) (M := M) g₀ g₁ -
            ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀)).toSection x := by
    rw [hsplit, iteratedCovGrad_add (I := I) g₀ 2 2 i _ _, SmoothCcTensor.toSection_add]
    rfl
  rw [hsec]
  refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 2 (2 + i) x _ _) ?_
  have h1 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
      ((iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
          ricciArmOrder0RiemannMixedCoeff (I := I) (M := M) g₀ g₁)).toSection x) ≤
      Cb i * tWindow (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x)) i := by
    rw [tWindow_eq_tripleSum (I := I) (M := M) g₀ T x i]
    exact hCb g₁ T htie hδ_le hδ0 hbound i x
  have h2 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
      ((iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciArmOrder0RiemannMixedCoeff (I := I) (M := M) g₀ g₁ -
          ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀)).toSection x) ≤
      Ca i * tWindow (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x)) i := by
    rw [tWindow_eq_tripleSum (I := I) (M := M) g₀ T x i]
    exact hCa g₁ T htie hδ_le hδ0 hbound i x
  rw [show (2 * Cb i + 2 * Ca i) *
      tWindow (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x)) i =
      2 * (Cb i * tWindow (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x)) i) +
        2 * (Ca i * tWindow (fun j => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x)) i) from by ring]
  linarith

set_option linter.unusedVariables false in
theorem slotInsertEndoCc_ricEndoBackgroundDifferenceField_perOrder_l2_ballUniform
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a →
          ‖iteratedCovGrad (I := I) g₀ 1 1 i
            (slotInsertEndoCc (I := I) (M := M) g₀ 0
              (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁))‖ ^ 2 ≤ K i := by
  obtain ⟨C, hC_nn, hgrid⟩ :=
    rfns_iteratedCovGrad_slotInsertEndoCc_zero_ricEndoBackgroundDifferenceField_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨Kg, hKg_nn, hKg⟩ :=
    curvDiffGrid_integral_ballUniform_window (I := I) (M := M) g₀ a ha_super hR
  refine ⟨fun i => C i * ∑ k ∈ Finset.range (i + 3), Kg k,
    fun i => mul_nonneg (hC_nn i) (Finset.sum_nonneg (fun k _ => hKg_nn k)), ?_⟩
  intro g₁ P δ hδ_le hδ htie hPball i hi
  by_cases hM : Nonempty M
  · obtain ⟨x₀⟩ := hM
    have hδ0 : 0 ≤ δ := by
      obtain ⟨v, hv⟩ : ∃ v : TangentSpace I x₀, v ≠ 0 := by
        haveI : Nontrivial (TangentSpace I x₀) := by
          have hfr : 0 < Module.finrank ℝ (TangentSpace I x₀) := by
            have heq : Module.finrank ℝ (TangentSpace I x₀) = Module.finrank ℝ E := rfl
            rw [heq]; exact Nat.pos_of_ne_zero (NeZero.ne _)
          exact Module.nontrivial_of_finrank_pos hfr
        exact exists_ne 0
      have hpos : 0 < g₀.inner x₀ v v := g₀.pos x₀ v hv
      have hbound := hδ x₀ v v
      have hsqrt_pos : 0 < Real.sqrt (g₀.inner x₀ v v) := Real.sqrt_pos.mpr hpos
      have habs_nn : 0 ≤ |ccTensorBilinSymm (I := I) g₀ P x₀ v v| := abs_nonneg _
      by_contra hδc
      have hδc' : δ < 0 := lt_of_not_ge hδc
      have hrhs_neg : δ * Real.sqrt (g₀.inner x₀ v v) * Real.sqrt (g₀.inner x₀ v v) < 0 := by
        have h1 : δ * Real.sqrt (g₀.inner x₀ v v) < 0 := mul_neg_of_neg_of_pos hδc' hsqrt_pos
        exact mul_neg_of_neg_of_pos h1 hsqrt_pos
      linarith [le_trans habs_nn hbound]
    have hkle : ∀ k ∈ Finset.range (i + 3), k ≤ a + 2 := by
      intro k hk
      rw [Finset.mem_range] at hk
      omega
    have hF_int : MeasureTheory.Integrable
        (fun x => C i * ∑ k ∈ Finset.range (i + 3),
          ∑ n ∈ Finset.range (k + 1),
            ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
              ∏ m : Fin n,
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
        (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
      (MeasureTheory.integrable_finset_sum _
        (fun k hk => (hKg P hPball k (hkle k hk)).1)).const_mul (C i)
    have key := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 1 (1 + i)
      (iteratedCovGrad (I := I) g₀ 1 1 i
        (slotInsertEndoCc (I := I) (M := M) g₀ 0
          (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁)))
      (fun x => C i * ∑ k ∈ Finset.range (i + 3),
        ∑ n ∈ Finset.range (k + 1),
          ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
            ∏ m : Fin n,
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
      hF_int
      (fun x => hgrid g₁ P htie hδ_le hδ0 hδ i x)
    refine le_trans key ?_
    rw [MeasureTheory.integral_const_mul,
      MeasureTheory.integral_finset_sum _ (fun k hk => (hKg P hPball k (hkle k hk)).1)]
    exact mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum (fun k hk => (hKg P hPball k (hkle k hk)).2)) (hC_nn i)
  · haveI hM' : IsEmpty M := not_nonempty_iff.mp hM
    have hz : ‖iteratedCovGrad (I := I) g₀ 1 1 i
        (slotInsertEndoCc (I := I) (M := M) g₀ 0
          (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁))‖ = 0 := by
      rw [SmoothCcTensor.norm_def, tensorL2Norm_def, tensorL2Inner,
        MeasureTheory.integral_of_isEmpty, Real.sqrt_zero]
    rw [hz]
    simpa using mul_nonneg (hC_nn i) (Finset.sum_nonneg (fun k _ => hKg_nn k))

set_option linter.unusedVariables false in
theorem ricciArmOrder0RiemannCoeff_backgroundDifference_perOrder_l2_ballUniform
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a →
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
              ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2 ≤ K i := by
  obtain ⟨C, hC_nn, hgrid⟩ :=
    rfns_iteratedCovGrad_ricciArmOrder0RiemannCoeff_backgroundDifference_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨Kg, hKg_nn, hKg⟩ :=
    curvDiffGrid_integral_ballUniform_window (I := I) (M := M) g₀ a ha_super hR
  refine ⟨fun i => C i * ∑ k ∈ Finset.range (i + 3), Kg k,
    fun i => mul_nonneg (hC_nn i) (Finset.sum_nonneg (fun k _ => hKg_nn k)), ?_⟩
  intro g₁ P δ hδ_le hδ htie hPball i hi
  by_cases hM : Nonempty M
  · obtain ⟨x₀⟩ := hM
    have hδ0 : 0 ≤ δ := by
      obtain ⟨v, hv⟩ : ∃ v : TangentSpace I x₀, v ≠ 0 := by
        haveI : Nontrivial (TangentSpace I x₀) := by
          have hfr : 0 < Module.finrank ℝ (TangentSpace I x₀) := by
            have heq : Module.finrank ℝ (TangentSpace I x₀) = Module.finrank ℝ E := rfl
            rw [heq]; exact Nat.pos_of_ne_zero (NeZero.ne _)
          exact Module.nontrivial_of_finrank_pos hfr
        exact exists_ne 0
      have hpos : 0 < g₀.inner x₀ v v := g₀.pos x₀ v hv
      have hbound := hδ x₀ v v
      have hsqrt_pos : 0 < Real.sqrt (g₀.inner x₀ v v) := Real.sqrt_pos.mpr hpos
      have habs_nn : 0 ≤ |ccTensorBilinSymm (I := I) g₀ P x₀ v v| := abs_nonneg _
      by_contra hδc
      have hδc' : δ < 0 := lt_of_not_ge hδc
      have hrhs_neg : δ * Real.sqrt (g₀.inner x₀ v v) * Real.sqrt (g₀.inner x₀ v v) < 0 := by
        have h1 : δ * Real.sqrt (g₀.inner x₀ v v) < 0 := mul_neg_of_neg_of_pos hδc' hsqrt_pos
        exact mul_neg_of_neg_of_pos h1 hsqrt_pos
      linarith [le_trans habs_nn hbound]
    have hkle : ∀ k ∈ Finset.range (i + 3), k ≤ a + 2 := by
      intro k hk
      rw [Finset.mem_range] at hk
      omega
    have hF_int : MeasureTheory.Integrable
        (fun x => C i * ∑ k ∈ Finset.range (i + 3),
          ∑ n ∈ Finset.range (k + 1),
            ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
              ∏ m : Fin n,
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
        (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
      (MeasureTheory.integrable_finset_sum _
        (fun k hk => (hKg P hPball k (hkle k hk)).1)).const_mul (C i)
    have key := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 2 (2 + i)
      (iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
          ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀))
      (fun x => C i * ∑ k ∈ Finset.range (i + 3),
        ∑ n ∈ Finset.range (k + 1),
          ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
            ∏ m : Fin n,
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
      hF_int
      (fun x => hgrid g₁ P htie hδ_le hδ0 hδ i x)
    refine le_trans key ?_
    rw [MeasureTheory.integral_const_mul,
      MeasureTheory.integral_finset_sum _ (fun k hk => (hKg P hPball k (hkle k hk)).1)]
    exact mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum (fun k hk => (hKg P hPball k (hkle k hk)).2)) (hC_nn i)
  · haveI hM' : IsEmpty M := not_nonempty_iff.mp hM
    have hz : ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
          ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀)‖ = 0 := by
      rw [SmoothCcTensor.norm_def, tensorL2Norm_def, tensorL2Inner,
        MeasureTheory.integral_of_isEmpty, Real.sqrt_zero]
    rw [hz]
    simpa using mul_nonneg (hC_nn i) (Finset.sum_nonneg (fun k _ => hKg_nn k))

set_option linter.unusedVariables false in
theorem ricciArmOrder0CurvCoeff_backgroundDifference_perOrder_l2_ballUniform
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a →
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
              ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2 ≤ K i := by
  obtain ⟨K, hK_nn, hK⟩ :=
    slotInsertEndoCc_ricEndoBackgroundDifferenceField_perOrder_l2_ballUniform
      (I := I) (M := M) g₀ a ha_super hR hδ₀
  refine ⟨fun i => 4 * (Module.finrank ℝ E : ℝ) * K i,
    fun i => mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (hK_nn i), ?_⟩
  intro g₁ P δ hδ_le hδ htie hPball i hi
  have hKi := hK g₁ P hδ_le hδ htie hPball i hi
  have hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 2 2 i
            (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
              ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)).toSection x) ≤
        4 * (Module.finrank ℝ E : ℝ) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
            ((iteratedCovGrad (I := I) g₀ 1 1 i
              (slotInsertEndoCc (I := I) (M := M) g₀ 0
                (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁))).toSection x) := by
    intro x
    have hsec : (iteratedCovGrad (I := I) g₀ 2 2 i
          (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
            ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)).toSection x =
        (iteratedCovGrad (I := I) g₀ 2 2 i
            (slotInsertEndoCc (I := I) (M := M) g₀ 1
              (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁))).toSection x +
          (iteratedCovGrad (I := I) g₀ 2 2 i
            (reindexCoeffGen (I := I) (M := M) g₀ 2 2
              (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
                (slotInsertEndoCc (I := I) (M := M) g₀ 1
                  (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁)))
              (Equiv.swap (0 : Fin 2) 1))).toSection x := by
      rw [ricciArmOrder0CurvCoeff_backgroundDifference_decomp (I := I) (M := M) g₀ g₁,
        iteratedCovGrad_add (I := I) g₀ 2 2 i
          (slotInsertEndoCc (I := I) (M := M) g₀ 1
            (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁))
          (reindexCoeffGen (I := I) (M := M) g₀ 2 2
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
              (slotInsertEndoCc (I := I) (M := M) g₀ 1
                (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁)))
            (Equiv.swap (0 : Fin 2) 1)),
        SmoothCcTensor.toSection_add]
      rfl
    rw [hsec]
    refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 2 (2 + i) x _ _) ?_
    have hswap : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 2 2 i
          (reindexCoeffGen (I := I) (M := M) g₀ 2 2
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
              (slotInsertEndoCc (I := I) (M := M) g₀ 1
                (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁)))
            (Equiv.swap (0 : Fin 2) 1))).toSection x) =
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 2 2 i
            (slotInsertEndoCc (I := I) (M := M) g₀ 1
              (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁))).toSection x) :=
      rfns_iteratedCovGrad_rsDomDomCongr_both_eq (I := I) (M := M) g₀ 2 2
        (Equiv.swap (0 : Fin 2) 1) (Equiv.swap (0 : Fin 2) 1)
        (slotInsertEndoCc (I := I) (M := M) g₀ 1
          (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁)) i x
    rw [hswap]
    have hendo : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 2 2 i
          (slotInsertEndoCc (I := I) (M := M) g₀ 1
            (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁))).toSection x) ≤
        (Module.finrank ℝ E : ℝ) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
            ((iteratedCovGrad (I := I) g₀ 1 1 i
              (slotInsertEndoCc (I := I) (M := M) g₀ 0
                (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁))).toSection x) := by
      have h := rfns_iteratedCovGrad_slotInsertEndoCc_le_endo (I := I) (M := M) g₀ 1
        (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁) i x
      rw [pow_one] at h
      exact h
    linarith [hendo]
  have hF_int : MeasureTheory.Integrable
      (fun x => 4 * (Module.finrank ℝ E : ℝ) *
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
          ((iteratedCovGrad (I := I) g₀ 1 1 i
            (slotInsertEndoCc (I := I) (M := M) g₀ 0
              (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁))).toSection x))
      (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    (integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 1 (1 + i)
      (iteratedCovGrad (I := I) g₀ 1 1 i
        (slotInsertEndoCc (I := I) (M := M) g₀ 0
          (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁)))).const_mul _
  have key := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 2 (2 + i)
    (iteratedCovGrad (I := I) g₀ 2 2 i
      (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
        ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀))
    (fun x => 4 * (Module.finrank ℝ E : ℝ) *
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 1 i
          (slotInsertEndoCc (I := I) (M := M) g₀ 0
            (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁))).toSection x))
    hF_int hpt
  refine le_trans key ?_
  rw [MeasureTheory.integral_const_mul]
  rw [← tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g₀ 1 (1 + i)
    (iteratedCovGrad (I := I) g₀ 1 1 i
      (slotInsertEndoCc (I := I) (M := M) g₀ 0
        (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁)))]
  rw [← SmoothCcTensor.norm_def]
  exact mul_le_mul_of_nonneg_left hKi (by positivity)

set_option linter.unusedVariables false in
/-- A product of tensor-jet fibre norms on one antidiagonal has a tame
integral bound from a zeroth-order pointwise bound, the top-order `L²` norm,
and the corresponding Gagliardo--Nirenberg estimates. -/
theorem grid_prod_int_le
    (g₀ : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2)
    {R : ℝ} (hR : 0 ≤ R)
    (i : ℕ) (hi1 : 1 ≤ i)
    {Λ : ℝ} (hΛ_nn : 0 ≤ Λ)
    (hΛsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (P.toSection x) ≤ Λ ^ 2)
    (hNi : ‖iteratedCovGrad (I := I) g₀ 0 2 i P‖ ≤ R)
    {C : ℝ} (hC_nn : 0 ≤ C)
    (hGNP : ∀ j : ℕ, 0 < j → j < i →
      (∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
              ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) ^ ((i : ℝ) / (j : ℝ))
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ^ ((j : ℝ) / (i : ℝ)) ≤
        C * Λ ^ (2 * (1 - (j : ℝ) / (i : ℝ))) * R ^ (2 * (j : ℝ) / (i : ℝ)))
    (n : ℕ) (hn_le : n ≤ i) (e : Fin n → ℕ) (he : ∑ m, e m = i) :
    MeasureTheory.Integrable
        (fun x => ∏ m : Fin n,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
        (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
      (∫ x, ∏ m : Fin n,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
        (i : ℝ) * (max Λ (max C 1)) ^ (7 * i) * R ^ 2 := by
  classical
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g₀
  set μ : MeasureTheory.Measure M := riemannianVolumeMeasure (I := I) (M := M) g₀ with hμ
  haveI : IsFiniteMeasure μ := by rw [hμ]; infer_instance
  have hi_pos : 0 < i := hi1
  have hiR_pos : (0 : ℝ) < (i : ℝ) := by exact_mod_cast hi_pos
  have hiR_ne : (i : ℝ) ≠ 0 := ne_of_gt hiR_pos
  have hnn : ∀ (j : ℕ) (x : M),
      0 ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x) :=
    fun j x => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + j) x _
  have hcont : ∀ j : ℕ, Continuous (fun x => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
      ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) := by
    intro j
    have hc := Integral.L2.SmoothCcTensor.continuous_inner_self (I := I) (M := M)
      (iteratedCovGrad (I := I) g₀ 0 2 j P)
    refine hc.congr (fun x => ?_)
    rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x),
      ← Integral.L2.SmoothCcTensor.toFun_apply (I := I) (M := M)
        (iteratedCovGrad (I := I) g₀ 0 2 j P) x]
  have hint : ∀ j : ℕ, MeasureTheory.Integrable
      (fun x => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) μ := by
    intro j
    rw [hμ]
    exact integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 0 (2 + j)
      (iteratedCovGrad (I := I) g₀ 0 2 j P)
  have hint_rpow : ∀ (j : ℕ) (p : ℝ), 0 ≤ p → MeasureTheory.Integrable
      (fun x => (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) ^ p) μ := by
    intro j p hp
    have hcp : Continuous (fun x => (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) ^ p) :=
      (hcont j).rpow_const (fun x => Or.inr hp)
    exact hcp.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hint_prod : MeasureTheory.Integrable
      (fun x => ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) μ := by
    have hcp : Continuous (fun x => ∏ m : Fin n,
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) :=
      continuous_finset_prod Finset.univ (fun m _ => hcont (e m))
    exact hcp.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  refine ⟨hint_prod, ?_⟩
  set Mbar : ℝ := max Λ (max C 1) with hMbar
  have hMbar1 : (1 : ℝ) ≤ Mbar := le_trans (le_max_right C 1) (le_max_right Λ _)
  have hMbar_nn : 0 ≤ Mbar := le_trans zero_le_one hMbar1
  have hΛ_le : Λ ≤ Mbar := le_max_left _ _
  have hC_le : C ≤ Mbar := le_trans (le_max_left C 1) (le_max_right Λ _)
  set Sset : Finset (Fin n) := Finset.univ.filter (fun m => 0 < e m) with hSset
  set Zset : Finset (Fin n) := Finset.univ.filter (fun m => ¬ (0 < e m)) with hZset
  have hsplit : ∀ x : M,
      (∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) =
        (∏ m ∈ Sset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) *
          (∏ m ∈ Zset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) := by
    intro x
    rw [hSset, hZset]
    exact (Finset.prod_filter_mul_prod_filter_not Finset.univ (fun m => 0 < e m)
      (fun m => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))).symm
  have hZbound : ∀ x : M,
      (∏ m ∈ Zset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ≤ Λ ^ (2 * Zset.card) := by
    intro x
    calc (∏ m ∈ Zset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
        ≤ ∏ _m ∈ Zset, Λ ^ 2 := by
          apply Finset.prod_le_prod (fun m _ => hnn (e m) x)
          intro m hm
          have hem0 : e m = 0 := by have := (Finset.mem_filter.mp hm).2; omega
          rw [hem0]; exact hΛsup x
      _ = Λ ^ (2 * Zset.card) := by rw [Finset.prod_const, ← pow_mul]
  have hZsum0 : ∑ m ∈ Zset, e m = 0 := by
    apply Finset.sum_eq_zero
    intro m hm
    have := (Finset.mem_filter.mp hm).2; omega
  have hSsum : ∑ m ∈ Sset, e m = i := by
    have h := Finset.sum_filter_add_sum_filter_not Finset.univ (fun m => 0 < e m) e
    rw [← hSset, ← hZset, hZsum0, add_zero, he] at h
    exact h
  have hScard_pos : 1 ≤ Sset.card := by
    rcases Nat.eq_zero_or_pos Sset.card with h0 | hp
    · exfalso
      rw [Finset.card_eq_zero] at h0
      rw [h0, Finset.sum_empty] at hSsum
      omega
    · exact hp
  rcases Nat.lt_or_ge Sset.card 2 with hScard_lt2 | hScard_ge2
  · have hScard1 : Sset.card = 1 := by omega
    obtain ⟨m₀, hm₀⟩ := Finset.card_eq_one.mp hScard1
    have hem₀ : e m₀ = i := by
      have hss : ∑ m ∈ Sset, e m = e m₀ := by rw [hm₀, Finset.sum_singleton]
      rw [hss] at hSsum; exact hSsum
    have hSprod : ∀ x : M,
        (∏ m ∈ Sset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) =
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection x) := by
      intro x; rw [hm₀, Finset.prod_singleton, hem₀]
    have hpt : ∀ x : M,
        (∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ≤
          Λ ^ (2 * Zset.card) * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection x) := by
      intro x
      rw [hsplit x, hSprod x]
      calc (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
              ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection x)) *
            (∏ m ∈ Zset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
          ≤ (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
              ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection x)) * Λ ^ (2 * Zset.card) :=
            mul_le_mul_of_nonneg_left (hZbound x) (hnn i x)
        _ = Λ ^ (2 * Zset.card) * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
              ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection x) := mul_comm _ _
    have hintFi : (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection x) ∂μ) ≤ R ^ 2 := by
      have heq : (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection x) ∂μ) =
          ‖iteratedCovGrad (I := I) g₀ 0 2 i P‖ ^ 2 := by
        rw [SmoothCcTensor.norm_def (iteratedCovGrad (I := I) g₀ 0 2 i P), hμ]
        exact (tensorL2Norm_sq_eq_integral_riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i)
          ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection)).symm
      rw [heq]
      nlinarith [hNi, norm_nonneg (iteratedCovGrad (I := I) g₀ 0 2 i P), hR]
    have hΛZ_nn : 0 ≤ Λ ^ (2 * Zset.card) := pow_nonneg hΛ_nn _
    calc (∫ x, ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x) ∂μ)
        ≤ ∫ x, Λ ^ (2 * Zset.card) * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection x) ∂μ :=
          MeasureTheory.integral_mono hint_prod ((hint i).const_mul _) hpt
      _ = Λ ^ (2 * Zset.card) * ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 2 i P).toSection x) ∂μ :=
          MeasureTheory.integral_const_mul _ _
      _ ≤ Λ ^ (2 * Zset.card) * R ^ 2 := mul_le_mul_of_nonneg_left hintFi hΛZ_nn
      _ ≤ (i : ℝ) * Mbar ^ (7 * i) * R ^ 2 := by
          have hZle : Zset.card ≤ i := le_trans (Finset.card_le_univ _) (by simpa using hn_le)
          have e1 : Λ ^ (2 * Zset.card) ≤ Mbar ^ (7 * i) :=
            le_trans (pow_le_pow_left₀ hΛ_nn hΛ_le _)
              (pow_le_pow_right₀ hMbar1 (by omega))
          have e4 : Λ ^ (2 * Zset.card) * R ^ 2 ≤ Mbar ^ (7 * i) * R ^ 2 :=
            mul_le_mul_of_nonneg_right e1 (sq_nonneg R)
          have e5 : Mbar ^ (7 * i) * R ^ 2 ≤ (i : ℝ) * Mbar ^ (7 * i) * R ^ 2 := by
            have h1i : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi1
            have hMR : 0 ≤ Mbar ^ (7 * i) * R ^ 2 :=
              mul_nonneg (pow_nonneg hMbar_nn _) (sq_nonneg R)
            calc Mbar ^ (7 * i) * R ^ 2 = 1 * (Mbar ^ (7 * i) * R ^ 2) := by ring
              _ ≤ (i : ℝ) * (Mbar ^ (7 * i) * R ^ 2) := mul_le_mul_of_nonneg_right h1i hMR
              _ = (i : ℝ) * Mbar ^ (7 * i) * R ^ 2 := by ring
          exact le_trans e4 e5
  · have hem_lt : ∀ m ∈ Sset, e m < i := by
      intro m hm
      have hmpos : 0 < e m := (Finset.mem_filter.mp hm).2
      have hadd : e m + ∑ m' ∈ Sset.erase m, e m' = ∑ m' ∈ Sset, e m' :=
        Finset.add_sum_erase Sset e hm
      rw [hSsum] at hadd
      have herase_ne : (Sset.erase m).Nonempty := by
        rw [← Finset.card_pos, Finset.card_erase_of_mem hm]; omega
      obtain ⟨m', hm'⟩ := herase_ne
      have hm'S : m' ∈ Sset := Finset.mem_of_mem_erase hm'
      have hm'pos : 1 ≤ e m' := (Finset.mem_filter.mp hm'S).2
      have hle : e m' ≤ ∑ m'' ∈ Sset.erase m, e m'' :=
        Finset.single_le_sum (fun k _ => Nat.zero_le _) hm'
      omega
    have hAMGM : ∀ x : M,
        (∏ m ∈ Sset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ≤
          ∑ m ∈ Sset, ((e m : ℝ) / i) *
            (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) := by
      intro x
      have hw_nn : ∀ m ∈ Sset, 0 ≤ (e m : ℝ) / i := fun m _ => by positivity
      have hw_sum : ∑ m ∈ Sset, (e m : ℝ) / i = 1 := by
        rw [← Finset.sum_div]
        rw [show (∑ m ∈ Sset, (e m : ℝ)) = ((i : ℕ) : ℝ) from by
          rw [← Nat.cast_sum]; exact_mod_cast hSsum]
        exact div_self hiR_ne
      have hz_nn : ∀ m ∈ Sset, 0 ≤ (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) :=
        fun m _ => Real.rpow_nonneg (hnn (e m) x) _
      have hAM := Real.geom_mean_le_arith_mean_weighted Sset (fun m => (e m : ℝ) / i)
        (fun m => (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)))
        hw_nn hw_sum hz_nn
      have hLHS : (∏ m ∈ Sset, ((riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)))
            ^ ((e m : ℝ) / i)) =
          ∏ m ∈ Sset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x) := by
        apply Finset.prod_congr rfl
        intro m hm
        have hmpos : 0 < e m := (Finset.mem_filter.mp hm).2
        have hemR_ne : (e m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hmpos.ne'
        rw [← Real.rpow_mul (hnn (e m) x)]
        rw [show ((i : ℝ) / (e m : ℝ)) * ((e m : ℝ) / i) = 1 by field_simp]
        rw [Real.rpow_one]
      rw [hLHS] at hAM
      exact hAM
    have hfactor : ∀ m ∈ Sset,
        (∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ) ≤
          Mbar ^ (5 * i) * R ^ 2 := by
      intro m hm
      have hmpos : 0 < e m := (Finset.mem_filter.mp hm).2
      have hem_lt_i : e m < i := hem_lt m hm
      have hemR_pos : (0 : ℝ) < (e m : ℝ) := by exact_mod_cast hmpos
      have hemR_ne : (e m : ℝ) ≠ 0 := ne_of_gt hemR_pos
      have hgn := hGNP (e m) hmpos hem_lt_i
      set Ival : ℝ := ∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ
        with hIval
      have hIval_nn : 0 ≤ Ival := by
        rw [hIval]; exact integral_nonneg (fun x => Real.rpow_nonneg (hnn (e m) x) _)
      have hθ_nn : 0 ≤ (e m : ℝ) / i := by positivity
      have hθ_le1 : (e m : ℝ) / i ≤ 1 := by
        rw [div_le_one hiR_pos]; exact_mod_cast Nat.le_of_lt hem_lt_i
      have hexp1_nn : 0 ≤ 2 * (1 - (e m : ℝ) / i) := by nlinarith
      have hexp1_le : 2 * (1 - (e m : ℝ) / i) ≤ 2 := by nlinarith
      have hΛpow : Λ ^ (2 * (1 - (e m : ℝ) / i)) ≤ Mbar ^ (2 : ℕ) := by
        calc Λ ^ (2 * (1 - (e m : ℝ) / i)) ≤ Mbar ^ (2 * (1 - (e m : ℝ) / i)) :=
              Real.rpow_le_rpow hΛ_nn hΛ_le hexp1_nn
          _ ≤ Mbar ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hMbar1 hexp1_le
          _ = Mbar ^ (2 : ℕ) := by rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      have hbase_le : C * Λ ^ (2 * (1 - (e m : ℝ) / i)) ≤ Mbar ^ (3 : ℕ) := by
        have h1 : C * Λ ^ (2 * (1 - (e m : ℝ) / i)) ≤ Mbar * Mbar ^ (2 : ℕ) :=
          mul_le_mul hC_le hΛpow (Real.rpow_nonneg hΛ_nn _) hMbar_nn
        calc C * Λ ^ (2 * (1 - (e m : ℝ) / i)) ≤ Mbar * Mbar ^ (2 : ℕ) := h1
          _ = Mbar ^ (3 : ℕ) := by ring
      have hbase_nn : 0 ≤ C * Λ ^ (2 * (1 - (e m : ℝ) / i)) :=
        mul_nonneg hC_nn (Real.rpow_nonneg hΛ_nn _)
      have hIval_eq : Ival = (Ival ^ ((e m : ℝ) / i)) ^ ((i : ℝ) / (e m : ℝ)) := by
        rw [← Real.rpow_mul hIval_nn]
        rw [show ((e m : ℝ) / i) * ((i : ℝ) / (e m : ℝ)) = 1 by field_simp]
        rw [Real.rpow_one]
      have hM3_one : (1 : ℝ) ≤ Mbar ^ (3 : ℕ) :=
        le_trans hMbar1 (le_self_pow₀ hMbar1 (by norm_num))
      have hidiv : (i : ℝ) / (e m : ℝ) ≤ (i : ℝ) :=
        div_le_self hiR_pos.le (by exact_mod_cast hmpos)
      have hsplit_pow : (C * Λ ^ (2 * (1 - (e m : ℝ) / i)) * R ^ (2 * (e m : ℝ) / i))
            ^ ((i : ℝ) / (e m : ℝ)) =
          (C * Λ ^ (2 * (1 - (e m : ℝ) / i))) ^ ((i : ℝ) / (e m : ℝ)) *
            (R ^ (2 * (e m : ℝ) / i)) ^ ((i : ℝ) / (e m : ℝ)) :=
        Real.mul_rpow hbase_nn (Real.rpow_nonneg hR _)
      have hRcollapse : (R ^ (2 * (e m : ℝ) / i)) ^ ((i : ℝ) / (e m : ℝ)) = R ^ (2 : ℕ) := by
        rw [← Real.rpow_mul hR]
        rw [show (2 * (e m : ℝ) / i) * ((i : ℝ) / (e m : ℝ)) = 2 by field_simp]
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      have hbasepow : (C * Λ ^ (2 * (1 - (e m : ℝ) / i))) ^ ((i : ℝ) / (e m : ℝ)) ≤
          Mbar ^ (5 * i) := by
        calc (C * Λ ^ (2 * (1 - (e m : ℝ) / i))) ^ ((i : ℝ) / (e m : ℝ))
            ≤ (Mbar ^ (3 : ℕ)) ^ ((i : ℝ) / (e m : ℝ)) :=
              Real.rpow_le_rpow hbase_nn hbase_le (by positivity)
          _ ≤ (Mbar ^ (3 : ℕ)) ^ ((i : ℝ)) :=
              Real.rpow_le_rpow_of_exponent_le hM3_one hidiv
          _ = (Mbar ^ (3 : ℕ)) ^ (i : ℕ) := by rw [Real.rpow_natCast]
          _ = Mbar ^ (3 * i) := by rw [← pow_mul]
          _ ≤ Mbar ^ (5 * i) := pow_le_pow_right₀ hMbar1 (by omega)
      calc Ival = (Ival ^ ((e m : ℝ) / i)) ^ ((i : ℝ) / (e m : ℝ)) := hIval_eq
        _ ≤ (C * Λ ^ (2 * (1 - (e m : ℝ) / i)) * R ^ (2 * (e m : ℝ) / i))
              ^ ((i : ℝ) / (e m : ℝ)) :=
            Real.rpow_le_rpow (Real.rpow_nonneg hIval_nn _) hgn (by positivity)
        _ = (C * Λ ^ (2 * (1 - (e m : ℝ) / i))) ^ ((i : ℝ) / (e m : ℝ)) *
              (R ^ (2 * (e m : ℝ) / i)) ^ ((i : ℝ) / (e m : ℝ)) := hsplit_pow
        _ = (C * Λ ^ (2 * (1 - (e m : ℝ) / i))) ^ ((i : ℝ) / (e m : ℝ)) * R ^ (2 : ℕ) := by
            rw [hRcollapse]
        _ ≤ Mbar ^ (5 * i) * R ^ 2 := mul_le_mul_of_nonneg_right hbasepow (sq_nonneg R)
    have hSsum_factor : ∑ m ∈ Sset, ((e m : ℝ) / i) *
        (∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ) ≤
        Mbar ^ (5 * i) * R ^ 2 := by
      have hw_nn : ∀ m ∈ Sset, 0 ≤ (e m : ℝ) / i := fun m _ => by positivity
      have hw_sum : ∑ m ∈ Sset, (e m : ℝ) / i = 1 := by
        rw [← Finset.sum_div]
        rw [show (∑ m ∈ Sset, (e m : ℝ)) = ((i : ℕ) : ℝ) from by
          rw [← Nat.cast_sum]; exact_mod_cast hSsum]
        exact div_self hiR_ne
      calc ∑ m ∈ Sset, ((e m : ℝ) / i) *
            (∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ)
          ≤ ∑ m ∈ Sset, ((e m : ℝ) / i) * (Mbar ^ (5 * i) * R ^ 2) := by
            apply Finset.sum_le_sum
            intro m hm
            exact mul_le_mul_of_nonneg_left (hfactor m hm) (hw_nn m hm)
        _ = (∑ m ∈ Sset, (e m : ℝ) / i) * (Mbar ^ (5 * i) * R ^ 2) := by rw [Finset.sum_mul]
        _ = Mbar ^ (5 * i) * R ^ 2 := by rw [hw_sum, one_mul]
    have hpt2 : ∀ x : M,
        (∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ≤
          Λ ^ (2 * Zset.card) * ∑ m ∈ Sset, ((e m : ℝ) / i) *
            (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) := by
      intro x
      rw [hsplit x]
      have hZnn : 0 ≤ ∏ m ∈ Zset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x) :=
        Finset.prod_nonneg (fun m _ => hnn (e m) x)
      have hsum_nn : 0 ≤ ∑ m ∈ Sset, ((e m : ℝ) / i) *
          (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) :=
        Finset.sum_nonneg (fun m _ => mul_nonneg (by positivity) (Real.rpow_nonneg (hnn (e m) x) _))
      calc (∏ m ∈ Sset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) *
            (∏ m ∈ Zset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
          ≤ (∑ m ∈ Sset, ((e m : ℝ) / i) *
              (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ))) *
              Λ ^ (2 * Zset.card) :=
            mul_le_mul (hAMGM x) (hZbound x) hZnn hsum_nn
        _ = Λ ^ (2 * Zset.card) * ∑ m ∈ Sset, ((e m : ℝ) / i) *
              (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) :=
            mul_comm _ _
    have hsum_int : MeasureTheory.Integrable
        (fun x => ∑ m ∈ Sset, ((e m : ℝ) / i) *
          (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ))) μ := by
      apply MeasureTheory.integrable_finset_sum
      intro m _
      exact (hint_rpow (e m) ((i : ℝ) / (e m : ℝ)) (by positivity)).const_mul _
    have hint_eq : (∫ x, ∑ m ∈ Sset, ((e m : ℝ) / i) *
          (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ) =
        ∑ m ∈ Sset, ((e m : ℝ) / i) *
          (∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ) := by
      rw [MeasureTheory.integral_finset_sum]
      · apply Finset.sum_congr rfl
        intro m _; rw [MeasureTheory.integral_const_mul]
      · intro m _
        exact (hint_rpow (e m) ((i : ℝ) / (e m : ℝ)) (by positivity)).const_mul _
    have hΛZ_nn : 0 ≤ Λ ^ (2 * Zset.card) := pow_nonneg hΛ_nn _
    calc (∫ x, ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x) ∂μ)
        ≤ ∫ x, Λ ^ (2 * Zset.card) * ∑ m ∈ Sset, ((e m : ℝ) / i) *
            (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ :=
          MeasureTheory.integral_mono hint_prod (hsum_int.const_mul _) hpt2
      _ = Λ ^ (2 * Zset.card) * ∫ x, ∑ m ∈ Sset, ((e m : ℝ) / i) *
            (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ :=
          MeasureTheory.integral_const_mul _ _
      _ ≤ Λ ^ (2 * Zset.card) * (Mbar ^ (5 * i) * R ^ 2) := by
          rw [hint_eq]
          exact mul_le_mul_of_nonneg_left hSsum_factor hΛZ_nn
      _ ≤ (i : ℝ) * Mbar ^ (7 * i) * R ^ 2 := by
          have hZle : Zset.card ≤ i := le_trans (Finset.card_le_univ _) (by simpa using hn_le)
          have e1 : Λ ^ (2 * Zset.card) ≤ Mbar ^ (2 * i) :=
            le_trans (pow_le_pow_left₀ hΛ_nn hΛ_le _) (pow_le_pow_right₀ hMbar1 (by omega))
          have e3 : Mbar ^ (2 * i) * Mbar ^ (5 * i) = Mbar ^ (7 * i) := by
            rw [← pow_add]; congr 1; ring
          have e4 : Λ ^ (2 * Zset.card) * (Mbar ^ (5 * i) * R ^ 2) ≤
              Mbar ^ (2 * i) * (Mbar ^ (5 * i) * R ^ 2) :=
            mul_le_mul_of_nonneg_right e1
              (mul_nonneg (pow_nonneg hMbar_nn _) (sq_nonneg R))
          have e5 : Mbar ^ (7 * i) * R ^ 2 ≤ (i : ℝ) * Mbar ^ (7 * i) * R ^ 2 := by
            have h1i : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi1
            have hMR : 0 ≤ Mbar ^ (7 * i) * R ^ 2 :=
              mul_nonneg (pow_nonneg hMbar_nn _) (sq_nonneg R)
            calc Mbar ^ (7 * i) * R ^ 2 = 1 * (Mbar ^ (7 * i) * R ^ 2) := by ring
              _ ≤ (i : ℝ) * (Mbar ^ (7 * i) * R ^ 2) := mul_le_mul_of_nonneg_right h1i hMR
              _ = (i : ℝ) * Mbar ^ (7 * i) * R ^ 2 := by ring
          calc Λ ^ (2 * Zset.card) * (Mbar ^ (5 * i) * R ^ 2)
              ≤ Mbar ^ (2 * i) * (Mbar ^ (5 * i) * R ^ 2) := e4
            _ = Mbar ^ (7 * i) * R ^ 2 := by rw [← mul_assoc, e3]
            _ ≤ (i : ℝ) * Mbar ^ (7 * i) * R ^ 2 := e5

set_option linter.unusedVariables false in
theorem antidiagonalTupleGrid_integral_ballUniform_tameWindow
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (P : SmoothCcTensor g₀ 0 2),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ (i : ℕ),
          MeasureTheory.Integrable
              (fun x => ∑ n ∈ Finset.range (i + 1),
                ∑ e ∈ Finset.Nat.antidiagonalTuple n i,
                  ∏ m : Fin n,
                    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                      ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
              (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
            (∫ x, ∑ n ∈ Finset.range (i + 1),
                  ∑ e ∈ Finset.Nat.antidiagonalTuple n i,
                    ∏ m : Fin n,
                      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                        ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)
                ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
              K i * (1 + ∑ j ∈ Finset.range (i + 1),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  classical
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g₀
  obtain ⟨Cemb, hCemb_nn, hCemb⟩ :=
    DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.deTurckSmoothRemainderDiff_supercritical_pointwise_jet_le_fixedWindow
      (I := I) (M := M) g₀ a ha_super
  set Lam : ℝ := Cemb * Real.sqrt ((a + 1 + 1 : ℕ) : ℝ) * R with hLam
  have hLam_nn : 0 ≤ Lam := by rw [hLam]; positivity
  set Cgn : ℕ → ℝ := fun k =>
    if h : 1 ≤ k then
      (DifferentialGeometry.Analysis.Sobolev.Tensor.exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
        (I := I) (M := M) g₀ 0 2 k h).choose
    else 0 with hCgn
  have hCgn_nn : ∀ k, 0 ≤ Cgn k := by
    intro k
    simp only [hCgn]
    split_ifs with h
    · exact (DifferentialGeometry.Analysis.Sobolev.Tensor.exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
        (I := I) (M := M) g₀ 0 2 k h).choose_spec.1
    · exact le_refl 0
  set Gfun : ℕ → ℝ := fun k => (k : ℝ) * (max Lam (max (Cgn k) 1)) ^ (7 * k) with hGfun
  have hGfun_nn : ∀ k, 0 ≤ Gfun k := by
    intro k
    rw [hGfun]
    apply mul_nonneg (Nat.cast_nonneg k)
    apply pow_nonneg
    exact le_trans zero_le_one
      (le_trans (le_max_right (Cgn k) 1) (le_max_right Lam _))
  set vol : ℝ := ((riemannianVolumeMeasure (I := I) (M := M) g₀) Set.univ).toReal with hvol
  have hvol_nn : 0 ≤ vol := ENNReal.toReal_nonneg
  have hK_nn : ∀ k, 0 ≤ (∑ n ∈ Finset.range (k + 1),
      ((Finset.Nat.antidiagonalTuple n k).card : ℝ)) * Gfun k + vol := by
    intro k
    exact add_nonneg
      (mul_nonneg (Finset.sum_nonneg (fun n _ => Nat.cast_nonneg _)) (hGfun_nn k)) hvol_nn
  refine ⟨fun k => (∑ n ∈ Finset.range (k + 1),
      ((Finset.Nat.antidiagonalTuple n k).card : ℝ)) * Gfun k + vol, hK_nn, ?_⟩
  intro P hPball i
  have hwin_nn : 0 ≤ ∑ j ∈ Finset.range (i + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hone_le : (1 : ℝ) ≤ 1 + ∑ j ∈ Finset.range (i + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 := by linarith
  by_cases hi0 : i = 0
  · subst hi0
    have hgrid0 : (fun x => ∑ n ∈ Finset.range (0 + 1),
        ∑ e ∈ Finset.Nat.antidiagonalTuple n 0, ∏ m : Fin n,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) = (fun _ : M => (1 : ℝ)) := by
      funext x
      simp only [Nat.zero_add, Finset.sum_range_one, Finset.Nat.antidiagonalTuple_zero_zero,
        Finset.sum_singleton, Finset.univ_eq_empty, Finset.prod_empty]
    refine ⟨?_, ?_⟩
    · rw [hgrid0]; exact MeasureTheory.integrable_const 1
    · rw [hgrid0, MeasureTheory.integral_const, smul_eq_mul, mul_one,
        MeasureTheory.measureReal_def, ← hvol]
      calc vol ≤ ((∑ n ∈ Finset.range (0 + 1),
              ((Finset.Nat.antidiagonalTuple n 0).card : ℝ)) * Gfun 0 + vol) * 1 := by
            rw [mul_one]
            exact le_add_of_nonneg_left
              (mul_nonneg (Finset.sum_nonneg (fun n _ => Nat.cast_nonneg _)) (hGfun_nn 0))
        _ ≤ ((∑ n ∈ Finset.range (0 + 1),
              ((Finset.Nat.antidiagonalTuple n 0).card : ℝ)) * Gfun 0 + vol) *
            (1 + ∑ j ∈ Finset.range (0 + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) :=
            mul_le_mul_of_nonneg_left hone_le (hK_nn 0)
  · have hi1 : 1 ≤ i := Nat.one_le_iff_ne_zero.mpr hi0
    have hΛsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (P.toSection x) ≤
        Lam ^ 2 := by
      intro x
      have hsum_le : ∑ j ∈ Finset.range (a + 1 + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 ≤ ((a + 1 + 1 : ℕ) : ℝ) * R ^ 2 := by
        calc ∑ j ∈ Finset.range (a + 1 + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2
            ≤ ∑ j ∈ Finset.range (a + 1 + 1), R ^ 2 := by
              apply Finset.sum_le_sum
              intro j hj
              have hjle : j ≤ a + 2 := by have := Finset.mem_range.mp hj; omega
              nlinarith [norm_nonneg (iteratedCovGrad (I := I) g₀ 0 2 j P), hPball j hjle, hR]
          _ = ((a + 1 + 1 : ℕ) : ℝ) * R ^ 2 := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have hsingle : riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (P.toSection x) ≤
          ∑ m ∈ Finset.range 3, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 m P).toSection x) := by
        have h0mem : (0 : ℕ) ∈ Finset.range 3 := by norm_num
        have hsl := Finset.single_le_sum
          (f := fun m => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 m P).toSection x))
          (fun m _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + m) x _) h0mem
        simpa using hsl
      have hLam2 : Lam ^ 2 = Cemb ^ 2 * ((a + 1 + 1 : ℕ) : ℝ) * R ^ 2 := by
        rw [hLam, mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
      have hchain : ∑ m ∈ Finset.range 3, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 m P).toSection x) ≤ Lam ^ 2 := by
        refine le_trans (hCemb P x) ?_
        rw [hLam2]
        calc Cemb ^ 2 * ∑ j ∈ Finset.range (a + 1 + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2
            ≤ Cemb ^ 2 * (((a + 1 + 1 : ℕ) : ℝ) * R ^ 2) :=
              mul_le_mul_of_nonneg_left hsum_le (by positivity)
          _ = Cemb ^ 2 * ((a + 1 + 1 : ℕ) : ℝ) * R ^ 2 := by ring
      exact le_trans hsingle hchain
    have hGNspec := (DifferentialGeometry.Analysis.Sobolev.Tensor.exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
      (I := I) (M := M) g₀ 0 2 i hi1).choose_spec.2
    have hGNP : ∀ j : ℕ, 0 < j → j < i →
        (∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
                ((iteratedCovGrad (I := I) g₀ 0 2 j P).toSection x)) ^ ((i : ℝ) / (j : ℝ))
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ^ ((j : ℝ) / (i : ℝ)) ≤
          Cgn i * Lam ^ (2 * (1 - (j : ℝ) / (i : ℝ))) *
            ‖iteratedCovGrad (I := I) g₀ 0 2 i P‖ ^ (2 * (j : ℝ) / (i : ℝ)) := by
      intro j hj0 hji
      have hb := hGNspec P Lam hLam_nn hΛsup j hj0 hji
      have hchoose : (DifferentialGeometry.Analysis.Sobolev.Tensor.exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
          (I := I) (M := M) g₀ 0 2 i hi1).choose = Cgn i := by
        rw [hCgn]; simp only [dif_pos hi1]
      rw [hchoose] at hb
      have hnorm : Integral.L2.tensorL2Norm (I := I) g₀ 0 (2 + i)
          (iteratedCovGrad (I := I) g₀ 0 2 i P).toFun = ‖iteratedCovGrad (I := I) g₀ 0 2 i P‖ :=
        (SmoothCcTensor.norm_def (iteratedCovGrad (I := I) g₀ 0 2 i P)).symm
      rw [hnorm] at hb
      exact hb
    have hPT : ∀ n ∈ Finset.range (i + 1), ∀ e ∈ Finset.Nat.antidiagonalTuple n i,
        MeasureTheory.Integrable (fun x => ∏ m : Fin n,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
          (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
        (∫ x, ∏ m : Fin n,
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
          Gfun i * ‖iteratedCovGrad (I := I) g₀ 0 2 i P‖ ^ 2 := by
      intro n hn e he
      have hn_le : n ≤ i := by have := Finset.mem_range.mp hn; omega
      have hsum_e : ∑ m, e m = i := Finset.Nat.mem_antidiagonalTuple.mp he
      have hres := grid_prod_int_le (I := I) (M := M) g₀ P
        (norm_nonneg (iteratedCovGrad (I := I) g₀ 0 2 i P)) i hi1 hLam_nn hΛsup
        (le_refl _) (hCgn_nn i) hGNP n hn_le e hsum_e
      refine ⟨hres.1, ?_⟩
      refine le_trans hres.2 (le_of_eq ?_)
      simp only [hGfun]
    have hgrid_int : MeasureTheory.Integrable (fun x => ∑ n ∈ Finset.range (i + 1),
        ∑ e ∈ Finset.Nat.antidiagonalTuple n i, ∏ m : Fin n,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
        (riemannianVolumeMeasure (I := I) (M := M) g₀) := by
      apply MeasureTheory.integrable_finset_sum
      intro n hn
      apply MeasureTheory.integrable_finset_sum
      intro e he
      exact (hPT n hn e he).1
    refine ⟨hgrid_int, ?_⟩
    rw [MeasureTheory.integral_finset_sum _
      (fun n hn => MeasureTheory.integrable_finset_sum _ (fun e he => (hPT n hn e he).1))]
    have hinner : ∀ n ∈ Finset.range (i + 1),
        (∫ x, ∑ e ∈ Finset.Nat.antidiagonalTuple n i, ∏ m : Fin n,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) =
        ∑ e ∈ Finset.Nat.antidiagonalTuple n i, ∫ x, ∏ m : Fin n,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀) := by
      intro n hn
      exact MeasureTheory.integral_finset_sum _ (fun e he => (hPT n hn e he).1)
    rw [Finset.sum_congr rfl hinner]
    have hle1 : ∑ n ∈ Finset.range (i + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n i,
          (∫ x, ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
        ∑ n ∈ Finset.range (i + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n i,
          Gfun i * ‖iteratedCovGrad (I := I) g₀ 0 2 i P‖ ^ 2 := by
      apply Finset.sum_le_sum; intro n hn
      apply Finset.sum_le_sum; intro e he
      exact (hPT n hn e he).2
    have heq2 : ∑ n ∈ Finset.range (i + 1), ∑ e ∈ Finset.Nat.antidiagonalTuple n i,
          Gfun i * ‖iteratedCovGrad (I := I) g₀ 0 2 i P‖ ^ 2 =
        (∑ n ∈ Finset.range (i + 1), ((Finset.Nat.antidiagonalTuple n i).card : ℝ)) *
          (Gfun i * ‖iteratedCovGrad (I := I) g₀ 0 2 i P‖ ^ 2) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl; intro n _
      rw [Finset.sum_const, nsmul_eq_mul]
    refine le_trans hle1 ?_
    rw [heq2]
    have htop_le : ‖iteratedCovGrad (I := I) g₀ 0 2 i P‖ ^ 2 ≤
        1 + ∑ j ∈ Finset.range (i + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 := by
      have hmem : i ∈ Finset.range (i + 1) := Finset.mem_range.mpr (by omega)
      have := Finset.single_le_sum
        (f := fun j => ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2)
        (fun j _ => sq_nonneg _) hmem
      linarith
    have hcard_nn : 0 ≤ ∑ n ∈ Finset.range (i + 1),
        ((Finset.Nat.antidiagonalTuple n i).card : ℝ) :=
      Finset.sum_nonneg (fun n _ => Nat.cast_nonneg _)
    calc (∑ n ∈ Finset.range (i + 1), ((Finset.Nat.antidiagonalTuple n i).card : ℝ)) *
            (Gfun i * ‖iteratedCovGrad (I := I) g₀ 0 2 i P‖ ^ 2)
        ≤ (∑ n ∈ Finset.range (i + 1), ((Finset.Nat.antidiagonalTuple n i).card : ℝ)) *
            (Gfun i * (1 + ∑ j ∈ Finset.range (i + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2)) := by
          refine mul_le_mul_of_nonneg_left ?_ hcard_nn
          exact mul_le_mul_of_nonneg_left htop_le (hGfun_nn i)
      _ = ((∑ n ∈ Finset.range (i + 1), ((Finset.Nat.antidiagonalTuple n i).card : ℝ)) *
            Gfun i) * (1 + ∑ j ∈ Finset.range (i + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by ring
      _ ≤ ((∑ n ∈ Finset.range (i + 1), ((Finset.Nat.antidiagonalTuple n i).card : ℝ)) *
            Gfun i + vol) * (1 + ∑ j ∈ Finset.range (i + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
          refine mul_le_mul_of_nonneg_right ?_ (by linarith)
          linarith

private lemma tame_sq_le_two_add (t u v c1 c2 : ℝ) (ht : 0 ≤ t) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (htri : t ≤ u + v) (h1 : u ^ 2 ≤ c1) (h2 : v ^ 2 ≤ c2) : t ^ 2 ≤ 2 * (c1 + c2) := by
  have huv : 0 ≤ u + v := by linarith
  nlinarith [mul_le_mul htri htri ht huv, sq_nonneg (u - v), h1, h2, hu, hv]

set_option linter.unusedSectionVars false in
theorem raisedKoszul_perOrder_l2_le_iteratedCovGrad_succ
    (g₀ g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
    (n : ℕ) :
    ‖iteratedCovGrad (I := I) g₀ 1 2 n (raisedKoszul (I := I) g₀ g₁)‖ ^ 2 ≤
      10 * ‖iteratedCovGrad (I := I) g₀ 0 2 (n + 1) T‖ ^ 2 := by
  have hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + n) x
          ((iteratedCovGrad (I := I) g₀ 1 2 n (raisedKoszul (I := I) g₀ g₁)).toSection x) ≤
        10 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (n + 1)) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (n + 1) T).toSection x) := by
    intro x
    exact rfns_iteratedCovGrad_raisedKoszul_pointwise (I := I) (M := M) g₀ g₁ T htie n x
  have hF_int : MeasureTheory.Integrable
      (fun x => 10 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (n + 1)) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (n + 1) T).toSection x))
      (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    (integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 0 (2 + (n + 1))
      (iteratedCovGrad (I := I) g₀ 0 2 (n + 1) T)).const_mul _
  have key := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 1 (2 + n)
    (iteratedCovGrad (I := I) g₀ 1 2 n (raisedKoszul (I := I) g₀ g₁))
    (fun x => 10 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (n + 1)) x
      ((iteratedCovGrad (I := I) g₀ 0 2 (n + 1) T).toSection x))
    hF_int hpt
  refine le_trans key ?_
  rw [MeasureTheory.integral_const_mul]
  rw [← tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g₀ 0
    (2 + (n + 1)) (iteratedCovGrad (I := I) g₀ 0 2 (n + 1) T)]
  rw [← SmoothCcTensor.norm_def]

set_option linter.unusedVariables false in
theorem slotInsertEndoCc_ricEndoBackgroundDifferenceField_perOrder_l2_tameEnvelope
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ (i : ℕ),
          ‖iteratedCovGrad (I := I) g₀ 1 1 i
              (slotInsertEndoCc (I := I) (M := M) g₀ 0
                (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁))‖ ^ 2 ≤
            K i * (1 + ∑ j ∈ Finset.range (i + 3),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  obtain ⟨C, hC_nn, hgrid⟩ :=
    rfns_iteratedCovGrad_slotInsertEndoCc_zero_ricEndoBackgroundDifferenceField_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨Kg, hKg_nn, hKg⟩ :=
    antidiagonalTupleGrid_integral_ballUniform_tameWindow (I := I) (M := M) g₀ a ha_super hR
  refine ⟨fun i => C i * ∑ k ∈ Finset.range (i + 3), Kg k,
    fun i => mul_nonneg (hC_nn i) (Finset.sum_nonneg (fun k _ => hKg_nn k)), ?_⟩
  intro g₁ P δ hδ_le hδ htie hPball i
  have hwin_nn : 0 ≤ ∑ j ∈ Finset.range (i + 3),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  by_cases hM : Nonempty M
  · obtain ⟨x₀⟩ := hM
    have hδ0 : 0 ≤ δ := by
      obtain ⟨v, hv⟩ : ∃ v : TangentSpace I x₀, v ≠ 0 := by
        haveI : Nontrivial (TangentSpace I x₀) := by
          have hfr : 0 < Module.finrank ℝ (TangentSpace I x₀) := by
            have heq : Module.finrank ℝ (TangentSpace I x₀) = Module.finrank ℝ E := rfl
            rw [heq]; exact Nat.pos_of_ne_zero (NeZero.ne _)
          exact Module.nontrivial_of_finrank_pos hfr
        exact exists_ne 0
      have hpos : 0 < g₀.inner x₀ v v := g₀.pos x₀ v hv
      have hbound := hδ x₀ v v
      have hsqrt_pos : 0 < Real.sqrt (g₀.inner x₀ v v) := Real.sqrt_pos.mpr hpos
      have habs_nn : 0 ≤ |ccTensorBilinSymm (I := I) g₀ P x₀ v v| := abs_nonneg _
      by_contra hδc
      have hδc' : δ < 0 := lt_of_not_ge hδc
      have hrhs_neg : δ * Real.sqrt (g₀.inner x₀ v v) * Real.sqrt (g₀.inner x₀ v v) < 0 := by
        have h1 : δ * Real.sqrt (g₀.inner x₀ v v) < 0 := mul_neg_of_neg_of_pos hδc' hsqrt_pos
        exact mul_neg_of_neg_of_pos h1 hsqrt_pos
      linarith [le_trans habs_nn hbound]
    have hF_int : MeasureTheory.Integrable
        (fun x => C i * ∑ k ∈ Finset.range (i + 3),
          ∑ n ∈ Finset.range (k + 1),
            ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
              ∏ m : Fin n,
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
        (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
      (MeasureTheory.integrable_finset_sum _
        (fun k hk => (hKg P hPball k).1)).const_mul (C i)
    have key := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 1 (1 + i)
      (iteratedCovGrad (I := I) g₀ 1 1 i
        (slotInsertEndoCc (I := I) (M := M) g₀ 0
          (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁)))
      (fun x => C i * ∑ k ∈ Finset.range (i + 3),
        ∑ n ∈ Finset.range (k + 1),
          ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
            ∏ m : Fin n,
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
      hF_int
      (fun x => hgrid g₁ P htie hδ_le hδ0 hδ i x)
    refine le_trans key ?_
    rw [MeasureTheory.integral_const_mul,
      MeasureTheory.integral_finset_sum _ (fun k hk => (hKg P hPball k).1)]
    have hsum_le : ∑ k ∈ Finset.range (i + 3),
          (∫ x, ∑ n ∈ Finset.range (k + 1),
              ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
                ∏ m : Fin n,
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
        (∑ k ∈ Finset.range (i + 3), Kg k) *
          (1 + ∑ j ∈ Finset.range (i + 3), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum (fun k hk => ?_)
      refine le_trans (hKg P hPball k).2 ?_
      refine mul_le_mul_of_nonneg_left ?_ (hKg_nn k)
      have hsub : ∑ j ∈ Finset.range (k + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 ≤
          ∑ j ∈ Finset.range (i + 3), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 := by
        refine Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_mono ?_) (fun j _ _ => sq_nonneg _)
        rw [Finset.mem_range] at hk
        omega
      linarith
    calc C i * ∑ k ∈ Finset.range (i + 3),
            (∫ x, ∑ n ∈ Finset.range (k + 1),
                ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
                  ∏ m : Fin n,
                    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                      ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀))
        ≤ C i * ((∑ k ∈ Finset.range (i + 3), Kg k) *
            (1 + ∑ j ∈ Finset.range (i + 3), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left hsum_le (hC_nn i)
      _ = (C i * ∑ k ∈ Finset.range (i + 3), Kg k) *
            (1 + ∑ j ∈ Finset.range (i + 3), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
          ring
  · haveI hM' : IsEmpty M := not_nonempty_iff.mp hM
    have hz : ‖iteratedCovGrad (I := I) g₀ 1 1 i
        (slotInsertEndoCc (I := I) (M := M) g₀ 0
          (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁))‖ = 0 := by
      rw [SmoothCcTensor.norm_def, tensorL2Norm_def, tensorL2Inner,
        MeasureTheory.integral_of_isEmpty, Real.sqrt_zero]
    rw [hz]
    have hK_nn : 0 ≤ C i * ∑ k ∈ Finset.range (i + 3), Kg k :=
      mul_nonneg (hC_nn i) (Finset.sum_nonneg (fun k _ => hKg_nn k))
    nlinarith [hwin_nn, hK_nn]

set_option linter.unusedVariables false in
theorem ricciArmOrder0RiemannCoeff_backgroundDifference_perOrder_l2_tameEnvelope
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ (i : ℕ),
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
              (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2 ≤
            K i * (1 + ∑ j ∈ Finset.range (i + 3),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  obtain ⟨C, hC_nn, hgrid⟩ :=
    rfns_iteratedCovGrad_ricciArmOrder0RiemannCoeff_backgroundDifference_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨Kg, hKg_nn, hKg⟩ :=
    antidiagonalTupleGrid_integral_ballUniform_tameWindow (I := I) (M := M) g₀ a ha_super hR
  refine ⟨fun i => C i * ∑ k ∈ Finset.range (i + 3), Kg k,
    fun i => mul_nonneg (hC_nn i) (Finset.sum_nonneg (fun k _ => hKg_nn k)), ?_⟩
  intro g₁ P δ hδ_le hδ htie hPball i
  have hwin_nn : 0 ≤ ∑ j ∈ Finset.range (i + 3),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  by_cases hM : Nonempty M
  · obtain ⟨x₀⟩ := hM
    have hδ0 : 0 ≤ δ := by
      obtain ⟨v, hv⟩ : ∃ v : TangentSpace I x₀, v ≠ 0 := by
        haveI : Nontrivial (TangentSpace I x₀) := by
          have hfr : 0 < Module.finrank ℝ (TangentSpace I x₀) := by
            have heq : Module.finrank ℝ (TangentSpace I x₀) = Module.finrank ℝ E := rfl
            rw [heq]; exact Nat.pos_of_ne_zero (NeZero.ne _)
          exact Module.nontrivial_of_finrank_pos hfr
        exact exists_ne 0
      have hpos : 0 < g₀.inner x₀ v v := g₀.pos x₀ v hv
      have hbound := hδ x₀ v v
      have hsqrt_pos : 0 < Real.sqrt (g₀.inner x₀ v v) := Real.sqrt_pos.mpr hpos
      have habs_nn : 0 ≤ |ccTensorBilinSymm (I := I) g₀ P x₀ v v| := abs_nonneg _
      by_contra hδc
      have hδc' : δ < 0 := lt_of_not_ge hδc
      have hrhs_neg : δ * Real.sqrt (g₀.inner x₀ v v) * Real.sqrt (g₀.inner x₀ v v) < 0 := by
        have h1 : δ * Real.sqrt (g₀.inner x₀ v v) < 0 := mul_neg_of_neg_of_pos hδc' hsqrt_pos
        exact mul_neg_of_neg_of_pos h1 hsqrt_pos
      linarith [le_trans habs_nn hbound]
    have hF_int : MeasureTheory.Integrable
        (fun x => C i * ∑ k ∈ Finset.range (i + 3),
          ∑ n ∈ Finset.range (k + 1),
            ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
              ∏ m : Fin n,
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
        (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
      (MeasureTheory.integrable_finset_sum _
        (fun k hk => (hKg P hPball k).1)).const_mul (C i)
    have key := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 2 (2 + i)
      (iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
          ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀))
      (fun x => C i * ∑ k ∈ Finset.range (i + 3),
        ∑ n ∈ Finset.range (k + 1),
          ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
            ∏ m : Fin n,
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
      hF_int
      (fun x => hgrid g₁ P htie hδ_le hδ0 hδ i x)
    refine le_trans key ?_
    rw [MeasureTheory.integral_const_mul,
      MeasureTheory.integral_finset_sum _ (fun k hk => (hKg P hPball k).1)]
    have hsum_le : ∑ k ∈ Finset.range (i + 3),
          (∫ x, ∑ n ∈ Finset.range (k + 1),
              ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
                ∏ m : Fin n,
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
        (∑ k ∈ Finset.range (i + 3), Kg k) *
          (1 + ∑ j ∈ Finset.range (i + 3), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum (fun k hk => ?_)
      refine le_trans (hKg P hPball k).2 ?_
      refine mul_le_mul_of_nonneg_left ?_ (hKg_nn k)
      have hsub : ∑ j ∈ Finset.range (k + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 ≤
          ∑ j ∈ Finset.range (i + 3), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 := by
        refine Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_mono ?_) (fun j _ _ => sq_nonneg _)
        rw [Finset.mem_range] at hk
        omega
      linarith
    calc C i * ∑ k ∈ Finset.range (i + 3),
            (∫ x, ∑ n ∈ Finset.range (k + 1),
                ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
                  ∏ m : Fin n,
                    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                      ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀))
        ≤ C i * ((∑ k ∈ Finset.range (i + 3), Kg k) *
            (1 + ∑ j ∈ Finset.range (i + 3), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left hsum_le (hC_nn i)
      _ = (C i * ∑ k ∈ Finset.range (i + 3), Kg k) *
            (1 + ∑ j ∈ Finset.range (i + 3), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
          ring
  · haveI hM' : IsEmpty M := not_nonempty_iff.mp hM
    have hz : ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
          ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀)‖ = 0 := by
      rw [SmoothCcTensor.norm_def, tensorL2Norm_def, tensorL2Inner,
        MeasureTheory.integral_of_isEmpty, Real.sqrt_zero]
    rw [hz]
    have hK_nn : 0 ≤ C i * ∑ k ∈ Finset.range (i + 3), Kg k :=
      mul_nonneg (hC_nn i) (Finset.sum_nonneg (fun k _ => hKg_nn k))
    nlinarith [hwin_nn, hK_nn]

set_option linter.unusedVariables false in
theorem ricciArmOrder0CurvCoeff_backgroundDifference_perOrder_l2_tameEnvelope
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ (i : ℕ),
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
              (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
                ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2 ≤
            K i * (1 + ∑ j ∈ Finset.range (i + 3),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  obtain ⟨K, hK_nn, hK⟩ :=
    slotInsertEndoCc_ricEndoBackgroundDifferenceField_perOrder_l2_tameEnvelope
      (I := I) (M := M) g₀ a ha_super hR hδ₀
  refine ⟨fun i => 4 * (Module.finrank ℝ E : ℝ) * K i,
    fun i => mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (hK_nn i), ?_⟩
  intro g₁ P δ hδ_le hδ htie hPball i
  have hKi := hK g₁ P hδ_le hδ htie hPball i
  have hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 2 2 i
            (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
              ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)).toSection x) ≤
        4 * (Module.finrank ℝ E : ℝ) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
            ((iteratedCovGrad (I := I) g₀ 1 1 i
              (slotInsertEndoCc (I := I) (M := M) g₀ 0
                (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁))).toSection x) := by
    intro x
    have hsec : (iteratedCovGrad (I := I) g₀ 2 2 i
          (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
            ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)).toSection x =
        (iteratedCovGrad (I := I) g₀ 2 2 i
            (slotInsertEndoCc (I := I) (M := M) g₀ 1
              (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁))).toSection x +
          (iteratedCovGrad (I := I) g₀ 2 2 i
            (reindexCoeffGen (I := I) (M := M) g₀ 2 2
              (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
                (slotInsertEndoCc (I := I) (M := M) g₀ 1
                  (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁)))
              (Equiv.swap (0 : Fin 2) 1))).toSection x := by
      rw [ricciArmOrder0CurvCoeff_backgroundDifference_decomp (I := I) (M := M) g₀ g₁,
        iteratedCovGrad_add (I := I) g₀ 2 2 i
          (slotInsertEndoCc (I := I) (M := M) g₀ 1
            (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁))
          (reindexCoeffGen (I := I) (M := M) g₀ 2 2
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
              (slotInsertEndoCc (I := I) (M := M) g₀ 1
                (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁)))
            (Equiv.swap (0 : Fin 2) 1)),
        SmoothCcTensor.toSection_add]
      rfl
    rw [hsec]
    refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 2 (2 + i) x _ _) ?_
    have hswap : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 2 2 i
          (reindexCoeffGen (I := I) (M := M) g₀ 2 2
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
              (slotInsertEndoCc (I := I) (M := M) g₀ 1
                (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁)))
            (Equiv.swap (0 : Fin 2) 1))).toSection x) =
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 2 2 i
            (slotInsertEndoCc (I := I) (M := M) g₀ 1
              (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁))).toSection x) :=
      rfns_iteratedCovGrad_rsDomDomCongr_both_eq (I := I) (M := M) g₀ 2 2
        (Equiv.swap (0 : Fin 2) 1) (Equiv.swap (0 : Fin 2) 1)
        (slotInsertEndoCc (I := I) (M := M) g₀ 1
          (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁)) i x
    rw [hswap]
    have hendo : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 2 2 i
          (slotInsertEndoCc (I := I) (M := M) g₀ 1
            (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁))).toSection x) ≤
        (Module.finrank ℝ E : ℝ) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
            ((iteratedCovGrad (I := I) g₀ 1 1 i
              (slotInsertEndoCc (I := I) (M := M) g₀ 0
                (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁))).toSection x) := by
      have h := rfns_iteratedCovGrad_slotInsertEndoCc_le_endo (I := I) (M := M) g₀ 1
        (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁) i x
      rw [pow_one] at h
      exact h
    linarith [hendo]
  have hF_int : MeasureTheory.Integrable
      (fun x => 4 * (Module.finrank ℝ E : ℝ) *
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
          ((iteratedCovGrad (I := I) g₀ 1 1 i
            (slotInsertEndoCc (I := I) (M := M) g₀ 0
              (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁))).toSection x))
      (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    (integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 1 (1 + i)
      (iteratedCovGrad (I := I) g₀ 1 1 i
        (slotInsertEndoCc (I := I) (M := M) g₀ 0
          (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁)))).const_mul _
  have key := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 2 (2 + i)
    (iteratedCovGrad (I := I) g₀ 2 2 i
      (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
        ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀))
    (fun x => 4 * (Module.finrank ℝ E : ℝ) *
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 1 i
          (slotInsertEndoCc (I := I) (M := M) g₀ 0
            (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁))).toSection x))
    hF_int hpt
  refine le_trans key ?_
  rw [MeasureTheory.integral_const_mul]
  rw [← tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g₀ 1 (1 + i)
    (iteratedCovGrad (I := I) g₀ 1 1 i
      (slotInsertEndoCc (I := I) (M := M) g₀ 0
        (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁)))]
  rw [← SmoothCcTensor.norm_def]
  calc 4 * (Module.finrank ℝ E : ℝ) *
          ‖iteratedCovGrad (I := I) g₀ 1 1 i
            (slotInsertEndoCc (I := I) (M := M) g₀ 0
              (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁))‖ ^ 2
      ≤ 4 * (Module.finrank ℝ E : ℝ) *
          (K i * (1 + ∑ j ∈ Finset.range (i + 3),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2)) := by
        refine mul_le_mul_of_nonneg_left hKi ?_
        exact mul_nonneg (by norm_num) (Nat.cast_nonneg _)
    _ = 4 * (Module.finrank ℝ E : ℝ) * K i *
          (1 + ∑ j ∈ Finset.range (i + 3),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by ring

set_option linter.unusedVariables false in
theorem ricciArmOrder0BaseCoeff_backgroundDifference_perOrder_l2_tameEnvelope
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ (i : ℕ),
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
              ((ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁) -
                (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
                  ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀))‖ ^ 2 ≤
            K i * (1 + ∑ j ∈ Finset.range (i + 3),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  obtain ⟨KR, hKR_nn, hKR⟩ :=
    ricciArmOrder0RiemannCoeff_backgroundDifference_perOrder_l2_tameEnvelope
      (I := I) (M := M) g₀ a ha_super hR hδ₀
  obtain ⟨KC, hKC_nn, hKC⟩ :=
    ricciArmOrder0CurvCoeff_backgroundDifference_perOrder_l2_tameEnvelope
      (I := I) (M := M) g₀ a ha_super hR hδ₀
  refine ⟨fun i => 2 * (KR i + KC i), fun i => by linarith [hKR_nn i, hKC_nn i], ?_⟩
  intro g₁ P δ hδ_le hδ htie hPball i
  have hwin_nn : 0 ≤ ∑ j ∈ Finset.range (i + 3),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hR2 := hKR g₁ P hδ_le hδ htie hPball i
  have hC2 := hKC g₁ P hδ_le hδ htie hPball i
  have hre : (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
        ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁) -
      (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
        ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) =
      (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
        ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) -
      (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
        ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) := by
    abel
  rw [hre, iteratedCovGrad_sub (I := I) g₀ 2 2 i
    (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
      ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀)
    (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
      ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)]
  have hkey := tame_sq_le_two_add
    ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
          ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀)
      - iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
          ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)‖
    ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
          ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀)‖
    ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
          ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)‖
    (KR i * (1 + ∑ j ∈ Finset.range (i + 3), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2))
    (KC i * (1 + ∑ j ∈ Finset.range (i + 3), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2))
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    (norm_sub_le _ _) hR2 hC2
  refine le_trans hkey (le_of_eq ?_)
  ring

set_option linter.unusedVariables false in
theorem ricciArmOrder0BaseCoeff_perOrder_l2_tameEnvelope_generic
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ (i : ℕ),
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
              (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁)‖ ^ 2 ≤
            K i * (1 + ∑ j ∈ Finset.range (i + 3),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  obtain ⟨KD, hKD_nn, hKD⟩ :=
    ricciArmOrder0BaseCoeff_backgroundDifference_perOrder_l2_tameEnvelope
      (I := I) (M := M) g₀ a ha_super hR hδ₀
  refine ⟨fun i => 2 * (‖iteratedCovGrad (I := I) g₀ 2 2 i
      (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
        ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2 + KD i),
    fun i => by
      linarith [hKD_nn i, sq_nonneg ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
          ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)‖], ?_⟩
  intro g₁ P δ hδ_le hδ htie hPball i
  have hwin_nn : 0 ≤ ∑ j ∈ Finset.range (i + 3),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hD := hKD g₁ P hδ_le hδ htie hPball i
  have hsplit : ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
      ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ =
      (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
        ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) +
      ((ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
          ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁) -
        (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
          ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)) := by
    abel
  rw [hsplit, iteratedCovGrad_add (I := I) g₀ 2 2 i
    (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
      ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)
    ((ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
        ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁) -
      (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
        ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀))]
  have hbg_le : ‖iteratedCovGrad (I := I) g₀ 2 2 i
      (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
        ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2 ≤
      ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
          ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2 *
        (1 + ∑ j ∈ Finset.range (i + 3), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
    have hbg_nn : 0 ≤ ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
          ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2 := sq_nonneg _
    nlinarith [hbg_nn, hwin_nn]
  have hkey := tame_sq_le_two_add
    ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
          ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)
      + iteratedCovGrad (I := I) g₀ 2 2 i
        ((ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
            ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁) -
          (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
            ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀))‖
    ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
          ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)‖
    ‖iteratedCovGrad (I := I) g₀ 2 2 i
        ((ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
            ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁) -
          (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
            ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀))‖
    (‖iteratedCovGrad (I := I) g₀ 2 2 i
        (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
          ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)‖ ^ 2 *
      (1 + ∑ j ∈ Finset.range (i + 3), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2))
    (KD i * (1 + ∑ j ∈ Finset.range (i + 3), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2))
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    (norm_add_le _ _) hbg_le hD
  refine le_trans hkey (le_of_eq ?_)
  ring

section TopSeparatedTransportMirrors

set_option backward.isDefEq.respectTransparency false

set_option linter.unusedSectionVars false in
private lemma tsCastRankCc_db_refl (g₀ : SmoothRiemannianMetric I M) (r : ℕ) {a : ℕ} (h : a = a)
    (W : SmoothCcTensor g₀ r a) : castRankCc_db g₀ r h W = W := rfl

set_option linter.unusedSectionVars false in
private lemma tsCovGrad_castRankCc_db (g₀ : SmoothRiemannianMetric I M) (r : ℕ) {a b : ℕ}
    (h : a = b) (W : SmoothCcTensor g₀ r a) :
    covGrad (I := I) (M := M) g₀ r b (castRankCc_db g₀ r h W) =
      castRankCc_db g₀ r (by omega : a + 1 = b + 1)
        (covGrad (I := I) (M := M) g₀ r a W) := by
  subst h; rfl

set_option linter.unusedSectionVars false in
private lemma tsCastRankCc_db_trans (g₀ : SmoothRiemannianMetric I M) (r : ℕ) {a b c : ℕ}
    (h₁ : a = b) (h₂ : b = c) (W : SmoothCcTensor g₀ r a) :
    castRankCc_db g₀ r h₂ (castRankCc_db g₀ r h₁ W) =
      castRankCc_db g₀ r (h₁.trans h₂) W := by
  subst h₁; subst h₂; rfl

set_option linter.unusedSectionVars false in
private lemma tsCastRankCc_db_sub (g₀ : SmoothRiemannianMetric I M) (r : ℕ) {a b : ℕ}
    (h : a = b) (W W' : SmoothCcTensor g₀ r a) :
    castRankCc_db g₀ r h (W - W') = castRankCc_db g₀ r h W - castRankCc_db g₀ r h W' := by
  subst h; rfl

set_option linter.unusedSectionVars false in
private lemma tsCastRankCc_db_add (g₀ : SmoothRiemannianMetric I M) (r : ℕ) {a b : ℕ}
    (h : a = b) (W W' : SmoothCcTensor g₀ r a) :
    castRankCc_db g₀ r h (W + W') = castRankCc_db g₀ r h W + castRankCc_db g₀ r h W' := by
  subst h; rfl

set_option linter.unusedSectionVars false in
private lemma tsExists_iteratedCovGrad_domDomCongrSection (g₀ : SmoothRiemannianMetric I M)
    {s : ℕ} (σ : Equiv.Perm (Fin s)) (S : SmoothCcTensor g₀ 0 s) (i : ℕ) :
    ∃ σ' : Equiv.Perm (Fin (s + i)),
      iteratedCovGrad (I := I) g₀ 0 s i (domDomCongrSection (I := I) g₀ σ S) =
        domDomCongrSection (I := I) g₀ σ' (iteratedCovGrad (I := I) g₀ 0 s i S) := by
  obtain ⟨σ', hσ'⟩ := exists_iteratedCovGrad_unit_toModel_domDomCongr (I := I) (M := M)
    g₀ s σ S (domDomCongrSection (I := I) g₀ σ S)
    (fun y => domDomCongrSection_unitModel (I := I) g₀ σ S y) i
  refine ⟨σ', ?_⟩
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g₀
  intro x
  rw [hσ' x, domDomCongrSection_unitModel]

set_option linter.unusedSectionVars false in
private lemma tsExists_covGrad_domDomCongrSection (g₀ : SmoothRiemannianMetric I M)
    {s : ℕ} (σ : Equiv.Perm (Fin s)) (S : SmoothCcTensor g₀ 0 s) :
    ∃ σ' : Equiv.Perm (Fin (s + 1)),
      covGrad (I := I) (M := M) g₀ 0 s (domDomCongrSection (I := I) g₀ σ S) =
        domDomCongrSection (I := I) g₀ σ' (covGrad (I := I) (M := M) g₀ 0 s S) := by
  obtain ⟨σ', hσ'⟩ := tsExists_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀ σ S 1
  rw [show iteratedCovGrad (I := I) g₀ 0 s 1 (domDomCongrSection (I := I) g₀ σ S) =
      covGrad (I := I) (M := M) g₀ 0 s (domDomCongrSection (I := I) g₀ σ S) from by
    rw [iteratedCovGrad_succ, iteratedCovGrad_zero]; rfl] at hσ'
  rw [show iteratedCovGrad (I := I) g₀ 0 s 1 S =
      covGrad (I := I) (M := M) g₀ 0 s S from by
    rw [iteratedCovGrad_succ, iteratedCovGrad_zero]; rfl] at hσ'
  exact ⟨σ', hσ'⟩

set_option linter.unusedSectionVars false in
private lemma tsDomDomCongrSection_refl (g₀ : SmoothRiemannianMetric I M) {s : ℕ}
    (S : SmoothCcTensor g₀ 0 s) :
    domDomCongrSection (I := I) g₀ (Equiv.refl (Fin s)) S = S := by
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g₀
  intro x
  rw [domDomCongrSection_unitModel]
  apply ContinuousMultilinearMap.ext
  intro v
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  rfl

set_option linter.unusedSectionVars false in
private lemma tsDomDomCongrSection_comp (g₀ : SmoothRiemannianMetric I M) {s : ℕ}
    (σ τ : Equiv.Perm (Fin s)) (S : SmoothCcTensor g₀ 0 s) :
    domDomCongrSection (I := I) g₀ τ (domDomCongrSection (I := I) g₀ σ S) =
      domDomCongrSection (I := I) g₀ (σ.trans τ) S := by
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g₀
  intro x
  rw [domDomCongrSection_unitModel, domDomCongrSection_unitModel,
    domDomCongrSection_unitModel]
  apply ContinuousMultilinearMap.ext
  intro v
  simp only [ContinuousMultilinearMap.domDomCongr_apply, Equiv.trans_apply]

set_option linter.unusedSectionVars false in
private lemma tsDomDomCongrSection_sub (g₀ : SmoothRiemannianMetric I M) {s : ℕ}
    (σ : Equiv.Perm (Fin s)) (S S' : SmoothCcTensor g₀ 0 s) :
    domDomCongrSection (I := I) g₀ σ (S - S') =
      domDomCongrSection (I := I) g₀ σ S - domDomCongrSection (I := I) g₀ σ S' := by
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g₀
  intro x
  have hsub : ∀ (A B : SmoothCcTensor g₀ 0 s) (y : M),
      unitModel (I := I) (M := M) g₀ s (A - B) y =
        unitModel (I := I) (M := M) g₀ s A y - unitModel (I := I) (M := M) g₀ s B y := by
    intro A B y
    simp only [unitModel]
    rw [show ((A - B).toSection y) = A.toSection y - B.toSection y from by
      rw [SmoothCcTensor.toSection_sub]; rfl]
    rw [ContinuousLinearMap.sub_apply, Tensor0SSpace.toModel_sub]
  rw [hsub, domDomCongrSection_unitModel, domDomCongrSection_unitModel,
    domDomCongrSection_unitModel, hsub S S' x]
  apply ContinuousMultilinearMap.ext
  intro v
  simp only [ContinuousMultilinearMap.sub_apply, ContinuousMultilinearMap.domDomCongr_apply]

set_option linter.unusedSectionVars false in
private lemma tsDomDomCongrSection_add (g₀ : SmoothRiemannianMetric I M) {s : ℕ}
    (σ : Equiv.Perm (Fin s)) (S S' : SmoothCcTensor g₀ 0 s) :
    domDomCongrSection (I := I) g₀ σ (S + S') =
      domDomCongrSection (I := I) g₀ σ S + domDomCongrSection (I := I) g₀ σ S' := by
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g₀
  intro x
  have hadd : ∀ (A B : SmoothCcTensor g₀ 0 s) (y : M),
      unitModel (I := I) (M := M) g₀ s (A + B) y =
        unitModel (I := I) (M := M) g₀ s A y + unitModel (I := I) (M := M) g₀ s B y := by
    intro A B y
    simp only [unitModel]
    rw [show ((A + B).toSection y) = A.toSection y + B.toSection y from by
      rw [SmoothCcTensor.toSection_add]; rfl]
    rw [ContinuousLinearMap.add_apply, Tensor0SSpace.toModel_add]
  rw [hadd, domDomCongrSection_unitModel, domDomCongrSection_unitModel,
    domDomCongrSection_unitModel, hadd S S' x]
  apply ContinuousMultilinearMap.ext
  intro v
  simp only [ContinuousMultilinearMap.add_apply, ContinuousMultilinearMap.domDomCongr_apply]

set_option linter.unusedSectionVars false in
private lemma tsIteratedCovGrad_covGrad_eq_cast (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (W : SmoothCcTensor g₀ r s) (i : ℕ) :
    iteratedCovGrad (I := I) g₀ r (s + 1) i (covGrad (I := I) (M := M) g₀ r s W) =
      castRankCc_db g₀ r (by omega : s + (i + 1) = (s + 1) + i)
        (iteratedCovGrad (I := I) g₀ r s (i + 1) W) := by
  induction i with
  | zero =>
      rw [iteratedCovGrad_zero, iteratedCovGrad_succ, iteratedCovGrad_zero]
      rfl
  | succ i ih =>
      rw [iteratedCovGrad_succ, ih]
      rw [tsCovGrad_castRankCc_db (I := I) (M := M) g₀ r
        (by omega : s + (i + 1) = (s + 1) + i)]
      rw [show iteratedCovGrad (I := I) g₀ r s (i + 1 + 1) W =
          covGrad (I := I) (M := M) g₀ r (s + (i + 1))
            (iteratedCovGrad (I := I) g₀ r s (i + 1) W) from by
        rw [iteratedCovGrad_succ]]

set_option linter.unusedSectionVars false in
private lemma tsExists_iteratedCovGrad_rsDomDomCongrSection (g₀ : SmoothRiemannianMetric I M)
    (r s : ℕ) (σ : Equiv.Perm (Fin s)) (Z : SmoothCcTensor g₀ r s) (i : ℕ) :
    ∃ σ' : Equiv.Perm (Fin (s + i)),
      ∀ x : M,
        ((iteratedCovGrad (I := I) g₀ r s i
            (rsDomDomCongrSection (I := I) (M := M) g₀ r s σ Z)).toSection x :
          Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (s + i) I x) =
        rsDomDomCongr (I := I) (M := M) σ'
          ((iteratedCovGrad (I := I) g₀ r s i Z).toSection x) := by
  induction i with
  | zero =>
      refine ⟨σ, fun x => ?_⟩
      rw [iteratedCovGrad_zero, iteratedCovGrad_zero]
      rfl
  | succ i ih =>
      obtain ⟨σ', hσ'⟩ := ih
      refine ⟨Equiv.Perm.decomposeFin.symm (0, σ'), fun x => ?_⟩
      rw [iteratedCovGrad_succ, iteratedCovGrad_succ]
      apply ContinuousLinearMap.ext
      intro d
      apply Tensor0SSpace.toModel_injective
      apply ContinuousMultilinearMap.ext
      intro v
      have hL := covGrad_rs_toModel_domDomCongr (I := I) (M := M) g₀ r (s + i) σ'
        (iteratedCovGrad (I := I) g₀ r s i Z)
        (iteratedCovGrad (I := I) g₀ r s i
          (rsDomDomCongrSection (I := I) (M := M) g₀ r s σ Z))
        (fun y d' => by
          rw [hσ' y]
          exact toModel_rsDomDomCongr_apply (I := I) (M := M) σ' _ d') x d v
      refine hL.trans ?_
      exact (congrArg (fun f => f v) (toModel_rsDomDomCongr_apply (I := I) (M := M)
        (Equiv.Perm.decomposeFin.symm (0, σ'))
        ((covGrad (I := I) (M := M) g₀ r (s + i)
          (iteratedCovGrad (I := I) g₀ r s i Z)).toSection x) d)).symm

section TsMetricLowering

open DifferentialGeometry.Integral.DivergenceTheorem

set_option backward.isDefEq.respectTransparency false

private def tsMetricCovec (g₀ : SmoothRiemannianMetric I M) (x : M) : Tensor0SSpace 2 I x :=
  (show ContinuousMultilinearMap ℝ (fun _ : Fin 2 => TangentSpace I x) ℝ from
    { toFun := fun m => g₀.inner x (m 0) (m 1)
      map_update_add' := by
        have h01 : (0 : Fin 2) ≠ 1 := by decide
        have h10 : (1 : Fin 2) ≠ 0 := by decide
        intro _ m i a a'
        fin_cases i <;>
          simp only [Fin.reduceFinMk, Fin.isValue, Function.update_self, ne_eq,
            Function.update_of_ne, h01, h10, not_false_eq_true, map_add,
            ContinuousLinearMap.add_apply]
      map_update_smul' := by
        have h01 : (0 : Fin 2) ≠ 1 := by decide
        have h10 : (1 : Fin 2) ≠ 0 := by decide
        intro _ m i c a
        fin_cases i <;>
          simp only [Fin.reduceFinMk, Fin.isValue, Function.update_self, ne_eq,
            Function.update_of_ne, h01, h10, not_false_eq_true, map_smul,
            ContinuousLinearMap.smul_apply]
      cont := ((g₀.inner x).continuous.comp (continuous_apply 0)).clm_apply
        (continuous_apply 1) }
    : Tensor0SSpace 2 I x)

set_option linter.unusedSectionVars false in
@[simp] private lemma tsMetricCovec_apply (g₀ : SmoothRiemannianMetric I M) (x : M)
    (m : Fin 2 → TangentSpace I x) :
    tsMetricCovec (I := I) g₀ x m = g₀.inner x (m 0) (m 1) := rfl

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
private theorem tsMetricCovec_section_contMDiff (g₀ : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) x (tsMetricCovec (I := I) g₀ x)) := by
  classical
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
  refine (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
      (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
      (fun x : M => (tsMetricCovec (I := I) g₀ x :
        Bundle.continuousMultilinearMap ℝ 2 E (TangentSpace I) x))).mpr ?_
  intro σ x₀
  set b := Module.finBasis ℝ E with hb
  set e₁ := trivializationAt E (TangentSpace I : M → Type _) x₀ with he₁def
  have he₁ : x₀ ∈ e₁.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) x₀
  have hframe := e₁.isLocalFrameOn_localFrame_baseSet I (⊤ : ℕ∞) b
  obtain ⟨Y, hY⟩ := hframe.exists_contMDiffSection_eqOn_nhd e₁.open_baseSet he₁
  have hscalar : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun x : M => g₀.inner x (Y (σ 0) x) (Y (σ 1) x)) x₀ :=
    (contMDiff_g_inner_of_smooth_sections (I := I) g₀ (Y (σ 0)) (Y (σ 1))).contMDiffAt
  refine hscalar.congr_of_eventuallyEq ?_
  have h_base₁ : ∀ᶠ x in 𝓝 x₀, x ∈ e₁.baseSet := e₁.open_baseSet.mem_nhds he₁
  filter_upwards [h_base₁, hY] with x hx₁ hYx
  rw [continuousMultilinearMap_basis_repr]
  have hframeEq : ∀ k : Fin 2, e₁.symmL ℝ x (b (σ k)) = (Y (σ k)) x := by
    intro k
    rw [hYx (σ k), Trivialization.localFrame_apply_of_mem_baseSet (hx := hx₁)]
    simp [Trivialization.basisAt]
  change g₀.inner x (e₁.symmL ℝ x (b (σ 0))) (e₁.symmL ℝ x (b (σ 1))) = _
  rw [hframeEq 0, hframeEq 1]

private def tsMetricField (g₀ : SmoothRiemannianMetric I M) :
    Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) ∞ 2 :=
  letI := Tensor0SBundle.tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
  ⟨fun x => tsMetricCovec (I := I) g₀ x, tsMetricCovec_section_contMDiff (I := I) g₀⟩

private def tsMetricCc (g₀ : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 0 2 where
  toSection :=
    MixedSection.fromMultilinearSection (𝕜 := ℝ) (F := E) (IB := I)
      (E := (TangentSpace I : M → Type _)) ∞ (tsMetricField (I := I) g₀)
  hasCompactSupport := HasCompactSupport.of_compactSpace _

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
private lemma tsMetricCc_unitModel (g₀ : SmoothRiemannianMetric I M) (x : M) :
    unitModel (I := I) (M := M) g₀ 2 (tsMetricCc (I := I) (M := M) g₀) x =
      Tensor0SSpace.toModel (tsMetricCovec (I := I) g₀ x) := by
  rw [unitModel]
  rw [show (tsMetricCc (I := I) (M := M) g₀).toSection x
        (unitTensor (I := I) (M := M) x) =
      (MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight
          (tsMetricField (I := I) g₀ x)
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))
      from rfl]
  rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
    ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
  rfl

set_option linter.unusedSectionVars false in
private lemma tsToModel_om_single (x : M) (om : Tensor0SSpace 1 I x)
    (m : Fin 1 → TangentSpace I x) :
    Tensor0SSpace.toModel om (fun k => (m k : E)) =
      cotangentToDual (I := I) (x := x) om (m 0) := by
  rw [show (fun k : Fin 1 => (m k : E)) = (fun _ : Fin 1 => (m 0 : E)) from by
    funext k; fin_cases k; rfl]
  rw [cotangentToDual_apply]
  rfl

set_option linter.unusedSectionVars false in
private lemma tsMetricCovec_curry_eq_flat (g₀ : SmoothRiemannianMetric I M) (x : M)
    (v : TangentSpace I x) :
    (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x) (tsMetricCovec (I := I) g₀ x) v =
      g0FlatCLM (I := I) g₀ x v := by
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro w
  have h1 := TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (n := 1)
    (T := tsMetricCovec (I := I) g₀ x) (v0 := v) (vs := fun k => w k)
  rw [show (Tensor0SSpace.toModel
        ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x)
          (tsMetricCovec (I := I) g₀ x) v)) w =
      Tensor0SSpace.toModel (tsMetricCovec (I := I) g₀ x)
        (Fin.cons v (fun k => w k)) from h1]
  rw [tsToModel_om_single (I := I) (M := M) x (g0FlatCLM (I := I) g₀ x v) w]
  rw [cotangentToDual_g0FlatCLM]
  rfl

private noncomputable def tsLoweredSlot0 (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (Z : SmoothCcTensor g₀ 1 (s + 1)) : SmoothCcTensor g₀ 0 (s + 2) :=
  appCc (I := I) (M := M) g₀ 2 (s + 2)
    (slotExtend (I := I) (M := M) g₀ 1 (s + 1) Z) (tsMetricCc (I := I) (M := M) g₀)

set_option linter.unusedSectionVars false in
private lemma tsMetricCc_toSection_unit (g₀ : SmoothRiemannianMetric I M) (x : M) :
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
        (tsMetricCc (I := I) (M := M) g₀).toSection x)
      (unitTensor (I := I) (M := M) x) = tsMetricCovec (I := I) g₀ x := by
  apply Tensor0SSpace.toModel_injective
  have h := tsMetricCc_unitModel (I := I) (M := M) g₀ x
  rw [unitModel] at h
  exact h

set_option linter.unusedSectionVars false in
private lemma tsLoweredSlot0_unitModel_apply (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (Z : SmoothCcTensor g₀ 1 (s + 1)) (x : M) (m : Fin (s + 2) → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ (s + 2) (tsLoweredSlot0 (I := I) (M := M) g₀ s Z) x m =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace (s + 1) I x from Z.toSection x)
          (g0FlatCLM (I := I) g₀ x (m 0)))
        (Matrix.vecTail m) := by
  classical
  rw [unitModel]
  rw [show ((tsLoweredSlot0 (I := I) (M := M) g₀ s Z).toSection x
        (unitTensor (I := I) (M := M) x)) =
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace (s + 2) I x from
        (slotExtend (I := I) (M := M) g₀ 1 (s + 1) Z).toSection x)
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          (tsMetricCc (I := I) (M := M) g₀).toSection x)
          (unitTensor (I := I) (M := M) x)) from rfl]
  rw [tsMetricCc_toSection_unit (I := I) (M := M) g₀ x]
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace (s + 2) I x from
        (slotExtend (I := I) (M := M) g₀ 1 (s + 1) Z).toSection x)
        (tsMetricCovec (I := I) g₀ x)) =
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x).symm
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace (s + 1) I x from Z.toSection x).comp
          ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x)
            (tsMetricCovec (I := I) g₀ x))) from rfl]
  rw [show m = Fin.cons (m 0) (Matrix.vecTail m) from by
    funext k
    refine Fin.cases rfl (fun j => rfl) k]
  have hkey := TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M) (n := s + 1)
    (T := (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x).symm
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace (s + 1) I x from Z.toSection x).comp
        ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 1 x) (tsMetricCovec (I := I) g₀ x))))
    (v0 := m 0) (vs := Matrix.vecTail (Fin.cons (m 0) (Matrix.vecTail m)))
  rw [ContinuousLinearEquiv.apply_symm_apply] at hkey
  rw [show (Fin.cons (m 0) (Matrix.vecTail (Fin.cons (m 0) (Matrix.vecTail m)))
        : Fin (s + 2) → TangentSpace I x) =
      Fin.cons (m 0) (Matrix.vecTail m) from by
    funext k
    refine Fin.cases rfl (fun j => rfl) k] at hkey
  rw [← hkey]
  rw [ContinuousLinearMap.comp_apply]
  rw [tsMetricCovec_curry_eq_flat (I := I) (M := M) g₀ x (m 0)]
  rw [show (Matrix.vecTail (Fin.cons (m 0) (Matrix.vecTail m))
        : Fin (s + 1) → TangentSpace I x) = Matrix.vecTail m from by
    funext k
    rfl]
  rfl

set_option linter.unusedSectionVars false in
private lemma tsInteriorProduct_toModel_eval (s : ℕ) (x : M) (vv : TangentSpace I x)
    (D : Tensor0SSpace (s + 1) I x) (w : Fin s → TangentSpace I x) :
    Tensor0SSpace.toModel
        (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) s x vv D) w =
      Tensor0SSpace.toModel D (Fin.cons (show E from vv) (fun k => (show E from w k))) := by
  have h1 : Tensor0SSpace.toModel
      (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) s x vv D) =
      Tensor0SBundle.model_interior_product (𝕜 := ℝ) (E := E) s (show E from vv)
        (Tensor0SSpace.toModel D) := rfl
  rw [h1]
  rfl

set_option linter.unusedSectionVars false in
private theorem tsLoweredSlot0_cometricRaise (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (W : SmoothCcTensor g₀ 0 (s + 2)) :
    tsLoweredSlot0 (I := I) (M := M) g₀ s
        (cometricRaiseSlot0Field (I := I) (M := M) g₀ s W) = W := by
  classical
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g₀
  intro x
  apply ContinuousMultilinearMap.ext
  intro m
  rw [tsLoweredSlot0_unitModel_apply (I := I) (M := M) g₀ s
    (cometricRaiseSlot0Field (I := I) (M := M) g₀ s W) x m]
  rw [cometricRaiseSlot0Field_toSection (I := I) (M := M) g₀ s W x]
  rw [cometricRaiseSlot0Fib_clm_apply (I := I) g₀ s x
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 2) I x from W.toSection x)
      (unitTensor (I := I) (M := M) x))
    (g0FlatCLM (I := I) g₀ x (m 0))]
  rw [tsInteriorProduct_toModel_eval (I := I) (M := M) (s + 1) x
    (inverseMetricSharpFib (I := I) g₀ x (g0FlatCLM (I := I) g₀ x (m 0)))
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 2) I x from W.toSection x)
      (unitTensor (I := I) (M := M) x)) (Matrix.vecTail m)]
  rw [inverseMetricSharpFib_g0FlatCLM]
  rw [unitModel]
  refine congrArg _ ?_
  funext k
  refine Fin.cases rfl (fun j => rfl) k

set_option linter.unusedSectionVars false in
private lemma tsExists_iteratedCovGrad_cometricRaiseSlot0Field (g₀ : SmoothRiemannianMetric I M)
    (s : ℕ) (W : SmoothCcTensor g₀ 0 (s + 2)) (i : ℕ) :
    ∃ σ : Equiv.Perm (Fin ((s + i) + 2)),
      iteratedCovGrad (I := I) g₀ 1 (s + 1) i
          (cometricRaiseSlot0Field (I := I) (M := M) g₀ s W) =
        castRankCc_db g₀ 1 (by omega : (s + i) + 1 = (s + 1) + i)
          (cometricRaiseSlot0Field (I := I) (M := M) g₀ (s + i)
            (domDomCongrSection (I := I) g₀ σ
              (castRankCc_db g₀ 0 (by omega : (s + 2) + i = (s + i) + 2)
                (iteratedCovGrad (I := I) g₀ 0 (s + 2) i W)))) := by
  induction i with
  | zero =>
      refine ⟨Equiv.refl _, ?_⟩
      rw [iteratedCovGrad_zero, iteratedCovGrad_zero]
      rw [show (castRankCc_db g₀ 0 (by omega : (s + 2) + 0 = (s + 0) + 2) W) = W from rfl]
      rw [tsDomDomCongrSection_refl (I := I) (M := M) g₀ W]
      rfl
  | succ i ih =>
      obtain ⟨σ, hσ⟩ := ih
      obtain ⟨σ', hσ'⟩ := tsExists_covGrad_domDomCongrSection (I := I) (M := M) g₀ σ
        (castRankCc_db g₀ 0 (by omega : (s + 2) + i = (s + i) + 2)
          (iteratedCovGrad (I := I) g₀ 0 (s + 2) i W))
      refine ⟨σ'.trans (Equiv.swap (0 : Fin ((s + i) + 2 + 1)) 1), ?_⟩
      rw [iteratedCovGrad_succ, hσ]
      rw [tsCovGrad_castRankCc_db (I := I) (M := M) g₀ 1
        (by omega : (s + i) + 1 = (s + 1) + i)]
      rw [covGrad_cometricRaiseSlot0Field_eq (I := I) (M := M) g₀ (s + i)]
      rw [hσ']
      rw [tsDomDomCongrSection_comp (I := I) (M := M) g₀ σ'
        (Equiv.swap (0 : Fin ((s + i) + 2 + 1)) 1)]
      rw [tsCovGrad_castRankCc_db (I := I) (M := M) g₀ 0
        (by omega : (s + 2) + i = (s + i) + 2)]
      rw [← iteratedCovGrad_succ]
      rfl

end TsMetricLowering

section TsHeadTransport

open DifferentialGeometry.Integral.DivergenceTheorem

set_option backward.isDefEq.respectTransparency false

set_option linter.unusedSectionVars false in
private lemma tsRfns_order_congr (g : SmoothRiemannianMetric I M)
    (r s : ℕ) {n n' : ℕ} (h : n = n') (S : SmoothCcTensor g r s) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g r (s + n) x
        ((iteratedCovGrad (I := I) g r s n S).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g r (s + n') x
        ((iteratedCovGrad (I := I) g r s n' S).toSection x) := by
  subst h; rfl

set_option linter.unusedSectionVars false in
private lemma tsRfns_domDomCongrSection_zero (g₀ : SmoothRiemannianMetric I M) {s : ℕ}
    (σ : Equiv.Perm (Fin s)) (S : SmoothCcTensor g₀ 0 s) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 s x
        ((domDomCongrSection (I := I) g₀ σ S).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 s x (S.toSection x) := by
  have h := riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M)
    g₀ σ S 0 x
  rw [iteratedCovGrad_zero, iteratedCovGrad_zero] at h
  exact h

set_option linter.unusedSectionVars false in
private lemma tsRfns_castRankCc_db_zero (g₀ : SmoothRiemannianMetric I M) (r : ℕ) {a b : ℕ}
    (h : a = b) (W : SmoothCcTensor g₀ r a) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ r b x
        ((castRankCc_db g₀ r h W).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ r a x (W.toSection x) := by
  subst h; rfl

set_option linter.unusedSectionVars false in
private lemma tsSlotExtend_sub (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (X X' : SmoothCcTensor g₀ r s) :
    slotExtend (I := I) (M := M) g₀ r s (X - X') =
      slotExtend (I := I) (M := M) g₀ r s X - slotExtend (I := I) (M := M) g₀ r s X' := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((slotExtend (I := I) (M := M) g₀ r s X -
        slotExtend (I := I) (M := M) g₀ r s X').toSection x) =
      (slotExtend (I := I) (M := M) g₀ r s X).toSection x -
        (slotExtend (I := I) (M := M) g₀ r s X').toSection x from by
    rw [SmoothCcTensor.toSection_sub]; rfl]
  rw [slotExtend_toSection, slotExtend_toSection, slotExtend_toSection]
  have e0 : (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from (X - X').toSection x) =
      (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from X.toSection x) -
        (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from X'.toSection x) := by
    rw [SmoothCcTensor.toSection_sub]; rfl
  apply ContinuousLinearMap.ext
  intro D
  rw [show ((show Tensor0SSpace (r + 1) I x →L[ℝ] Tensor0SSpace (s + 1) I x from
        (show TensorRSSpace (r + 1) (s + 1) I x from
          slotExtendFib (I := I) (M := M) g₀ r s x
            (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from X.toSection x)) -
        (show TensorRSSpace (r + 1) (s + 1) I x from
          slotExtendFib (I := I) (M := M) g₀ r s x
            (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from X'.toSection x))) D) =
      (show Tensor0SSpace (r + 1) I x →L[ℝ] Tensor0SSpace (s + 1) I x from
        slotExtendFib (I := I) (M := M) g₀ r s x
          (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from X.toSection x)) D -
      (show Tensor0SSpace (r + 1) I x →L[ℝ] Tensor0SSpace (s + 1) I x from
        slotExtendFib (I := I) (M := M) g₀ r s x
          (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from X'.toSection x)) D from rfl]
  rw [show ((show Tensor0SSpace (r + 1) I x →L[ℝ] Tensor0SSpace (s + 1) I x from
        slotExtendFib (I := I) (M := M) g₀ r s x
          (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from (X - X').toSection x)) D) =
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x).symm
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from (X - X').toSection x).comp
          ((tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) r x) D)) from rfl]
  rw [e0, ContinuousLinearMap.sub_comp, map_sub]
  rfl

set_option linter.unusedSectionVars false in
private lemma tsAppCc_sub_left (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (Φ Φ' : SmoothCcTensor g₀ r s) (W : SmoothCcTensor g₀ 0 r) :
    appCc (I := I) (M := M) g₀ r s (Φ - Φ') W =
      appCc (I := I) (M := M) g₀ r s Φ W - appCc (I := I) (M := M) g₀ r s Φ' W := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((appCc (I := I) (M := M) g₀ r s Φ W -
        appCc (I := I) (M := M) g₀ r s Φ' W).toSection x) =
      (appCc (I := I) (M := M) g₀ r s Φ W).toSection x -
        (appCc (I := I) (M := M) g₀ r s Φ' W).toSection x from by
    rw [SmoothCcTensor.toSection_sub]; rfl]
  rw [appCc_toSection, appCc_toSection, appCc_toSection]
  rw [show ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from (Φ - Φ').toSection x)) =
      (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ.toSection x) -
        (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from Φ'.toSection x) from by
    rw [SmoothCcTensor.toSection_sub]; rfl]
  rw [ContinuousLinearMap.sub_comp]

set_option linter.unusedSectionVars false in
private lemma tsRsDomDomCongr_sub {r s : ℕ} {x : M} (σ : Equiv.Perm (Fin s))
    (T T' : TensorRSSpace r s I x) :
    rsDomDomCongr (I := I) (M := M) σ (T - T') =
      rsDomDomCongr (I := I) (M := M) σ T - rsDomDomCongr (I := I) (M := M) σ T' := by
  apply ContinuousLinearMap.ext
  intro d
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  have hL := congrArg (fun f => f v)
    (toModel_rsDomDomCongr_apply (I := I) (M := M) σ (T - T') d)
  refine hL.trans ?_
  have e1 : ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from T - T') d) =
      (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from T) d -
        (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from T') d := rfl
  have e2 : ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
        rsDomDomCongr (I := I) (M := M) σ T - rsDomDomCongr (I := I) (M := M) σ T') d) =
      (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
          rsDomDomCongr (I := I) (M := M) σ T) d -
        (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
          rsDomDomCongr (I := I) (M := M) σ T') d := rfl
  have h1 : Tensor0SSpace.toModel
      ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
        rsDomDomCongr (I := I) (M := M) σ T) d) v =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from T) d)
        (fun k => v (σ k)) := by
    have := congrArg (fun f => f v) (toModel_rsDomDomCongr_apply (I := I) (M := M) σ T d)
    refine this.trans ?_
    simp only [ContinuousMultilinearMap.domDomCongr_apply]
  have h2 : Tensor0SSpace.toModel
      ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
        rsDomDomCongr (I := I) (M := M) σ T') d) v =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from T') d)
        (fun k => v (σ k)) := by
    have := congrArg (fun f => f v) (toModel_rsDomDomCongr_apply (I := I) (M := M) σ T' d)
    refine this.trans ?_
    simp only [ContinuousMultilinearMap.domDomCongr_apply]
  calc ContinuousMultilinearMap.domDomCongr σ
        (Tensor0SSpace.toModel
          ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from T - T') d)) v
      = Tensor0SSpace.toModel
          ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from T - T') d)
          (fun k => v (σ k)) := by
        simp only [ContinuousMultilinearMap.domDomCongr_apply]
    _ = Tensor0SSpace.toModel
          ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from T) d -
            (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from T') d)
          (fun k => v (σ k)) := by rw [e1]
    _ = Tensor0SSpace.toModel
          ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from T) d)
          (fun k => v (σ k)) -
        Tensor0SSpace.toModel
          ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from T') d)
          (fun k => v (σ k)) := by
        rw [Tensor0SSpace.toModel_sub]
        simp only [ContinuousMultilinearMap.sub_apply]
    _ = Tensor0SSpace.toModel
          ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
            rsDomDomCongr (I := I) (M := M) σ T) d) v -
        Tensor0SSpace.toModel
          ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
            rsDomDomCongr (I := I) (M := M) σ T') d) v := by rw [h1, h2]
    _ = Tensor0SSpace.toModel
          ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
            rsDomDomCongr (I := I) (M := M) σ T -
              rsDomDomCongr (I := I) (M := M) σ T') d) v := by
        rw [e2, Tensor0SSpace.toModel_sub]
        simp only [ContinuousMultilinearMap.sub_apply]

set_option linter.unusedSectionVars false in
private lemma tsExists_loweredPair_headTransport (g₀ : SmoothRiemannianMetric I M)
    (σ₀ : Equiv.Perm (Fin (2 + 2)))
    (Y : SmoothCcTensor g₀ 1 (2 + 1)) (i : ℕ) (HY : SmoothCcTensor g₀ 1 ((2 + 1) + i)) :
    ∃ Hd : SmoothCcTensor g₀ 0 ((2 + 2) + i), ∀ x : M,
      (riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + 2) + i) x (Hd.toSection x) ≤
        (Module.finrank ℝ E : ℝ) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
            ((tsMetricCc (I := I) (M := M) g₀).toSection x) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 ((2 + 1) + i) x (HY.toSection x)) ∧
      (riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + 2) + i) x
          ((iteratedCovGrad (I := I) g₀ 0 (2 + 2) i
              (domDomCongrSection (I := I) g₀ σ₀
                (tsLoweredSlot0 (I := I) (M := M) g₀ 2 Y)) - Hd).toSection x) ≤
        2 * ((Module.finrank ℝ E : ℝ) *
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
              ((tsMetricCc (I := I) (M := M) g₀).toSection x) *
            riemannianFiberNormSq (I := I) (M := M) g₀ 1 ((2 + 1) + i) x
              ((iteratedCovGrad (I := I) g₀ 1 (2 + 1) i Y - HY).toSection x)) +
        2 * ((i : ℝ) * appCcGdiag (E := E) i *
            ∑ k ∈ Finset.range i,
              ((Module.finrank ℝ E : ℝ) *
                riemannianFiberNormSq (I := I) (M := M) g₀ 1 ((2 + 1) + (i - (k + 1))) x
                  ((iteratedCovGrad (I := I) g₀ 1 (2 + 1) (i - (k + 1)) Y).toSection x)) *
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (k + 1)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (k + 1)
                  (tsMetricCc (I := I) (M := M) g₀)).toSection x))) := by
  classical
  obtain ⟨σ₂, hσ₂⟩ := exists_iteratedCovGrad_slotExtend_rsDomDomCongr (I := I) (M := M)
    g₀ 1 (2 + 1) Y i
  obtain ⟨σ₁, hσ₁⟩ := tsExists_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
    σ₀ (tsLoweredSlot0 (I := I) (M := M) g₀ 2 Y) i
  set n : ℝ := (Module.finrank ℝ E : ℝ) with hn_def
  set gW : SmoothCcTensor g₀ 0 2 := tsMetricCc (I := I) (M := M) g₀ with hgW_def
  set TransHead : SmoothCcTensor g₀ (1 + 1) (((2 + 1) + 1) + i) :=
    rsDomDomCongrSection (I := I) (M := M) g₀ (1 + 1) (((2 + 1) + 1) + i) σ₂
      (castRankCc_db g₀ (1 + 1) (by omega : (((2 + 1) + i) + 1) = ((2 + 1) + 1) + i)
        (slotExtend (I := I) (M := M) g₀ 1 ((2 + 1) + i) HY)) with hTransHead_def
  refine ⟨domDomCongrSection (I := I) g₀ σ₁
    (appCc (I := I) (M := M) g₀ 2 ((2 + 2) + i) TransHead gW), fun x => ?_⟩
  have hgW_nn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (gW.toSection x) :=
    riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 2 x _
  have hn_nn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hTransHead_rfns : ∀ (V : SmoothCcTensor g₀ 1 ((2 + 1) + i)),
      riemannianFiberNormSq (I := I) (M := M) g₀ (1 + 1) (((2 + 1) + 1) + i) x
        ((rsDomDomCongrSection (I := I) (M := M) g₀ (1 + 1) (((2 + 1) + 1) + i) σ₂
          (castRankCc_db g₀ (1 + 1) (by omega : (((2 + 1) + i) + 1) = ((2 + 1) + 1) + i)
            (slotExtend (I := I) (M := M) g₀ 1 ((2 + 1) + i) V))).toSection x) =
      n * riemannianFiberNormSq (I := I) (M := M) g₀ 1 ((2 + 1) + i) x (V.toSection x) := by
    intro V
    rw [rsDomDomCongrSection_toSection]
    rw [riemannianFiberNormSq_domDomCongr_covariant (I := I) (M := M) g₀ (1 + 1)
      (((2 + 1) + 1) + i) x σ₂ _]
    rw [tsRfns_castRankCc_db_zero (I := I) (M := M) g₀ (1 + 1)
      (by omega : (((2 + 1) + i) + 1) = ((2 + 1) + 1) + i)
      (slotExtend (I := I) (M := M) g₀ 1 ((2 + 1) + i) V) x]
    rw [rfns_slotExtend_eq (I := I) (M := M) g₀ 1 ((2 + 1) + i) V x]
  constructor
  · rw [tsRfns_domDomCongrSection_zero (I := I) (M := M) g₀ σ₁ _ x]
    rw [appCc_toSection]
    refine le_trans (riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g₀ 0 2
      ((2 + 2) + i) x
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace ((2 + 2) + i) I x from
        TransHead.toSection x)
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from gW.toSection x)) ?_
    rw [hTransHead_def, hTransHead_rfns HY]
    exact le_of_eq (by ring)
  · have hcorner := iteratedCovGrad_appCc_eq_coeffCorner_add_lower (I := I) (M := M) g₀ 2
      (2 + 2) (slotExtend (I := I) (M := M) g₀ 1 (2 + 1) Y) gW i
    have hlow : tsLoweredSlot0 (I := I) (M := M) g₀ 2 Y =
        appCc (I := I) (M := M) g₀ 2 (2 + 2)
          (slotExtend (I := I) (M := M) g₀ 1 (2 + 1) Y) gW := rfl
    have hsplit : iteratedCovGrad (I := I) g₀ 0 (2 + 2) i
          (domDomCongrSection (I := I) g₀ σ₀
            (tsLoweredSlot0 (I := I) (M := M) g₀ 2 Y)) -
          domDomCongrSection (I := I) g₀ σ₁
            (appCc (I := I) (M := M) g₀ 2 ((2 + 2) + i) TransHead gW) =
        domDomCongrSection (I := I) g₀ σ₁
          (appCc (I := I) (M := M) g₀ 2 ((2 + 2) + i)
              (iteratedCovGrad (I := I) g₀ 2 (2 + 2) i
                (slotExtend (I := I) (M := M) g₀ 1 (2 + 1) Y) - TransHead) gW +
            ∑ k ∈ Finset.range i,
              appCcRS (I := I) (M := M) g₀ 0 (2 + (k + 1)) ((2 + 2) + i)
                (appCcLeibnizPsi (I := I) (M := M) g₀ 2 (2 + 2)
                  (slotExtend (I := I) (M := M) g₀ 1 (2 + 1) Y) i (k + 1))
                (iteratedCovGrad (I := I) g₀ 0 2 (k + 1) gW)) := by
      rw [hσ₁, hlow, hcorner]
      rw [← tsDomDomCongrSection_sub (I := I) (M := M) g₀ σ₁]
      refine congrArg (fun Z => domDomCongrSection (I := I) g₀ σ₁ Z) ?_
      rw [tsAppCc_sub_left (I := I) (M := M) g₀ 2 ((2 + 2) + i) _ TransHead gW]
      rw [add_sub_right_comm]
    rw [hsplit]
    rw [tsRfns_domDomCongrSection_zero (I := I) (M := M) g₀ σ₁ _ x]
    rw [show (((appCc (I := I) (M := M) g₀ 2 ((2 + 2) + i)
          (iteratedCovGrad (I := I) g₀ 2 (2 + 2) i
            (slotExtend (I := I) (M := M) g₀ 1 (2 + 1) Y) - TransHead) gW +
        ∑ k ∈ Finset.range i,
          appCcRS (I := I) (M := M) g₀ 0 (2 + (k + 1)) ((2 + 2) + i)
            (appCcLeibnizPsi (I := I) (M := M) g₀ 2 (2 + 2)
              (slotExtend (I := I) (M := M) g₀ 1 (2 + 1) Y) i (k + 1))
            (iteratedCovGrad (I := I) g₀ 0 2 (k + 1) gW)).toSection x)) =
        (appCc (I := I) (M := M) g₀ 2 ((2 + 2) + i)
          (iteratedCovGrad (I := I) g₀ 2 (2 + 2) i
            (slotExtend (I := I) (M := M) g₀ 1 (2 + 1) Y) - TransHead) gW).toSection x +
        (∑ k ∈ Finset.range i,
          appCcRS (I := I) (M := M) g₀ 0 (2 + (k + 1)) ((2 + 2) + i)
            (appCcLeibnizPsi (I := I) (M := M) g₀ 2 (2 + 2)
              (slotExtend (I := I) (M := M) g₀ 1 (2 + 1) Y) i (k + 1))
            (iteratedCovGrad (I := I) g₀ 0 2 (k + 1) gW)).toSection x from by
      rw [SmoothCcTensor.toSection_add]; rfl]
    refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 ((2 + 2) + i) x _ _) ?_
    have hA : riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + 2) + i) x
        ((appCc (I := I) (M := M) g₀ 2 ((2 + 2) + i)
          (iteratedCovGrad (I := I) g₀ 2 (2 + 2) i
            (slotExtend (I := I) (M := M) g₀ 1 (2 + 1) Y) - TransHead) gW).toSection x) ≤
        n * riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (gW.toSection x) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 ((2 + 1) + i) x
            ((iteratedCovGrad (I := I) g₀ 1 (2 + 1) i Y - HY).toSection x) := by
      rw [appCc_toSection]
      refine le_trans (riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g₀ 0 2
        ((2 + 2) + i) x _ _) ?_
      have hD : riemannianFiberNormSq (I := I) (M := M) g₀ 2 ((2 + 2) + i) x
          ((iteratedCovGrad (I := I) g₀ 2 (2 + 2) i
            (slotExtend (I := I) (M := M) g₀ 1 (2 + 1) Y) - TransHead).toSection x) =
          n * riemannianFiberNormSq (I := I) (M := M) g₀ 1 ((2 + 1) + i) x
            ((iteratedCovGrad (I := I) g₀ 1 (2 + 1) i Y - HY).toSection x) := by
        rw [show ((iteratedCovGrad (I := I) g₀ 2 (2 + 2) i
              (slotExtend (I := I) (M := M) g₀ 1 (2 + 1) Y) - TransHead).toSection x) =
            (iteratedCovGrad (I := I) g₀ 2 (2 + 2) i
              (slotExtend (I := I) (M := M) g₀ 1 (2 + 1) Y)).toSection x -
              TransHead.toSection x from by
          rw [SmoothCcTensor.toSection_sub]; rfl]
        rw [hσ₂ x]
        rw [hTransHead_def, rsDomDomCongrSection_toSection]
        rw [← tsRsDomDomCongr_sub (I := I) (M := M) σ₂]
        rw [riemannianFiberNormSq_domDomCongr_covariant (I := I) (M := M) g₀ (1 + 1)
          (((2 + 1) + 1) + i) x σ₂ _]
        rw [show ((castRankCc_db g₀ (1 + 1)
              (by omega : (((2 + 1) + i) + 1) = ((2 + 1) + 1) + i)
              (slotExtend (I := I) (M := M) g₀ 1 ((2 + 1) + i)
                (iteratedCovGrad (I := I) g₀ 1 (2 + 1) i Y))).toSection x -
            (castRankCc_db g₀ (1 + 1)
              (by omega : (((2 + 1) + i) + 1) = ((2 + 1) + 1) + i)
              (slotExtend (I := I) (M := M) g₀ 1 ((2 + 1) + i) HY)).toSection x) =
            ((castRankCc_db g₀ (1 + 1)
              (by omega : (((2 + 1) + i) + 1) = ((2 + 1) + 1) + i)
              (slotExtend (I := I) (M := M) g₀ 1 ((2 + 1) + i)
                  (iteratedCovGrad (I := I) g₀ 1 (2 + 1) i Y) -
                slotExtend (I := I) (M := M) g₀ 1 ((2 + 1) + i) HY)).toSection x) from by
          rw [tsCastRankCc_db_sub, SmoothCcTensor.toSection_sub]; rfl]
        rw [← tsSlotExtend_sub (I := I) (M := M) g₀ 1 ((2 + 1) + i)]
        rw [tsRfns_castRankCc_db_zero (I := I) (M := M) g₀ (1 + 1)
          (by omega : (((2 + 1) + i) + 1) = ((2 + 1) + 1) + i) _ x]
        rw [rfns_slotExtend_eq (I := I) (M := M) g₀ 1 ((2 + 1) + i) _ x]
      rw [hD]
      have hgWx := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 2 x (gW.toSection x)
      have hYd := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 ((2 + 1) + i) x
        ((iteratedCovGrad (I := I) g₀ 1 (2 + 1) i Y - HY).toSection x)
      exact le_of_eq (by ring)
    have tsCorrTerm_le : ∀ k ∈ Finset.range i,
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + 2) + i) x
          ((appCcRS (I := I) (M := M) g₀ 0 (2 + (k + 1)) ((2 + 2) + i)
            (appCcLeibnizPsi (I := I) (M := M) g₀ 2 (2 + 2)
              (slotExtend (I := I) (M := M) g₀ 1 (2 + 1) Y) i (k + 1))
            (iteratedCovGrad (I := I) g₀ 0 2 (k + 1) gW)).toSection x) ≤
        appCcGdiag (E := E) i *
          ((n * riemannianFiberNormSq (I := I) (M := M) g₀ 1
              ((2 + 1) + (i - (k + 1))) x
              ((iteratedCovGrad (I := I) g₀ 1 (2 + 1) (i - (k + 1)) Y).toSection x)) *
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (k + 1)) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (k + 1) gW).toSection x)) := by
      intro k hk
      have hk_le : k + 1 ≤ i := by
        rw [Finset.mem_range] at hk; omega
      rw [appCcRS_toSection]
      refine le_trans (riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g₀ 0
        (2 + (k + 1)) ((2 + 2) + i) x _ _) ?_
      have hΨ : riemannianFiberNormSq (I := I) (M := M) g₀ (2 + (k + 1)) ((2 + 2) + i) x
          ((appCcLeibnizPsi (I := I) (M := M) g₀ 2 (2 + 2)
            (slotExtend (I := I) (M := M) g₀ 1 (2 + 1) Y) i (k + 1)).toSection x) ≤
          appCcGdiag (E := E) i *
            (n * riemannianFiberNormSq (I := I) (M := M) g₀ 1
              ((2 + 1) + (i - (k + 1))) x
              ((iteratedCovGrad (I := I) g₀ 1 (2 + 1) (i - (k + 1)) Y).toSection x)) := by
        have hw := rfns_iteratedCovGrad_appCcLeibnizPsi_window_le (I := I) (M := M) g₀ 2
          (2 + 2) (slotExtend (I := I) (M := M) g₀ 1 (2 + 1) Y) i (k + 1) 0 hk_le x
        rw [iteratedCovGrad_zero] at hw
        rw [tsRfns_order_congr (I := I) (M := M) g₀ 2 (2 + 2)
          (show (i - (k + 1)) + 0 = i - (k + 1) from by omega)
          (slotExtend (I := I) (M := M) g₀ 1 (2 + 1) Y) x] at hw
        refine le_trans hw ?_
        exact mul_le_mul_of_nonneg_left
          (rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 1 (2 + 1)
            Y (i - (k + 1)) x)
          (appCcGdiag_nonneg (E := E) i)
      refine le_trans (mul_le_mul_of_nonneg_right hΨ
        (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + (k + 1)) x _)) ?_
      exact le_of_eq (by ring)
    have hB : riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + 2) + i) x
        ((∑ k ∈ Finset.range i,
          appCcRS (I := I) (M := M) g₀ 0 (2 + (k + 1)) ((2 + 2) + i)
            (appCcLeibnizPsi (I := I) (M := M) g₀ 2 (2 + 2)
              (slotExtend (I := I) (M := M) g₀ 1 (2 + 1) Y) i (k + 1))
            (iteratedCovGrad (I := I) g₀ 0 2 (k + 1) gW)).toSection x) ≤
        (i : ℝ) * appCcGdiag (E := E) i *
          ∑ k ∈ Finset.range i,
            (n * riemannianFiberNormSq (I := I) (M := M) g₀ 1 ((2 + 1) + (i - (k + 1))) x
              ((iteratedCovGrad (I := I) g₀ 1 (2 + 1) (i - (k + 1)) Y).toSection x)) *
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (k + 1)) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (k + 1) gW).toSection x) := by
      rw [SmoothCcTensor.toSection_sum_apply]
      refine le_trans (riemannianFiberNormSq_sum_le_card_mul (I := I) (M := M) g₀ 0
        ((2 + 2) + i) x (Finset.range i) _) ?_
      rw [Finset.card_range]
      calc ((i : ℕ) : ℝ) * ∑ k ∈ Finset.range i,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + 2) + i) x
              ((appCcRS (I := I) (M := M) g₀ 0 (2 + (k + 1)) ((2 + 2) + i)
                (appCcLeibnizPsi (I := I) (M := M) g₀ 2 (2 + 2)
                  (slotExtend (I := I) (M := M) g₀ 1 (2 + 1) Y) i (k + 1))
                (iteratedCovGrad (I := I) g₀ 0 2 (k + 1) gW)).toSection x)
          ≤ ((i : ℕ) : ℝ) * ∑ k ∈ Finset.range i,
              appCcGdiag (E := E) i *
                ((n * riemannianFiberNormSq (I := I) (M := M) g₀ 1
                    ((2 + 1) + (i - (k + 1))) x
                    ((iteratedCovGrad (I := I) g₀ 1 (2 + 1) (i - (k + 1)) Y).toSection x)) *
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (k + 1)) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 (k + 1) gW).toSection x)) := by
            refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun k hk => ?_))
              (Nat.cast_nonneg i)
            exact tsCorrTerm_le k hk
        _ = (i : ℝ) * appCcGdiag (E := E) i *
              ∑ k ∈ Finset.range i,
                (n * riemannianFiberNormSq (I := I) (M := M) g₀ 1
                  ((2 + 1) + (i - (k + 1))) x
                  ((iteratedCovGrad (I := I) g₀ 1 (2 + 1) (i - (k + 1)) Y).toSection x)) *
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (k + 1)) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (k + 1) gW).toSection x) := by
            rw [Finset.mul_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl (fun k _ => by ring)
    calc 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + 2) + i) x
            ((appCc (I := I) (M := M) g₀ 2 ((2 + 2) + i)
              (iteratedCovGrad (I := I) g₀ 2 (2 + 2) i
                (slotExtend (I := I) (M := M) g₀ 1 (2 + 1) Y) - TransHead) gW).toSection x) +
          2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + 2) + i) x
            ((∑ k ∈ Finset.range i,
              appCcRS (I := I) (M := M) g₀ 0 (2 + (k + 1)) ((2 + 2) + i)
                (appCcLeibnizPsi (I := I) (M := M) g₀ 2 (2 + 2)
                  (slotExtend (I := I) (M := M) g₀ 1 (2 + 1) Y) i (k + 1))
                (iteratedCovGrad (I := I) g₀ 0 2 (k + 1) gW)).toSection x)
        ≤ 2 * (n * riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (gW.toSection x) *
              riemannianFiberNormSq (I := I) (M := M) g₀ 1 ((2 + 1) + i) x
                ((iteratedCovGrad (I := I) g₀ 1 (2 + 1) i Y - HY).toSection x)) +
            2 * ((i : ℝ) * appCcGdiag (E := E) i *
              ∑ k ∈ Finset.range i,
                (n * riemannianFiberNormSq (I := I) (M := M) g₀ 1
                  ((2 + 1) + (i - (k + 1))) x
                  ((iteratedCovGrad (I := I) g₀ 1 (2 + 1) (i - (k + 1)) Y).toSection x)) *
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (k + 1)) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (k + 1) gW).toSection x)) := by
          have h2 : (0 : ℝ) ≤ 2 := by norm_num
          exact add_le_add (mul_le_mul_of_nonneg_left hA h2)
            (mul_le_mul_of_nonneg_left hB h2)
      _ = _ := by rw [hgW_def, hn_def]

end TsHeadTransport

section TsCarrierSplit

set_option backward.isDefEq.respectTransparency false

set_option linter.unusedSectionVars false in
private lemma tsConnDiff_carrier_split (g₀ g₁ : SmoothRiemannianMetric I M) (j : ℕ) :
    iteratedCovGrad (I := I) g₀ 1 2 j (connDiffSection (I := I) g₁ g₀) =
      appCcRS (I := I) (M := M) g₀ 1 1 (2 + j)
          (iteratedCovGrad (I := I) g₀ 1 2 j (raisedKoszul (I := I) g₀ g₁))
          (sharpFlatEndoCc (I := I) g₀ g₁) +
        ∑ k ∈ Finset.range j,
          appCcRS (I := I) (M := M) g₀ 1 (1 + (k + 1)) (2 + j)
            (appCcLeibnizPsi (I := I) (M := M) g₀ 1 2 (raisedKoszul (I := I) g₀ g₁) j (k + 1))
            (iteratedCovGrad (I := I) g₀ 1 1 (k + 1) (sharpFlatEndoCc (I := I) g₀ g₁)) := by
  rw [connDiffSection_eq_appCcRS_raisedKoszul_sharpFlatEndoCc (I := I) (M := M) g₀ g₁]
  rw [iteratedCovGrad_appCcRS_eq (I := I) (M := M) g₀ 1 1 2
    (raisedKoszul (I := I) g₀ g₁) (sharpFlatEndoCc (I := I) g₀ g₁) j]
  rw [Finset.sum_range_succ' (fun k =>
    appCcRS (I := I) (M := M) g₀ 1 (1 + k) (2 + j)
      (appCcLeibnizPsi (I := I) (M := M) g₀ 1 2 (raisedKoszul (I := I) g₀ g₁) j k)
      (iteratedCovGrad (I := I) g₀ 1 1 k (sharpFlatEndoCc (I := I) g₀ g₁))) j]
  have hf0 : appCcRS (I := I) (M := M) g₀ 1 (1 + 0) (2 + j)
      (appCcLeibnizPsi (I := I) (M := M) g₀ 1 2 (raisedKoszul (I := I) g₀ g₁) j 0)
      (iteratedCovGrad (I := I) g₀ 1 1 0 (sharpFlatEndoCc (I := I) g₀ g₁)) =
      appCcRS (I := I) (M := M) g₀ 1 1 (2 + j)
        (iteratedCovGrad (I := I) g₀ 1 2 j (raisedKoszul (I := I) g₀ g₁))
        (sharpFlatEndoCc (I := I) g₀ g₁) :=
    congrArg (fun Z : SmoothCcTensor g₀ 1 (2 + j) =>
      appCcRS (I := I) (M := M) g₀ 1 1 (2 + j) Z (sharpFlatEndoCc (I := I) g₀ g₁))
      (appCcLeibnizPsi_zero_right_eq (I := I) (M := M) g₀ 1 2
        (raisedKoszul (I := I) g₀ g₁) j)
  rw [hf0]
  exact add_comm _ _

set_option linter.unusedSectionVars false in
private lemma tsRfns_rsDomDomCongrSection_zero (g₀ : SmoothRiemannianMetric I M)
    (r s : ℕ) (σ : Equiv.Perm (Fin s)) (Z : SmoothCcTensor g₀ r s) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ r s x
        ((rsDomDomCongrSection (I := I) (M := M) g₀ r s σ Z).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ r s x (Z.toSection x) := by
  rw [rsDomDomCongrSection_toSection]
  exact riemannianFiberNormSq_domDomCongr_covariant (I := I) (M := M) g₀ r s x σ _

set_option linter.unusedSectionVars false in
private lemma tsRfns_iteratedCovGrad_rsDomDomCongrSection_eq
    (g₀ : SmoothRiemannianMetric I M) (r s : ℕ) (σ : Equiv.Perm (Fin s))
    (Z : SmoothCcTensor g₀ r s) (m : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ r (s + m) x
        ((iteratedCovGrad (I := I) g₀ r s m
          (rsDomDomCongrSection (I := I) (M := M) g₀ r s σ Z)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ r (s + m) x
        ((iteratedCovGrad (I := I) g₀ r s m Z).toSection x) :=
  rfns_iteratedCovGrad_rs_eq_of_section_domDomCongr (I := I) (M := M) g₀ r s σ Z
    (rsDomDomCongrSection (I := I) (M := M) g₀ r s σ Z)
    (fun y d => by
      rw [rsDomDomCongrSection_toSection, toModel_rsDomDomCongr_apply]) m x

end TsCarrierSplit

end TopSeparatedTransportMirrors

section TopSeparatedRungRLD

open DifferentialGeometry.Integral.DivergenceTheorem

set_option backward.isDefEq.respectTransparency false

private lemma tsTgridSum_le_boundedWindow (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j)
    {W₀ K W : ℕ} (hK : W₀ ≤ K + 1) (hW : W₀ ≤ W) :
    ∑ k ∈ Finset.range W₀, Combinatorics.antidiagonalTupleGrid b k ≤
      Combinatorics.boundedFactorGridWindow b K W := by
  calc ∑ k ∈ Finset.range W₀, Combinatorics.antidiagonalTupleGrid b k
      = ∑ k ∈ Finset.range W₀, Combinatorics.boundedFactorGrid b K k :=
        Finset.sum_congr rfl (fun k hk =>
          Combinatorics.antidiagonalTupleGrid_eq_boundedFactorGrid b
            (by rw [Finset.mem_range] at hk; omega))
    _ ≤ Combinatorics.boundedFactorGridWindow b K W := by
        rw [Combinatorics.boundedFactorGridWindow]
        refine Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_subset_range.mpr hW) ?_
        intro k _ _
        exact Combinatorics.boundedFactorGrid_nonneg b hb K k

private lemma tsResSum_le_boundedWindow (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) (j : ℕ) :
    ∑ k ∈ Finset.range j, b (j - k) * Combinatorics.antidiagonalTupleGrid b (k + 1) ≤
      (j : ℝ) * Combinatorics.boundedFactorGridWindow b j (j + 2) := by
  calc ∑ k ∈ Finset.range j, b (j - k) * Combinatorics.antidiagonalTupleGrid b (k + 1)
      ≤ ∑ _k ∈ Finset.range j, Combinatorics.boundedFactorGridWindow b j (j + 2) := by
        refine Finset.sum_le_sum (fun k hk => ?_)
        rw [Finset.mem_range] at hk
        rw [Combinatorics.antidiagonalTupleGrid_eq_boundedFactorGrid b
          (show k + 1 ≤ j from by omega)]
        refine le_trans (Combinatorics.single_factor_mul_boundedFactorGrid_le b hb
          (k + 1) (j - k) (by omega) (by omega)) ?_
        rw [show (k + 1) + (j - k) = j + 1 from by omega]
        exact Combinatorics.boundedFactorGrid_le_boundedFactorGridWindow b hb (by omega)
    _ = (j : ℝ) * Combinatorics.boundedFactorGridWindow b j (j + 2) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

private lemma tsRfns_sub_le (g : SmoothRiemannianMetric I M) (r s : ℕ) (x : M)
    (P Q : TensorRSSpace r s I x) :
    riemannianFiberNormSq (I := I) (M := M) g r s x (P - Q) ≤
      2 * riemannianFiberNormSq (I := I) (M := M) g r s x P +
        2 * riemannianFiberNormSq (I := I) (M := M) g r s x Q := by
  have h1 := riemannianFiberNormSq_add_le (I := I) (M := M) g r s x P (-Q)
  have h2 := rfns_neg_pt (I := I) (M := M) g r s x Q
  rw [h2] at h1
  rw [sub_eq_add_neg]
  exact h1

set_option linter.unusedVariables false in
private theorem tsExists_quad_jets (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ}
    (hδ₀ : δ₀ < 1) :
    ∃ KQ : ℕ → ℝ, (∀ m, 0 ≤ KQ m) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (m : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + m) x
            ((iteratedCovGrad (I := I) g₀ 1 3 m
              (quadraticConnDiffCc (I := I) (M := M) g₀ g₁)).toSection x) ≤
          KQ m * Combinatorics.boundedFactorGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x)) (m + 1) (m + 3) := by
  classical
  obtain ⟨CA, hCA_nn, hCA⟩ := exists_rfns_iteratedCovGrad_connDiffSection_tgrid
    (I := I) (M := M) g₀ hδ₀
  refine ⟨fun m => appCcGdiag (E := E) m *
      ∑ a ∈ Finset.range (m + 1),
        ((Module.finrank ℝ E : ℝ) * CA a) *
          ((∑ l ∈ Finset.range (m + 1 - a), CA l) *
            Combinatorics.windowPairCellCount (a + 2) ((m - a) + 2)),
    fun m => mul_nonneg (appCcGdiag_nonneg (E := E) m)
      (Finset.sum_nonneg (fun a _ => mul_nonneg
        (mul_nonneg (Nat.cast_nonneg _) (hCA_nn a))
        (mul_nonneg (Finset.sum_nonneg (fun l _ => hCA_nn l))
          (Combinatorics.windowPairCellCount_nonneg _ _)))), ?_⟩
  intro g₁ T htie δ hδ_le hδ0 hbound m x
  set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
    ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x) with hb_def
  have hb : ∀ l, 0 ≤ b l :=
    fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
  set Wfin : ℝ := Combinatorics.boundedFactorGridWindow b (m + 1) (m + 3) with hWfin_def
  have hWfin_nn : 0 ≤ Wfin := Combinatorics.boundedFactorGridWindow_nonneg b hb (m + 1) (m + 3)
  have hquad : quadraticConnDiffCc (I := I) (M := M) g₀ g₁ =
      appCcRS (I := I) (M := M) g₀ 1 2 3
        (armSlotEndoPassZeroCc (I := I) (M := M) g₀
          (connDiffArmFieldPt (I := I) (M := M) g₀ g₁))
        (connDiffSection (I := I) g₁ g₀) := rfl
  rw [hquad]
  refine le_trans (rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le
    (I := I) (M := M) g₀ m 1 2 3
    (armSlotEndoPassZeroCc (I := I) (M := M) g₀
      (connDiffArmFieldPt (I := I) (M := M) g₀ g₁))
    (connDiffSection (I := I) g₁ g₀) x) ?_
  have hterm : ∀ a ∈ Finset.range (m + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (3 + a) x
          ((iteratedCovGrad (I := I) g₀ 2 3 a
            (armSlotEndoPassZeroCc (I := I) (M := M) g₀
              (connDiffArmFieldPt (I := I) (M := M) g₀ g₁))).toSection x) *
        (∑ l ∈ Finset.range (m + 1 - a),
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + l) x
            ((iteratedCovGrad (I := I) g₀ 1 2 l
              (connDiffSection (I := I) g₁ g₀)).toSection x)) ≤
      (((Module.finrank ℝ E : ℝ) * CA a) *
        ((∑ l ∈ Finset.range (m + 1 - a), CA l) *
          Combinatorics.windowPairCellCount (a + 2) ((m - a) + 2))) * Wfin := by
    intro a ha
    rw [Finset.mem_range] at ha
    have hΦ : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (3 + a) x
        ((iteratedCovGrad (I := I) g₀ 2 3 a
          (armSlotEndoPassZeroCc (I := I) (M := M) g₀
            (connDiffArmFieldPt (I := I) (M := M) g₀ g₁))).toSection x) ≤
        ((Module.finrank ℝ E : ℝ) * CA a) *
          Combinatorics.boundedFactorGridWindow b (m + 1) (a + 2) := by
      refine le_trans (rfns_iteratedCovGrad_armSlotPass_connDiffArm_le (I := I) (M := M)
        g₀ g₁ a x) ?_
      rw [mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
      refine le_trans (hCA g₁ T htie hδ_le hδ0 hbound a x) ?_
      refine mul_le_mul_of_nonneg_left ?_ (hCA_nn a)
      exact tsTgridSum_le_boundedWindow b hb (by omega) (by omega)
    have hW : (∑ l ∈ Finset.range (m + 1 - a),
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + l) x
          ((iteratedCovGrad (I := I) g₀ 1 2 l
            (connDiffSection (I := I) g₁ g₀)).toSection x)) ≤
        (∑ l ∈ Finset.range (m + 1 - a), CA l) *
          Combinatorics.boundedFactorGridWindow b (m + 1) ((m - a) + 2) := by
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum (fun l hl => ?_)
      rw [Finset.mem_range] at hl
      refine le_trans (hCA g₁ T htie hδ_le hδ0 hbound l x) ?_
      refine mul_le_mul_of_nonneg_left ?_ (hCA_nn l)
      exact tsTgridSum_le_boundedWindow b hb (by omega) (by omega)
    have hpair : Combinatorics.boundedFactorGridWindow b (m + 1) (a + 2) *
        Combinatorics.boundedFactorGridWindow b (m + 1) ((m - a) + 2) ≤
        Combinatorics.windowPairCellCount (a + 2) ((m - a) + 2) * Wfin := by
      refine le_trans (Combinatorics.boundedFactorGridWindow_mul_le b hb (m + 1)
        (a + 2) ((m - a) + 2) (by omega) (by omega)) ?_
      refine mul_le_mul_of_nonneg_left ?_ (Combinatorics.windowPairCellCount_nonneg _ _)
      rw [hWfin_def]
      refine Combinatorics.boundedFactorGridWindow_mono b hb (le_refl _) ?_
      omega
    calc riemannianFiberNormSq (I := I) (M := M) g₀ 2 (3 + a) x
            ((iteratedCovGrad (I := I) g₀ 2 3 a
              (armSlotEndoPassZeroCc (I := I) (M := M) g₀
                (connDiffArmFieldPt (I := I) (M := M) g₀ g₁))).toSection x) *
          (∑ l ∈ Finset.range (m + 1 - a),
            riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 1 2 l
                (connDiffSection (I := I) g₁ g₀)).toSection x))
        ≤ (((Module.finrank ℝ E : ℝ) * CA a) *
            Combinatorics.boundedFactorGridWindow b (m + 1) (a + 2)) *
          ((∑ l ∈ Finset.range (m + 1 - a), CA l) *
            Combinatorics.boundedFactorGridWindow b (m + 1) ((m - a) + 2)) := by
          refine mul_le_mul hΦ hW (Finset.sum_nonneg (fun l _ =>
            riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 (2 + l) x _)) ?_
          exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hCA_nn a))
            (Combinatorics.boundedFactorGridWindow_nonneg b hb _ _)
      _ = (((Module.finrank ℝ E : ℝ) * CA a) * (∑ l ∈ Finset.range (m + 1 - a), CA l)) *
            (Combinatorics.boundedFactorGridWindow b (m + 1) (a + 2) *
              Combinatorics.boundedFactorGridWindow b (m + 1) ((m - a) + 2)) := by ring
      _ ≤ (((Module.finrank ℝ E : ℝ) * CA a) * (∑ l ∈ Finset.range (m + 1 - a), CA l)) *
            (Combinatorics.windowPairCellCount (a + 2) ((m - a) + 2) * Wfin) := by
          refine mul_le_mul_of_nonneg_left hpair ?_
          exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hCA_nn a))
            (Finset.sum_nonneg (fun l _ => hCA_nn l))
      _ = (((Module.finrank ℝ E : ℝ) * CA a) *
            ((∑ l ∈ Finset.range (m + 1 - a), CA l) *
              Combinatorics.windowPairCellCount (a + 2) ((m - a) + 2))) * Wfin := by ring
  change appCcGdiag (E := E) m *
      (∑ a ∈ Finset.range (m + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (3 + a) x
            ((iteratedCovGrad (I := I) g₀ 2 3 a
              (armSlotEndoPassZeroCc (I := I) (M := M) g₀
                (connDiffArmFieldPt (I := I) (M := M) g₀ g₁))).toSection x) *
          ∑ l ∈ Finset.range (m + 1 - a),
            riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 1 2 l
                (connDiffSection (I := I) g₁ g₀)).toSection x)) ≤
    (appCcGdiag (E := E) m *
      ∑ a ∈ Finset.range (m + 1),
        ((Module.finrank ℝ E : ℝ) * CA a) *
          ((∑ l ∈ Finset.range (m + 1 - a), CA l) *
            Combinatorics.windowPairCellCount (a + 2) ((m - a) + 2))) * Wfin
  rw [mul_assoc, Finset.sum_mul]
  refine mul_le_mul_of_nonneg_left ?_ (appCcGdiag_nonneg (E := E) m)
  exact Finset.sum_le_sum hterm

set_option linter.unusedVariables false in
private theorem tsExists_palatiniPair_jets (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ}
    (hδ₀ : δ₀ < 1) :
    ∃ KP : ℕ → ℝ, (∀ m, 0 ≤ KP m) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (m : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + m) x
            ((iteratedCovGrad (I := I) g₀ 1 3 m
              (rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (Equiv.swap (1 : Fin 3) 2)
                  (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀) +
                    quadraticConnDiffCc (I := I) (M := M) g₀ g₁) -
                rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (finRotate 3)
                  (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀) +
                    quadraticConnDiffCc (I := I) (M := M) g₀ g₁))).toSection x) ≤
          KP m * Combinatorics.boundedFactorGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x)) (m + 2) (m + 3) := by
  classical
  obtain ⟨CA, hCA_nn, hCA⟩ := exists_rfns_iteratedCovGrad_connDiffSection_tgrid
    (I := I) (M := M) g₀ hδ₀
  obtain ⟨KQ, hKQ_nn, hKQ⟩ := tsExists_quad_jets (I := I) (M := M) g₀ hδ₀
  refine ⟨fun m => 8 * (CA (m + 1) + KQ m),
    fun m => by have := hCA_nn (m + 1); have := hKQ_nn m; linarith, ?_⟩
  intro g₁ T htie δ hδ_le hδ0 hbound m x
  set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
    ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x) with hb_def
  have hb : ∀ l, 0 ≤ b l :=
    fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
  set A : SmoothCcTensor g₀ 1 3 :=
    covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀) +
      quadraticConnDiffCc (I := I) (M := M) g₀ g₁ with hA_def
  set Wfin : ℝ := Combinatorics.boundedFactorGridWindow b (m + 2) (m + 3) with hWfin_def
  have hWfin_nn : 0 ≤ Wfin :=
    Combinatorics.boundedFactorGridWindow_nonneg b hb (m + 2) (m + 3)
  have hAjets : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + m) x
      ((iteratedCovGrad (I := I) g₀ 1 3 m A).toSection x) ≤
      (2 * CA (m + 1) + 2 * KQ m) * Wfin := by
    rw [hA_def, iteratedCovGrad_add]
    rw [show ((iteratedCovGrad (I := I) g₀ 1 3 m
          (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀)) +
        iteratedCovGrad (I := I) g₀ 1 3 m
          (quadraticConnDiffCc (I := I) (M := M) g₀ g₁)).toSection x) =
        (iteratedCovGrad (I := I) g₀ 1 3 m
          (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀))).toSection x +
        (iteratedCovGrad (I := I) g₀ 1 3 m
          (quadraticConnDiffCc (I := I) (M := M) g₀ g₁)).toSection x from by
      rw [SmoothCcTensor.toSection_add]; rfl]
    refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 1 (3 + m) x _ _) ?_
    have hcd : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + m) x
        ((iteratedCovGrad (I := I) g₀ 1 3 m
          (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀))).toSection x) ≤
        CA (m + 1) * Wfin := by
      rw [tsIteratedCovGrad_covGrad_eq_cast (I := I) (M := M) g₀ 1 2
        (connDiffSection (I := I) g₁ g₀) m]
      rw [tsRfns_castRankCc_db_zero (I := I) (M := M) g₀ 1
        (by omega : 2 + (m + 1) = (2 + 1) + m)
        (iteratedCovGrad (I := I) g₀ 1 2 (m + 1) (connDiffSection (I := I) g₁ g₀)) x]
      refine le_trans (hCA g₁ T htie hδ_le hδ0 hbound (m + 1) x) ?_
      refine mul_le_mul_of_nonneg_left ?_ (hCA_nn (m + 1))
      exact tsTgridSum_le_boundedWindow b hb (by omega) (by omega)
    have hq : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + m) x
        ((iteratedCovGrad (I := I) g₀ 1 3 m
          (quadraticConnDiffCc (I := I) (M := M) g₀ g₁)).toSection x) ≤
        KQ m * Wfin := by
      refine le_trans (hKQ g₁ T htie hδ_le hδ0 hbound m x) ?_
      refine mul_le_mul_of_nonneg_left ?_ (hKQ_nn m)
      rw [hWfin_def]
      exact Combinatorics.boundedFactorGridWindow_mono b hb (by omega) (le_refl _)
    nlinarith [hcd, hq]
  rw [show ((iteratedCovGrad (I := I) g₀ 1 3 m
        (rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (Equiv.swap (1 : Fin 3) 2) A -
          rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (finRotate 3) A)).toSection x) =
      (iteratedCovGrad (I := I) g₀ 1 3 m
        (rsDomDomCongrSection (I := I) (M := M) g₀ 1 3
          (Equiv.swap (1 : Fin 3) 2) A)).toSection x -
      (iteratedCovGrad (I := I) g₀ 1 3 m
        (rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (finRotate 3) A)).toSection x from by
    rw [iteratedCovGrad_sub, SmoothCcTensor.toSection_sub]; rfl]
  refine le_trans (tsRfns_sub_le (I := I) (M := M) g₀ 1 (3 + m) x _ _) ?_
  rw [tsRfns_iteratedCovGrad_rsDomDomCongrSection_eq (I := I) (M := M) g₀ 1 3
    (Equiv.swap (1 : Fin 3) 2) A m x]
  rw [tsRfns_iteratedCovGrad_rsDomDomCongrSection_eq (I := I) (M := M) g₀ 1 3
    (finRotate 3) A m x]
  nlinarith [hAjets]

set_option linter.unusedVariables false in
theorem rfns_iteratedCovGrad_riemannLoweredBackgroundDifference_topSeparated_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Ktop : ℝ, 0 ≤ Ktop ∧ ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (i : ℕ),
        ∃ Hd : SmoothCcTensor g₀ 0 (4 + i),
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x (Hd.toSection x) ≤
              Ktop * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x)) ∧
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
                ((iteratedCovGrad (I := I) g₀ 0 4 i
                    (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁) -
                  Hd).toSection x) ≤
              Kc i * Combinatorics.boundedFactorGridWindow
                (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x)) (i + 1) (i + 3)) := by
  classical
  obtain ⟨Kt0, hKt0_nn, Kc0, hKc0_nn, hbot⟩ :=
    rfns_iteratedCovGrad_connDiffSection_topSeparated_le (I := I) (M := M) g₀ hδ₀
  obtain ⟨KP, hKP_nn, hKP⟩ := tsExists_palatiniPair_jets (I := I) (M := M) g₀ hδ₀
  obtain ⟨KQ, hKQ_nn, hKQ⟩ := tsExists_quad_jets (I := I) (M := M) g₀ hδ₀
  obtain ⟨cg, hcg_nn, hcg⟩ := exists_backgroundJet_rfns_bound (I := I) (M := M) g₀ 0 2
    (tsMetricCc (I := I) (M := M) g₀)
  set n : ℝ := (Module.finrank ℝ E : ℝ) with hn_def
  have hn_nn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  refine ⟨n * cg 0 * (4 * Kt0),
    mul_nonneg (mul_nonneg hn_nn (hcg_nn 0)) (mul_nonneg (by norm_num) hKt0_nn), ?_⟩
  refine ⟨fun i => 2 * (n * cg 0 *
      (4 * (2 * (Kc0 (i + 1) * ((i + 1 : ℕ) : ℝ)) + 2 * KQ i))) +
      2 * ((i : ℝ) * appCcGdiag (E := E) i *
        ∑ k ∈ Finset.range i, (n * KP (i - (k + 1))) * cg (k + 1)),
    fun i => by
      have h1 : (0 : ℝ) ≤ Kc0 (i + 1) * ((i + 1 : ℕ) : ℝ) :=
        mul_nonneg (hKc0_nn (i + 1)) (Nat.cast_nonneg _)
      have h2 : (0 : ℝ) ≤ KQ i := hKQ_nn i
      have h3 : (0 : ℝ) ≤ ∑ k ∈ Finset.range i, (n * KP (i - (k + 1))) * cg (k + 1) :=
        Finset.sum_nonneg (fun k _ => mul_nonneg (mul_nonneg hn_nn (hKP_nn _)) (hcg_nn _))
      have h4 : (0 : ℝ) ≤ (i : ℝ) * appCcGdiag (E := E) i :=
        mul_nonneg (Nat.cast_nonneg _) (appCcGdiag_nonneg (E := E) i)
      have h5 : (0 : ℝ) ≤ n * cg 0 := mul_nonneg hn_nn (hcg_nn 0)
      nlinarith [mul_nonneg h4 h3, mul_nonneg h5 (by linarith : (0:ℝ) ≤ 4 * (2 * (Kc0 (i + 1) * ((i + 1 : ℕ) : ℝ)) + 2 * KQ i))], ?_⟩
  intro g₁ T htie δ hδ_le hδ0 hbound i
  have hpal := riemannLoweredBackgroundDifference_palatini_repr (I := I) (M := M) g₀ g₁
  set A : SmoothCcTensor g₀ 1 3 :=
    covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀) +
      quadraticConnDiffCc (I := I) (M := M) g₀ g₁ with hA_def
  set PA : SmoothCcTensor g₀ 1 3 :=
    rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (Equiv.swap (1 : Fin 3) 2) A -
      rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (finRotate 3) A with hPA_def
  have hswap : tsLoweredSlot0 (I := I) (M := M) g₀ 2 PA =
      domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
        (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁) := by
    rw [← hpal]
    exact tsLoweredSlot0_cometricRaise (I := I) (M := M) g₀ 2 _
  have hCD4 : riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁ =
      domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
        (tsLoweredSlot0 (I := I) (M := M) g₀ 2 PA) := by
    rw [hswap, tsDomDomCongrSection_comp, Equiv.swap_swap, tsDomDomCongrSection_refl]
  set HeadCore : SmoothCcTensor g₀ 1 (2 + (i + 1)) :=
    appCcRS (I := I) (M := M) g₀ 1 1 (2 + (i + 1))
      (iteratedCovGrad (I := I) g₀ 1 2 (i + 1) (raisedKoszul (I := I) g₀ g₁))
      (sharpFlatEndoCc (I := I) g₀ g₁) with hHeadCore_def
  set HA : SmoothCcTensor g₀ 1 (3 + i) :=
    castRankCc_db g₀ 1 (by omega : 2 + (i + 1) = 3 + i) HeadCore with hHA_def
  obtain ⟨τ₁, hτ₁⟩ := tsExists_iteratedCovGrad_rsDomDomCongrSection (I := I) (M := M)
    g₀ 1 3 (Equiv.swap (1 : Fin 3) 2) A i
  obtain ⟨τ₂, hτ₂⟩ := tsExists_iteratedCovGrad_rsDomDomCongrSection (I := I) (M := M)
    g₀ 1 3 (finRotate 3) A i
  set HPA : SmoothCcTensor g₀ 1 (3 + i) :=
    rsDomDomCongrSection (I := I) (M := M) g₀ 1 (3 + i) τ₁ HA -
      rsDomDomCongrSection (I := I) (M := M) g₀ 1 (3 + i) τ₂ HA with hHPA_def
  obtain ⟨Hd, hHd⟩ := tsExists_loweredPair_headTransport (I := I) (M := M) g₀
    (Equiv.swap (0 : Fin 4) 1) PA i HPA
  refine ⟨Hd, ?_, ?_⟩
  · intro x
    have h1 := (hHd x).1
    have hHPA_rfns : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
        (HPA.toSection x) ≤
        4 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + (i + 1)) x
          (HeadCore.toSection x) := by
      rw [hHPA_def]
      rw [show ((rsDomDomCongrSection (I := I) (M := M) g₀ 1 (3 + i) τ₁ HA -
            rsDomDomCongrSection (I := I) (M := M) g₀ 1 (3 + i) τ₂ HA).toSection x) =
          (rsDomDomCongrSection (I := I) (M := M) g₀ 1 (3 + i) τ₁ HA).toSection x -
            (rsDomDomCongrSection (I := I) (M := M) g₀ 1 (3 + i) τ₂ HA).toSection x from by
        rw [SmoothCcTensor.toSection_sub]; rfl]
      refine le_trans (tsRfns_sub_le (I := I) (M := M) g₀ 1 (3 + i) x _ _) ?_
      rw [tsRfns_rsDomDomCongrSection_zero (I := I) (M := M) g₀ 1 (3 + i) τ₁ HA x,
        tsRfns_rsDomDomCongrSection_zero (I := I) (M := M) g₀ 1 (3 + i) τ₂ HA x]
      rw [hHA_def, tsRfns_castRankCc_db_zero (I := I) (M := M) g₀ 1
        (by omega : 2 + (i + 1) = 3 + i) HeadCore x]
      linarith [riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 (2 + (i + 1)) x
        (HeadCore.toSection x)]
    have hHC := (hbot g₁ T htie hδ_le hδ0 hbound (i + 1) x).1
    rw [tsRfns_order_congr (I := I) (M := M) g₀ 0 2
      (show (i + 1) + 1 = i + 2 from by omega) T x] at hHC
    have hgW := hcg 0 x
    rw [show (iteratedCovGrad (I := I) g₀ 0 2 0 (tsMetricCc (I := I) (M := M) g₀)) =
        tsMetricCc (I := I) (M := M) g₀ from iteratedCovGrad_zero (I := I) g₀ 0 2 _] at hgW
    have hb_nn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
      ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x)
    have hHC_nn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 (2 + (i + 1)) x
      (HeadCore.toSection x)
    have hgW_nn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 2 x
      ((tsMetricCc (I := I) (M := M) g₀).toSection x)
    have hHPA_nn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 (3 + i) x
      (HPA.toSection x)
    calc riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x (Hd.toSection x)
        ≤ n * riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
            ((tsMetricCc (I := I) (M := M) g₀).toSection x) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x (HPA.toSection x) := h1
      _ ≤ n * cg 0 *
          (4 * (Kt0 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x))) := by
          have hstep1 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
              (HPA.toSection x) ≤
              4 * (Kt0 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x)) := by
            refine le_trans hHPA_rfns ?_
            linarith [hHC]
          have hng : 0 ≤ n * riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
              ((tsMetricCc (I := I) (M := M) g₀).toSection x) :=
            mul_nonneg hn_nn hgW_nn
          calc n * riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
                ((tsMetricCc (I := I) (M := M) g₀).toSection x) *
                riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x (HPA.toSection x)
              ≤ n * riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
                  ((tsMetricCc (I := I) (M := M) g₀).toSection x) *
                (4 * (Kt0 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x))) :=
                mul_le_mul_of_nonneg_left hstep1 hng
            _ ≤ n * cg 0 *
                (4 * (Kt0 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x))) := by
                refine mul_le_mul_of_nonneg_right ?_ ?_
                · exact mul_le_mul_of_nonneg_left hgW hn_nn
                · exact mul_nonneg (by norm_num) (mul_nonneg hKt0_nn hb_nn)
      _ = n * cg 0 * (4 * Kt0) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x) := by ring
  · intro x
    have h2 := (hHd x).2
    set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
      ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x) with hb_def
    have hb : ∀ l, 0 ≤ b l :=
      fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
    set Wfin : ℝ := Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) with hWfin_def
    have hWfin_nn : 0 ≤ Wfin :=
      Combinatorics.boundedFactorGridWindow_nonneg b hb (i + 1) (i + 3)
    rw [show (iteratedCovGrad (I := I) g₀ 0 4 i
          (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)) =
        iteratedCovGrad (I := I) g₀ 0 4 i
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
            (tsLoweredSlot0 (I := I) (M := M) g₀ 2 PA)) from by rw [← hCD4]]
    refine le_trans h2 ?_
    have hAdiff : iteratedCovGrad (I := I) g₀ 1 3 i A - HA =
        castRankCc_db g₀ 1 (by omega : 2 + (i + 1) = 3 + i)
          (iteratedCovGrad (I := I) g₀ 1 2 (i + 1) (connDiffSection (I := I) g₁ g₀) -
            HeadCore) +
        iteratedCovGrad (I := I) g₀ 1 3 i (quadraticConnDiffCc (I := I) (M := M) g₀ g₁) := by
      rw [hA_def, iteratedCovGrad_add]
      rw [show (iteratedCovGrad (I := I) g₀ 1 3 i
            (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀))) =
          castRankCc_db g₀ 1 (by omega : 2 + (i + 1) = 3 + i)
            (iteratedCovGrad (I := I) g₀ 1 2 (i + 1) (connDiffSection (I := I) g₁ g₀))
          from tsIteratedCovGrad_covGrad_eq_cast (I := I) (M := M) g₀ 1 2
            (connDiffSection (I := I) g₁ g₀) i]
      rw [hHA_def]
      rw [tsCastRankCc_db_sub (I := I) (M := M) g₀ 1
        (by omega : 2 + (i + 1) = 3 + i)]
      exact add_sub_right_comm _ _ _
    have hdiff_pt : ((iteratedCovGrad (I := I) g₀ 1 3 i PA - HPA).toSection x :
        Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace (3 + i) I x) =
        rsDomDomCongr (I := I) (M := M) τ₁
            ((iteratedCovGrad (I := I) g₀ 1 3 i A - HA).toSection x) -
          rsDomDomCongr (I := I) (M := M) τ₂
            ((iteratedCovGrad (I := I) g₀ 1 3 i A - HA).toSection x) := by
      rw [show ((iteratedCovGrad (I := I) g₀ 1 3 i PA - HPA).toSection x) =
          (iteratedCovGrad (I := I) g₀ 1 3 i PA).toSection x - HPA.toSection x from by
        rw [SmoothCcTensor.toSection_sub]; rfl]
      rw [hPA_def, iteratedCovGrad_sub]
      rw [show ((iteratedCovGrad (I := I) g₀ 1 3 i
            (rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (Equiv.swap (1 : Fin 3) 2) A) -
          iteratedCovGrad (I := I) g₀ 1 3 i
            (rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (finRotate 3) A)).toSection x) =
          (iteratedCovGrad (I := I) g₀ 1 3 i
            (rsDomDomCongrSection (I := I) (M := M) g₀ 1 3
              (Equiv.swap (1 : Fin 3) 2) A)).toSection x -
          (iteratedCovGrad (I := I) g₀ 1 3 i
            (rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (finRotate 3) A)).toSection x
          from by rw [SmoothCcTensor.toSection_sub]; rfl]
      rw [hτ₁ x, hτ₂ x]
      rw [hHPA_def]
      rw [show ((rsDomDomCongrSection (I := I) (M := M) g₀ 1 (3 + i) τ₁ HA -
            rsDomDomCongrSection (I := I) (M := M) g₀ 1 (3 + i) τ₂ HA).toSection x) =
          (rsDomDomCongrSection (I := I) (M := M) g₀ 1 (3 + i) τ₁ HA).toSection x -
            (rsDomDomCongrSection (I := I) (M := M) g₀ 1 (3 + i) τ₂ HA).toSection x from by
        rw [SmoothCcTensor.toSection_sub]; rfl]
      rw [rsDomDomCongrSection_toSection, rsDomDomCongrSection_toSection]
      rw [show ((iteratedCovGrad (I := I) g₀ 1 3 i A - HA).toSection x) =
          (iteratedCovGrad (I := I) g₀ 1 3 i A).toSection x - HA.toSection x from by
        rw [SmoothCcTensor.toSection_sub]; rfl]
      rw [tsRsDomDomCongr_sub (I := I) (M := M) τ₁, tsRsDomDomCongr_sub (I := I) (M := M) τ₂]
      abel
    have hPAHPA : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 3 i PA - HPA).toSection x) ≤
        4 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
          ((iteratedCovGrad (I := I) g₀ 1 3 i A - HA).toSection x) := by
      rw [hdiff_pt]
      refine le_trans (tsRfns_sub_le (I := I) (M := M) g₀ 1 (3 + i) x _ _) ?_
      rw [riemannianFiberNormSq_domDomCongr_covariant (I := I) (M := M) g₀ 1 (3 + i) x τ₁ _,
        riemannianFiberNormSq_domDomCongr_covariant (I := I) (M := M) g₀ 1 (3 + i) x τ₂ _]
      linarith [riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 (3 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 3 i A - HA).toSection x)]
    have hAHA : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 3 i A - HA).toSection x) ≤
        2 * (Kc0 (i + 1) * ((i + 1 : ℕ) : ℝ)) * Wfin + 2 * KQ i * Wfin := by
      rw [hAdiff]
      rw [show ((castRankCc_db g₀ 1 (by omega : 2 + (i + 1) = 3 + i)
            (iteratedCovGrad (I := I) g₀ 1 2 (i + 1) (connDiffSection (I := I) g₁ g₀) -
              HeadCore) +
          iteratedCovGrad (I := I) g₀ 1 3 i
            (quadraticConnDiffCc (I := I) (M := M) g₀ g₁)).toSection x) =
          (castRankCc_db g₀ 1 (by omega : 2 + (i + 1) = 3 + i)
            (iteratedCovGrad (I := I) g₀ 1 2 (i + 1) (connDiffSection (I := I) g₁ g₀) -
              HeadCore)).toSection x +
          (iteratedCovGrad (I := I) g₀ 1 3 i
            (quadraticConnDiffCc (I := I) (M := M) g₀ g₁)).toSection x from by
        rw [SmoothCcTensor.toSection_add]; rfl]
      refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 1 (3 + i) x _ _) ?_
      rw [tsRfns_castRankCc_db_zero (I := I) (M := M) g₀ 1
        (by omega : 2 + (i + 1) = 3 + i) _ x]
      have hres := (hbot g₁ T htie hδ_le hδ0 hbound (i + 1) x).2
      rw [hHeadCore_def]
      have hresW : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + (i + 1)) x
          ((iteratedCovGrad (I := I) g₀ 1 2 (i + 1) (connDiffSection (I := I) g₁ g₀) -
            appCcRS (I := I) (M := M) g₀ 1 1 (2 + (i + 1))
              (iteratedCovGrad (I := I) g₀ 1 2 (i + 1) (raisedKoszul (I := I) g₀ g₁))
              (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x) ≤
          Kc0 (i + 1) * (((i + 1 : ℕ) : ℝ) * Wfin) := by
        refine le_trans hres ?_
        refine mul_le_mul_of_nonneg_left ?_ (hKc0_nn (i + 1))
        refine le_trans (tsResSum_le_boundedWindow b hb (i + 1)) ?_
        rw [show (i + 1) + 2 = i + 3 from by omega]
      have hqW := hKQ g₁ T htie hδ_le hδ0 hbound i x
      nlinarith [hresW, hqW, hWfin_nn, hKc0_nn (i + 1), hKQ_nn i]
    have hcorr : ∀ k ∈ Finset.range i,
        (n * riemannianFiberNormSq (I := I) (M := M) g₀ 1 ((2 + 1) + (i - (k + 1))) x
          ((iteratedCovGrad (I := I) g₀ 1 (2 + 1) (i - (k + 1)) PA).toSection x)) *
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (k + 1)) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (k + 1)
            (tsMetricCc (I := I) (M := M) g₀)).toSection x) ≤
        ((n * KP (i - (k + 1))) * cg (k + 1)) * Wfin := by
      intro k hk
      rw [Finset.mem_range] at hk
      have hPAj : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + (i - (k + 1))) x
          ((iteratedCovGrad (I := I) g₀ 1 3 (i - (k + 1)) PA).toSection x) ≤
          KP (i - (k + 1)) * Wfin := by
        rw [hPA_def, hA_def]
        refine le_trans (hKP g₁ T htie hδ_le hδ0 hbound (i - (k + 1)) x) ?_
        refine mul_le_mul_of_nonneg_left ?_ (hKP_nn (i - (k + 1)))
        rw [hWfin_def]
        exact Combinatorics.boundedFactorGridWindow_mono b hb (by omega) (by omega)
      have hgj := hcg (k + 1) x
      have hPAj_nn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1
        (3 + (i - (k + 1))) x
        ((iteratedCovGrad (I := I) g₀ 1 3 (i - (k + 1)) PA).toSection x)
      have hgj_nn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + (k + 1)) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (k + 1)
          (tsMetricCc (I := I) (M := M) g₀)).toSection x)
      calc (n * riemannianFiberNormSq (I := I) (M := M) g₀ 1 ((2 + 1) + (i - (k + 1))) x
            ((iteratedCovGrad (I := I) g₀ 1 (2 + 1) (i - (k + 1)) PA).toSection x)) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (k + 1)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (k + 1)
              (tsMetricCc (I := I) (M := M) g₀)).toSection x)
          ≤ (n * (KP (i - (k + 1)) * Wfin)) * cg (k + 1) := by
            refine mul_le_mul ?_ hgj hgj_nn ?_
            · exact mul_le_mul_of_nonneg_left hPAj hn_nn
            · exact mul_nonneg hn_nn (mul_nonneg (hKP_nn _) hWfin_nn)
        _ = ((n * KP (i - (k + 1))) * cg (k + 1)) * Wfin := by ring
    have hterm2 : (∑ k ∈ Finset.range i,
        (n * riemannianFiberNormSq (I := I) (M := M) g₀ 1 ((2 + 1) + (i - (k + 1))) x
          ((iteratedCovGrad (I := I) g₀ 1 (2 + 1) (i - (k + 1)) PA).toSection x)) *
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (k + 1)) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (k + 1)
            (tsMetricCc (I := I) (M := M) g₀)).toSection x)) ≤
        (∑ k ∈ Finset.range i, (n * KP (i - (k + 1))) * cg (k + 1)) * Wfin := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum hcorr
    have hterm1 : n * riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
          ((tsMetricCc (I := I) (M := M) g₀).toSection x) *
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 ((2 + 1) + i) x
          ((iteratedCovGrad (I := I) g₀ 1 (2 + 1) i PA - HPA).toSection x) ≤
        n * cg 0 * (4 * (2 * (Kc0 (i + 1) * ((i + 1 : ℕ) : ℝ)) * Wfin +
          2 * KQ i * Wfin)) := by
      have hgW := hcg 0 x
      rw [show (iteratedCovGrad (I := I) g₀ 0 2 0 (tsMetricCc (I := I) (M := M) g₀)) =
          tsMetricCc (I := I) (M := M) g₀ from iteratedCovGrad_zero (I := I) g₀ 0 2 _] at hgW
      have hd_le : riemannianFiberNormSq (I := I) (M := M) g₀ 1 ((2 + 1) + i) x
          ((iteratedCovGrad (I := I) g₀ 1 (2 + 1) i PA - HPA).toSection x) ≤
          4 * (2 * (Kc0 (i + 1) * ((i + 1 : ℕ) : ℝ)) * Wfin + 2 * KQ i * Wfin) := by
        refine le_trans hPAHPA ?_
        nlinarith [hAHA, riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 (3 + i) x
          ((iteratedCovGrad (I := I) g₀ 1 3 i A - HA).toSection x)]
      have hgW_nn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 2 x
        ((tsMetricCc (I := I) (M := M) g₀).toSection x)
      have hd_nn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 ((2 + 1) + i) x
        ((iteratedCovGrad (I := I) g₀ 1 (2 + 1) i PA - HPA).toSection x)
      calc n * riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
            ((tsMetricCc (I := I) (M := M) g₀).toSection x) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 ((2 + 1) + i) x
            ((iteratedCovGrad (I := I) g₀ 1 (2 + 1) i PA - HPA).toSection x)
          ≤ n * riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
              ((tsMetricCc (I := I) (M := M) g₀).toSection x) *
            (4 * (2 * (Kc0 (i + 1) * ((i + 1 : ℕ) : ℝ)) * Wfin + 2 * KQ i * Wfin)) :=
            mul_le_mul_of_nonneg_left hd_le (mul_nonneg hn_nn hgW_nn)
        _ ≤ n * cg 0 * (4 * (2 * (Kc0 (i + 1) * ((i + 1 : ℕ) : ℝ)) * Wfin +
            2 * KQ i * Wfin)) := by
            refine mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hgW hn_nn) ?_
            have h1 : (0 : ℝ) ≤ 2 * (Kc0 (i + 1) * ((i + 1 : ℕ) : ℝ)) * Wfin :=
              mul_nonneg (mul_nonneg (by norm_num)
                (mul_nonneg (hKc0_nn _) (Nat.cast_nonneg _))) hWfin_nn
            have h2 : (0 : ℝ) ≤ 2 * KQ i * Wfin :=
              mul_nonneg (mul_nonneg (by norm_num) (hKQ_nn i)) hWfin_nn
            linarith
    calc 2 * (n * riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
            ((tsMetricCc (I := I) (M := M) g₀).toSection x) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 ((2 + 1) + i) x
            ((iteratedCovGrad (I := I) g₀ 1 (2 + 1) i PA - HPA).toSection x)) +
        2 * ((i : ℝ) * appCcGdiag (E := E) i *
          ∑ k ∈ Finset.range i,
            (n * riemannianFiberNormSq (I := I) (M := M) g₀ 1 ((2 + 1) + (i - (k + 1))) x
              ((iteratedCovGrad (I := I) g₀ 1 (2 + 1) (i - (k + 1)) PA).toSection x)) *
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (k + 1)) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (k + 1)
                (tsMetricCc (I := I) (M := M) g₀)).toSection x))
        ≤ 2 * (n * cg 0 * (4 * (2 * (Kc0 (i + 1) * ((i + 1 : ℕ) : ℝ)) * Wfin +
            2 * KQ i * Wfin))) +
          2 * ((i : ℝ) * appCcGdiag (E := E) i *
            ((∑ k ∈ Finset.range i, (n * KP (i - (k + 1))) * cg (k + 1)) * Wfin)) := by
          refine add_le_add (mul_le_mul_of_nonneg_left hterm1 (by norm_num)) ?_
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          exact mul_le_mul_of_nonneg_left hterm2
            (mul_nonneg (Nat.cast_nonneg _) (appCcGdiag_nonneg (E := E) i))
      _ = (2 * (n * cg 0 *
            (4 * (2 * (Kc0 (i + 1) * ((i + 1 : ℕ) : ℝ)) + 2 * KQ i))) +
          2 * ((i : ℝ) * appCcGdiag (E := E) i *
            ∑ k ∈ Finset.range i, (n * KP (i - (k + 1))) * cg (k + 1))) * Wfin := by
          ring

end TopSeparatedRungRLD

section TopSeparatedRungSlotInsert

open DifferentialGeometry.Integral.DivergenceTheorem

set_option backward.isDefEq.respectTransparency false

set_option linter.unusedSectionVars false in
private lemma tsCometricRaise_sub (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (W W' : SmoothCcTensor g₀ 0 (s + 2)) :
    cometricRaiseSlot0Field (I := I) (M := M) g₀ s (W - W') =
      cometricRaiseSlot0Field (I := I) (M := M) g₀ s W -
        cometricRaiseSlot0Field (I := I) (M := M) g₀ s W' := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((cometricRaiseSlot0Field (I := I) (M := M) g₀ s W -
        cometricRaiseSlot0Field (I := I) (M := M) g₀ s W').toSection x) =
      (cometricRaiseSlot0Field (I := I) (M := M) g₀ s W).toSection x -
        (cometricRaiseSlot0Field (I := I) (M := M) g₀ s W').toSection x from by
    rw [SmoothCcTensor.toSection_sub]; rfl]
  rw [cometricRaiseSlot0Field_toSection, cometricRaiseSlot0Field_toSection,
    cometricRaiseSlot0Field_toSection]
  rw [show ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 2) I x from
        (W - W').toSection x) (unitTensor (I := I) (M := M) x)) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 2) I x from W.toSection x)
          (unitTensor (I := I) (M := M) x) -
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 2) I x from W'.toSection x)
          (unitTensor (I := I) (M := M) x) from by
    rw [show ((W - W').toSection x) = W.toSection x - W'.toSection x from by
      rw [SmoothCcTensor.toSection_sub]; rfl]
    rfl]
  apply ContinuousLinearMap.ext
  intro om
  rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
        (show TensorRSSpace 1 (s + 1) I x from
          cometricRaiseSlot0Fib g₀ s x
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 2) I x from W.toSection x)
              (unitTensor (I := I) (M := M) x))) -
        (show TensorRSSpace 1 (s + 1) I x from
          cometricRaiseSlot0Fib g₀ s x
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 2) I x from W'.toSection x)
              (unitTensor (I := I) (M := M) x)))) om) =
      (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
        cometricRaiseSlot0Fib g₀ s x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 2) I x from W.toSection x)
            (unitTensor (I := I) (M := M) x))) om -
      (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
        cometricRaiseSlot0Fib g₀ s x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 2) I x from W'.toSection x)
            (unitTensor (I := I) (M := M) x))) om from rfl]
  rw [cometricRaiseSlot0Fib_clm_apply, cometricRaiseSlot0Fib_clm_apply,
    cometricRaiseSlot0Fib_clm_apply]
  set DW : Tensor0SSpace (s + 2) I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 2) I x from W.toSection x)
      (unitTensor (I := I) (M := M) x) with hDW_def
  set DW' : Tensor0SSpace (s + 2) I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 2) I x from W'.toSection x)
      (unitTensor (I := I) (M := M) x) with hDW'_def
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro w
  calc Tensor0SSpace.toModel
        (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) (s + 1) x
          (inverseMetricSharpFib (I := I) g₀ x om) (DW - DW')) w
      = Tensor0SSpace.toModel (DW - DW')
          (Fin.cons (show E from inverseMetricSharpFib (I := I) g₀ x om)
            (fun k => (show E from w k))) :=
        tsInteriorProduct_toModel_eval (I := I) (M := M) (s + 1) x
          (inverseMetricSharpFib (I := I) g₀ x om) (DW - DW') w
    _ = Tensor0SSpace.toModel DW
          (Fin.cons (show E from inverseMetricSharpFib (I := I) g₀ x om)
            (fun k => (show E from w k))) -
        Tensor0SSpace.toModel DW'
          (Fin.cons (show E from inverseMetricSharpFib (I := I) g₀ x om)
            (fun k => (show E from w k))) := by
        rw [Tensor0SSpace.toModel_sub]
        simp only [ContinuousMultilinearMap.sub_apply]
    _ = Tensor0SSpace.toModel
          (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) (s + 1) x
            (inverseMetricSharpFib (I := I) g₀ x om) DW) w -
        Tensor0SSpace.toModel
          (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) (s + 1) x
            (inverseMetricSharpFib (I := I) g₀ x om) DW') w := by
        rw [tsInteriorProduct_toModel_eval (I := I) (M := M) (s + 1) x
          (inverseMetricSharpFib (I := I) g₀ x om) DW w]
        rw [tsInteriorProduct_toModel_eval (I := I) (M := M) (s + 1) x
          (inverseMetricSharpFib (I := I) g₀ x om) DW' w]
    _ = Tensor0SSpace.toModel
          (Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) (s + 1) x
            (inverseMetricSharpFib (I := I) g₀ x om) DW -
          Tensor0SBundle.interior_product (𝕜 := ℝ) (I := I) (s + 1) x
            (inverseMetricSharpFib (I := I) g₀ x om) DW') w := by
        rw [Tensor0SSpace.toModel_sub]
        simp only [ContinuousMultilinearMap.sub_apply]

set_option linter.unusedSectionVars false in
private lemma tsRfns_cometricRaise_eq (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (W : SmoothCcTensor g₀ 0 (s + 2)) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 1 (s + 1) x
        ((cometricRaiseSlot0Field (I := I) (M := M) g₀ s W).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + 2) x (W.toSection x) := by
  have h := rfns_iteratedCovGrad_cometricRaiseSlot0Field_eq (I := I) (M := M) g₀ s W 0 x
  rw [iteratedCovGrad_zero, iteratedCovGrad_zero] at h
  exact h

set_option linter.unusedSectionVars false in
private lemma tsAppCcRS_coeffCorner_split (g₀ : SmoothRiemannianMetric I M) (a b c : ℕ)
    (Φ : SmoothCcTensor g₀ b c) (W : SmoothCcTensor g₀ a b) (j : ℕ) :
    iteratedCovGrad (I := I) g₀ a c j (appCcRS (I := I) (M := M) g₀ a b c Φ W) =
      appCcRS (I := I) (M := M) g₀ a b (c + j)
          (iteratedCovGrad (I := I) g₀ b c j Φ) W +
        ∑ k ∈ Finset.range j,
          appCcRS (I := I) (M := M) g₀ a (b + (k + 1)) (c + j)
            (appCcLeibnizPsi (I := I) (M := M) g₀ b c Φ j (k + 1))
            (iteratedCovGrad (I := I) g₀ a b (k + 1) W) := by
  rw [iteratedCovGrad_appCcRS_eq (I := I) (M := M) g₀ a b c Φ W j]
  rw [Finset.sum_range_succ' (fun k =>
    appCcRS (I := I) (M := M) g₀ a (b + k) (c + j)
      (appCcLeibnizPsi (I := I) (M := M) g₀ b c Φ j k)
      (iteratedCovGrad (I := I) g₀ a b k W)) j]
  have hf0 : appCcRS (I := I) (M := M) g₀ a (b + 0) (c + j)
      (appCcLeibnizPsi (I := I) (M := M) g₀ b c Φ j 0)
      (iteratedCovGrad (I := I) g₀ a b 0 W) =
      appCcRS (I := I) (M := M) g₀ a b (c + j)
        (iteratedCovGrad (I := I) g₀ b c j Φ) W :=
    congrArg (fun Z : SmoothCcTensor g₀ b (c + j) =>
      appCcRS (I := I) (M := M) g₀ a b (c + j) Z W)
      (appCcLeibnizPsi_zero_right_eq (I := I) (M := M) g₀ b c Φ j)
  rw [hf0]
  exact add_comm _ _

set_option linter.unusedSectionVars false in
private lemma tsParallel_argCorner_head_le (g₀ : SmoothRiemannianMetric I M) (p a b : ℕ)
    (Φ : SmoothCcTensor g₀ a b) (i : ℕ) (HX : SmoothCcTensor g₀ p (a + i)) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ p (b + i) x
        ((appCcRS (I := I) (M := M) g₀ p (a + i) (b + i)
          (appCcLeibnizPsi (I := I) (M := M) g₀ a b Φ i i) HX).toSection x) ≤
      riemannianFiberNormSq (I := I) (M := M) g₀ a b x (Φ.toSection x) *
        riemannianFiberNormSq (I := I) (M := M) g₀ p (a + i) x (HX.toSection x) :=
  rfns_appCcRS_appCcLeibnizPsi_diag_le (I := I) (M := M) g₀ p a b Φ i HX x

set_option linter.unusedSectionVars false in
private lemma tsParallel_argCorner_residual_le (g₀ : SmoothRiemannianMetric I M) (p a b : ℕ)
    (Φ : SmoothCcTensor g₀ a b)
    (hΦ : covGrad (I := I) (M := M) g₀ a b Φ = 0)
    (X : SmoothCcTensor g₀ p a) (i : ℕ) (HX : SmoothCcTensor g₀ p (a + i)) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ p (b + i) x
        ((iteratedCovGrad (I := I) g₀ p b i (appCcRS (I := I) (M := M) g₀ p a b Φ X) -
          appCcRS (I := I) (M := M) g₀ p (a + i) (b + i)
            (appCcLeibnizPsi (I := I) (M := M) g₀ a b Φ i i) HX).toSection x) ≤
      2 * (riemannianFiberNormSq (I := I) (M := M) g₀ a b x (Φ.toSection x) *
        riemannianFiberNormSq (I := I) (M := M) g₀ p (a + i) x
          ((iteratedCovGrad (I := I) g₀ p a i X - HX).toSection x)) := by
  have hsplit : iteratedCovGrad (I := I) g₀ p b i
        (appCcRS (I := I) (M := M) g₀ p a b Φ X) -
        appCcRS (I := I) (M := M) g₀ p (a + i) (b + i)
          (appCcLeibnizPsi (I := I) (M := M) g₀ a b Φ i i) HX =
      appCcRS (I := I) (M := M) g₀ p (a + i) (b + i)
          (appCcLeibnizPsi (I := I) (M := M) g₀ a b Φ i i)
          (iteratedCovGrad (I := I) g₀ p a i X - HX) +
        ∑ k ∈ Finset.range i,
          appCcRS (I := I) (M := M) g₀ p (a + k) (b + i)
            (appCcLeibnizPsi (I := I) (M := M) g₀ a b Φ i k)
            (iteratedCovGrad (I := I) g₀ p a k X) := by
    rw [iteratedCovGrad_appCcRS_eq_argCorner_add_lower (I := I) (M := M) g₀ p a b Φ X i]
    rw [appCcRS_sub_right_cc (I := I) (M := M) g₀ p (a + i) (b + i)
      (appCcLeibnizPsi (I := I) (M := M) g₀ a b Φ i i)
      (iteratedCovGrad (I := I) g₀ p a i X) HX]
    exact add_sub_right_comm _ _ _
  rw [hsplit]
  rw [show (((appCcRS (I := I) (M := M) g₀ p (a + i) (b + i)
        (appCcLeibnizPsi (I := I) (M := M) g₀ a b Φ i i)
        (iteratedCovGrad (I := I) g₀ p a i X - HX) +
      ∑ k ∈ Finset.range i,
        appCcRS (I := I) (M := M) g₀ p (a + k) (b + i)
          (appCcLeibnizPsi (I := I) (M := M) g₀ a b Φ i k)
          (iteratedCovGrad (I := I) g₀ p a k X)).toSection x)) =
      (appCcRS (I := I) (M := M) g₀ p (a + i) (b + i)
        (appCcLeibnizPsi (I := I) (M := M) g₀ a b Φ i i)
        (iteratedCovGrad (I := I) g₀ p a i X - HX)).toSection x +
      (∑ k ∈ Finset.range i,
        appCcRS (I := I) (M := M) g₀ p (a + k) (b + i)
          (appCcLeibnizPsi (I := I) (M := M) g₀ a b Φ i k)
          (iteratedCovGrad (I := I) g₀ p a k X)).toSection x from by
    rw [SmoothCcTensor.toSection_add]; rfl]
  refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ p (b + i) x _ _) ?_
  have hcorr : riemannianFiberNormSq (I := I) (M := M) g₀ p (b + i) x
      ((∑ k ∈ Finset.range i,
        appCcRS (I := I) (M := M) g₀ p (a + k) (b + i)
          (appCcLeibnizPsi (I := I) (M := M) g₀ a b Φ i k)
          (iteratedCovGrad (I := I) g₀ p a k X)).toSection x) ≤ 0 := by
    refine le_trans (rfns_appCcRS_argLower_le (I := I) (M := M) g₀ p a b Φ X i x) ?_
    have hzero : ∀ k ∈ Finset.range i,
        riemannianFiberNormSq (I := I) (M := M) g₀ a (b + (i - k)) x
            ((iteratedCovGrad (I := I) g₀ a b (i - k) Φ).toSection x) *
          riemannianFiberNormSq (I := I) (M := M) g₀ p (a + k) x
            ((iteratedCovGrad (I := I) g₀ p a k X).toSection x) = 0 := by
      intro k hk
      rw [Finset.mem_range] at hk
      rw [show i - k = (i - k - 1) + 1 from by omega]
      rw [iteratedCovGrad_zero_of_covGrad_zero (I := I) (M := M) g₀ a b Φ hΦ (i - k - 1)]
      rw [SmoothCcTensor.toSection_zero]
      simp only [ContMDiffSection.coe_zero, Pi.zero_apply]
      rw [riemannianFiberNormSq_zero (I := I) (M := M) g₀ a (b + ((i - k - 1) + 1)) x]
      ring
    rw [Finset.sum_congr rfl hzero, Finset.sum_const, smul_zero, mul_zero]
  have hhead := le_trans
    (rfns_appCcRS_appCcLeibnizPsi_diag_le (I := I) (M := M) g₀ p a b Φ i
      (iteratedCovGrad (I := I) g₀ p a i X - HX) x) (le_refl _)
  linarith [hhead, hcorr]

set_option linter.unusedVariables false in
theorem rfns_iteratedCovGrad_slotInsertEndoCc_zero_ricEndoBackgroundDifferenceField_topSeparated_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Ktop : ℝ, 0 ≤ Ktop ∧ ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (i : ℕ),
        ∃ Hd : SmoothCcTensor g₀ 1 (1 + i),
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x (Hd.toSection x) ≤
              Ktop * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x)) ∧
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
                ((iteratedCovGrad (I := I) g₀ 1 1 i
                    (slotInsertEndoCc (I := I) (M := M) g₀ 0
                      (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁)) -
                  Hd).toSection x) ≤
              Kc i * Combinatorics.boundedFactorGridWindow
                (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x)) (i + 1) (i + 3)) := by
  classical
  obtain ⟨KtA, hKtA_nn, KcA, hKcA_nn, hA⟩ :=
    rfns_iteratedCovGrad_riemannLoweredBackgroundDifference_topSeparated_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨S, hS_nn, hS⟩ :=
    exists_rfns_iteratedCovGrad_sharpFlatEndoCc_tgrid (I := I) (M := M) g₀ hδ₀
  obtain ⟨CDel, hCDel_nn, hCDel⟩ :=
    rfns_iteratedCovGrad_ricciMixedSharpBackgroundDifference_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨cPhi, hcPhi_nn, hcPhi⟩ := exists_bound_riemannianFiberNormSq_smoothCcTensor
    (I := I) (M := M) g₀ 4 2 (cometricDoubleTraceField (I := I) g₀ 2)
  obtain ⟨cB, hcB_nn, hcB⟩ := exists_backgroundJet_rfns_bound (I := I) (M := M) g₀ 1 1
    (slotInsertEndoCc (I := I) (M := M) g₀ 0 (ricEndoRaisedField (I := I) (M := M) g₀))
  obtain ⟨cId, hcId_nn, hcId⟩ := exists_bound_riemannianFiberNormSq_smoothCcTensor
    (I := I) (M := M) g₀ 1 1
    (slotInsertEndoCc (I := I) (M := M) g₀ 0 (fullRaisedEndoField (I := I) (M := M) g₀ g₀))
  refine ⟨cPhi * KtA * S 0,
    mul_nonneg (mul_nonneg hcPhi_nn hKtA_nn) (hS_nn 0), ?_⟩
  refine ⟨fun i => 4 * (cPhi * (KcA i) * S 0) +
      4 * ((i : ℝ) * ∑ k ∈ Finset.range i,
        appCcGdiag (E := E) i * CDel (i - (k + 1)) * S (k + 1) *
          Combinatorics.windowPairCellCount ((i - (k + 1)) + 3) (k + 2)) +
      4 * (appCcGdiag (E := E) i * ∑ a' ∈ Finset.range (i + 1),
        cB a' * (∑ l ∈ Finset.range (i + 1 - a'), (2 * S 0 + 2 * cId + S l))),
    fun i => by
      have h1 : (0 : ℝ) ≤ cPhi * (KcA i) * S 0 :=
        mul_nonneg (mul_nonneg hcPhi_nn (hKcA_nn i)) (hS_nn 0)
      have h2 : (0 : ℝ) ≤ (i : ℝ) * ∑ k ∈ Finset.range i,
          appCcGdiag (E := E) i * CDel (i - (k + 1)) * S (k + 1) *
            Combinatorics.windowPairCellCount ((i - (k + 1)) + 3) (k + 2) :=
        mul_nonneg (Nat.cast_nonneg i) (Finset.sum_nonneg fun k _ =>
          mul_nonneg (mul_nonneg (mul_nonneg (appCcGdiag_nonneg (E := E) i)
            (hCDel_nn _)) (hS_nn _)) (Combinatorics.windowPairCellCount_nonneg _ _))
      have h3 : (0 : ℝ) ≤ appCcGdiag (E := E) i * ∑ a' ∈ Finset.range (i + 1),
          cB a' * (∑ l ∈ Finset.range (i + 1 - a'), (2 * S 0 + 2 * cId + S l)) :=
        mul_nonneg (appCcGdiag_nonneg (E := E) i) (Finset.sum_nonneg fun a' _ =>
          mul_nonneg (hcB_nn a') (Finset.sum_nonneg fun l _ => by
            have := hS_nn 0; have := hS_nn l; linarith))
      linarith, ?_⟩
  intro g₁ T htie δ hδ_le hδ0 hbound i
  obtain ⟨HdA, hHdA_head, hHdA_res⟩ := hA g₁ T htie hδ_le hδ0 hbound i
  set dTr : SmoothCcTensor g₀ 4 2 := cometricDoubleTraceField (I := I) g₀ 2 with hdTr_def
  set RLD : SmoothCcTensor g₀ 0 4 :=
    riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁ with hRLD_def
  set Z : SmoothCcTensor g₀ 0 2 := appCcRS (I := I) (M := M) g₀ 0 4 2 dTr RLD with hZ_def
  set ZS : SmoothCcTensor g₀ 0 2 :=
    domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) Z with hZS_def
  set sF : SmoothCcTensor g₀ 1 1 := sharpFlatEndoCc (I := I) g₀ g₁ with hsF_def
  set B0f : SmoothCcTensor g₀ 1 1 :=
    slotInsertEndoCc (I := I) (M := M) g₀ 0 (ricEndoRaisedField (I := I) (M := M) g₀)
    with hB0f_def
  set Dg : SmoothCcTensor g₀ 1 1 :=
    slotInsertEndoCc (I := I) (M := M) g₀ 0 (gInvDiffRaisedEndoField (I := I) g₀ g₁)
    with hDg_def
  set InsId : SmoothCcTensor g₀ 1 1 :=
    slotInsertEndoCc (I := I) (M := M) g₀ 0 (fullRaisedEndoField (I := I) (M := M) g₀ g₀)
    with hInsId_def
  set Delta : SmoothCcTensor g₀ 1 1 :=
    slotInsertEndoCc (I := I) (M := M) g₀ 0 (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁) -
      slotInsertEndoCc (I := I) (M := M) g₀ 0 (ricEndoRaisedField (I := I) (M := M) g₀)
    with hDelta_def
  have hdTr_par : covGrad (I := I) (M := M) g₀ 4 2 dTr = 0 :=
    cometricDoubleTraceField_covGrad_eq_zero (I := I) g₀ 2
  have hsF_split : sF = Dg + InsId := by
    rw [hsF_def, hDg_def, hInsId_def,
      sharpFlatEndoCc_eq_slotInsert_fullRaised (I := I) (M := M) g₀ g₁,
      fullRaisedEndoField_diff_split (I := I) (M := M) g₀ g₁,
      slotInsertEndoCc_add_endo (I := I) (M := M) g₀ 0]
  have hDg_eq : Dg = sF - InsId := eq_sub_of_add_eq hsF_split.symm
  have hBmix : slotInsertEndoCc (I := I) (M := M) g₀ 0
      (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁) = Delta + B0f := by
    rw [hDelta_def, hB0f_def]; abel
  have hDeltaDg : appCcRS (I := I) (M := M) g₀ 1 1 1 Delta Dg =
      appCcRS (I := I) (M := M) g₀ 1 1 1 Delta sF -
        appCcRS (I := I) (M := M) g₀ 1 1 1 Delta InsId := by
    rw [hDg_eq]
    exact appCcRS_sub_right_cc (I := I) (M := M) g₀ 1 1 1 Delta sF InsId
  have hInsRet : appCcRS (I := I) (M := M) g₀ 1 1 1 Delta InsId = Delta := by
    rw [hInsId_def]
    exact appCcRS_slotInsert_id_eq (I := I) (M := M) g₀ 0 1 Delta
  have hXsplit : slotInsertEndoCc (I := I) (M := M) g₀ 0
        (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁) =
      appCcRS (I := I) (M := M) g₀ 1 1 1 Delta sF +
        appCcRS (I := I) (M := M) g₀ 1 1 1 B0f Dg := by
    calc slotInsertEndoCc (I := I) (M := M) g₀ 0
          (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁)
        = (slotInsertEndoCc (I := I) (M := M) g₀ 0
              (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁) -
            slotInsertEndoCc (I := I) (M := M) g₀ 0
              (ricEndoRaisedField (I := I) (M := M) g₀)) +
          appCcRS (I := I) (M := M) g₀ 1 1 1
            (slotInsertEndoCc (I := I) (M := M) g₀ 0
              (ricMixedSharpEndoField (I := I) (M := M) g₀ g₁))
            (slotInsertEndoCc (I := I) (M := M) g₀ 0
              (gInvDiffRaisedEndoField (I := I) g₀ g₁)) :=
          slotInsertEndoCc_zero_ricEndoBackgroundDifference_telescope (I := I) (M := M) g₀ g₁
      _ = Delta + appCcRS (I := I) (M := M) g₀ 1 1 1 (Delta + B0f) Dg := by
          rw [← hDelta_def, ← hDg_def, hBmix]
      _ = Delta + (appCcRS (I := I) (M := M) g₀ 1 1 1 Delta Dg +
            appCcRS (I := I) (M := M) g₀ 1 1 1 B0f Dg) := by
          rw [appCcRS_add_left_cc (I := I) (M := M) g₀ 1 1 1 Delta B0f Dg]
      _ = Delta + ((appCcRS (I := I) (M := M) g₀ 1 1 1 Delta sF - Delta) +
            appCcRS (I := I) (M := M) g₀ 1 1 1 B0f Dg) := by
          rw [hDeltaDg, hInsRet]
      _ = appCcRS (I := I) (M := M) g₀ 1 1 1 Delta sF +
            appCcRS (I := I) (M := M) g₀ 1 1 1 B0f Dg := by abel
  have hΔrepr := slotInsert_ricMixedSharp_sub_ricEndoRaised_eq_raise_doubleTrace
    (I := I) (M := M) g₀ g₁
  obtain ⟨σs, hσs⟩ := tsExists_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
    (Equiv.swap (0 : Fin 2) 1) Z i
  obtain ⟨σr, hσr⟩ := tsExists_iteratedCovGrad_cometricRaiseSlot0Field (I := I) (M := M)
    g₀ 0 ZS i
  set HdZ : SmoothCcTensor g₀ 0 (2 + i) :=
    appCcRS (I := I) (M := M) g₀ 0 (4 + i) (2 + i)
      (appCcLeibnizPsi (I := I) (M := M) g₀ 4 2 dTr i i) HdA with hHdZ_def
  set HdD : SmoothCcTensor g₀ 1 (1 + i) :=
    castRankCc_db g₀ 1 (by omega : (0 + i) + 1 = (0 + 1) + i)
      (cometricRaiseSlot0Field (I := I) (M := M) g₀ (0 + i)
        (domDomCongrSection (I := I) g₀ σr
          (castRankCc_db g₀ 0 (by omega : (0 + 2) + i = (0 + i) + 2)
            (domDomCongrSection (I := I) g₀ σs HdZ)))) with hHdD_def
  refine ⟨appCcRS (I := I) (M := M) g₀ 1 1 (1 + i) HdD sF, ?_, ?_⟩
  · intro x
    have hHdD_rfns : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
        (HdD.toSection x) =
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x (HdZ.toSection x) := by
      rw [hHdD_def]
      rw [tsRfns_castRankCc_db_zero (I := I) (M := M) g₀ 1
        (by omega : (0 + i) + 1 = (0 + 1) + i) _ x]
      rw [tsRfns_cometricRaise_eq (I := I) (M := M) g₀ (0 + i) _ x]
      rw [tsRfns_domDomCongrSection_zero (I := I) (M := M) g₀ σr _ x]
      rw [tsRfns_castRankCc_db_zero (I := I) (M := M) g₀ 0
        (by omega : (0 + 2) + i = (0 + i) + 2) _ x]
      rw [tsRfns_domDomCongrSection_zero (I := I) (M := M) g₀ σs _ x]
    rw [appCcRS_toSection (I := I) (M := M) g₀ 1 1 (1 + i) HdD sF x]
    refine le_trans (riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g₀ 1 1 (1 + i) x
      _ _) ?_
    have hHdZ_le : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + i) x
        (HdZ.toSection x) ≤
        cPhi * (KtA * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x)) := by
      rw [hHdZ_def]
      refine le_trans (tsParallel_argCorner_head_le (I := I) (M := M) g₀ 0 4 2 dTr i HdA x) ?_
      exact mul_le_mul (hcPhi x) (hHdA_head x)
        (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (4 + i) x _) hcPhi_nn
    have hsF0 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x (sF.toSection x) ≤ S 0 := by
      have h := hS g₁ T htie hδ_le hδ0 hbound 0 x
      rw [iteratedCovGrad_zero] at h
      rw [Combinatorics.antidiagonalTupleGrid_zero, mul_one] at h
      exact h
    have hb_nn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
      ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x)
    have hHdD_nn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 (1 + i) x
      (HdD.toSection x)
    have hsF_nn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 1 x (sF.toSection x)
    calc riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x (HdD.toSection x) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x (sF.toSection x)
        ≤ (cPhi * (KtA * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x))) * S 0 := by
          refine mul_le_mul ?_ hsF0 hsF_nn ?_
          · rw [hHdD_rfns]; exact hHdZ_le
          · exact mul_nonneg hcPhi_nn (mul_nonneg hKtA_nn hb_nn)
      _ = cPhi * KtA * S 0 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x) := by ring
  · intro x
    set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
      ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x) with hb_def
    have hb : ∀ l, 0 ≤ b l :=
      fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
    set Wfin : ℝ := Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) with hWfin_def
    have hWfin_nn : 0 ≤ Wfin :=
      Combinatorics.boundedFactorGridWindow_nonneg b hb (i + 1) (i + 3)
    have hWfin_one : 1 ≤ Wfin :=
      Combinatorics.one_le_boundedFactorGridWindow b hb (by omega)
    have hNdDiff : iteratedCovGrad (I := I) g₀ 1 1 i Delta - HdD =
        castRankCc_db g₀ 1 (by omega : (0 + i) + 1 = (0 + 1) + i)
          (cometricRaiseSlot0Field (I := I) (M := M) g₀ (0 + i)
            (domDomCongrSection (I := I) g₀ σr
              (castRankCc_db g₀ 0 (by omega : (0 + 2) + i = (0 + i) + 2)
                (domDomCongrSection (I := I) g₀ σs
                  (iteratedCovGrad (I := I) g₀ 0 2 i Z - HdZ))))) := by
      have hNdDelta : iteratedCovGrad (I := I) g₀ 1 1 i Delta =
          castRankCc_db g₀ 1 (by omega : (0 + i) + 1 = (0 + 1) + i)
            (cometricRaiseSlot0Field (I := I) (M := M) g₀ (0 + i)
              (domDomCongrSection (I := I) g₀ σr
                (castRankCc_db g₀ 0 (by omega : (0 + 2) + i = (0 + i) + 2)
                  (domDomCongrSection (I := I) g₀ σs
                    (iteratedCovGrad (I := I) g₀ 0 2 i Z))))) := by
        calc iteratedCovGrad (I := I) g₀ 1 1 i Delta
            = iteratedCovGrad (I := I) g₀ 1 (0 + 1) i
                (cometricRaiseSlot0Field (I := I) (M := M) g₀ 0 ZS) := by
              rw [hDelta_def, hΔrepr, hZS_def, hZ_def, hdTr_def, hRLD_def]
          _ = castRankCc_db g₀ 1 (by omega : (0 + i) + 1 = (0 + 1) + i)
                (cometricRaiseSlot0Field (I := I) (M := M) g₀ (0 + i)
                  (domDomCongrSection (I := I) g₀ σr
                    (castRankCc_db g₀ 0 (by omega : (0 + 2) + i = (0 + i) + 2)
                      (iteratedCovGrad (I := I) g₀ 0 (0 + 2) i ZS)))) := hσr
          _ = _ := by
              rw [show (iteratedCovGrad (I := I) g₀ 0 (0 + 2) i ZS) =
                  domDomCongrSection (I := I) g₀ σs
                    (iteratedCovGrad (I := I) g₀ 0 2 i Z) from by
                rw [← hσs, hZS_def]]
      rw [hNdDelta, hHdD_def]
      rw [← tsCastRankCc_db_sub (I := I) (M := M) g₀ 1
        (by omega : (0 + i) + 1 = (0 + 1) + i)]
      rw [← tsCometricRaise_sub (I := I) (M := M) g₀ (0 + i)]
      rw [← tsDomDomCongrSection_sub (I := I) (M := M) g₀ σr]
      rw [← tsCastRankCc_db_sub (I := I) (M := M) g₀ 0
        (by omega : (0 + 2) + i = (0 + i) + 2)]
      rw [← tsDomDomCongrSection_sub (I := I) (M := M) g₀ σs]
    have hΔres : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 1 i Delta - HdD).toSection x) ≤
        2 * (cPhi * (KcA i * Wfin)) := by
      rw [hNdDiff]
      rw [tsRfns_castRankCc_db_zero (I := I) (M := M) g₀ 1
        (by omega : (0 + i) + 1 = (0 + 1) + i) _ x]
      rw [tsRfns_cometricRaise_eq (I := I) (M := M) g₀ (0 + i) _ x]
      rw [tsRfns_domDomCongrSection_zero (I := I) (M := M) g₀ σr _ x]
      rw [tsRfns_castRankCc_db_zero (I := I) (M := M) g₀ 0
        (by omega : (0 + 2) + i = (0 + i) + 2) _ x]
      rw [tsRfns_domDomCongrSection_zero (I := I) (M := M) g₀ σs _ x]
      rw [hHdZ_def, hZ_def]
      refine le_trans (tsParallel_argCorner_residual_le (I := I) (M := M) g₀ 0 4 2 dTr
        hdTr_par RLD i HdA x) ?_
      have hres := hHdA_res x
      have hd_nn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (4 + i) x
        ((iteratedCovGrad (I := I) g₀ 0 4 i RLD - HdA).toSection x)
      have hKcW_nn : 0 ≤ KcA i * Wfin := mul_nonneg (hKcA_nn i) hWfin_nn
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      refine mul_le_mul (hcPhi x) ?_ hd_nn hcPhi_nn
      exact hres
    set P1t := appCcRS (I := I) (M := M) g₀ 1 1 (1 + i)
        (iteratedCovGrad (I := I) g₀ 1 1 i Delta - HdD) sF with hP1t_def
    set P2t := ∑ k ∈ Finset.range i,
        appCcRS (I := I) (M := M) g₀ 1 (1 + (k + 1)) (1 + i)
          (appCcLeibnizPsi (I := I) (M := M) g₀ 1 1 Delta i (k + 1))
          (iteratedCovGrad (I := I) g₀ 1 1 (k + 1) sF) with hP2t_def
    set P3t := iteratedCovGrad (I := I) g₀ 1 1 i
        (appCcRS (I := I) (M := M) g₀ 1 1 1 B0f Dg) with hP3t_def
    have hsplit : iteratedCovGrad (I := I) g₀ 1 1 i
          (slotInsertEndoCc (I := I) (M := M) g₀ 0
            (ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁)) -
          appCcRS (I := I) (M := M) g₀ 1 1 (1 + i) HdD sF =
        P1t + (P2t + P3t) := by
      rw [hP1t_def, hP2t_def, hP3t_def, hXsplit]
      rw [iteratedCovGrad_add (I := I) g₀ 1 1 i
        (appCcRS (I := I) (M := M) g₀ 1 1 1 Delta sF)
        (appCcRS (I := I) (M := M) g₀ 1 1 1 B0f Dg)]
      rw [tsAppCcRS_coeffCorner_split (I := I) (M := M) g₀ 1 1 1 Delta sF i]
      rw [appCcRS_sub_left_cc (I := I) (M := M) g₀ 1 1 (1 + i)
        (iteratedCovGrad (I := I) g₀ 1 1 i Delta) HdD sF]
      abel
    rw [hsplit]
    rw [show ((P1t + (P2t + P3t)).toSection x) =
        P1t.toSection x + (P2t + P3t).toSection x from by
      rw [SmoothCcTensor.toSection_add]; rfl]
    refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 1 (1 + i) x _ _) ?_
    rw [show ((P2t + P3t).toSection x) = P2t.toSection x + P3t.toSection x from by
      rw [SmoothCcTensor.toSection_add]; rfl]
    have hP1 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
        (P1t.toSection x) ≤ 2 * (cPhi * (KcA i)) * S 0 * Wfin := by
      rw [hP1t_def]
      rw [appCcRS_toSection (I := I) (M := M) g₀ 1 1 (1 + i)
        (iteratedCovGrad (I := I) g₀ 1 1 i Delta - HdD) sF x]
      refine le_trans (riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g₀ 1 1
        (1 + i) x _ _) ?_
      have hsF0 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x (sF.toSection x) ≤
          S 0 := by
        have h := hS g₁ T htie hδ_le hδ0 hbound 0 x
        rw [iteratedCovGrad_zero] at h
        rw [Combinatorics.antidiagonalTupleGrid_zero, mul_one] at h
        exact h
      have hsF_nn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 1 x
        (sF.toSection x)
      calc riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
            ((iteratedCovGrad (I := I) g₀ 1 1 i Delta - HdD).toSection x) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x (sF.toSection x)
          ≤ (2 * (cPhi * (KcA i * Wfin))) * S 0 := by
            refine mul_le_mul hΔres hsF0 hsF_nn ?_
            exact mul_nonneg (by norm_num)
              (mul_nonneg hcPhi_nn (mul_nonneg (hKcA_nn i) hWfin_nn))
        _ = 2 * (cPhi * (KcA i)) * S 0 * Wfin := by ring
    have hP2 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
        (P2t.toSection x) ≤
        ((i : ℝ) * ∑ k ∈ Finset.range i,
          appCcGdiag (E := E) i * CDel (i - (k + 1)) * S (k + 1) *
            Combinatorics.windowPairCellCount ((i - (k + 1)) + 3) (k + 2)) * Wfin := by
      rw [hP2t_def]
      rw [SmoothCcTensor.toSection_sum_apply]
      refine le_trans (riemannianFiberNormSq_sum_le_card_mul (I := I) (M := M) g₀ 1
        (1 + i) x (Finset.range i) _) ?_
      rw [Finset.card_range]
      have hterm : ∀ k ∈ Finset.range i,
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
            ((appCcRS (I := I) (M := M) g₀ 1 (1 + (k + 1)) (1 + i)
              (appCcLeibnizPsi (I := I) (M := M) g₀ 1 1 Delta i (k + 1))
              (iteratedCovGrad (I := I) g₀ 1 1 (k + 1) sF)).toSection x) ≤
          (appCcGdiag (E := E) i * CDel (i - (k + 1)) * S (k + 1) *
            Combinatorics.windowPairCellCount ((i - (k + 1)) + 3) (k + 2)) * Wfin := by
        intro k hk
        rw [Finset.mem_range] at hk
        rw [appCcRS_toSection (I := I) (M := M) g₀ 1 (1 + (k + 1)) (1 + i)
          (appCcLeibnizPsi (I := I) (M := M) g₀ 1 1 Delta i (k + 1))
          (iteratedCovGrad (I := I) g₀ 1 1 (k + 1) sF) x]
        refine le_trans (riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g₀ 1
          (1 + (k + 1)) (1 + i) x _ _) ?_
        have hPsi : riemannianFiberNormSq (I := I) (M := M) g₀ (1 + (k + 1)) (1 + i) x
            ((appCcLeibnizPsi (I := I) (M := M) g₀ 1 1 Delta i (k + 1)).toSection x) ≤
            appCcGdiag (E := E) i *
              riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + (i - (k + 1))) x
                ((iteratedCovGrad (I := I) g₀ 1 1 (i - (k + 1)) Delta).toSection x) := by
          have hw := rfns_iteratedCovGrad_appCcLeibnizPsi_window_le (I := I) (M := M) g₀ 1 1
            Delta i (k + 1) 0 (by omega) x
          rw [iteratedCovGrad_zero] at hw
          rw [tsRfns_order_congr (I := I) (M := M) g₀ 1 1
            (show (i - (k + 1)) + 0 = i - (k + 1) from by omega) Delta x] at hw
          exact hw
        have hDeltaJets : riemannianFiberNormSq (I := I) (M := M) g₀ 1
            (1 + (i - (k + 1))) x
            ((iteratedCovGrad (I := I) g₀ 1 1 (i - (k + 1)) Delta).toSection x) ≤
            CDel (i - (k + 1)) *
              Combinatorics.boundedFactorGridWindow b (i + 1) ((i - (k + 1)) + 3) := by
          refine le_trans (hCDel g₁ T htie hδ_le hδ0 hbound (i - (k + 1)) x) ?_
          refine mul_le_mul_of_nonneg_left ?_ (hCDel_nn (i - (k + 1)))
          exact tsTgridSum_le_boundedWindow b hb (by omega) (by omega)
        have hsFjet : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + (k + 1)) x
            ((iteratedCovGrad (I := I) g₀ 1 1 (k + 1) sF).toSection x) ≤
            S (k + 1) * Combinatorics.boundedFactorGridWindow b (i + 1) (k + 2) := by
          refine le_trans (hS g₁ T htie hδ_le hδ0 hbound (k + 1) x) ?_
          refine mul_le_mul_of_nonneg_left ?_ (hS_nn (k + 1))
          rw [Combinatorics.antidiagonalTupleGrid_eq_boundedFactorGrid b
            (show k + 1 ≤ i + 1 from by omega)]
          exact Combinatorics.boundedFactorGrid_le_boundedFactorGridWindow b hb (by omega)
        have hpair : Combinatorics.boundedFactorGridWindow b (i + 1) ((i - (k + 1)) + 3) *
            Combinatorics.boundedFactorGridWindow b (i + 1) (k + 2) ≤
            Combinatorics.windowPairCellCount ((i - (k + 1)) + 3) (k + 2) * Wfin := by
          refine le_trans (Combinatorics.boundedFactorGridWindow_mul_le b hb (i + 1)
            ((i - (k + 1)) + 3) (k + 2) (by omega) (by omega)) ?_
          refine mul_le_mul_of_nonneg_left ?_
            (Combinatorics.windowPairCellCount_nonneg _ _)
          rw [hWfin_def]
          refine Combinatorics.boundedFactorGridWindow_mono b hb (le_refl _) ?_
          omega
        calc riemannianFiberNormSq (I := I) (M := M) g₀ (1 + (k + 1)) (1 + i) x
              ((appCcLeibnizPsi (I := I) (M := M) g₀ 1 1 Delta i (k + 1)).toSection x) *
            riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + (k + 1)) x
              ((iteratedCovGrad (I := I) g₀ 1 1 (k + 1) sF).toSection x)
            ≤ (appCcGdiag (E := E) i *
                (CDel (i - (k + 1)) *
                  Combinatorics.boundedFactorGridWindow b (i + 1) ((i - (k + 1)) + 3))) *
              (S (k + 1) * Combinatorics.boundedFactorGridWindow b (i + 1) (k + 2)) := by
              refine mul_le_mul ?_ hsFjet
                (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 (1 + (k + 1)) x _) ?_
              · refine le_trans hPsi ?_
                exact mul_le_mul_of_nonneg_left hDeltaJets (appCcGdiag_nonneg (E := E) i)
              · exact mul_nonneg (appCcGdiag_nonneg (E := E) i)
                  (mul_nonneg (hCDel_nn _)
                    (Combinatorics.boundedFactorGridWindow_nonneg b hb _ _))
          _ = (appCcGdiag (E := E) i * CDel (i - (k + 1)) * S (k + 1)) *
              (Combinatorics.boundedFactorGridWindow b (i + 1) ((i - (k + 1)) + 3) *
                Combinatorics.boundedFactorGridWindow b (i + 1) (k + 2)) := by ring
          _ ≤ (appCcGdiag (E := E) i * CDel (i - (k + 1)) * S (k + 1)) *
              (Combinatorics.windowPairCellCount ((i - (k + 1)) + 3) (k + 2) * Wfin) := by
              refine mul_le_mul_of_nonneg_left hpair ?_
              exact mul_nonneg (mul_nonneg (appCcGdiag_nonneg (E := E) i)
                (hCDel_nn _)) (hS_nn _)
          _ = (appCcGdiag (E := E) i * CDel (i - (k + 1)) * S (k + 1) *
              Combinatorics.windowPairCellCount ((i - (k + 1)) + 3) (k + 2)) * Wfin := by
              ring
      calc ((i : ℕ) : ℝ) * ∑ k ∈ Finset.range i,
            riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
              ((appCcRS (I := I) (M := M) g₀ 1 (1 + (k + 1)) (1 + i)
                (appCcLeibnizPsi (I := I) (M := M) g₀ 1 1 Delta i (k + 1))
                (iteratedCovGrad (I := I) g₀ 1 1 (k + 1) sF)).toSection x)
          ≤ ((i : ℕ) : ℝ) * ∑ k ∈ Finset.range i,
              (appCcGdiag (E := E) i * CDel (i - (k + 1)) * S (k + 1) *
                Combinatorics.windowPairCellCount ((i - (k + 1)) + 3) (k + 2)) * Wfin :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) (Nat.cast_nonneg i)
        _ = ((i : ℝ) * ∑ k ∈ Finset.range i,
              appCcGdiag (E := E) i * CDel (i - (k + 1)) * S (k + 1) *
                Combinatorics.windowPairCellCount ((i - (k + 1)) + 3) (k + 2)) * Wfin := by
            rw [← Finset.sum_mul]
            ring
    have hP3 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
        (P3t.toSection x) ≤
        (appCcGdiag (E := E) i * ∑ a' ∈ Finset.range (i + 1),
          cB a' * (∑ l ∈ Finset.range (i + 1 - a'), (2 * S 0 + 2 * cId + S l))) * Wfin := by
      rw [hP3t_def]
      refine le_trans (rfns_iteratedCovGrad_appCcRS_diagonalProductGrid_rankLeft_le
        (I := I) (M := M) g₀ i 1 1 1 B0f Dg x) ?_
      have hDjet : ∀ l : ℕ, l ≤ i →
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
            ((iteratedCovGrad (I := I) g₀ 1 1 l Dg).toSection x) ≤
          (2 * S 0 + 2 * cId + S l) * Wfin := by
        intro l hl
        match l with
        | 0 =>
          rw [iteratedCovGrad_zero]
          have hDx : riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x (Dg.toSection x) ≤
              2 * S 0 + 2 * cId := by
            rw [hDg_eq]
            rw [show ((sF - InsId).toSection x) = sF.toSection x - InsId.toSection x from by
              rw [SmoothCcTensor.toSection_sub]; rfl]
            refine le_trans (tsRfns_sub_le (I := I) (M := M) g₀ 1 1 x _ _) ?_
            have hsF0 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x
                (sF.toSection x) ≤ S 0 := by
              have h := hS g₁ T htie hδ_le hδ0 hbound 0 x
              rw [iteratedCovGrad_zero] at h
              rw [Combinatorics.antidiagonalTupleGrid_zero, mul_one] at h
              exact h
            have hIdx := hcId x
            rw [hInsId_def] at *
            linarith
          calc riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x (Dg.toSection x)
              ≤ 2 * S 0 + 2 * cId := hDx
            _ = (2 * S 0 + 2 * cId) * 1 := by ring
            _ ≤ (2 * S 0 + 2 * cId + S 0) * Wfin := by
                refine mul_le_mul ?_ hWfin_one (by norm_num) ?_
                · have := hS_nn 0; linarith
                · have := hS_nn 0; have := hcId_nn; linarith
        | (l' + 1) =>
          have hNdD : iteratedCovGrad (I := I) g₀ 1 1 (l' + 1) Dg =
              iteratedCovGrad (I := I) g₀ 1 1 (l' + 1) sF := by
            rw [hDg_eq, iteratedCovGrad_sub (I := I) g₀ 1 1 (l' + 1) sF InsId]
            rw [hInsId_def,
              iteratedCovGrad_slotInsert_fullRaised_id_succ_eq_zero (I := I) (M := M) g₀ l']
            rw [sub_zero]
          rw [hNdD]
          refine le_trans (hS g₁ T htie hδ_le hδ0 hbound (l' + 1) x) ?_
          have hgrid : Combinatorics.antidiagonalTupleGrid b (l' + 1) ≤ Wfin := by
            rw [Combinatorics.antidiagonalTupleGrid_eq_boundedFactorGrid b
              (show l' + 1 ≤ i + 1 from by omega)]
            rw [hWfin_def]
            exact Combinatorics.boundedFactorGrid_le_boundedFactorGridWindow b hb (by omega)
          calc S (l' + 1) * Combinatorics.antidiagonalTupleGrid b (l' + 1)
              ≤ S (l' + 1) * Wfin := mul_le_mul_of_nonneg_left hgrid (hS_nn (l' + 1))
            _ ≤ (2 * S 0 + 2 * cId + S (l' + 1)) * Wfin := by
                refine mul_le_mul_of_nonneg_right ?_ hWfin_nn
                have := hS_nn 0
                linarith [hcId_nn]
      have hterm : ∀ a' ∈ Finset.range (i + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + a') x
              ((iteratedCovGrad (I := I) g₀ 1 1 a' B0f).toSection x) *
            (∑ l ∈ Finset.range (i + 1 - a'),
              riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
                ((iteratedCovGrad (I := I) g₀ 1 1 l Dg).toSection x)) ≤
          (cB a' * (∑ l ∈ Finset.range (i + 1 - a'), (2 * S 0 + 2 * cId + S l))) * Wfin := by
        intro a' ha'
        rw [Finset.mem_range] at ha'
        have hB : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + a') x
            ((iteratedCovGrad (I := I) g₀ 1 1 a' B0f).toSection x) ≤ cB a' := by
          have h := hcB a' x
          rw [hB0f_def]
          exact h
        have hDsum : (∑ l ∈ Finset.range (i + 1 - a'),
            riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
              ((iteratedCovGrad (I := I) g₀ 1 1 l Dg).toSection x)) ≤
            (∑ l ∈ Finset.range (i + 1 - a'), (2 * S 0 + 2 * cId + S l)) * Wfin := by
          rw [Finset.sum_mul]
          refine Finset.sum_le_sum (fun l hl => ?_)
          rw [Finset.mem_range] at hl
          exact hDjet l (by omega)
        calc riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + a') x
              ((iteratedCovGrad (I := I) g₀ 1 1 a' B0f).toSection x) *
            (∑ l ∈ Finset.range (i + 1 - a'),
              riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
                ((iteratedCovGrad (I := I) g₀ 1 1 l Dg).toSection x))
            ≤ cB a' * ((∑ l ∈ Finset.range (i + 1 - a'),
                (2 * S 0 + 2 * cId + S l)) * Wfin) := by
              refine mul_le_mul hB hDsum ?_ (hcB_nn a')
              exact Finset.sum_nonneg (fun l _ =>
                riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 (1 + l) x _)
          _ = (cB a' * (∑ l ∈ Finset.range (i + 1 - a'),
                (2 * S 0 + 2 * cId + S l))) * Wfin := by ring
      calc appCcGdiag (E := E) i *
            ∑ a' ∈ Finset.range (i + 1),
              riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + a') x
                  ((iteratedCovGrad (I := I) g₀ 1 1 a' B0f).toSection x) *
                ∑ l ∈ Finset.range (i + 1 - a'),
                  riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + l) x
                    ((iteratedCovGrad (I := I) g₀ 1 1 l Dg).toSection x)
          ≤ appCcGdiag (E := E) i *
            ∑ a' ∈ Finset.range (i + 1),
              (cB a' * (∑ l ∈ Finset.range (i + 1 - a'),
                (2 * S 0 + 2 * cId + S l))) * Wfin :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm)
              (appCcGdiag_nonneg (E := E) i)
        _ = (appCcGdiag (E := E) i * ∑ a' ∈ Finset.range (i + 1),
              cB a' * (∑ l ∈ Finset.range (i + 1 - a'), (2 * S 0 + 2 * cId + S l))) *
            Wfin := by
            rw [← Finset.sum_mul]
            ring
    have hP23 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
        (P2t.toSection x + P3t.toSection x) ≤
        2 * (((i : ℝ) * ∑ k ∈ Finset.range i,
            appCcGdiag (E := E) i * CDel (i - (k + 1)) * S (k + 1) *
              Combinatorics.windowPairCellCount ((i - (k + 1)) + 3) (k + 2)) * Wfin) +
        2 * ((appCcGdiag (E := E) i * ∑ a' ∈ Finset.range (i + 1),
            cB a' * (∑ l ∈ Finset.range (i + 1 - a'), (2 * S 0 + 2 * cId + S l))) * Wfin) := by
      refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 1 (1 + i) x _ _) ?_
      exact add_le_add (mul_le_mul_of_nonneg_left hP2 (by norm_num))
        (mul_le_mul_of_nonneg_left hP3 (by norm_num))
    calc 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x (P1t.toSection x) +
        2 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
          (P2t.toSection x + P3t.toSection x)
        ≤ 2 * (2 * (cPhi * (KcA i)) * S 0 * Wfin) +
          2 * (2 * (((i : ℝ) * ∑ k ∈ Finset.range i,
              appCcGdiag (E := E) i * CDel (i - (k + 1)) * S (k + 1) *
                Combinatorics.windowPairCellCount ((i - (k + 1)) + 3) (k + 2)) * Wfin) +
            2 * ((appCcGdiag (E := E) i * ∑ a' ∈ Finset.range (i + 1),
              cB a' * (∑ l ∈ Finset.range (i + 1 - a'),
                (2 * S 0 + 2 * cId + S l))) * Wfin)) :=
          add_le_add (mul_le_mul_of_nonneg_left hP1 (by norm_num))
            (mul_le_mul_of_nonneg_left hP23 (by norm_num))
      _ = (4 * (cPhi * (KcA i) * S 0) +
          4 * ((i : ℝ) * ∑ k ∈ Finset.range i,
            appCcGdiag (E := E) i * CDel (i - (k + 1)) * S (k + 1) *
              Combinatorics.windowPairCellCount ((i - (k + 1)) + 3) (k + 2)) +
          4 * (appCcGdiag (E := E) i * ∑ a' ∈ Finset.range (i + 1),
            cB a' * (∑ l ∈ Finset.range (i + 1 - a'), (2 * S 0 + 2 * cId + S l)))) *
          Wfin := by ring

end TopSeparatedRungSlotInsert

section TopSeparatedRungLoweringSplit

open DifferentialGeometry.Integral.DivergenceTheorem

set_option backward.isDefEq.respectTransparency false

set_option linter.unusedVariables false in
theorem rfns_iteratedCovGrad_riemannG1LoweringDifference_topSeparated_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Ktop : ℝ, 0 ≤ Ktop ∧ ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (i : ℕ),
        ∃ Hd : SmoothCcTensor g₀ 0 (4 + i),
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x (Hd.toSection x) ≤
              Ktop * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x)) ∧
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
                ((iteratedCovGrad (I := I) g₀ 0 4 i
                    (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁ -
                      riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁) -
                  Hd).toSection x) ≤
              Kc i * Combinatorics.boundedFactorGridWindow
                (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x)) (i + 1) (i + 3)) := by
  classical
  obtain ⟨KtA, hKtA_nn, KcA, hKcA_nn, hA⟩ :=
    rfns_iteratedCovGrad_riemannLoweredBackgroundDifference_topSeparated_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨CA, hCA_nn, hCA⟩ :=
    rfns_iteratedCovGrad_riemannLoweredBackgroundDifference_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨cfix, hcfix_nn, hcfix⟩ := exists_backgroundJet_rfns_bound (I := I) (M := M) g₀ 0 4
    (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)
  set n : ℝ := (Module.finrank ℝ E : ℝ) with hn_def
  have hn_nn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  refine ⟨n ^ 5 * KtA, mul_nonneg (pow_nonneg hn_nn 5) hKtA_nn, ?_⟩
  refine ⟨fun i => 2 * (n ^ 5 * (2 * KcA i + 2 * cfix i)) +
      2 * ((i : ℝ) * appCcGdiag (E := E) i *
        ∑ k ∈ Finset.range i, 2 * n ^ 3 * (CA k + cfix k)),
    fun i => by
      have h1 : (0 : ℝ) ≤ n ^ 5 * (2 * KcA i + 2 * cfix i) :=
        mul_nonneg (pow_nonneg hn_nn 5) (by have := hKcA_nn i; have := hcfix_nn i; linarith)
      have h2 : (0 : ℝ) ≤ (i : ℝ) * appCcGdiag (E := E) i *
          ∑ k ∈ Finset.range i, 2 * n ^ 3 * (CA k + cfix k) :=
        mul_nonneg (mul_nonneg (Nat.cast_nonneg i) (appCcGdiag_nonneg (E := E) i))
          (Finset.sum_nonneg fun k _ => mul_nonneg
            (mul_nonneg (by norm_num) (pow_nonneg hn_nn 3))
            (by have := hCA_nn k; have := hcfix_nn k; linarith))
      linarith, ?_⟩
  intro g₁ T htie δ hδ_le hδ0 hbound i
  obtain ⟨HdA, hHdA_head, hHdA_res⟩ := hA g₁ T htie hδ_le hδ0 hbound i
  set Dress : SmoothCcTensor g₀ 4 4 :=
    slotInsertEndoCc (I := I) (M := M) g₀ 3
      (perturbationSharpEndoField (I := I) (M := M) g₀ T) with hDress_def
  set RLCmix : SmoothCcTensor g₀ 0 4 := riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁
    with hRLCmix_def
  set RLCfix : SmoothCcTensor g₀ 0 4 := riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀
    with hRLCfix_def
  set RLD : SmoothCcTensor g₀ 0 4 :=
    riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁ with hRLD_def
  have hmix_split : RLCmix = RLD + RLCfix := by
    rw [hRLD_def, riemannLoweredBackgroundDifference, ← hRLCmix_def, ← hRLCfix_def]
    abel
  set WS : SmoothCcTensor g₀ 0 4 :=
    domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1) RLCmix with hWS_def
  set Ybig : SmoothCcTensor g₀ 0 4 :=
    appCcRS (I := I) (M := M) g₀ 0 4 4 Dress WS with hYbig_def
  have hrepr : riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁ -
      riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁ =
      domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1) Ybig := by
    rw [hYbig_def, hWS_def, hRLCmix_def, hDress_def]
    exact riemannG1LoweringDifference_slotInsert_repr (I := I) (M := M) g₀ g₁ T htie
  obtain ⟨σo, hσo⟩ := tsExists_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
    (Equiv.swap (0 : Fin 4) 1) Ybig i
  obtain ⟨σw, hσw⟩ := tsExists_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
    (Equiv.swap (0 : Fin 4) 1) RLCmix i
  set Hd0 : SmoothCcTensor g₀ 0 (4 + i) :=
    appCcRS (I := I) (M := M) g₀ 0 (4 + i) (4 + i)
      (appCcLeibnizPsi (I := I) (M := M) g₀ 4 4 Dress i i)
      (domDomCongrSection (I := I) g₀ σw HdA) with hHd0_def
  have hDress0 : ∀ y : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 4 4 y (Dress.toSection y) ≤ n ^ 5 := by
    intro y
    have h1 := rfns_iteratedCovGrad_slotInsert3_perturbationSharp_le (I := I) (M := M)
      g₀ T 0 y
    rw [iteratedCovGrad_zero, iteratedCovGrad_zero] at h1
    have h2 := rfns_symmS_zero_le_of_ball (I := I) (M := M) g₀ T hδ0 hbound y
    have hδ1 : δ ^ 2 ≤ 1 := by nlinarith [hδ0, lt_of_le_of_lt hδ_le hδ₀]
    have h3 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 y
        ((symmS (I := I) (M := M) g₀ T).toSection y) ≤ n ^ 2 := by
      refine le_trans h2 ?_
      calc n ^ 2 * δ ^ 2 ≤ n ^ 2 * 1 :=
            mul_le_mul_of_nonneg_left hδ1 (pow_nonneg hn_nn 2)
        _ = n ^ 2 := by ring
    rw [hDress_def]
    refine le_trans h1 ?_
    calc n ^ 3 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 y
          ((symmS (I := I) (M := M) g₀ T).toSection y)
        ≤ n ^ 3 * n ^ 2 := mul_le_mul_of_nonneg_left h3 (pow_nonneg hn_nn 3)
      _ = n ^ 5 := by ring
  refine ⟨domDomCongrSection (I := I) g₀ σo Hd0, ?_, ?_⟩
  · intro x
    rw [tsRfns_domDomCongrSection_zero (I := I) (M := M) g₀ σo Hd0 x]
    rw [hHd0_def]
    refine le_trans (rfns_appCcRS_appCcLeibnizPsi_diag_le (I := I) (M := M) g₀ 0 4 4
      Dress i (domDomCongrSection (I := I) g₀ σw HdA) x) ?_
    rw [tsRfns_domDomCongrSection_zero (I := I) (M := M) g₀ σw HdA x]
    have hb_nn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
      ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x)
    calc riemannianFiberNormSq (I := I) (M := M) g₀ 4 4 x (Dress.toSection x) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x (HdA.toSection x)
        ≤ n ^ 5 * (KtA * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x)) := by
          refine mul_le_mul (hDress0 x) (hHdA_head x) ?_ (pow_nonneg hn_nn 5)
          exact riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (4 + i) x _
      _ = n ^ 5 * KtA * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x) := by ring
  · intro x
    set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
      ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x) with hb_def
    have hb : ∀ l, 0 ≤ b l :=
      fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
    set Wfin : ℝ := Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) with hWfin_def
    have hWfin_nn : 0 ≤ Wfin :=
      Combinatorics.boundedFactorGridWindow_nonneg b hb (i + 1) (i + 3)
    have hWfin_one : 1 ≤ Wfin :=
      Combinatorics.one_le_boundedFactorGridWindow b hb (by omega)
    have hdiff : iteratedCovGrad (I := I) g₀ 0 4 i
          (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁ -
            riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁) -
          domDomCongrSection (I := I) g₀ σo Hd0 =
        domDomCongrSection (I := I) g₀ σo
          (iteratedCovGrad (I := I) g₀ 0 4 i Ybig - Hd0) := by
      rw [hrepr, hσo]
      rw [tsDomDomCongrSection_sub (I := I) (M := M) g₀ σo]
    rw [hdiff]
    rw [tsRfns_domDomCongrSection_zero (I := I) (M := M) g₀ σo _ x]
    have hWSsplit : iteratedCovGrad (I := I) g₀ 0 4 i WS -
        domDomCongrSection (I := I) g₀ σw HdA =
        domDomCongrSection (I := I) g₀ σw
          ((iteratedCovGrad (I := I) g₀ 0 4 i RLD - HdA) +
            iteratedCovGrad (I := I) g₀ 0 4 i RLCfix) := by
      rw [hWS_def, hσw]
      rw [← tsDomDomCongrSection_sub (I := I) (M := M) g₀ σw]
      rw [show iteratedCovGrad (I := I) g₀ 0 4 i RLCmix =
          iteratedCovGrad (I := I) g₀ 0 4 i RLD +
            iteratedCovGrad (I := I) g₀ 0 4 i RLCfix from by
        rw [← iteratedCovGrad_add (I := I) g₀ 0 4 i RLD RLCfix, ← hmix_split]]
      rw [add_sub_right_comm]
    have hfirst : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
        ((appCcRS (I := I) (M := M) g₀ 0 (4 + i) (4 + i)
          (appCcLeibnizPsi (I := I) (M := M) g₀ 4 4 Dress i i)
          (iteratedCovGrad (I := I) g₀ 0 4 i WS -
            domDomCongrSection (I := I) g₀ σw HdA)).toSection x) ≤
        n ^ 5 * ((2 * KcA i + 2 * cfix i) * Wfin) := by
      refine le_trans (rfns_appCcRS_appCcLeibnizPsi_diag_le (I := I) (M := M) g₀ 0 4 4
        Dress i _ x) ?_
      have hinner : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
          ((iteratedCovGrad (I := I) g₀ 0 4 i WS -
            domDomCongrSection (I := I) g₀ σw HdA).toSection x) ≤
          (2 * KcA i + 2 * cfix i) * Wfin := by
        rw [hWSsplit]
        rw [tsRfns_domDomCongrSection_zero (I := I) (M := M) g₀ σw _ x]
        rw [show (((iteratedCovGrad (I := I) g₀ 0 4 i RLD - HdA) +
              iteratedCovGrad (I := I) g₀ 0 4 i RLCfix).toSection x) =
            (iteratedCovGrad (I := I) g₀ 0 4 i RLD - HdA).toSection x +
              (iteratedCovGrad (I := I) g₀ 0 4 i RLCfix).toSection x from by
          rw [SmoothCcTensor.toSection_add]; rfl]
        refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 (4 + i)
          x _ _) ?_
        have h1 := hHdA_res x
        have h2 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 4 i RLCfix).toSection x) ≤
            cfix i * Wfin := by
          have h2a : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
              ((iteratedCovGrad (I := I) g₀ 0 4 i RLCfix).toSection x) ≤ cfix i := by
            rw [hRLCfix_def]
            exact hcfix i x
          calc riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
                ((iteratedCovGrad (I := I) g₀ 0 4 i RLCfix).toSection x)
              ≤ cfix i := h2a
            _ = cfix i * 1 := by ring
            _ ≤ cfix i * Wfin := mul_le_mul_of_nonneg_left hWfin_one (hcfix_nn i)
        calc 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
              ((iteratedCovGrad (I := I) g₀ 0 4 i RLD - HdA).toSection x) +
            2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
              ((iteratedCovGrad (I := I) g₀ 0 4 i RLCfix).toSection x)
            ≤ 2 * (KcA i * Wfin) + 2 * (cfix i * Wfin) := by
              refine add_le_add (mul_le_mul_of_nonneg_left h1 (by norm_num))
                (mul_le_mul_of_nonneg_left h2 (by norm_num))
          _ = (2 * KcA i + 2 * cfix i) * Wfin := by ring
      refine mul_le_mul (hDress0 x) hinner
        (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (4 + i) x _)
        (pow_nonneg hn_nn 5)
    have hcorr : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
        ((∑ k ∈ Finset.range i,
          appCcRS (I := I) (M := M) g₀ 0 (4 + k) (4 + i)
            (appCcLeibnizPsi (I := I) (M := M) g₀ 4 4 Dress i k)
            (iteratedCovGrad (I := I) g₀ 0 4 k WS)).toSection x) ≤
        (i : ℝ) * appCcGdiag (E := E) i *
          ∑ k ∈ Finset.range i, (2 * n ^ 3 * (CA k + cfix k)) * Wfin := by
      refine le_trans (rfns_appCcRS_argLower_le (I := I) (M := M) g₀ 0 4 4 Dress WS i x) ?_
      rw [mul_assoc, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg i)
      refine mul_le_mul_of_nonneg_left ?_ (appCcGdiag_nonneg (E := E) i)
      refine Finset.sum_le_sum (fun k hk => ?_)
      rw [Finset.mem_range] at hk
      have hDjet : riemannianFiberNormSq (I := I) (M := M) g₀ 4 (4 + (i - k)) x
          ((iteratedCovGrad (I := I) g₀ 4 4 (i - k) Dress).toSection x) ≤
          n ^ 3 * b (i - k) := by
        rw [hDress_def]
        refine le_trans (rfns_iteratedCovGrad_slotInsert3_perturbationSharp_le
          (I := I) (M := M) g₀ T (i - k) x) ?_
        refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hn_nn 3)
        exact rfns_iteratedCovGrad_symmS_pointwise (I := I) (M := M) g₀ T (i - k) x
      have hWjet : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + k) x
          ((iteratedCovGrad (I := I) g₀ 0 4 k WS).toSection x) ≤
          2 * (CA k * (∑ k' ∈ Finset.range (k + 3),
            Combinatorics.antidiagonalTupleGrid b k')) + 2 * cfix k := by
        rw [hWS_def]
        rw [riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M)
          g₀ (Equiv.swap (0 : Fin 4) 1) RLCmix k x]
        rw [show iteratedCovGrad (I := I) g₀ 0 4 k RLCmix =
            iteratedCovGrad (I := I) g₀ 0 4 k RLD +
              iteratedCovGrad (I := I) g₀ 0 4 k RLCfix from by
          rw [← iteratedCovGrad_add (I := I) g₀ 0 4 k RLD RLCfix, ← hmix_split]]
        rw [show ((iteratedCovGrad (I := I) g₀ 0 4 k RLD +
              iteratedCovGrad (I := I) g₀ 0 4 k RLCfix).toSection x) =
            (iteratedCovGrad (I := I) g₀ 0 4 k RLD).toSection x +
              (iteratedCovGrad (I := I) g₀ 0 4 k RLCfix).toSection x from by
          rw [SmoothCcTensor.toSection_add]; rfl]
        refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 (4 + k)
          x _ _) ?_
        have h1 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + k) x
            ((iteratedCovGrad (I := I) g₀ 0 4 k RLD).toSection x) ≤
            CA k * (∑ k' ∈ Finset.range (k + 3),
              Combinatorics.antidiagonalTupleGrid b k') := by
          have h := hCA g₁ T htie hδ_le hδ0 hbound k x
          rw [hRLD_def]
          exact h
        have h2 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + k) x
            ((iteratedCovGrad (I := I) g₀ 0 4 k RLCfix).toSection x) ≤ cfix k := by
          rw [hRLCfix_def]; exact hcfix k x
        exact add_le_add (mul_le_mul_of_nonneg_left h1 (by norm_num))
          (mul_le_mul_of_nonneg_left h2 (by norm_num))
      have hbW : b (i - k) * (∑ k' ∈ Finset.range (k + 3),
          Combinatorics.antidiagonalTupleGrid b k') ≤ Wfin := by
        refine le_trans (mul_le_mul_of_nonneg_left
          (tsTgridSum_le_boundedWindow b hb (show k + 3 ≤ (i + 1) + 1 from by omega)
            (le_refl (k + 3))) (hb (i - k))) ?_
        refine le_trans (Combinatorics.single_factor_mul_boundedFactorGridWindow_le b hb
          (show 1 ≤ i - k from by omega) (show i - k ≤ i + 1 from by omega)) ?_
        rw [hWfin_def]
        refine Combinatorics.boundedFactorGridWindow_mono b hb (le_refl _) ?_
        omega
      have hbAlone : b (i - k) ≤ Wfin := by
        have h1 := Combinatorics.single_factor_mul_boundedFactorGrid_le b hb 0 (i - k)
          (show 1 ≤ i - k from by omega) (show i - k ≤ i + 1 from by omega)
        rw [Combinatorics.boundedFactorGrid_zero, mul_one] at h1
        refine le_trans h1 ?_
        rw [show 0 + (i - k) = i - k from by omega, hWfin_def]
        exact Combinatorics.boundedFactorGrid_le_boundedFactorGridWindow b hb (by omega)
      calc riemannianFiberNormSq (I := I) (M := M) g₀ 4 (4 + (i - k)) x
            ((iteratedCovGrad (I := I) g₀ 4 4 (i - k) Dress).toSection x) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + k) x
            ((iteratedCovGrad (I := I) g₀ 0 4 k WS).toSection x)
          ≤ (n ^ 3 * b (i - k)) *
            (2 * (CA k * (∑ k' ∈ Finset.range (k + 3),
              Combinatorics.antidiagonalTupleGrid b k')) + 2 * cfix k) := by
            refine mul_le_mul hDjet hWjet ?_ ?_
            · exact riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (4 + k) x _
            · exact mul_nonneg (pow_nonneg hn_nn 3) (hb (i - k))
        _ = 2 * n ^ 3 * CA k *
              (b (i - k) * (∑ k' ∈ Finset.range (k + 3),
                Combinatorics.antidiagonalTupleGrid b k')) +
            2 * n ^ 3 * cfix k * b (i - k) := by ring
        _ ≤ 2 * n ^ 3 * CA k * Wfin + 2 * n ^ 3 * cfix k * Wfin := by
            refine add_le_add ?_ ?_
            · refine mul_le_mul_of_nonneg_left hbW ?_
              exact mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hn_nn 3)) (hCA_nn k)
            · refine mul_le_mul_of_nonneg_left hbAlone ?_
              exact mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hn_nn 3))
                (hcfix_nn k)
        _ = (2 * n ^ 3 * (CA k + cfix k)) * Wfin := by ring
    have hsplitY : iteratedCovGrad (I := I) g₀ 0 4 i Ybig - Hd0 =
        appCcRS (I := I) (M := M) g₀ 0 (4 + i) (4 + i)
            (appCcLeibnizPsi (I := I) (M := M) g₀ 4 4 Dress i i)
            (iteratedCovGrad (I := I) g₀ 0 4 i WS -
              domDomCongrSection (I := I) g₀ σw HdA) +
          ∑ k ∈ Finset.range i,
            appCcRS (I := I) (M := M) g₀ 0 (4 + k) (4 + i)
              (appCcLeibnizPsi (I := I) (M := M) g₀ 4 4 Dress i k)
              (iteratedCovGrad (I := I) g₀ 0 4 k WS) := by
      rw [hYbig_def]
      rw [iteratedCovGrad_appCcRS_eq_argCorner_add_lower (I := I) (M := M) g₀ 0 4 4
        Dress WS i]
      rw [hHd0_def]
      rw [appCcRS_sub_right_cc (I := I) (M := M) g₀ 0 (4 + i) (4 + i)
        (appCcLeibnizPsi (I := I) (M := M) g₀ 4 4 Dress i i)
        (iteratedCovGrad (I := I) g₀ 0 4 i WS)
        (domDomCongrSection (I := I) g₀ σw HdA)]
      exact add_sub_right_comm _ _ _
    rw [hsplitY]
    rw [show ((appCcRS (I := I) (M := M) g₀ 0 (4 + i) (4 + i)
          (appCcLeibnizPsi (I := I) (M := M) g₀ 4 4 Dress i i)
          (iteratedCovGrad (I := I) g₀ 0 4 i WS -
            domDomCongrSection (I := I) g₀ σw HdA) +
        ∑ k ∈ Finset.range i,
          appCcRS (I := I) (M := M) g₀ 0 (4 + k) (4 + i)
            (appCcLeibnizPsi (I := I) (M := M) g₀ 4 4 Dress i k)
            (iteratedCovGrad (I := I) g₀ 0 4 k WS)).toSection x) =
        (appCcRS (I := I) (M := M) g₀ 0 (4 + i) (4 + i)
          (appCcLeibnizPsi (I := I) (M := M) g₀ 4 4 Dress i i)
          (iteratedCovGrad (I := I) g₀ 0 4 i WS -
            domDomCongrSection (I := I) g₀ σw HdA)).toSection x +
        (∑ k ∈ Finset.range i,
          appCcRS (I := I) (M := M) g₀ 0 (4 + k) (4 + i)
            (appCcLeibnizPsi (I := I) (M := M) g₀ 4 4 Dress i k)
            (iteratedCovGrad (I := I) g₀ 0 4 k WS)).toSection x from by
      rw [SmoothCcTensor.toSection_add]; rfl]
    refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 (4 + i) x _ _) ?_
    calc 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
          ((appCcRS (I := I) (M := M) g₀ 0 (4 + i) (4 + i)
            (appCcLeibnizPsi (I := I) (M := M) g₀ 4 4 Dress i i)
            (iteratedCovGrad (I := I) g₀ 0 4 i WS -
              domDomCongrSection (I := I) g₀ σw HdA)).toSection x) +
        2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
          ((∑ k ∈ Finset.range i,
            appCcRS (I := I) (M := M) g₀ 0 (4 + k) (4 + i)
              (appCcLeibnizPsi (I := I) (M := M) g₀ 4 4 Dress i k)
              (iteratedCovGrad (I := I) g₀ 0 4 k WS)).toSection x)
        ≤ 2 * (n ^ 5 * ((2 * KcA i + 2 * cfix i) * Wfin)) +
          2 * ((i : ℝ) * appCcGdiag (E := E) i *
            ∑ k ∈ Finset.range i, (2 * n ^ 3 * (CA k + cfix k)) * Wfin) :=
        add_le_add (mul_le_mul_of_nonneg_left hfirst (by norm_num))
          (mul_le_mul_of_nonneg_left hcorr (by norm_num))
      _ = (2 * (n ^ 5 * (2 * KcA i + 2 * cfix i)) +
          2 * ((i : ℝ) * appCcGdiag (E := E) i *
            ∑ k ∈ Finset.range i, 2 * n ^ 3 * (CA k + cfix k))) * Wfin := by
          rw [← Finset.sum_mul]
          ring

end TopSeparatedRungLoweringSplit

section TopSeparatedRungCurvCoeff

open DifferentialGeometry.Integral.DivergenceTheorem

set_option backward.isDefEq.respectTransparency false

set_option linter.unusedSectionVars false in
private lemma tsSlotInsertEndoCc_succ_eq_reindex_slotExtend
    (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (Λ : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)) :
    slotInsertEndoCc (I := I) (M := M) g₀ (s + 1) Λ =
      reindexCoeffGen (I := I) (M := M) g₀ (s + 1 + 1) (s + 1 + 1)
        (rsDomDomCongrSection (I := I) (M := M) g₀ (s + 1 + 1) (s + 1 + 1)
          (Equiv.swap (0 : Fin (s + 1 + 1)) 1)
          (slotExtend (I := I) (M := M) g₀ (s + 1) (s + 1)
            (slotInsertEndoCc (I := I) (M := M) g₀ s Λ)))
        (Equiv.swap (0 : Fin (s + 1 + 1)) 1) := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  change Tensor0SSpace.toModel
      ((show Tensor0SSpace (s + 1 + 1) I x →L[ℝ] Tensor0SSpace (s + 1 + 1) I x from
        (slotInsertEndoCc (I := I) (M := M) g₀ (s + 1) Λ).toSection x) D) m =
    Tensor0SSpace.toModel
      ((show Tensor0SSpace (s + 1 + 1) I x →L[ℝ] Tensor0SSpace (s + 1 + 1) I x from
        (reindexCoeffGen (I := I) (M := M) g₀ (s + 1 + 1) (s + 1 + 1)
          (rsDomDomCongrSection (I := I) (M := M) g₀ (s + 1 + 1) (s + 1 + 1)
            (Equiv.swap (0 : Fin (s + 1 + 1)) 1)
            (slotExtend (I := I) (M := M) g₀ (s + 1) (s + 1)
              (slotInsertEndoCc (I := I) (M := M) g₀ s Λ)))
          (Equiv.swap (0 : Fin (s + 1 + 1)) 1)).toSection x) D) m
  rw [slotInsertEndoCc_toSection, slotInsertEndoFib_apply_eval]
  rw [reindexCoeffGen_toSection, reindexCoeffFibGen_apply, rsDomDomCongrSection_toSection,
    toModel_rsDomDomCongr_apply, ContinuousMultilinearMap.domDomCongr_apply, slotExtend_toSection]
  rw [show (fun k : Fin (s + 1 + 1) => m ((Equiv.swap (0 : Fin (s + 1 + 1)) 1) k)) =
      Fin.cons (m 1) (fun j : Fin (s + 1) =>
        m ((Equiv.swap (0 : Fin (s + 1 + 1)) 1) (Fin.succ j))) from by
    funext k
    refine Fin.cases ?_ (fun j => ?_) k
    · simp only [Fin.cons_zero, Equiv.swap_apply_left]
    · simp only [Fin.cons_succ]]
  rw [slotExtendFib_apply_eval]
  rw [slotInsertEndoCc_toSection, slotInsertEndoFib_apply_eval,
    TensorMultilinear.tensor0S_curry_apply_eval,
    Tensor0SSpace.toModel_ofModel, ContinuousMultilinearMap.domDomCongr_apply]
  have hswap_succ0 : (Equiv.swap (0 : Fin (s + 1 + 1)) 1) (Fin.succ (0 : Fin (s + 1))) = 0 := by
    rw [show (Fin.succ (0 : Fin (s + 1)) : Fin (s + 1 + 1)) = 1 from rfl, Equiv.swap_apply_right]
  rw [hswap_succ0]
  congr 1
  funext k
  refine Fin.cases ?_ (fun k₁ => ?_) k
  · rw [Equiv.swap_apply_left,
      show (1 : Fin (s + 1 + 1)) = Fin.succ (0 : Fin (s + 1)) from rfl, Fin.cons_succ,
      Function.update_self, Function.update_self]
  · refine Fin.cases ?_ (fun k₂ => ?_) k₁
    · have h10 : (1 : Fin (s + 1 + 1)) ≠ 0 := by
        rw [show (1 : Fin (s + 1 + 1)) = Fin.succ (0 : Fin (s + 1)) from rfl]
        exact Fin.succ_ne_zero _
      rw [show (Fin.succ (0 : Fin (s + 1)) : Fin (s + 1 + 1)) = 1 from rfl,
        Function.update_of_ne h10, Equiv.swap_apply_right, Fin.cons_zero]
    · have hne0 : (Fin.succ (Fin.succ k₂) : Fin (s + 1 + 1)) ≠ 0 := Fin.succ_ne_zero _
      have hne1 : (Fin.succ (Fin.succ k₂) : Fin (s + 1 + 1)) ≠ 1 := by
        rw [show (1 : Fin (s + 1 + 1)) = Fin.succ (0 : Fin (s + 1)) from rfl]
        exact fun h => Fin.succ_ne_zero _ (Fin.succ_injective _ h)
      rw [Function.update_of_ne hne0, Equiv.swap_apply_of_ne_of_ne hne0 hne1, Fin.cons_succ,
        Function.update_of_ne (Fin.succ_ne_zero k₂)]
      change m (Fin.succ (Fin.succ k₂)) =
        m ((Equiv.swap (0 : Fin (s + 1 + 1)) 1) (Fin.succ (Fin.succ k₂)))
      rw [Equiv.swap_apply_of_ne_of_ne hne0 hne1]

set_option linter.unusedSectionVars false in
private lemma tsReindexCoeffGen_sub (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (R₁ R₂ : SmoothCcTensor g₀ r s) (σ' : Equiv.Perm (Fin r)) :
    reindexCoeffGen (I := I) (M := M) g₀ r s (R₁ - R₂) σ' =
      reindexCoeffGen (I := I) (M := M) g₀ r s R₁ σ' -
        reindexCoeffGen (I := I) (M := M) g₀ r s R₂ σ' := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((reindexCoeffGen (I := I) (M := M) g₀ r s R₁ σ' -
        reindexCoeffGen (I := I) (M := M) g₀ r s R₂ σ').toSection x) =
      (reindexCoeffGen (I := I) (M := M) g₀ r s R₁ σ').toSection x -
        (reindexCoeffGen (I := I) (M := M) g₀ r s R₂ σ').toSection x from by
    rw [SmoothCcTensor.toSection_sub]; rfl]
  rw [reindexCoeffGen_toSection, reindexCoeffGen_toSection, reindexCoeffGen_toSection]
  rw [show ((R₁ - R₂).toSection x) = R₁.toSection x - R₂.toSection x from by
    rw [SmoothCcTensor.toSection_sub]; rfl]
  rw [reindexCoeffFibGen, reindexCoeffFibGen, reindexCoeffFibGen]
  exact ContinuousLinearMap.sub_comp _ _ _

set_option linter.unusedSectionVars false in
private lemma tsRfns_reindexCoeffGen_zero (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (R : SmoothCcTensor g₀ r s) (σ' : Equiv.Perm (Fin r)) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ r s x
        ((reindexCoeffGen (I := I) (M := M) g₀ r s R σ').toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ r s x (R.toSection x) := by
  have h := rfns_iteratedCovGrad_reindexCoeffGen_eq (I := I) (M := M) g₀ r s R σ' 0 x
  rw [iteratedCovGrad_zero, iteratedCovGrad_zero] at h
  exact h

set_option linter.unusedSectionVars false in
private lemma tsExists_slotExtend_headTransport (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (V : SmoothCcTensor g₀ r s) (i : ℕ) (HV : SmoothCcTensor g₀ r (s + i)) :
    ∃ HW : SmoothCcTensor g₀ (r + 1) ((s + 1) + i),
      (∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g₀ (r + 1) ((s + 1) + i) x
            (HW.toSection x) ≤
          (Module.finrank ℝ E : ℝ) *
            riemannianFiberNormSq (I := I) (M := M) g₀ r (s + i) x (HV.toSection x)) ∧
      (∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g₀ (r + 1) ((s + 1) + i) x
            ((iteratedCovGrad (I := I) g₀ (r + 1) (s + 1) i
                (slotExtend (I := I) (M := M) g₀ r s V) - HW).toSection x) ≤
          (Module.finrank ℝ E : ℝ) *
            riemannianFiberNormSq (I := I) (M := M) g₀ r (s + i) x
              ((iteratedCovGrad (I := I) g₀ r s i V - HV).toSection x)) := by
  obtain ⟨σa, hσa⟩ := exists_iteratedCovGrad_slotExtend_rsDomDomCongr (I := I) (M := M)
    g₀ r s V i
  refine ⟨rsDomDomCongrSection (I := I) (M := M) g₀ (r + 1) ((s + 1) + i) σa
    (castRankCc_db g₀ (r + 1) (by omega : (s + i) + 1 = (s + 1) + i)
      (slotExtend (I := I) (M := M) g₀ r (s + i) HV)), ?_, ?_⟩
  · intro x
    rw [tsRfns_rsDomDomCongrSection_zero (I := I) (M := M) g₀ (r + 1) ((s + 1) + i) σa _ x]
    rw [tsRfns_castRankCc_db_zero (I := I) (M := M) g₀ (r + 1)
      (by omega : (s + i) + 1 = (s + 1) + i) _ x]
    rw [rfns_slotExtend_eq (I := I) (M := M) g₀ r (s + i) HV x]
  · intro x
    have hpt : ((iteratedCovGrad (I := I) g₀ (r + 1) (s + 1) i
          (slotExtend (I := I) (M := M) g₀ r s V) -
        rsDomDomCongrSection (I := I) (M := M) g₀ (r + 1) ((s + 1) + i) σa
          (castRankCc_db g₀ (r + 1) (by omega : (s + i) + 1 = (s + 1) + i)
            (slotExtend (I := I) (M := M) g₀ r (s + i) HV))).toSection x) =
        rsDomDomCongr (I := I) (M := M) σa
          ((castRankCc_db g₀ (r + 1) (by omega : (s + i) + 1 = (s + 1) + i)
            (slotExtend (I := I) (M := M) g₀ r (s + i)
              (iteratedCovGrad (I := I) g₀ r s i V - HV))).toSection x) := by
      rw [show ((iteratedCovGrad (I := I) g₀ (r + 1) (s + 1) i
            (slotExtend (I := I) (M := M) g₀ r s V) -
          rsDomDomCongrSection (I := I) (M := M) g₀ (r + 1) ((s + 1) + i) σa
            (castRankCc_db g₀ (r + 1) (by omega : (s + i) + 1 = (s + 1) + i)
              (slotExtend (I := I) (M := M) g₀ r (s + i) HV))).toSection x) =
          (iteratedCovGrad (I := I) g₀ (r + 1) (s + 1) i
            (slotExtend (I := I) (M := M) g₀ r s V)).toSection x -
          (rsDomDomCongrSection (I := I) (M := M) g₀ (r + 1) ((s + 1) + i) σa
            (castRankCc_db g₀ (r + 1) (by omega : (s + i) + 1 = (s + 1) + i)
              (slotExtend (I := I) (M := M) g₀ r (s + i) HV))).toSection x from by
        rw [SmoothCcTensor.toSection_sub]; rfl]
      rw [hσa x, rsDomDomCongrSection_toSection]
      rw [← tsRsDomDomCongr_sub (I := I) (M := M) σa]
      rw [show ((castRankCc_db g₀ (r + 1) (by omega : (s + i) + 1 = (s + 1) + i)
            (slotExtend (I := I) (M := M) g₀ r (s + i)
              (iteratedCovGrad (I := I) g₀ r s i V))).toSection x -
          (castRankCc_db g₀ (r + 1) (by omega : (s + i) + 1 = (s + 1) + i)
            (slotExtend (I := I) (M := M) g₀ r (s + i) HV)).toSection x) =
          ((castRankCc_db g₀ (r + 1) (by omega : (s + i) + 1 = (s + 1) + i)
            (slotExtend (I := I) (M := M) g₀ r (s + i)
                (iteratedCovGrad (I := I) g₀ r s i V) -
              slotExtend (I := I) (M := M) g₀ r (s + i) HV)).toSection x) from by
        rw [tsCastRankCc_db_sub, SmoothCcTensor.toSection_sub]; rfl]
      rw [← tsSlotExtend_sub (I := I) (M := M) g₀ r (s + i)]
    rw [hpt]
    rw [riemannianFiberNormSq_domDomCongr_covariant (I := I) (M := M) g₀ (r + 1)
      ((s + 1) + i) x σa _]
    rw [tsRfns_castRankCc_db_zero (I := I) (M := M) g₀ (r + 1)
      (by omega : (s + i) + 1 = (s + 1) + i) _ x]
    rw [rfns_slotExtend_eq (I := I) (M := M) g₀ r (s + i) _ x]

set_option linter.unusedSectionVars false in
private lemma tsExists_rsDDC_headTransport (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (σ : Equiv.Perm (Fin s)) (V : SmoothCcTensor g₀ r s) (i : ℕ)
    (HV : SmoothCcTensor g₀ r (s + i)) :
    ∃ HW : SmoothCcTensor g₀ r (s + i),
      (∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g₀ r (s + i) x (HW.toSection x) ≤
          riemannianFiberNormSq (I := I) (M := M) g₀ r (s + i) x (HV.toSection x)) ∧
      (∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g₀ r (s + i) x
            ((iteratedCovGrad (I := I) g₀ r s i
                (rsDomDomCongrSection (I := I) (M := M) g₀ r s σ V) - HW).toSection x) ≤
          riemannianFiberNormSq (I := I) (M := M) g₀ r (s + i) x
            ((iteratedCovGrad (I := I) g₀ r s i V - HV).toSection x)) := by
  obtain ⟨σ', hσ'⟩ := tsExists_iteratedCovGrad_rsDomDomCongrSection (I := I) (M := M)
    g₀ r s σ V i
  refine ⟨rsDomDomCongrSection (I := I) (M := M) g₀ r (s + i) σ' HV, ?_, ?_⟩
  · intro x
    rw [tsRfns_rsDomDomCongrSection_zero (I := I) (M := M) g₀ r (s + i) σ' HV x]
  · intro x
    have hpt : ((iteratedCovGrad (I := I) g₀ r s i
          (rsDomDomCongrSection (I := I) (M := M) g₀ r s σ V) -
        rsDomDomCongrSection (I := I) (M := M) g₀ r (s + i) σ' HV).toSection x) =
        rsDomDomCongr (I := I) (M := M) σ'
          ((iteratedCovGrad (I := I) g₀ r s i V - HV).toSection x) := by
      rw [show ((iteratedCovGrad (I := I) g₀ r s i
            (rsDomDomCongrSection (I := I) (M := M) g₀ r s σ V) -
          rsDomDomCongrSection (I := I) (M := M) g₀ r (s + i) σ' HV).toSection x) =
          (iteratedCovGrad (I := I) g₀ r s i
            (rsDomDomCongrSection (I := I) (M := M) g₀ r s σ V)).toSection x -
          (rsDomDomCongrSection (I := I) (M := M) g₀ r (s + i) σ' HV).toSection x from by
        rw [SmoothCcTensor.toSection_sub]; rfl]
      rw [hσ' x, rsDomDomCongrSection_toSection]
      rw [← tsRsDomDomCongr_sub (I := I) (M := M) σ']
      rw [show ((iteratedCovGrad (I := I) g₀ r s i V).toSection x - HV.toSection x) =
          ((iteratedCovGrad (I := I) g₀ r s i V - HV).toSection x) from by
        rw [SmoothCcTensor.toSection_sub]; rfl]
    rw [hpt]
    rw [riemannianFiberNormSq_domDomCongr_covariant (I := I) (M := M) g₀ r (s + i) x σ' _]

set_option linter.unusedVariables false in
theorem rfns_iteratedCovGrad_ricciArmOrder0CurvCoeff_backgroundDifference_topSeparated_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Ktop : ℝ, 0 ≤ Ktop ∧ ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (i : ℕ),
        ∃ Hd : SmoothCcTensor g₀ 2 (2 + i),
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x (Hd.toSection x) ≤
              Ktop * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x)) ∧
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
                ((iteratedCovGrad (I := I) g₀ 2 2 i
                    (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
                      ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) -
                  Hd).toSection x) ≤
              Kc i * Combinatorics.boundedFactorGridWindow
                (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x)) (i + 1) (i + 3)) := by
  classical
  obtain ⟨KtB, hKtB_nn, KcB, hKcB_nn, hB⟩ :=
    rfns_iteratedCovGrad_slotInsertEndoCc_zero_ricEndoBackgroundDifferenceField_topSeparated_le
      (I := I) (M := M) g₀ hδ₀
  set n : ℝ := (Module.finrank ℝ E : ℝ) with hn_def
  have hn_nn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  refine ⟨4 * (n * KtB), by positivity, ?_⟩
  refine ⟨fun i => 4 * (n * KcB i),
    fun i => by have := hKcB_nn i; positivity, ?_⟩
  intro g₁ T htie δ hδ_le hδ0 hbound i
  obtain ⟨HdB, hB_head, hB_res⟩ := hB g₁ T htie hδ_le hδ0 hbound i
  set Lam := ricEndoBackgroundDifferenceField (I := I) (M := M) g₀ g₁ with hLam_def
  set X : SmoothCcTensor g₀ 1 1 := slotInsertEndoCc (I := I) (M := M) g₀ 0 Lam with hX_def
  set V : SmoothCcTensor g₀ 2 2 := slotInsertEndoCc (I := I) (M := M) g₀ 1 Lam with hV_def
  have hVrepr : V =
      reindexCoeffGen (I := I) (M := M) g₀ 2 2
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
          (slotExtend (I := I) (M := M) g₀ 1 1 X))
        (Equiv.swap (0 : Fin 2) 1) := by
    rw [hV_def, hX_def]
    exact tsSlotInsertEndoCc_succ_eq_reindex_slotExtend (I := I) (M := M) g₀ 0 Lam
  obtain ⟨HdX1, hX1_head, hX1_res⟩ := tsExists_slotExtend_headTransport (I := I) (M := M)
    g₀ 1 1 X i HdB
  obtain ⟨HdX2, hX2_head, hX2_res⟩ := tsExists_rsDDC_headTransport (I := I) (M := M)
    g₀ 2 2 (Equiv.swap (0 : Fin 2) 1) (slotExtend (I := I) (M := M) g₀ 1 1 X) i HdX1
  set HdV : SmoothCcTensor g₀ 2 (2 + i) :=
    reindexCoeffGen (I := I) (M := M) g₀ 2 (2 + i) HdX2 (Equiv.swap (0 : Fin 2) 1)
    with hHdV_def
  have hHdV_head : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x (HdV.toSection x) ≤
        n * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x (HdB.toSection x) := by
    intro x
    rw [hHdV_def, tsRfns_reindexCoeffGen_zero (I := I) (M := M) g₀ 2 (2 + i) HdX2 _ x]
    exact le_trans (hX2_head x) (hX1_head x)
  have hHdV_res : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 2 2 i V - HdV).toSection x) ≤
        n * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
          ((iteratedCovGrad (I := I) g₀ 1 1 i X - HdB).toSection x) := by
    intro x
    have hVd : iteratedCovGrad (I := I) g₀ 2 2 i V - HdV =
        reindexCoeffGen (I := I) (M := M) g₀ 2 (2 + i)
          (iteratedCovGrad (I := I) g₀ 2 2 i
              (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
                (slotExtend (I := I) (M := M) g₀ 1 1 X)) - HdX2)
          (Equiv.swap (0 : Fin 2) 1) := by
      rw [hVrepr, hHdV_def]
      rw [iteratedCovGrad_reindexCoeffGen (I := I) (M := M) g₀ 2 2 _ _ i]
      rw [tsReindexCoeffGen_sub (I := I) (M := M) g₀ 2 (2 + i)]
    rw [hVd]
    rw [tsRfns_reindexCoeffGen_zero (I := I) (M := M) g₀ 2 (2 + i) _ _ x]
    exact le_trans (hX2_res x) (hX1_res x)
  obtain ⟨HdV2i, h2i_head, h2i_res⟩ := tsExists_rsDDC_headTransport (I := I) (M := M)
    g₀ 2 2 (Equiv.swap (0 : Fin 2) 1) V i HdV
  set HdV2 : SmoothCcTensor g₀ 2 (2 + i) :=
    reindexCoeffGen (I := I) (M := M) g₀ 2 (2 + i) HdV2i (Equiv.swap (0 : Fin 2) 1)
    with hHdV2_def
  set V2 : SmoothCcTensor g₀ 2 2 :=
    reindexCoeffGen (I := I) (M := M) g₀ 2 2
      (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1) V)
      (Equiv.swap (0 : Fin 2) 1) with hV2_def
  have hHdV2_head : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x (HdV2.toSection x) ≤
        n * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x (HdB.toSection x) := by
    intro x
    rw [hHdV2_def, tsRfns_reindexCoeffGen_zero (I := I) (M := M) g₀ 2 (2 + i) HdV2i _ x]
    exact le_trans (h2i_head x) (hHdV_head x)
  have hHdV2_res : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 2 2 i V2 - HdV2).toSection x) ≤
        n * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
          ((iteratedCovGrad (I := I) g₀ 1 1 i X - HdB).toSection x) := by
    intro x
    have hV2d : iteratedCovGrad (I := I) g₀ 2 2 i V2 - HdV2 =
        reindexCoeffGen (I := I) (M := M) g₀ 2 (2 + i)
          (iteratedCovGrad (I := I) g₀ 2 2 i
              (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1) V) -
            HdV2i)
          (Equiv.swap (0 : Fin 2) 1) := by
      rw [hV2_def, hHdV2_def]
      rw [iteratedCovGrad_reindexCoeffGen (I := I) (M := M) g₀ 2 2 _ _ i]
      rw [tsReindexCoeffGen_sub (I := I) (M := M) g₀ 2 (2 + i)]
    rw [hV2d]
    rw [tsRfns_reindexCoeffGen_zero (I := I) (M := M) g₀ 2 (2 + i) _ _ x]
    exact le_trans (h2i_res x) (hHdV_res x)
  refine ⟨HdV + HdV2, ?_, ?_⟩
  · intro x
    rw [show ((HdV + HdV2).toSection x) = HdV.toSection x + HdV2.toSection x from by
      rw [SmoothCcTensor.toSection_add]; rfl]
    refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 2 (2 + i) x _ _) ?_
    have h1 := le_trans (hHdV_head x) (mul_le_mul_of_nonneg_left (hB_head x) hn_nn)
    have h2 := le_trans (hHdV2_head x) (mul_le_mul_of_nonneg_left (hB_head x) hn_nn)
    calc 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x (HdV.toSection x) +
        2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x (HdV2.toSection x)
        ≤ 2 * (n * (KtB * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x))) +
          2 * (n * (KtB * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x))) :=
          add_le_add (mul_le_mul_of_nonneg_left h1 (by norm_num))
            (mul_le_mul_of_nonneg_left h2 (by norm_num))
      _ = 4 * (n * KtB) * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x) := by ring
  · intro x
    have hdecomp := ricciArmOrder0CurvCoeff_backgroundDifference_decomp (I := I) (M := M)
      g₀ g₁
    have hsplit : iteratedCovGrad (I := I) g₀ 2 2 i
          (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
            ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) -
          (HdV + HdV2) =
        (iteratedCovGrad (I := I) g₀ 2 2 i V - HdV) +
          (iteratedCovGrad (I := I) g₀ 2 2 i V2 - HdV2) := by
      rw [show (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
            ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) = V + V2 from by
        rw [hV_def, hV2_def, hLam_def]
        exact hdecomp]
      rw [iteratedCovGrad_add (I := I) g₀ 2 2 i V V2]
      abel
    rw [hsplit]
    rw [show (((iteratedCovGrad (I := I) g₀ 2 2 i V - HdV) +
          (iteratedCovGrad (I := I) g₀ 2 2 i V2 - HdV2)).toSection x) =
        (iteratedCovGrad (I := I) g₀ 2 2 i V - HdV).toSection x +
          (iteratedCovGrad (I := I) g₀ 2 2 i V2 - HdV2).toSection x from by
      rw [SmoothCcTensor.toSection_add]; rfl]
    refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 2 (2 + i) x _ _) ?_
    have h1 := le_trans (hHdV_res x) (mul_le_mul_of_nonneg_left (hB_res x) hn_nn)
    have h2 := le_trans (hHdV2_res x) (mul_le_mul_of_nonneg_left (hB_res x) hn_nn)
    calc 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 2 2 i V - HdV).toSection x) +
        2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 2 2 i V2 - HdV2).toSection x)
        ≤ 2 * (n * (KcB i * Combinatorics.boundedFactorGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x)) (i + 1) (i + 3))) +
          2 * (n * (KcB i * Combinatorics.boundedFactorGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x)) (i + 1) (i + 3))) :=
          add_le_add (mul_le_mul_of_nonneg_left h1 (by norm_num))
            (mul_le_mul_of_nonneg_left h2 (by norm_num))
      _ = 4 * (n * KcB i) * Combinatorics.boundedFactorGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x)) (i + 1) (i + 3) := by
          ring

end TopSeparatedRungCurvCoeff

section TopSeparatedRungRiemannCoeff

open DifferentialGeometry.Integral.DivergenceTheorem

set_option backward.isDefEq.respectTransparency false

set_option linter.unusedVariables false in
theorem rfns_iteratedCovGrad_ricciArmOrder0RiemannCoeff_backgroundDifference_topSeparated_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Ktop : ℝ, 0 ≤ Ktop ∧ ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ0 : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (i : ℕ),
        ∃ Hd : SmoothCcTensor g₀ 2 (2 + i),
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x (Hd.toSection x) ≤
              Ktop * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x)) ∧
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
                ((iteratedCovGrad (I := I) g₀ 2 2 i
                    (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                      ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) -
                  Hd).toSection x) ≤
              Kc i * Combinatorics.boundedFactorGridWindow
                (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x)) (i + 1) (i + 3)) := by
  classical
  obtain ⟨KtA, hKtA_nn, KcA, hKcA_nn, hA⟩ :=
    rfns_iteratedCovGrad_riemannLoweredBackgroundDifference_topSeparated_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨KtA', hKtA'_nn, KcA', hKcA'_nn, hA'⟩ :=
    rfns_iteratedCovGrad_riemannG1LoweringDifference_topSeparated_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨CA, hCA_nn, hCA⟩ :=
    rfns_iteratedCovGrad_riemannLoweredBackgroundDifference_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨C1, hC1_nn, hC1⟩ :=
    rfns_iteratedCovGrad_riemannG1LoweringDifference_diagonalProductGrid_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨CD, hCD_nn, hCD⟩ := exists_rfns_iteratedCovGrad_pairTraceOp_diff_grid
    (I := I) (M := M) g₀ hδ₀
  obtain ⟨cfix, hcfix_nn, hcfix⟩ := exists_backgroundJet_rfns_bound (I := I) (M := M) g₀ 0 4
    (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)
  obtain ⟨cP, hcP_nn, hcP⟩ := exists_bound_riemannianFiberNormSq_smoothCcTensor
    (I := I) (M := M) g₀ 6 2 (pairTraceOp (I := I) (M := M) g₀ g₀)
  set n : ℝ := (Module.finrank ℝ E : ℝ) with hn_def
  have hn_nn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  refine ⟨8 * (n * n) * (CD 0 + cP) * (2 * KtA' + 2 * KtA),
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg hn_nn hn_nn))
      (add_nonneg (hCD_nn 0) hcP_nn)) (by linarith [hKtA'_nn, hKtA_nn]), ?_⟩
  refine ⟨fun i => 4 * (2 * (2 * (CD 0 * (n * n) *
        (4 * KcA' i + 4 * KcA i + 2 * cfix i)) +
      2 * ((i : ℝ) * appCcGdiag (E := E) i *
        ∑ k ∈ Finset.range i, CD (i - k) * (n * n) *
          ((2 * C1 k + 4 * CA k) *
              Combinatorics.windowPairCellCount ((i - k) + 1) (k + 3) + 4 * cfix k))) +
      2 * (2 * (cP * (n * n)) * (2 * KcA' i + 2 * KcA i))),
    fun i => by
      have hp1 : (0 : ℝ) ≤ CD 0 * (n * n) * (4 * KcA' i + 4 * KcA i + 2 * cfix i) :=
        mul_nonneg (mul_nonneg (hCD_nn 0) (mul_nonneg hn_nn hn_nn))
          (by have := hKcA'_nn i; have := hKcA_nn i; have := hcfix_nn i; linarith)
      have hp2 : (0 : ℝ) ≤ (i : ℝ) * appCcGdiag (E := E) i *
          ∑ k ∈ Finset.range i, CD (i - k) * (n * n) *
            ((2 * C1 k + 4 * CA k) *
                Combinatorics.windowPairCellCount ((i - k) + 1) (k + 3) + 4 * cfix k) :=
        mul_nonneg (mul_nonneg (Nat.cast_nonneg i) (appCcGdiag_nonneg (E := E) i))
          (Finset.sum_nonneg fun k _ => mul_nonneg
            (mul_nonneg (hCD_nn _) (mul_nonneg hn_nn hn_nn))
            (add_nonneg
              (mul_nonneg (by have := hC1_nn k; have := hCA_nn k; linarith)
                (Combinatorics.windowPairCellCount_nonneg _ _))
              (by have := hcfix_nn k; linarith)))
      have hp3 : (0 : ℝ) ≤ 2 * (cP * (n * n)) * (2 * KcA' i + 2 * KcA i) :=
        mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg hcP_nn (mul_nonneg hn_nn hn_nn)))
          (by have := hKcA'_nn i; have := hKcA_nn i; linarith)
      linarith, ?_⟩
  intro g₁ T htie δ hδ_le hδ0 hbound i
  obtain ⟨HdA, hHdA_head, hHdA_res⟩ := hA g₁ T htie hδ_le hδ0 hbound i
  obtain ⟨HdA', hHdA'_head, hHdA'_res⟩ := hA' g₁ T htie hδ_le hδ0 hbound i
  set RLC11 : SmoothCcTensor g₀ 0 4 := riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁
    with hRLC11_def
  set RLC01 : SmoothCcTensor g₀ 0 4 := riemannLoweredCc (I := I) (M := M) g₀ g₀ g₁
    with hRLC01_def
  set RLCfix : SmoothCcTensor g₀ 0 4 := riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀
    with hRLCfix_def
  set Vd : SmoothCcTensor g₀ 0 4 := RLC11 - RLCfix with hVd_def
  set phiDt : SmoothCcTensor g₀ 6 2 := pairTraceOp (I := I) (M := M) g₀ g₀ with hphiDt_def
  set Dpt : SmoothCcTensor g₀ 6 2 :=
    pairTraceOp (I := I) (M := M) g₀ g₁ - pairTraceOp (I := I) (M := M) g₀ g₀ with hDpt_def
  have hphiDt_par : covGrad (I := I) (M := M) g₀ 6 2 phiDt = 0 := by
    rw [hphiDt_def, pairTraceOp_self_eq (I := I) (M := M) g₀]
    exact phiDtPair_covGrad_zero (I := I) (M := M) g₀
  have hIter2 : ∀ Z : SmoothCcTensor g₀ 0 4,
      slotExtendIter (I := I) (M := M) g₀ 0 4 2 Z =
        slotExtend (I := I) (M := M) g₀ 1 5 (slotExtend (I := I) (M := M) g₀ 0 4 Z) :=
    fun Z => rfl
  set WBig : SmoothCcTensor g₀ 2 6 :=
    rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
      (slotExtend (I := I) (M := M) g₀ 1 5
        (slotExtend (I := I) (M := M) g₀ 0 4 RLC11)) with hWBig_def
  set WVd : SmoothCcTensor g₀ 2 6 :=
    rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
      (slotExtend (I := I) (M := M) g₀ 1 5
        (slotExtend (I := I) (M := M) g₀ 0 4 Vd)) with hWVd_def
  have hWfix_sub : rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 sigmaE0
        (slotExtend (I := I) (M := M) g₀ 1 5
          (slotExtend (I := I) (M := M) g₀ 0 4 RLCfix)) =
      WBig - WVd := by
    rw [hWBig_def, hWVd_def, hVd_def]
    rw [tsSlotExtend_sub (I := I) (M := M) g₀ 0 4 RLC11 RLCfix]
    rw [tsSlotExtend_sub (I := I) (M := M) g₀ 1 5]
    rw [rsDomDomCongrSection_sub_cc (I := I) (M := M) g₀ 2 6 sigmaE0]
    abel
  have hRiemD : ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
      ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ =
      (2 : ℝ) • appCcRS (I := I) (M := M) g₀ 2 6 2 Dpt WBig +
        (2 : ℝ) • appCcRS (I := I) (M := M) g₀ 2 6 2 phiDt WVd := by
    have hL1 := riemannCoeff_eq_pairTrace_L11 (I := I) (M := M) g₀ g₁
    have hL0 := riemannCoeff_eq_pairTrace_L11 (I := I) (M := M) g₀ g₀
    rw [hIter2 (riemannLoweredCc (I := I) (M := M) g₀ g₁ g₁)] at hL1
    rw [hIter2 (riemannLoweredCc (I := I) (M := M) g₀ g₀ g₀)] at hL0
    rw [hL1, hL0]
    rw [show (pairTraceOp (I := I) (M := M) g₀ g₁) = Dpt + phiDt from by
      rw [hDpt_def, hphiDt_def]; abel]
    rw [appCcRS_add_left_cc (I := I) (M := M) g₀ 2 6 2 Dpt phiDt]
    rw [← hWBig_def, ← hRLCfix_def, hWfix_sub]
    rw [appCcRS_sub_right_cc (I := I) (M := M) g₀ 2 6 2 phiDt WBig WVd]
    rw [smul_add, smul_sub]
    abel
  obtain ⟨HW1c, h1c_head, h1c_res⟩ := tsExists_slotExtend_headTransport (I := I) (M := M)
    g₀ 0 4 RLC11 i (HdA' + HdA)
  obtain ⟨HW2c, h2c_head, h2c_res⟩ := tsExists_slotExtend_headTransport (I := I) (M := M)
    g₀ 1 5 (slotExtend (I := I) (M := M) g₀ 0 4 RLC11) i HW1c
  obtain ⟨HW11, h11_head, h11_res⟩ := tsExists_rsDDC_headTransport (I := I) (M := M)
    g₀ 2 6 sigmaE0
    (slotExtend (I := I) (M := M) g₀ 1 5 (slotExtend (I := I) (M := M) g₀ 0 4 RLC11))
    i HW2c
  obtain ⟨HW1d, h1d_head, h1d_res⟩ := tsExists_slotExtend_headTransport (I := I) (M := M)
    g₀ 0 4 Vd i (HdA' + HdA)
  obtain ⟨HW2d, h2d_head, h2d_res⟩ := tsExists_slotExtend_headTransport (I := I) (M := M)
    g₀ 1 5 (slotExtend (I := I) (M := M) g₀ 0 4 Vd) i HW1d
  obtain ⟨HWd, hWd_head, hWd_res⟩ := tsExists_rsDDC_headTransport (I := I) (M := M)
    g₀ 2 6 sigmaE0
    (slotExtend (I := I) (M := M) g₀ 1 5 (slotExtend (I := I) (M := M) g₀ 0 4 Vd))
    i HW2d
  set HdT1 : SmoothCcTensor g₀ 2 (2 + i) :=
    appCcRS (I := I) (M := M) g₀ 2 (6 + i) (2 + i)
      (appCcLeibnizPsi (I := I) (M := M) g₀ 6 2 Dpt i i) HW11 with hHdT1_def
  set HdT2 : SmoothCcTensor g₀ 2 (2 + i) :=
    appCcRS (I := I) (M := M) g₀ 2 (6 + i) (2 + i)
      (appCcLeibnizPsi (I := I) (M := M) g₀ 6 2 phiDt i i) HWd with hHdT2_def
  have hHVc_head : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x ((HdA' + HdA).toSection x) ≤
        (2 * KtA' + 2 * KtA) * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x) := by
    intro x
    rw [show ((HdA' + HdA).toSection x) = HdA'.toSection x + HdA.toSection x from by
      rw [SmoothCcTensor.toSection_add]; rfl]
    refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 (4 + i) x _ _) ?_
    have h1 := hHdA'_head x
    have h2 := hHdA_head x
    calc 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x (HdA'.toSection x) +
        2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x (HdA.toSection x)
        ≤ 2 * (KtA' * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x)) +
          2 * (KtA * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x)) :=
          add_le_add (mul_le_mul_of_nonneg_left h1 (by norm_num))
            (mul_le_mul_of_nonneg_left h2 (by norm_num))
      _ = (2 * KtA' + 2 * KtA) * riemannianFiberNormSq (I := I) (M := M) g₀ 0
            (2 + (i + 2)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x) := by ring
  refine ⟨(2 : ℝ) • (HdT1 + HdT2), ?_, ?_⟩
  · intro x
    rw [show (((2 : ℝ) • (HdT1 + HdT2)).toSection x) =
        (2 : ℝ) • ((HdT1 + HdT2).toSection x) from by
      rw [SmoothCcTensor.toSection_smul]; rfl]
    rw [rfns_smul_pt (I := I) (M := M) g₀ 2 (2 + i) x 2 _]
    rw [show ((HdT1 + HdT2).toSection x) = HdT1.toSection x + HdT2.toSection x from by
      rw [SmoothCcTensor.toSection_add]; rfl]
    have hb_nn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
      ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x)
    have hHVchain : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + i) x
        (HW11.toSection x) ≤
        (n * n) * ((2 * KtA' + 2 * KtA) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x)) := by
      refine le_trans (h11_head x) ?_
      refine le_trans (h2c_head x) ?_
      calc n * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (5 + i) x (HW1c.toSection x)
          ≤ n * (n * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
              ((HdA' + HdA).toSection x)) :=
            mul_le_mul_of_nonneg_left (h1c_head x) hn_nn
        _ ≤ n * (n * ((2 * KtA' + 2 * KtA) *
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x))) := by
            refine mul_le_mul_of_nonneg_left ?_ hn_nn
            exact mul_le_mul_of_nonneg_left (hHVc_head x) hn_nn
        _ = (n * n) * ((2 * KtA' + 2 * KtA) *
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x)) := by ring
    have hHWdchain : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + i) x
        (HWd.toSection x) ≤
        (n * n) * ((2 * KtA' + 2 * KtA) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x)) := by
      refine le_trans (hWd_head x) ?_
      refine le_trans (h2d_head x) ?_
      calc n * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (5 + i) x (HW1d.toSection x)
          ≤ n * (n * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
              ((HdA' + HdA).toSection x)) :=
            mul_le_mul_of_nonneg_left (h1d_head x) hn_nn
        _ ≤ n * (n * ((2 * KtA' + 2 * KtA) *
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x))) := by
            refine mul_le_mul_of_nonneg_left ?_ hn_nn
            exact mul_le_mul_of_nonneg_left (hHVc_head x) hn_nn
        _ = (n * n) * ((2 * KtA' + 2 * KtA) *
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x)) := by ring
    have hDpt0 : riemannianFiberNormSq (I := I) (M := M) g₀ 6 2 x (Dpt.toSection x) ≤
        CD 0 := by
      have h := hCD g₁ T htie hδ_le hδ0 hbound 0 x
      rw [iteratedCovGrad_zero] at h
      rw [Finset.sum_range_one, Combinatorics.antidiagonalTupleGrid_zero, mul_one] at h
      rw [hDpt_def]
      exact h
    have hT1 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
        (HdT1.toSection x) ≤
        CD 0 * ((n * n) * ((2 * KtA' + 2 * KtA) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x))) := by
      rw [hHdT1_def]
      refine le_trans (rfns_appCcRS_appCcLeibnizPsi_diag_le (I := I) (M := M) g₀ 2 6 2
        Dpt i HW11 x) ?_
      refine mul_le_mul hDpt0 hHVchain
        (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (6 + i) x _) (hCD_nn 0)
    have hT2 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
        (HdT2.toSection x) ≤
        cP * ((n * n) * ((2 * KtA' + 2 * KtA) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x))) := by
      rw [hHdT2_def]
      refine le_trans (rfns_appCcRS_appCcLeibnizPsi_diag_le (I := I) (M := M) g₀ 2 6 2
        phiDt i HWd x) ?_
      refine mul_le_mul ?_ hHWdchain
        (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (6 + i) x _) hcP_nn
      rw [hphiDt_def]
      exact hcP x
    calc (2 : ℝ) ^ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
          (HdT1.toSection x + HdT2.toSection x)
        ≤ (2 : ℝ) ^ 2 * (2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            (HdT1.toSection x) +
          2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x (HdT2.toSection x)) :=
          mul_le_mul_of_nonneg_left
            (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 2 (2 + i) x _ _)
            (by norm_num)
      _ ≤ (2 : ℝ) ^ 2 * (2 * (CD 0 * ((n * n) * ((2 * KtA' + 2 * KtA) *
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x)))) +
          2 * (cP * ((n * n) * ((2 * KtA' + 2 * KtA) *
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x))))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          exact add_le_add (mul_le_mul_of_nonneg_left hT1 (by norm_num))
            (mul_le_mul_of_nonneg_left hT2 (by norm_num))
      _ = 8 * (n * n) * (CD 0 + cP) * (2 * KtA' + 2 * KtA) *
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x) := by ring
  · intro x
    set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
      ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x) with hb_def
    have hb : ∀ l, 0 ≤ b l :=
      fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
    set Wfin : ℝ := Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) with hWfin_def
    have hWfin_nn : 0 ≤ Wfin :=
      Combinatorics.boundedFactorGridWindow_nonneg b hb (i + 1) (i + 3)
    have hWfin_one : 1 ≤ Wfin :=
      Combinatorics.one_le_boundedFactorGridWindow b hb (by omega)
    have hVd_res : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
        ((iteratedCovGrad (I := I) g₀ 0 4 i Vd - (HdA' + HdA)).toSection x) ≤
        (2 * KcA' i + 2 * KcA i) * Wfin := by
      have hVd_split : iteratedCovGrad (I := I) g₀ 0 4 i Vd - (HdA' + HdA) =
          (iteratedCovGrad (I := I) g₀ 0 4 i (RLC11 - RLC01) - HdA') +
            (iteratedCovGrad (I := I) g₀ 0 4 i
              (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁) - HdA) := by
        rw [show (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁) =
            RLC01 - RLCfix from by
          rw [riemannLoweredBackgroundDifference, hRLC01_def, hRLCfix_def]]
        rw [show Vd = (RLC11 - RLC01) + (RLC01 - RLCfix) from by rw [hVd_def]; abel]
        rw [iteratedCovGrad_add (I := I) g₀ 0 4 i (RLC11 - RLC01) (RLC01 - RLCfix)]
        abel
      rw [hVd_split]
      rw [show (((iteratedCovGrad (I := I) g₀ 0 4 i (RLC11 - RLC01) - HdA') +
            (iteratedCovGrad (I := I) g₀ 0 4 i
              (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁) -
              HdA)).toSection x) =
          (iteratedCovGrad (I := I) g₀ 0 4 i (RLC11 - RLC01) - HdA').toSection x +
            (iteratedCovGrad (I := I) g₀ 0 4 i
              (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁) -
              HdA).toSection x from by
        rw [SmoothCcTensor.toSection_add]; rfl]
      refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 (4 + i) x _ _) ?_
      have h1 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
          ((iteratedCovGrad (I := I) g₀ 0 4 i (RLC11 - RLC01) - HdA').toSection x) ≤
          KcA' i * Wfin := by
        have h := hHdA'_res x
        rw [hRLC11_def, hRLC01_def]
        exact h
      have h2 := hHdA_res x
      calc 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 4 i (RLC11 - RLC01) - HdA').toSection x) +
          2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 4 i
              (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁) -
              HdA).toSection x)
          ≤ 2 * (KcA' i * Wfin) + 2 * (KcA i * Wfin) :=
            add_le_add (mul_le_mul_of_nonneg_left h1 (by norm_num))
              (mul_le_mul_of_nonneg_left h2 (by norm_num))
        _ = (2 * KcA' i + 2 * KcA i) * Wfin := by ring
    have hRLC11_res : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
        ((iteratedCovGrad (I := I) g₀ 0 4 i RLC11 - (HdA' + HdA)).toSection x) ≤
        (4 * KcA' i + 4 * KcA i + 2 * cfix i) * Wfin := by
      have hsplit : iteratedCovGrad (I := I) g₀ 0 4 i RLC11 - (HdA' + HdA) =
          (iteratedCovGrad (I := I) g₀ 0 4 i Vd - (HdA' + HdA)) +
            iteratedCovGrad (I := I) g₀ 0 4 i RLCfix := by
        rw [show RLC11 = Vd + RLCfix from by rw [hVd_def]; abel]
        rw [iteratedCovGrad_add (I := I) g₀ 0 4 i Vd RLCfix]
        abel
      rw [hsplit]
      rw [show (((iteratedCovGrad (I := I) g₀ 0 4 i Vd - (HdA' + HdA)) +
            iteratedCovGrad (I := I) g₀ 0 4 i RLCfix).toSection x) =
          (iteratedCovGrad (I := I) g₀ 0 4 i Vd - (HdA' + HdA)).toSection x +
            (iteratedCovGrad (I := I) g₀ 0 4 i RLCfix).toSection x from by
        rw [SmoothCcTensor.toSection_add]; rfl]
      refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 (4 + i) x _ _) ?_
      have h2 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
          ((iteratedCovGrad (I := I) g₀ 0 4 i RLCfix).toSection x) ≤ cfix i * Wfin := by
        have h2a : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 4 i RLCfix).toSection x) ≤ cfix i := by
          rw [hRLCfix_def]
          exact hcfix i x
        calc riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
              ((iteratedCovGrad (I := I) g₀ 0 4 i RLCfix).toSection x)
            ≤ cfix i := h2a
          _ = cfix i * 1 := by ring
          _ ≤ cfix i * Wfin := mul_le_mul_of_nonneg_left hWfin_one (hcfix_nn i)
      calc 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 4 i Vd - (HdA' + HdA)).toSection x) +
          2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 4 i RLCfix).toSection x)
          ≤ 2 * ((2 * KcA' i + 2 * KcA i) * Wfin) + 2 * (cfix i * Wfin) :=
            add_le_add (mul_le_mul_of_nonneg_left hVd_res (by norm_num))
              (mul_le_mul_of_nonneg_left h2 (by norm_num))
        _ = (4 * KcA' i + 4 * KcA i + 2 * cfix i) * Wfin := by ring
    have hT2res : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 2 2 i
            (appCcRS (I := I) (M := M) g₀ 2 6 2 phiDt WVd) - HdT2).toSection x) ≤
        2 * (cP * ((n * n) * ((2 * KcA' i + 2 * KcA i) * Wfin))) := by
      rw [hHdT2_def]
      refine le_trans (tsParallel_argCorner_residual_le (I := I) (M := M) g₀ 2 6 2
        phiDt hphiDt_par WVd i HWd x) ?_
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      have hchain : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + i) x
          ((iteratedCovGrad (I := I) g₀ 2 6 i WVd - HWd).toSection x) ≤
          (n * n) * ((2 * KcA' i + 2 * KcA i) * Wfin) := by
        have hs1 := hWd_res x
        rw [← hWVd_def] at hs1
        refine le_trans hs1 ?_
        refine le_trans (h2d_res x) ?_
        calc n * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (5 + i) x
              ((iteratedCovGrad (I := I) g₀ 1 5 i
                (slotExtend (I := I) (M := M) g₀ 0 4 Vd) - HW1d).toSection x)
            ≤ n * (n * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
                ((iteratedCovGrad (I := I) g₀ 0 4 i Vd - (HdA' + HdA)).toSection x)) :=
              mul_le_mul_of_nonneg_left (h1d_res x) hn_nn
          _ ≤ n * (n * ((2 * KcA' i + 2 * KcA i) * Wfin)) := by
              refine mul_le_mul_of_nonneg_left ?_ hn_nn
              exact mul_le_mul_of_nonneg_left hVd_res hn_nn
          _ = (n * n) * ((2 * KcA' i + 2 * KcA i) * Wfin) := by ring
      have hp0 : riemannianFiberNormSq (I := I) (M := M) g₀ 6 2 x (phiDt.toSection x) ≤
          cP := by
        rw [hphiDt_def]; exact hcP x
      refine mul_le_mul hp0 hchain
        (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (6 + i) x _) hcP_nn
    have hT1res : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 2 2 i
            (appCcRS (I := I) (M := M) g₀ 2 6 2 Dpt WBig) - HdT1).toSection x) ≤
        2 * (CD 0 * (n * n) * (4 * KcA' i + 4 * KcA i + 2 * cfix i)) * Wfin +
        2 * ((i : ℝ) * appCcGdiag (E := E) i *
          ∑ k ∈ Finset.range i, (CD (i - k) * (n * n) *
            ((2 * C1 k + 4 * CA k) *
                Combinatorics.windowPairCellCount ((i - k) + 1) (k + 3) + 4 * cfix k)) *
            Wfin) := by
      have hsplitT1 : iteratedCovGrad (I := I) g₀ 2 2 i
            (appCcRS (I := I) (M := M) g₀ 2 6 2 Dpt WBig) - HdT1 =
          appCcRS (I := I) (M := M) g₀ 2 (6 + i) (2 + i)
              (appCcLeibnizPsi (I := I) (M := M) g₀ 6 2 Dpt i i)
              (iteratedCovGrad (I := I) g₀ 2 6 i WBig - HW11) +
            ∑ k ∈ Finset.range i,
              appCcRS (I := I) (M := M) g₀ 2 (6 + k) (2 + i)
                (appCcLeibnizPsi (I := I) (M := M) g₀ 6 2 Dpt i k)
                (iteratedCovGrad (I := I) g₀ 2 6 k WBig) := by
        rw [iteratedCovGrad_appCcRS_eq_argCorner_add_lower (I := I) (M := M) g₀ 2 6 2
          Dpt WBig i]
        rw [hHdT1_def]
        rw [appCcRS_sub_right_cc (I := I) (M := M) g₀ 2 (6 + i) (2 + i)
          (appCcLeibnizPsi (I := I) (M := M) g₀ 6 2 Dpt i i)
          (iteratedCovGrad (I := I) g₀ 2 6 i WBig) HW11]
        exact add_sub_right_comm _ _ _
      rw [hsplitT1]
      rw [show ((appCcRS (I := I) (M := M) g₀ 2 (6 + i) (2 + i)
            (appCcLeibnizPsi (I := I) (M := M) g₀ 6 2 Dpt i i)
            (iteratedCovGrad (I := I) g₀ 2 6 i WBig - HW11) +
          ∑ k ∈ Finset.range i,
            appCcRS (I := I) (M := M) g₀ 2 (6 + k) (2 + i)
              (appCcLeibnizPsi (I := I) (M := M) g₀ 6 2 Dpt i k)
              (iteratedCovGrad (I := I) g₀ 2 6 k WBig)).toSection x) =
          (appCcRS (I := I) (M := M) g₀ 2 (6 + i) (2 + i)
            (appCcLeibnizPsi (I := I) (M := M) g₀ 6 2 Dpt i i)
            (iteratedCovGrad (I := I) g₀ 2 6 i WBig - HW11)).toSection x +
          (∑ k ∈ Finset.range i,
            appCcRS (I := I) (M := M) g₀ 2 (6 + k) (2 + i)
              (appCcLeibnizPsi (I := I) (M := M) g₀ 6 2 Dpt i k)
              (iteratedCovGrad (I := I) g₀ 2 6 k WBig)).toSection x from by
        rw [SmoothCcTensor.toSection_add]; rfl]
      refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 2 (2 + i) x _ _) ?_
      have hDpt0 : riemannianFiberNormSq (I := I) (M := M) g₀ 6 2 x (Dpt.toSection x) ≤
          CD 0 := by
        have h := hCD g₁ T htie hδ_le hδ0 hbound 0 x
        rw [iteratedCovGrad_zero] at h
        rw [Finset.sum_range_one, Combinatorics.antidiagonalTupleGrid_zero, mul_one] at h
        rw [hDpt_def]
        exact h
      have hpiece1 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
          ((appCcRS (I := I) (M := M) g₀ 2 (6 + i) (2 + i)
            (appCcLeibnizPsi (I := I) (M := M) g₀ 6 2 Dpt i i)
            (iteratedCovGrad (I := I) g₀ 2 6 i WBig - HW11)).toSection x) ≤
          CD 0 * (n * n) * (4 * KcA' i + 4 * KcA i + 2 * cfix i) * Wfin := by
        refine le_trans (rfns_appCcRS_appCcLeibnizPsi_diag_le (I := I) (M := M) g₀ 2 6 2
          Dpt i _ x) ?_
        have hchain : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 6 i WBig - HW11).toSection x) ≤
            (n * n) * ((4 * KcA' i + 4 * KcA i + 2 * cfix i) * Wfin) := by
          have hs1 := h11_res x
          rw [← hWBig_def] at hs1
          refine le_trans hs1 ?_
          refine le_trans (h2c_res x) ?_
          calc n * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (5 + i) x
                ((iteratedCovGrad (I := I) g₀ 1 5 i
                  (slotExtend (I := I) (M := M) g₀ 0 4 RLC11) - HW1c).toSection x)
              ≤ n * (n * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
                  ((iteratedCovGrad (I := I) g₀ 0 4 i RLC11 -
                    (HdA' + HdA)).toSection x)) :=
                mul_le_mul_of_nonneg_left (h1c_res x) hn_nn
            _ ≤ n * (n * ((4 * KcA' i + 4 * KcA i + 2 * cfix i) * Wfin)) := by
                refine mul_le_mul_of_nonneg_left ?_ hn_nn
                exact mul_le_mul_of_nonneg_left hRLC11_res hn_nn
            _ = (n * n) * ((4 * KcA' i + 4 * KcA i + 2 * cfix i) * Wfin) := by ring
        calc riemannianFiberNormSq (I := I) (M := M) g₀ 6 2 x (Dpt.toSection x) *
              riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + i) x
                ((iteratedCovGrad (I := I) g₀ 2 6 i WBig - HW11).toSection x)
            ≤ CD 0 * ((n * n) * ((4 * KcA' i + 4 * KcA i + 2 * cfix i) * Wfin)) := by
              refine mul_le_mul hDpt0 hchain
                (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (6 + i) x _)
                (hCD_nn 0)
          _ = CD 0 * (n * n) * (4 * KcA' i + 4 * KcA i + 2 * cfix i) * Wfin := by ring
      have hpiece2 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
          ((∑ k ∈ Finset.range i,
            appCcRS (I := I) (M := M) g₀ 2 (6 + k) (2 + i)
              (appCcLeibnizPsi (I := I) (M := M) g₀ 6 2 Dpt i k)
              (iteratedCovGrad (I := I) g₀ 2 6 k WBig)).toSection x) ≤
          (i : ℝ) * appCcGdiag (E := E) i *
            ∑ k ∈ Finset.range i, (CD (i - k) * (n * n) *
              ((2 * C1 k + 4 * CA k) *
                  Combinatorics.windowPairCellCount ((i - k) + 1) (k + 3) + 4 * cfix k)) *
              Wfin := by
        refine le_trans (rfns_appCcRS_argLower_le (I := I) (M := M) g₀ 2 6 2 Dpt WBig i x) ?_
        rw [mul_assoc, mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg i)
        refine mul_le_mul_of_nonneg_left ?_ (appCcGdiag_nonneg (E := E) i)
        refine Finset.sum_le_sum (fun k hk => ?_)
        rw [Finset.mem_range] at hk
        have hDptjet : riemannianFiberNormSq (I := I) (M := M) g₀ 6 (2 + (i - k)) x
            ((iteratedCovGrad (I := I) g₀ 6 2 (i - k) Dpt).toSection x) ≤
            CD (i - k) * (∑ l ∈ Finset.range ((i - k) + 1),
              Combinatorics.antidiagonalTupleGrid b l) := by
          have h := hCD g₁ T htie hδ_le hδ0 hbound (i - k) x
          rw [hDpt_def]
          exact h
        have hWjet : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + k) x
            ((iteratedCovGrad (I := I) g₀ 2 6 k WBig).toSection x) ≤
            (n * n) * ((2 * C1 k + 4 * CA k) * (∑ k' ∈ Finset.range (k + 3),
              Combinatorics.antidiagonalTupleGrid b k') + 4 * cfix k) := by
          rw [hWBig_def]
          rw [tsRfns_iteratedCovGrad_rsDomDomCongrSection_eq (I := I) (M := M) g₀ 2 6
            sigmaE0 _ k x]
          refine le_trans (rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 1 5
            (slotExtend (I := I) (M := M) g₀ 0 4 RLC11) k x) ?_
          have hinner : riemannianFiberNormSq (I := I) (M := M) g₀ 1 ((4 + 1) + k) x
              ((iteratedCovGrad (I := I) g₀ 1 (4 + 1) k
                (slotExtend (I := I) (M := M) g₀ 0 4 RLC11)).toSection x) ≤
              n * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + k) x
                ((iteratedCovGrad (I := I) g₀ 0 4 k RLC11).toSection x) :=
            rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 0 4 RLC11 k x
          have hRLC11jet : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + k) x
              ((iteratedCovGrad (I := I) g₀ 0 4 k RLC11).toSection x) ≤
              (2 * C1 k + 4 * CA k) * (∑ k' ∈ Finset.range (k + 3),
                Combinatorics.antidiagonalTupleGrid b k') + 4 * cfix k := by
            have hsplit11 : iteratedCovGrad (I := I) g₀ 0 4 k RLC11 =
                iteratedCovGrad (I := I) g₀ 0 4 k (RLC11 - RLC01) +
                  (iteratedCovGrad (I := I) g₀ 0 4 k
                    (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁) +
                    iteratedCovGrad (I := I) g₀ 0 4 k RLCfix) := by
              rw [← iteratedCovGrad_add (I := I) g₀ 0 4 k
                (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁) RLCfix]
              rw [← iteratedCovGrad_add (I := I) g₀ 0 4 k (RLC11 - RLC01) _]
              refine congrArg (fun Z => iteratedCovGrad (I := I) g₀ 0 4 k Z) ?_
              rw [show (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁) =
                  RLC01 - RLCfix from by
                rw [riemannLoweredBackgroundDifference, hRLC01_def, hRLCfix_def]]
              abel
            rw [hsplit11]
            rw [show ((iteratedCovGrad (I := I) g₀ 0 4 k (RLC11 - RLC01) +
                  (iteratedCovGrad (I := I) g₀ 0 4 k
                    (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁) +
                    iteratedCovGrad (I := I) g₀ 0 4 k RLCfix)).toSection x) =
                (iteratedCovGrad (I := I) g₀ 0 4 k (RLC11 - RLC01)).toSection x +
                  ((iteratedCovGrad (I := I) g₀ 0 4 k
                    (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)).toSection x +
                    (iteratedCovGrad (I := I) g₀ 0 4 k RLCfix).toSection x) from by
              rw [SmoothCcTensor.toSection_add, SmoothCcTensor.toSection_add]; rfl]
            refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 (4 + k)
              x _ _) ?_
            have hd1 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + k) x
                ((iteratedCovGrad (I := I) g₀ 0 4 k (RLC11 - RLC01)).toSection x) ≤
                C1 k * (∑ k' ∈ Finset.range (k + 3),
                  Combinatorics.antidiagonalTupleGrid b k') := by
              have h := hC1 g₁ T htie hδ_le hδ0 hbound k x
              rw [hRLC11_def, hRLC01_def]
              exact h
            have hd23 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + k) x
                ((iteratedCovGrad (I := I) g₀ 0 4 k
                    (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)).toSection x +
                  (iteratedCovGrad (I := I) g₀ 0 4 k RLCfix).toSection x) ≤
                2 * (CA k * (∑ k' ∈ Finset.range (k + 3),
                  Combinatorics.antidiagonalTupleGrid b k')) + 2 * cfix k := by
              refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0
                (4 + k) x _ _) ?_
              have hd2 := hCA g₁ T htie hδ_le hδ0 hbound k x
              have hd3 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + k) x
                  ((iteratedCovGrad (I := I) g₀ 0 4 k RLCfix).toSection x) ≤ cfix k := by
                rw [hRLCfix_def]; exact hcfix k x
              exact add_le_add (mul_le_mul_of_nonneg_left hd2 (by norm_num))
                (mul_le_mul_of_nonneg_left hd3 (by norm_num))
            calc 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + k) x
                  ((iteratedCovGrad (I := I) g₀ 0 4 k (RLC11 - RLC01)).toSection x) +
                2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + k) x
                  ((iteratedCovGrad (I := I) g₀ 0 4 k
                      (riemannLoweredBackgroundDifference (I := I) (M := M)
                        g₀ g₁)).toSection x +
                    (iteratedCovGrad (I := I) g₀ 0 4 k RLCfix).toSection x)
                ≤ 2 * (C1 k * (∑ k' ∈ Finset.range (k + 3),
                    Combinatorics.antidiagonalTupleGrid b k')) +
                  2 * (2 * (CA k * (∑ k' ∈ Finset.range (k + 3),
                    Combinatorics.antidiagonalTupleGrid b k')) + 2 * cfix k) :=
                  add_le_add (mul_le_mul_of_nonneg_left hd1 (by norm_num))
                    (mul_le_mul_of_nonneg_left hd23 (by norm_num))
              _ = (2 * C1 k + 4 * CA k) * (∑ k' ∈ Finset.range (k + 3),
                    Combinatorics.antidiagonalTupleGrid b k') + 4 * cfix k := by ring
          calc n * riemannianFiberNormSq (I := I) (M := M) g₀ 1 ((4 + 1) + k) x
                ((iteratedCovGrad (I := I) g₀ 1 (4 + 1) k
                  (slotExtend (I := I) (M := M) g₀ 0 4 RLC11)).toSection x)
              ≤ n * (n * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + k) x
                  ((iteratedCovGrad (I := I) g₀ 0 4 k RLC11).toSection x)) :=
                mul_le_mul_of_nonneg_left hinner hn_nn
            _ ≤ n * (n * ((2 * C1 k + 4 * CA k) * (∑ k' ∈ Finset.range (k + 3),
                  Combinatorics.antidiagonalTupleGrid b k') + 4 * cfix k)) := by
                refine mul_le_mul_of_nonneg_left ?_ hn_nn
                exact mul_le_mul_of_nonneg_left hRLC11jet hn_nn
            _ = (n * n) * ((2 * C1 k + 4 * CA k) * (∑ k' ∈ Finset.range (k + 3),
                  Combinatorics.antidiagonalTupleGrid b k') + 4 * cfix k) := by ring
        have hDptW : (∑ l ∈ Finset.range ((i - k) + 1),
            Combinatorics.antidiagonalTupleGrid b l) ≤
            Combinatorics.boundedFactorGridWindow b (i + 1) ((i - k) + 1) :=
          tsTgridSum_le_boundedWindow b hb (by omega) (le_refl _)
        have htgW : (∑ k' ∈ Finset.range (k + 3),
            Combinatorics.antidiagonalTupleGrid b k') ≤
            Combinatorics.boundedFactorGridWindow b (i + 1) (k + 3) :=
          tsTgridSum_le_boundedWindow b hb (by omega) (le_refl _)
        have hWpair : Combinatorics.boundedFactorGridWindow b (i + 1) ((i - k) + 1) *
            Combinatorics.boundedFactorGridWindow b (i + 1) (k + 3) ≤
            Combinatorics.windowPairCellCount ((i - k) + 1) (k + 3) * Wfin := by
          refine le_trans (Combinatorics.boundedFactorGridWindow_mul_le b hb (i + 1)
            ((i - k) + 1) (k + 3) (by omega) (by omega)) ?_
          refine mul_le_mul_of_nonneg_left ?_
            (Combinatorics.windowPairCellCount_nonneg _ _)
          rw [hWfin_def]
          refine Combinatorics.boundedFactorGridWindow_mono b hb (le_refl _) ?_
          omega
        have hDptWfin : Combinatorics.boundedFactorGridWindow b (i + 1) ((i - k) + 1) ≤
            Wfin := by
          rw [hWfin_def]
          exact Combinatorics.boundedFactorGridWindow_mono b hb (le_refl _) (by omega)
        calc riemannianFiberNormSq (I := I) (M := M) g₀ 6 (2 + (i - k)) x
              ((iteratedCovGrad (I := I) g₀ 6 2 (i - k) Dpt).toSection x) *
            riemannianFiberNormSq (I := I) (M := M) g₀ 2 (6 + k) x
              ((iteratedCovGrad (I := I) g₀ 2 6 k WBig).toSection x)
            ≤ (CD (i - k) * (∑ l ∈ Finset.range ((i - k) + 1),
                Combinatorics.antidiagonalTupleGrid b l)) *
              ((n * n) * ((2 * C1 k + 4 * CA k) * (∑ k' ∈ Finset.range (k + 3),
                Combinatorics.antidiagonalTupleGrid b k') + 4 * cfix k)) := by
              refine mul_le_mul hDptjet hWjet
                (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 2 (6 + k) x _) ?_
              exact mul_nonneg (hCD_nn _) (Finset.sum_nonneg fun l _ =>
                Combinatorics.antidiagonalTupleGrid_nonneg b hb l)
          _ ≤ (CD (i - k) * Combinatorics.boundedFactorGridWindow b (i + 1)
                ((i - k) + 1)) *
              ((n * n) * ((2 * C1 k + 4 * CA k) *
                Combinatorics.boundedFactorGridWindow b (i + 1) (k + 3) + 4 * cfix k)) := by
              refine mul_le_mul ?_ ?_ ?_ ?_
              · exact mul_le_mul_of_nonneg_left hDptW (hCD_nn _)
              · refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hn_nn hn_nn)
                refine add_le_add ?_ (le_refl _)
                refine mul_le_mul_of_nonneg_left htgW ?_
                have := hC1_nn k; have := hCA_nn k; linarith
              · refine mul_nonneg (mul_nonneg hn_nn hn_nn) ?_
                refine add_nonneg ?_ ?_
                · refine mul_nonneg ?_ (Finset.sum_nonneg fun k' _ =>
                    Combinatorics.antidiagonalTupleGrid_nonneg b hb k')
                  have := hC1_nn k; have := hCA_nn k; linarith
                · have := hcfix_nn k; linarith
              · exact mul_nonneg (hCD_nn _)
                  (Combinatorics.boundedFactorGridWindow_nonneg b hb _ _)
          _ = CD (i - k) * (n * n) * (2 * C1 k + 4 * CA k) *
                (Combinatorics.boundedFactorGridWindow b (i + 1) ((i - k) + 1) *
                  Combinatorics.boundedFactorGridWindow b (i + 1) (k + 3)) +
              CD (i - k) * (n * n) * (4 * cfix k) *
                Combinatorics.boundedFactorGridWindow b (i + 1) ((i - k) + 1) := by ring
          _ ≤ CD (i - k) * (n * n) * (2 * C1 k + 4 * CA k) *
                (Combinatorics.windowPairCellCount ((i - k) + 1) (k + 3) * Wfin) +
              CD (i - k) * (n * n) * (4 * cfix k) * Wfin := by
              refine add_le_add ?_ ?_
              · refine mul_le_mul_of_nonneg_left hWpair ?_
                refine mul_nonneg (mul_nonneg (hCD_nn _) (mul_nonneg hn_nn hn_nn)) ?_
                have := hC1_nn k; have := hCA_nn k; linarith
              · refine mul_le_mul_of_nonneg_left hDptWfin ?_
                refine mul_nonneg (mul_nonneg (hCD_nn _) (mul_nonneg hn_nn hn_nn)) ?_
                have := hcfix_nn k; linarith
          _ = (CD (i - k) * (n * n) *
              ((2 * C1 k + 4 * CA k) *
                  Combinatorics.windowPairCellCount ((i - k) + 1) (k + 3) + 4 * cfix k)) *
              Wfin := by ring
      calc 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((appCcRS (I := I) (M := M) g₀ 2 (6 + i) (2 + i)
              (appCcLeibnizPsi (I := I) (M := M) g₀ 6 2 Dpt i i)
              (iteratedCovGrad (I := I) g₀ 2 6 i WBig - HW11)).toSection x) +
          2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((∑ k ∈ Finset.range i,
              appCcRS (I := I) (M := M) g₀ 2 (6 + k) (2 + i)
                (appCcLeibnizPsi (I := I) (M := M) g₀ 6 2 Dpt i k)
                (iteratedCovGrad (I := I) g₀ 2 6 k WBig)).toSection x)
          ≤ 2 * (CD 0 * (n * n) * (4 * KcA' i + 4 * KcA i + 2 * cfix i) * Wfin) +
            2 * ((i : ℝ) * appCcGdiag (E := E) i *
              ∑ k ∈ Finset.range i, (CD (i - k) * (n * n) *
                ((2 * C1 k + 4 * CA k) *
                    Combinatorics.windowPairCellCount ((i - k) + 1) (k + 3) +
                  4 * cfix k)) * Wfin) :=
          add_le_add (mul_le_mul_of_nonneg_left hpiece1 (by norm_num))
            (mul_le_mul_of_nonneg_left hpiece2 (by norm_num))
      _ = 2 * (CD 0 * (n * n) * (4 * KcA' i + 4 * KcA i + 2 * cfix i)) * Wfin +
          2 * ((i : ℝ) * appCcGdiag (E := E) i *
            ∑ k ∈ Finset.range i, (CD (i - k) * (n * n) *
              ((2 * C1 k + 4 * CA k) *
                  Combinatorics.windowPairCellCount ((i - k) + 1) (k + 3) + 4 * cfix k)) *
              Wfin) := by ring
    have hsmul_diff : iteratedCovGrad (I := I) g₀ 2 2 i
          (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
            ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) -
          (2 : ℝ) • (HdT1 + HdT2) =
        (2 : ℝ) • ((iteratedCovGrad (I := I) g₀ 2 2 i
            (appCcRS (I := I) (M := M) g₀ 2 6 2 Dpt WBig) - HdT1) +
          (iteratedCovGrad (I := I) g₀ 2 2 i
            (appCcRS (I := I) (M := M) g₀ 2 6 2 phiDt WVd) - HdT2)) := by
      rw [hRiemD]
      rw [iteratedCovGrad_add (I := I) g₀ 2 2 i _ _]
      rw [iteratedCovGrad_smul_pt (I := I) (M := M) g₀ 2 2 i 2 _]
      rw [iteratedCovGrad_smul_pt (I := I) (M := M) g₀ 2 2 i 2 _]
      simp only [smul_add, smul_sub]
      abel
    rw [hsmul_diff]
    rw [show (((2 : ℝ) • ((iteratedCovGrad (I := I) g₀ 2 2 i
          (appCcRS (I := I) (M := M) g₀ 2 6 2 Dpt WBig) - HdT1) +
        (iteratedCovGrad (I := I) g₀ 2 2 i
          (appCcRS (I := I) (M := M) g₀ 2 6 2 phiDt WVd) - HdT2))).toSection x) =
        (2 : ℝ) • (((iteratedCovGrad (I := I) g₀ 2 2 i
          (appCcRS (I := I) (M := M) g₀ 2 6 2 Dpt WBig) - HdT1) +
        (iteratedCovGrad (I := I) g₀ 2 2 i
          (appCcRS (I := I) (M := M) g₀ 2 6 2 phiDt WVd) - HdT2)).toSection x) from by
      rw [SmoothCcTensor.toSection_smul]; rfl]
    rw [rfns_smul_pt (I := I) (M := M) g₀ 2 (2 + i) x 2 _]
    rw [show ((((iteratedCovGrad (I := I) g₀ 2 2 i
          (appCcRS (I := I) (M := M) g₀ 2 6 2 Dpt WBig) - HdT1) +
        (iteratedCovGrad (I := I) g₀ 2 2 i
          (appCcRS (I := I) (M := M) g₀ 2 6 2 phiDt WVd) - HdT2)).toSection x)) =
        ((iteratedCovGrad (I := I) g₀ 2 2 i
          (appCcRS (I := I) (M := M) g₀ 2 6 2 Dpt WBig) - HdT1).toSection x) +
        ((iteratedCovGrad (I := I) g₀ 2 2 i
          (appCcRS (I := I) (M := M) g₀ 2 6 2 phiDt WVd) - HdT2).toSection x) from by
      rw [SmoothCcTensor.toSection_add]; rfl]
    calc (2 : ℝ) ^ 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
          (((iteratedCovGrad (I := I) g₀ 2 2 i
            (appCcRS (I := I) (M := M) g₀ 2 6 2 Dpt WBig) - HdT1).toSection x) +
          ((iteratedCovGrad (I := I) g₀ 2 2 i
            (appCcRS (I := I) (M := M) g₀ 2 6 2 phiDt WVd) - HdT2).toSection x))
        ≤ (2 : ℝ) ^ 2 * (2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (appCcRS (I := I) (M := M) g₀ 2 6 2 Dpt WBig) - HdT1).toSection x) +
          2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (appCcRS (I := I) (M := M) g₀ 2 6 2 phiDt WVd) - HdT2).toSection x)) :=
          mul_le_mul_of_nonneg_left
            (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 2 (2 + i) x _ _)
            (by norm_num)
      _ ≤ (2 : ℝ) ^ 2 * (2 * (2 * (CD 0 * (n * n) *
              (4 * KcA' i + 4 * KcA i + 2 * cfix i)) * Wfin +
            2 * ((i : ℝ) * appCcGdiag (E := E) i *
              ∑ k ∈ Finset.range i, (CD (i - k) * (n * n) *
                ((2 * C1 k + 4 * CA k) *
                    Combinatorics.windowPairCellCount ((i - k) + 1) (k + 3) +
                  4 * cfix k)) * Wfin)) +
          2 * (2 * (cP * ((n * n) * ((2 * KcA' i + 2 * KcA i) * Wfin))))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          exact add_le_add (mul_le_mul_of_nonneg_left hT1res (by norm_num))
            (mul_le_mul_of_nonneg_left hT2res (by norm_num))
      _ = (4 * (2 * (2 * (CD 0 * (n * n) *
              (4 * KcA' i + 4 * KcA i + 2 * cfix i)) +
            2 * ((i : ℝ) * appCcGdiag (E := E) i *
              ∑ k ∈ Finset.range i, CD (i - k) * (n * n) *
                ((2 * C1 k + 4 * CA k) *
                    Combinatorics.windowPairCellCount ((i - k) + 1) (k + 3) +
                  4 * cfix k))) +
          2 * (2 * (cP * (n * n)) * (2 * KcA' i + 2 * KcA i)))) * Wfin := by
          rw [← Finset.sum_mul]
          ring

end TopSeparatedRungRiemannCoeff

section TopSeparatedResidualIntegrator

open DifferentialGeometry.Integral.DivergenceTheorem

set_option backward.isDefEq.respectTransparency false

set_option linter.unusedVariables false in
theorem boundedFactorGridWindow_integral_ballUniform_tameWindow
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R) :
    ∃ K : ℕ → ℝ, (∀ i, 0 ≤ K i) ∧
      ∀ (P : SmoothCcTensor g₀ 0 2),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a →
          MeasureTheory.Integrable
              (fun x => Combinatorics.boundedFactorGridWindow
                (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3))
              (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
            (∫ x, Combinatorics.boundedFactorGridWindow
                  (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3)
                ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
              K i * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  classical
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g₀
  obtain ⟨Kt, hKt_nn, hKt⟩ := antidiagonalTupleGrid_integral_ballUniform_tameWindow
    (I := I) (M := M) g₀ a ha_super hR
  refine ⟨fun i => (∑ k ∈ Finset.range (i + 3), Kt k) * (1 + R ^ 2),
    fun i => mul_nonneg (Finset.sum_nonneg fun k _ => hKt_nn k) (by positivity), ?_⟩
  intro P hPball i hia
  set b : M → ℕ → ℝ := fun x l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
    ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x) with hb_def
  have hb : ∀ (x : M) (l : ℕ), 0 ≤ b x l :=
    fun x l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
  have hcont : ∀ l : ℕ, Continuous (fun x => b x l) := by
    intro l
    have hc := Integral.L2.SmoothCcTensor.continuous_inner_self (I := I) (M := M)
      (iteratedCovGrad (I := I) g₀ 0 2 l P)
    refine hc.congr (fun x => ?_)
    change tensorInnerPointwise (I := I) (M := M) g₀ 0 (2 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 2 l P).toFun x)
        ((iteratedCovGrad (I := I) g₀ 0 2 l P).toFun x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)
    rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g₀ 0 (2 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x),
      ← Integral.L2.SmoothCcTensor.toFun_apply (I := I) (M := M)
        (iteratedCovGrad (I := I) g₀ 0 2 l P) x]
  have hWcont : Continuous (fun x =>
      Combinatorics.boundedFactorGridWindow (b x) (i + 1) (i + 3)) := by
    simp only [Combinatorics.boundedFactorGridWindow, Combinatorics.boundedFactorGrid]
    refine continuous_finset_sum _ (fun k _ => ?_)
    refine continuous_finset_sum _ (fun n _ => ?_)
    refine continuous_finset_sum _ (fun e _ => ?_)
    exact continuous_finset_prod _ (fun m _ => hcont (e m))
  have hint : MeasureTheory.Integrable
      (fun x => Combinatorics.boundedFactorGridWindow (b x) (i + 1) (i + 3))
      (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    hWcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  refine ⟨hint, ?_⟩
  have hint_k : ∀ k : ℕ, MeasureTheory.Integrable
      (fun x => Combinatorics.antidiagonalTupleGrid (b x) k)
      (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    fun k => (hKt P hPball k).1
  have hint2_k : ∀ k : ℕ,
      (∫ x, Combinatorics.antidiagonalTupleGrid (b x) k
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
        Kt k * (1 + ∑ j ∈ Finset.range (k + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) :=
    fun k => (hKt P hPball k).2
  have hmaj_int : MeasureTheory.Integrable
      (fun x => ∑ k ∈ Finset.range (i + 3), Combinatorics.antidiagonalTupleGrid (b x) k)
      (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    MeasureTheory.integrable_finset_sum _ (fun k _ => hint_k k)
  have hmono : ∀ x : M,
      Combinatorics.boundedFactorGridWindow (b x) (i + 1) (i + 3) ≤
        ∑ k ∈ Finset.range (i + 3), Combinatorics.antidiagonalTupleGrid (b x) k := by
    intro x
    rw [Combinatorics.boundedFactorGridWindow]
    exact Finset.sum_le_sum (fun k _ =>
      Combinatorics.boundedFactorGrid_le_antidiagonalTupleGrid (b x) (hb x) (i + 1) k)
  refine le_trans (MeasureTheory.integral_mono hint hmaj_int hmono) ?_
  rw [MeasureTheory.integral_finset_sum _ (fun k _ => hint_k k)]
  have hterm : ∀ k ∈ Finset.range (i + 3),
      (∫ x, Combinatorics.antidiagonalTupleGrid (b x) k
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
        Kt k * (1 + R ^ 2) * (1 + ∑ j ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
    intro k hk
    rw [Finset.mem_range] at hk
    refine le_trans (hint2_k k) ?_
    have hsum_nn : (0 : ℝ) ≤ ∑ j ∈ Finset.range (i + 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 :=
      Finset.sum_nonneg fun j _ => sq_nonneg _
    by_cases hk2 : k ≤ i + 1
    · have hsub : (∑ j ∈ Finset.range (k + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤
          ∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 := by
        refine Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_subset_range.mpr (by omega)) ?_
        intro j _ _
        exact sq_nonneg _
      have h1 : Kt k * (1 + ∑ j ∈ Finset.range (k + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤
          Kt k * (1 + ∑ j ∈ Finset.range (i + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
        refine mul_le_mul_of_nonneg_left (by linarith) (hKt_nn k)
      refine le_trans h1 ?_
      nlinarith [hKt_nn k, sq_nonneg R, hsum_nn,
        mul_nonneg (hKt_nn k) (add_nonneg (by norm_num : (0:ℝ) ≤ 1) hsum_nn)]
    · have hk_eq : k = i + 2 := by omega
      subst hk_eq
      have hsplit : (∑ j ∈ Finset.range ((i + 2) + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) =
          (∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) +
            ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P‖ ^ 2 :=
        Finset.sum_range_succ _ (i + 2)

      have htop : ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P‖ ^ 2 ≤ R ^ 2 := by
        have h := hPball (i + 2) (by omega)
        nlinarith [norm_nonneg (iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P)]
      rw [hsplit]
      nlinarith [hKt_nn (i + 2), hsum_nn, sq_nonneg R,
        mul_nonneg (hKt_nn (i + 2)) hsum_nn,
        mul_nonneg (mul_nonneg (hKt_nn (i + 2)) (sq_nonneg R)) hsum_nn]
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.sum_mul, ← Finset.sum_mul]

private theorem productTerm_integral_tame_le_ordS
    (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (u : SmoothCcTensor g₀ 0 s)
    {R : ℝ} (hR : 0 ≤ R)
    (i : ℕ) (hi1 : 1 ≤ i)
    {Λ : ℝ} (hΛ_nn : 0 ≤ Λ)
    (hΛsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 s x (u.toSection x) ≤ Λ ^ 2)
    (hNi : ‖iteratedCovGrad (I := I) g₀ 0 s i u‖ ≤ R)
    {C : ℝ} (hC_nn : 0 ≤ C)
    (hGNP : ∀ j : ℕ, 0 < j → j < i →
      (∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + j) x
              ((iteratedCovGrad (I := I) g₀ 0 s j u).toSection x)) ^ ((i : ℝ) / (j : ℝ))
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ^ ((j : ℝ) / (i : ℝ)) ≤
        C * Λ ^ (2 * (1 - (j : ℝ) / (i : ℝ))) * R ^ (2 * (j : ℝ) / (i : ℝ)))
    (n : ℕ) (hn_le : n ≤ i) (e : Fin n → ℕ) (he : ∑ m, e m = i) :
    MeasureTheory.Integrable
        (fun x => ∏ m : Fin n,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x))
        (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
      (∫ x, ∏ m : Fin n,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
        (i : ℝ) * (max Λ (max C 1)) ^ (7 * i) * R ^ 2 := by
  classical
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g₀
  set μ : MeasureTheory.Measure M := riemannianVolumeMeasure (I := I) (M := M) g₀ with hμ
  haveI : IsFiniteMeasure μ := by rw [hμ]; infer_instance
  have hi_pos : 0 < i := hi1
  have hiR_pos : (0 : ℝ) < (i : ℝ) := by exact_mod_cast hi_pos
  have hiR_ne : (i : ℝ) ≠ 0 := ne_of_gt hiR_pos
  have hnn : ∀ (j : ℕ) (x : M),
      0 ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + j) x
        ((iteratedCovGrad (I := I) g₀ 0 s j u).toSection x) :=
    fun j x => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (s + j) x _
  have hcont : ∀ j : ℕ, Continuous (fun x => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + j) x
      ((iteratedCovGrad (I := I) g₀ 0 s j u).toSection x)) := by
    intro j
    have hc := Integral.L2.SmoothCcTensor.continuous_inner_self (I := I) (M := M)
      (iteratedCovGrad (I := I) g₀ 0 s j u)
    refine hc.congr (fun x => ?_)
    rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g₀ 0 (s + j) x
        ((iteratedCovGrad (I := I) g₀ 0 s j u).toSection x),
      ← Integral.L2.SmoothCcTensor.toFun_apply (I := I) (M := M)
        (iteratedCovGrad (I := I) g₀ 0 s j u) x]
  have hint : ∀ j : ℕ, MeasureTheory.Integrable
      (fun x => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + j) x
        ((iteratedCovGrad (I := I) g₀ 0 s j u).toSection x)) μ := by
    intro j
    rw [hμ]
    exact integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 0 (s + j)
      (iteratedCovGrad (I := I) g₀ 0 s j u)
  have hint_rpow : ∀ (j : ℕ) (p : ℝ), 0 ≤ p → MeasureTheory.Integrable
      (fun x => (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + j) x
        ((iteratedCovGrad (I := I) g₀ 0 s j u).toSection x)) ^ p) μ := by
    intro j p hp
    have hcp : Continuous (fun x => (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + j) x
        ((iteratedCovGrad (I := I) g₀ 0 s j u).toSection x)) ^ p) :=
      (hcont j).rpow_const (fun x => Or.inr hp)
    exact hcp.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hint_prod : MeasureTheory.Integrable
      (fun x => ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
        ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x)) μ := by
    have hcp : Continuous (fun x => ∏ m : Fin n,
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x)) :=
      continuous_finset_prod Finset.univ (fun m _ => hcont (e m))
    exact hcp.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  refine ⟨hint_prod, ?_⟩
  set Mbar : ℝ := max Λ (max C 1) with hMbar
  have hMbar1 : (1 : ℝ) ≤ Mbar := le_trans (le_max_right C 1) (le_max_right Λ _)
  have hMbar_nn : 0 ≤ Mbar := le_trans zero_le_one hMbar1
  have hΛ_le : Λ ≤ Mbar := le_max_left _ _
  have hC_le : C ≤ Mbar := le_trans (le_max_left C 1) (le_max_right Λ _)
  set Sset : Finset (Fin n) := Finset.univ.filter (fun m => 0 < e m) with hSset
  set Zset : Finset (Fin n) := Finset.univ.filter (fun m => ¬ (0 < e m)) with hZset
  have hsplit : ∀ x : M,
      (∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x)) =
        (∏ m ∈ Sset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x)) *
          (∏ m ∈ Zset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x)) := by
    intro x
    rw [hSset, hZset]
    exact (Finset.prod_filter_mul_prod_filter_not Finset.univ (fun m => 0 < e m)
      (fun m => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
        ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x))).symm
  have hZbound : ∀ x : M,
      (∏ m ∈ Zset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
        ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x)) ≤ Λ ^ (2 * Zset.card) := by
    intro x
    calc (∏ m ∈ Zset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x))
        ≤ ∏ _m ∈ Zset, Λ ^ 2 := by
          apply Finset.prod_le_prod (fun m _ => hnn (e m) x)
          intro m hm
          have hem0 : e m = 0 := by have := (Finset.mem_filter.mp hm).2; omega
          rw [hem0]; exact hΛsup x
      _ = Λ ^ (2 * Zset.card) := by rw [Finset.prod_const, ← pow_mul]
  have hZsum0 : ∑ m ∈ Zset, e m = 0 := by
    apply Finset.sum_eq_zero
    intro m hm
    have := (Finset.mem_filter.mp hm).2; omega
  have hSsum : ∑ m ∈ Sset, e m = i := by
    have h := Finset.sum_filter_add_sum_filter_not Finset.univ (fun m => 0 < e m) e
    rw [← hSset, ← hZset, hZsum0, add_zero, he] at h
    exact h
  have hScard_pos : 1 ≤ Sset.card := by
    rcases Nat.eq_zero_or_pos Sset.card with h0 | hp
    · exfalso
      rw [Finset.card_eq_zero] at h0
      rw [h0, Finset.sum_empty] at hSsum
      omega
    · exact hp
  rcases Nat.lt_or_ge Sset.card 2 with hScard_lt2 | hScard_ge2
  · have hScard1 : Sset.card = 1 := by omega
    obtain ⟨m₀, hm₀⟩ := Finset.card_eq_one.mp hScard1
    have hem₀ : e m₀ = i := by
      have hss : ∑ m ∈ Sset, e m = e m₀ := by rw [hm₀, Finset.sum_singleton]
      rw [hss] at hSsum; exact hSsum
    have hSprod : ∀ x : M,
        (∏ m ∈ Sset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x)) =
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + i) x
            ((iteratedCovGrad (I := I) g₀ 0 s i u).toSection x) := by
      intro x; rw [hm₀, Finset.prod_singleton, hem₀]
    have hpt : ∀ x : M,
        (∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x)) ≤
          Λ ^ (2 * Zset.card) * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + i) x
            ((iteratedCovGrad (I := I) g₀ 0 s i u).toSection x) := by
      intro x
      rw [hsplit x, hSprod x]
      calc (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + i) x
              ((iteratedCovGrad (I := I) g₀ 0 s i u).toSection x)) *
            (∏ m ∈ Zset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x))
          ≤ (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + i) x
              ((iteratedCovGrad (I := I) g₀ 0 s i u).toSection x)) * Λ ^ (2 * Zset.card) :=
            mul_le_mul_of_nonneg_left (hZbound x) (hnn i x)
        _ = Λ ^ (2 * Zset.card) * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + i) x
              ((iteratedCovGrad (I := I) g₀ 0 s i u).toSection x) := mul_comm _ _
    have hintFi : (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + i) x
        ((iteratedCovGrad (I := I) g₀ 0 s i u).toSection x) ∂μ) ≤ R ^ 2 := by
      have heq : (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + i) x
          ((iteratedCovGrad (I := I) g₀ 0 s i u).toSection x) ∂μ) =
          ‖iteratedCovGrad (I := I) g₀ 0 s i u‖ ^ 2 := by
        rw [SmoothCcTensor.norm_def (iteratedCovGrad (I := I) g₀ 0 s i u), hμ]
        exact (tensorL2Norm_sq_eq_integral_riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + i)
          ((iteratedCovGrad (I := I) g₀ 0 s i u).toSection)).symm
      rw [heq]
      nlinarith [hNi, norm_nonneg (iteratedCovGrad (I := I) g₀ 0 s i u), hR]
    have hΛZ_nn : 0 ≤ Λ ^ (2 * Zset.card) := pow_nonneg hΛ_nn _
    calc (∫ x, ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x) ∂μ)
        ≤ ∫ x, Λ ^ (2 * Zset.card) * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + i) x
            ((iteratedCovGrad (I := I) g₀ 0 s i u).toSection x) ∂μ :=
          MeasureTheory.integral_mono hint_prod ((hint i).const_mul _) hpt
      _ = Λ ^ (2 * Zset.card) * ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + i) x
            ((iteratedCovGrad (I := I) g₀ 0 s i u).toSection x) ∂μ :=
          MeasureTheory.integral_const_mul _ _
      _ ≤ Λ ^ (2 * Zset.card) * R ^ 2 := mul_le_mul_of_nonneg_left hintFi hΛZ_nn
      _ ≤ (i : ℝ) * Mbar ^ (7 * i) * R ^ 2 := by
          have hZle : Zset.card ≤ i := le_trans (Finset.card_le_univ _) (by simpa using hn_le)
          have e1 : Λ ^ (2 * Zset.card) ≤ Mbar ^ (7 * i) :=
            le_trans (pow_le_pow_left₀ hΛ_nn hΛ_le _)
              (pow_le_pow_right₀ hMbar1 (by omega))
          have e4 : Λ ^ (2 * Zset.card) * R ^ 2 ≤ Mbar ^ (7 * i) * R ^ 2 :=
            mul_le_mul_of_nonneg_right e1 (sq_nonneg R)
          have e5 : Mbar ^ (7 * i) * R ^ 2 ≤ (i : ℝ) * Mbar ^ (7 * i) * R ^ 2 := by
            have h1i : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi1
            have hMR : 0 ≤ Mbar ^ (7 * i) * R ^ 2 :=
              mul_nonneg (pow_nonneg hMbar_nn _) (sq_nonneg R)
            calc Mbar ^ (7 * i) * R ^ 2 = 1 * (Mbar ^ (7 * i) * R ^ 2) := by ring
              _ ≤ (i : ℝ) * (Mbar ^ (7 * i) * R ^ 2) := mul_le_mul_of_nonneg_right h1i hMR
              _ = (i : ℝ) * Mbar ^ (7 * i) * R ^ 2 := by ring
          exact le_trans e4 e5
  · have hem_lt : ∀ m ∈ Sset, e m < i := by
      intro m hm
      have hmpos : 0 < e m := (Finset.mem_filter.mp hm).2
      have hadd : e m + ∑ m' ∈ Sset.erase m, e m' = ∑ m' ∈ Sset, e m' :=
        Finset.add_sum_erase Sset e hm
      rw [hSsum] at hadd
      have herase_ne : (Sset.erase m).Nonempty := by
        rw [← Finset.card_pos, Finset.card_erase_of_mem hm]; omega
      obtain ⟨m', hm'⟩ := herase_ne
      have hm'S : m' ∈ Sset := Finset.mem_of_mem_erase hm'
      have hm'pos : 1 ≤ e m' := (Finset.mem_filter.mp hm'S).2
      have hle : e m' ≤ ∑ m'' ∈ Sset.erase m, e m'' :=
        Finset.single_le_sum (fun k _ => Nat.zero_le _) hm'
      omega
    have hAMGM : ∀ x : M,
        (∏ m ∈ Sset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x)) ≤
          ∑ m ∈ Sset, ((e m : ℝ) / i) *
            (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) := by
      intro x
      have hw_nn : ∀ m ∈ Sset, 0 ≤ (e m : ℝ) / i := fun m _ => by positivity
      have hw_sum : ∑ m ∈ Sset, (e m : ℝ) / i = 1 := by
        rw [← Finset.sum_div]
        rw [show (∑ m ∈ Sset, (e m : ℝ)) = ((i : ℕ) : ℝ) from by
          rw [← Nat.cast_sum]; exact_mod_cast hSsum]
        exact div_self hiR_ne
      have hz_nn : ∀ m ∈ Sset, 0 ≤ (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) :=
        fun m _ => Real.rpow_nonneg (hnn (e m) x) _
      have hAM := Real.geom_mean_le_arith_mean_weighted Sset (fun m => (e m : ℝ) / i)
        (fun m => (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x)) ^ ((i : ℝ) / (e m : ℝ)))
        hw_nn hw_sum hz_nn
      have hLHS : (∏ m ∈ Sset, ((riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x)) ^ ((i : ℝ) / (e m : ℝ)))
            ^ ((e m : ℝ) / i)) =
          ∏ m ∈ Sset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x) := by
        apply Finset.prod_congr rfl
        intro m hm
        have hmpos : 0 < e m := (Finset.mem_filter.mp hm).2
        have hemR_ne : (e m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hmpos.ne'
        rw [← Real.rpow_mul (hnn (e m) x)]
        rw [show ((i : ℝ) / (e m : ℝ)) * ((e m : ℝ) / i) = 1 by field_simp]
        rw [Real.rpow_one]
      rw [hLHS] at hAM
      exact hAM
    have hfactor : ∀ m ∈ Sset,
        (∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ) ≤
          Mbar ^ (5 * i) * R ^ 2 := by
      intro m hm
      have hmpos : 0 < e m := (Finset.mem_filter.mp hm).2
      have hem_lt_i : e m < i := hem_lt m hm
      have hemR_pos : (0 : ℝ) < (e m : ℝ) := by exact_mod_cast hmpos
      have hemR_ne : (e m : ℝ) ≠ 0 := ne_of_gt hemR_pos
      have hgn := hGNP (e m) hmpos hem_lt_i
      set Ival : ℝ := ∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ
        with hIval
      have hIval_nn : 0 ≤ Ival := by
        rw [hIval]; exact integral_nonneg (fun x => Real.rpow_nonneg (hnn (e m) x) _)
      have hθ_nn : 0 ≤ (e m : ℝ) / i := by positivity
      have hθ_le1 : (e m : ℝ) / i ≤ 1 := by
        rw [div_le_one hiR_pos]; exact_mod_cast Nat.le_of_lt hem_lt_i
      have hexp1_nn : 0 ≤ 2 * (1 - (e m : ℝ) / i) := by nlinarith
      have hexp1_le : 2 * (1 - (e m : ℝ) / i) ≤ 2 := by nlinarith
      have hΛpow : Λ ^ (2 * (1 - (e m : ℝ) / i)) ≤ Mbar ^ (2 : ℕ) := by
        calc Λ ^ (2 * (1 - (e m : ℝ) / i)) ≤ Mbar ^ (2 * (1 - (e m : ℝ) / i)) :=
              Real.rpow_le_rpow hΛ_nn hΛ_le hexp1_nn
          _ ≤ Mbar ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hMbar1 hexp1_le
          _ = Mbar ^ (2 : ℕ) := by rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      have hbase_le : C * Λ ^ (2 * (1 - (e m : ℝ) / i)) ≤ Mbar ^ (3 : ℕ) := by
        have h1 : C * Λ ^ (2 * (1 - (e m : ℝ) / i)) ≤ Mbar * Mbar ^ (2 : ℕ) :=
          mul_le_mul hC_le hΛpow (Real.rpow_nonneg hΛ_nn _) hMbar_nn
        calc C * Λ ^ (2 * (1 - (e m : ℝ) / i)) ≤ Mbar * Mbar ^ (2 : ℕ) := h1
          _ = Mbar ^ (3 : ℕ) := by ring
      have hbase_nn : 0 ≤ C * Λ ^ (2 * (1 - (e m : ℝ) / i)) :=
        mul_nonneg hC_nn (Real.rpow_nonneg hΛ_nn _)
      have hIval_eq : Ival = (Ival ^ ((e m : ℝ) / i)) ^ ((i : ℝ) / (e m : ℝ)) := by
        rw [← Real.rpow_mul hIval_nn]
        rw [show ((e m : ℝ) / i) * ((i : ℝ) / (e m : ℝ)) = 1 by field_simp]
        rw [Real.rpow_one]
      have hM3_one : (1 : ℝ) ≤ Mbar ^ (3 : ℕ) :=
        le_trans hMbar1 (le_self_pow₀ hMbar1 (by norm_num))
      have hidiv : (i : ℝ) / (e m : ℝ) ≤ (i : ℝ) :=
        div_le_self hiR_pos.le (by exact_mod_cast hmpos)
      have hsplit_pow : (C * Λ ^ (2 * (1 - (e m : ℝ) / i)) * R ^ (2 * (e m : ℝ) / i))
            ^ ((i : ℝ) / (e m : ℝ)) =
          (C * Λ ^ (2 * (1 - (e m : ℝ) / i))) ^ ((i : ℝ) / (e m : ℝ)) *
            (R ^ (2 * (e m : ℝ) / i)) ^ ((i : ℝ) / (e m : ℝ)) :=
        Real.mul_rpow hbase_nn (Real.rpow_nonneg hR _)
      have hRcollapse : (R ^ (2 * (e m : ℝ) / i)) ^ ((i : ℝ) / (e m : ℝ)) = R ^ (2 : ℕ) := by
        rw [← Real.rpow_mul hR]
        rw [show (2 * (e m : ℝ) / i) * ((i : ℝ) / (e m : ℝ)) = 2 by field_simp]
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      have hbasepow : (C * Λ ^ (2 * (1 - (e m : ℝ) / i))) ^ ((i : ℝ) / (e m : ℝ)) ≤
          Mbar ^ (5 * i) := by
        calc (C * Λ ^ (2 * (1 - (e m : ℝ) / i))) ^ ((i : ℝ) / (e m : ℝ))
            ≤ (Mbar ^ (3 : ℕ)) ^ ((i : ℝ) / (e m : ℝ)) :=
              Real.rpow_le_rpow hbase_nn hbase_le (by positivity)
          _ ≤ (Mbar ^ (3 : ℕ)) ^ ((i : ℝ)) :=
              Real.rpow_le_rpow_of_exponent_le hM3_one hidiv
          _ = (Mbar ^ (3 : ℕ)) ^ (i : ℕ) := by rw [Real.rpow_natCast]
          _ = Mbar ^ (3 * i) := by rw [← pow_mul]
          _ ≤ Mbar ^ (5 * i) := pow_le_pow_right₀ hMbar1 (by omega)
      calc Ival = (Ival ^ ((e m : ℝ) / i)) ^ ((i : ℝ) / (e m : ℝ)) := hIval_eq
        _ ≤ (C * Λ ^ (2 * (1 - (e m : ℝ) / i)) * R ^ (2 * (e m : ℝ) / i))
              ^ ((i : ℝ) / (e m : ℝ)) :=
            Real.rpow_le_rpow (Real.rpow_nonneg hIval_nn _) hgn (by positivity)
        _ = (C * Λ ^ (2 * (1 - (e m : ℝ) / i))) ^ ((i : ℝ) / (e m : ℝ)) *
              (R ^ (2 * (e m : ℝ) / i)) ^ ((i : ℝ) / (e m : ℝ)) := hsplit_pow
        _ = (C * Λ ^ (2 * (1 - (e m : ℝ) / i))) ^ ((i : ℝ) / (e m : ℝ)) * R ^ (2 : ℕ) := by
            rw [hRcollapse]
        _ ≤ Mbar ^ (5 * i) * R ^ 2 := mul_le_mul_of_nonneg_right hbasepow (sq_nonneg R)
    have hSsum_factor : ∑ m ∈ Sset, ((e m : ℝ) / i) *
        (∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ) ≤
        Mbar ^ (5 * i) * R ^ 2 := by
      have hw_nn : ∀ m ∈ Sset, 0 ≤ (e m : ℝ) / i := fun m _ => by positivity
      have hw_sum : ∑ m ∈ Sset, (e m : ℝ) / i = 1 := by
        rw [← Finset.sum_div]
        rw [show (∑ m ∈ Sset, (e m : ℝ)) = ((i : ℕ) : ℝ) from by
          rw [← Nat.cast_sum]; exact_mod_cast hSsum]
        exact div_self hiR_ne
      calc ∑ m ∈ Sset, ((e m : ℝ) / i) *
            (∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ)
          ≤ ∑ m ∈ Sset, ((e m : ℝ) / i) * (Mbar ^ (5 * i) * R ^ 2) := by
            apply Finset.sum_le_sum
            intro m hm
            exact mul_le_mul_of_nonneg_left (hfactor m hm) (hw_nn m hm)
        _ = (∑ m ∈ Sset, (e m : ℝ) / i) * (Mbar ^ (5 * i) * R ^ 2) := by rw [Finset.sum_mul]
        _ = Mbar ^ (5 * i) * R ^ 2 := by rw [hw_sum, one_mul]
    have hpt2 : ∀ x : M,
        (∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x)) ≤
          Λ ^ (2 * Zset.card) * ∑ m ∈ Sset, ((e m : ℝ) / i) *
            (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) := by
      intro x
      rw [hsplit x]
      have hZnn : 0 ≤ ∏ m ∈ Zset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x) :=
        Finset.prod_nonneg (fun m _ => hnn (e m) x)
      have hsum_nn : 0 ≤ ∑ m ∈ Sset, ((e m : ℝ) / i) *
          (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) :=
        Finset.sum_nonneg (fun m _ => mul_nonneg (by positivity) (Real.rpow_nonneg (hnn (e m) x) _))
      calc (∏ m ∈ Sset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x)) *
            (∏ m ∈ Zset, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x))
          ≤ (∑ m ∈ Sset, ((e m : ℝ) / i) *
              (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x)) ^ ((i : ℝ) / (e m : ℝ))) *
              Λ ^ (2 * Zset.card) :=
            mul_le_mul (hAMGM x) (hZbound x) hZnn hsum_nn
        _ = Λ ^ (2 * Zset.card) * ∑ m ∈ Sset, ((e m : ℝ) / i) *
              (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) :=
            mul_comm _ _
    have hsum_int : MeasureTheory.Integrable
        (fun x => ∑ m ∈ Sset, ((e m : ℝ) / i) *
          (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x)) ^ ((i : ℝ) / (e m : ℝ))) μ := by
      apply MeasureTheory.integrable_finset_sum
      intro m _
      exact (hint_rpow (e m) ((i : ℝ) / (e m : ℝ)) (by positivity)).const_mul _
    have hint_eq : (∫ x, ∑ m ∈ Sset, ((e m : ℝ) / i) *
          (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ) =
        ∑ m ∈ Sset, ((e m : ℝ) / i) *
          (∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ) := by
      rw [MeasureTheory.integral_finset_sum]
      · apply Finset.sum_congr rfl
        intro m _; rw [MeasureTheory.integral_const_mul]
      · intro m _
        exact (hint_rpow (e m) ((i : ℝ) / (e m : ℝ)) (by positivity)).const_mul _
    have hΛZ_nn : 0 ≤ Λ ^ (2 * Zset.card) := pow_nonneg hΛ_nn _
    calc (∫ x, ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x) ∂μ)
        ≤ ∫ x, Λ ^ (2 * Zset.card) * ∑ m ∈ Sset, ((e m : ℝ) / i) *
            (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ :=
          MeasureTheory.integral_mono hint_prod (hsum_int.const_mul _) hpt2
      _ = Λ ^ (2 * Zset.card) * ∫ x, ∑ m ∈ Sset, ((e m : ℝ) / i) *
            (riemannianFiberNormSq (I := I) (M := M) g₀ 0 (s + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 s (e m) u).toSection x)) ^ ((i : ℝ) / (e m : ℝ)) ∂μ :=
          MeasureTheory.integral_const_mul _ _
      _ ≤ Λ ^ (2 * Zset.card) * (Mbar ^ (5 * i) * R ^ 2) := by
          rw [hint_eq]
          exact mul_le_mul_of_nonneg_left hSsum_factor hΛZ_nn
      _ ≤ (i : ℝ) * Mbar ^ (7 * i) * R ^ 2 := by
          have hZle : Zset.card ≤ i := le_trans (Finset.card_le_univ _) (by simpa using hn_le)
          have e1 : Λ ^ (2 * Zset.card) ≤ Mbar ^ (2 * i) :=
            le_trans (pow_le_pow_left₀ hΛ_nn hΛ_le _) (pow_le_pow_right₀ hMbar1 (by omega))
          have e3 : Mbar ^ (2 * i) * Mbar ^ (5 * i) = Mbar ^ (7 * i) := by
            rw [← pow_add]; congr 1; ring
          have e4 : Λ ^ (2 * Zset.card) * (Mbar ^ (5 * i) * R ^ 2) ≤
              Mbar ^ (2 * i) * (Mbar ^ (5 * i) * R ^ 2) :=
            mul_le_mul_of_nonneg_right e1
              (mul_nonneg (pow_nonneg hMbar_nn _) (sq_nonneg R))
          have e5 : Mbar ^ (7 * i) * R ^ 2 ≤ (i : ℝ) * Mbar ^ (7 * i) * R ^ 2 := by
            have h1i : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi1
            have hMR : 0 ≤ Mbar ^ (7 * i) * R ^ 2 :=
              mul_nonneg (pow_nonneg hMbar_nn _) (sq_nonneg R)
            calc Mbar ^ (7 * i) * R ^ 2 = 1 * (Mbar ^ (7 * i) * R ^ 2) := by ring
              _ ≤ (i : ℝ) * (Mbar ^ (7 * i) * R ^ 2) := mul_le_mul_of_nonneg_right h1i hMR
              _ = (i : ℝ) * Mbar ^ (7 * i) * R ^ 2 := by ring
          calc Λ ^ (2 * Zset.card) * (Mbar ^ (5 * i) * R ^ 2)
              ≤ Mbar ^ (2 * i) * (Mbar ^ (5 * i) * R ^ 2) := e4
            _ = Mbar ^ (7 * i) * R ^ 2 := by rw [← mul_assoc, e3]
            _ ≤ (i : ℝ) * Mbar ^ (7 * i) * R ^ 2 := e5

set_option linter.unusedVariables false in
private theorem cappedTopLayerCell_integral_le
    (g₀ : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g₀ 0 2)
    {Lam : ℝ} (hLam_nn : 0 ≤ Lam)
    (hΛsup_low : ∀ (m : ℕ), m ≤ 2 → ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m) x
        ((iteratedCovGrad (I := I) g₀ 0 2 m P).toSection x) ≤ Lam ^ 2)
    (Cgn : ℕ → ℝ) (hCgn_nn : ∀ k, 0 ≤ Cgn k)
    (hGNv : ∀ (i₀ : ℕ), 1 ≤ i₀ → ∀ (j : ℕ), 0 < j → j < i₀ →
      (∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + 2) + j) x
              ((iteratedCovGrad (I := I) g₀ 0 (2 + 2) j
                (iteratedCovGrad (I := I) g₀ 0 2 2 P)).toSection x)) ^ ((i₀ : ℝ) / (j : ℝ))
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ^ ((j : ℝ) / (i₀ : ℝ)) ≤
        Cgn i₀ * Lam ^ (2 * (1 - (j : ℝ) / (i₀ : ℝ))) *
          ‖iteratedCovGrad (I := I) g₀ 0 (2 + 2) i₀
            (iteratedCovGrad (I := I) g₀ 0 2 2 P)‖ ^ (2 * (j : ℝ) / (i₀ : ℝ)))
    (i n : ℕ) (e : Fin n → ℕ) (hn : n ≤ i + 2)
    (he_sum : ∑ m, e m = i + 2) (he_cap : ∀ m, e m ≤ i + 1)
    (MBv : ℝ) (hMBv1 : 1 ≤ MBv) (hMBv_Lam : Lam ≤ MBv)
    (hMBv_vol : ((riemannianVolumeMeasure (I := I) (M := M) g₀) Set.univ).toReal ≤ MBv)
    (hMBv_Cgn : ∀ k, k ≤ i → Cgn k ≤ MBv) :
    (∫ x, ∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)
      ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
      (((i : ℝ) + 2) * MBv ^ (9 * (i + 2))) *
        (1 + ∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  classical
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g₀
  set μ : MeasureTheory.Measure M := riemannianVolumeMeasure (I := I) (M := M) g₀ with hμ
  haveI : IsFiniteMeasure μ := by rw [hμ]; infer_instance
  have hMBv_nn : 0 ≤ MBv := le_trans zero_le_one hMBv1
  have hLam2_nn : 0 ≤ Lam ^ 2 := sq_nonneg _
  set Wsum : ℝ := 1 + ∑ j ∈ Finset.range (i + 2),
    ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 with hWsum
  have hWsum1 : 1 ≤ Wsum := by
    rw [hWsum]
    have := Finset.sum_nonneg (fun j (_ : j ∈ Finset.range (i + 2)) =>
      sq_nonneg (‖iteratedCovGrad (I := I) g₀ 0 2 j P‖))
    linarith
  have hWsum_nn : 0 ≤ Wsum := le_trans zero_le_one hWsum1
  set F : M → ℝ := fun x => ∏ m : Fin n,
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
      ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x) with hF
  have hfac_nn : ∀ (m : Fin n) (x : M),
      0 ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x) :=
    fun m x => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + e m) x _
  have hfac_cont : ∀ m : Fin n, Continuous (fun x =>
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) := by
    intro m
    have hc := Integral.L2.SmoothCcTensor.continuous_inner_self (I := I) (M := M)
      (iteratedCovGrad (I := I) g₀ 0 2 (e m) P)
    refine hc.congr (fun x => ?_)
    rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g₀ 0 (2 + e m) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x),
      ← Integral.L2.SmoothCcTensor.toFun_apply (I := I) (M := M)
        (iteratedCovGrad (I := I) g₀ 0 2 (e m) P) x]
  have hF_int : MeasureTheory.Integrable F μ := by
    have hcp : Continuous F := by
      rw [hF]; exact continuous_finset_prod _ (fun m _ => hfac_cont m)
    exact hcp.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  set high : Finset (Fin n) := Finset.univ.filter (fun m => 3 ≤ e m) with hhigh
  set low : Finset (Fin n) := Finset.univ.filter (fun m => ¬ 3 ≤ e m) with hlow
  have hmem_high : ∀ m : Fin n, m ∈ high ↔ 3 ≤ e m := fun m => by
    rw [hhigh, Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ m, h⟩⟩
  have hmem_low : ∀ m : Fin n, m ∈ low ↔ ¬ 3 ≤ e m := fun m => by
    rw [hlow, Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ m, h⟩⟩
  have hlowbnd : ∀ (x : M),
      (∏ m ∈ low, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ≤ Lam ^ (2 * low.card) := by
    intro x
    calc (∏ m ∈ low, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
        ≤ ∏ _m ∈ low, Lam ^ 2 := by
          apply Finset.prod_le_prod (fun m _ => hfac_nn m x)
          intro m hm
          have hem : e m ≤ 2 := by
            have := (hmem_low m).mp hm; omega
          exact hΛsup_low (e m) hem x
      _ = Lam ^ (2 * low.card) := by rw [Finset.prod_const, ← pow_mul, Nat.mul_comm]
  by_cases hne : high.Nonempty
  · have hcard_pos : 0 < high.card := Finset.Nonempty.card_pos hne
    set i₀ : ℕ := ∑ m ∈ high, (e m - 2) with hi₀
    have hge3 : ∀ m ∈ high, 3 ≤ e m := fun m hm => (hmem_high m).mp hm
    have hn'_le : high.card ≤ i₀ := by
      rw [hi₀, Finset.card_eq_sum_ones]
      apply Finset.sum_le_sum
      intro m hm; have := hge3 m hm; omega
    have hi₀_ge1 : 1 ≤ i₀ := le_trans hcard_pos hn'_le
    have heq_sum : (∑ m ∈ high, e m) = i₀ + 2 * high.card := by
      have h1 : (∑ m ∈ high, e m) = ∑ m ∈ high, ((e m - 2) + 2) :=
        Finset.sum_congr rfl (fun m hm => by have := hge3 m hm; omega)
      rw [h1, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, ← hi₀,
        Nat.mul_comm]
    have hsum_high_le : (∑ m ∈ high, e m) ≤ i + 2 := by
      calc (∑ m ∈ high, e m) ≤ ∑ m : Fin n, e m :=
            Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
        _ = i + 2 := he_sum
    have hi₀_bound : 2 + i₀ ≤ i + 1 := by
      rcases Nat.lt_or_ge high.card 2 with h1 | h2
      · have hcard1 : high.card = 1 := by omega
        obtain ⟨m₀, hm₀⟩ := Finset.card_eq_one.mp hcard1
        have hsingle : (∑ m ∈ high, e m) = e m₀ := by rw [hm₀, Finset.sum_singleton]
        have hcap0 : e m₀ ≤ i + 1 := he_cap m₀
        omega
      · omega
    set ι : Fin high.card → {m // m ∈ high} := fun m' => (Finset.equivFin high).symm m' with hι
    set e' : Fin high.card → ℕ := fun m' => e ((ι m' : Fin n)) - 2 with he'
    have hge3' : ∀ m' : Fin high.card, 3 ≤ e ((ι m' : Fin n)) :=
      fun m' => hge3 _ (ι m').2
    have he'_sum : (∑ m', e' m') = i₀ := by
      rw [hi₀, ← Finset.sum_coe_sort high (fun m => e m - 2)]
      exact Equiv.sum_comp (Finset.equivFin high).symm (fun m : {m // m ∈ high} => e ↑m - 2)
    have hcongr_local : ∀ (x : M) (n₁ n₂ : ℕ), n₁ = n₂ →
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + n₁) x
          ((iteratedCovGrad (I := I) g₀ 0 2 n₁ P).toSection x) =
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + n₂) x
          ((iteratedCovGrad (I := I) g₀ 0 2 n₂ P).toSection x) := by
      intro x n₁ n₂ h; subst h; rfl
    have hcellprod : ∀ x : M,
        (∏ m ∈ high, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) =
        ∏ m' : Fin high.card,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + 2) + e' m') x
            ((iteratedCovGrad (I := I) g₀ 0 (2 + 2) (e' m')
              (iteratedCovGrad (I := I) g₀ 0 2 2 P)).toSection x) := by
      intro x
      rw [← Finset.prod_coe_sort high (fun m =>
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)),
        ← Equiv.prod_comp (Finset.equivFin high).symm
          (fun m : {m // m ∈ high} =>
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e ↑m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e ↑m) P).toSection x))]
      refine Finset.prod_congr rfl (fun m' _ => ?_)
      symm
      rw [rfns_iteratedCovGrad_comp (I := I) (M := M) g₀ 0 2 2 (e' m') P x]
      exact hcongr_local x (2 + e' m') (e ((ι m' : Fin n))) (by
        have := hge3' m'; simp only [he']; omega)
    have hΛsup_v2 : ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 2) x
          ((iteratedCovGrad (I := I) g₀ 0 2 2 P).toSection x) ≤ Lam ^ 2 :=
      hΛsup_low 2 (le_refl 2)
    have htmpl := productTerm_integral_tame_le_ordS (I := I) (M := M) g₀ (2 + 2)
      (iteratedCovGrad (I := I) g₀ 0 2 2 P)
      (norm_nonneg (iteratedCovGrad (I := I) g₀ 0 (2 + 2) i₀
        (iteratedCovGrad (I := I) g₀ 0 2 2 P)))
      i₀ hi₀_ge1 hLam_nn hΛsup_v2 (le_refl _) (hCgn_nn i₀) (hGNv i₀ hi₀_ge1)
      high.card hn'_le e' he'_sum
    have hhigh_int : MeasureTheory.Integrable
        (fun x => ∏ m ∈ high, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) μ := by
      have hcp : Continuous (fun x => ∏ m ∈ high,
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) :=
        continuous_finset_prod _ (fun m _ => hfac_cont m)
      exact hcp.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hnorm_int : ∀ (s' : ℕ) (w : Integral.L2.SmoothCcTensor g₀ 0 s'),
        (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 s' x (w.toSection x) ∂μ) = ‖w‖ ^ 2 := by
      intro s' w
      rw [SmoothCcTensor.norm_def w, hμ]
      exact (tensorL2Norm_sq_eq_integral_riemannianFiberNormSq (I := I) (M := M) g₀ 0 s'
        (w.toSection)).symm
    have hhigh_le : (∫ x, ∏ m ∈ high,
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x) ∂μ) ≤
        (i₀ : ℝ) * (max Lam (max (Cgn i₀) 1)) ^ (7 * i₀) *
          ‖iteratedCovGrad (I := I) g₀ 0 (2 + 2) i₀
            (iteratedCovGrad (I := I) g₀ 0 2 2 P)‖ ^ 2 := by
      rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hcellprod)]
      exact htmpl.2
    have hRsq_le : ‖iteratedCovGrad (I := I) g₀ 0 (2 + 2) i₀
        (iteratedCovGrad (I := I) g₀ 0 2 2 P)‖ ^ 2 ≤ Wsum := by
      have e1 : ‖iteratedCovGrad (I := I) g₀ 0 (2 + 2) i₀
          (iteratedCovGrad (I := I) g₀ 0 2 2 P)‖ ^ 2 =
          ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + 2) + i₀) x
            ((iteratedCovGrad (I := I) g₀ 0 (2 + 2) i₀
              (iteratedCovGrad (I := I) g₀ 0 2 2 P)).toSection x) ∂μ :=
        (hnorm_int ((2 + 2) + i₀) (iteratedCovGrad (I := I) g₀ 0 (2 + 2) i₀
          (iteratedCovGrad (I := I) g₀ 0 2 2 P))).symm
      have e2 : (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + 2) + i₀) x
            ((iteratedCovGrad (I := I) g₀ 0 (2 + 2) i₀
              (iteratedCovGrad (I := I) g₀ 0 2 2 P)).toSection x) ∂μ) =
          ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (2 + i₀)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (2 + i₀) P).toSection x) ∂μ := by
        apply MeasureTheory.integral_congr_ae
        refine Filter.Eventually.of_forall (fun x => ?_)
        exact rfns_iteratedCovGrad_comp (I := I) (M := M) g₀ 0 2 2 i₀ P x
      have e3 : (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (2 + i₀)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (2 + i₀) P).toSection x) ∂μ) =
          ‖iteratedCovGrad (I := I) g₀ 0 2 (2 + i₀) P‖ ^ 2 :=
        hnorm_int (2 + (2 + i₀)) (iteratedCovGrad (I := I) g₀ 0 2 (2 + i₀) P)
      have hmem : 2 + i₀ ∈ Finset.range (i + 2) := Finset.mem_range.mpr (by omega)
      have hle_sum : ‖iteratedCovGrad (I := I) g₀ 0 2 (2 + i₀) P‖ ^ 2 ≤
          ∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 :=
        Finset.single_le_sum
          (f := fun j => ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2)
          (fun j _ => sq_nonneg _) hmem
      rw [e1, e2, e3, hWsum]; linarith
    have hRsq_nn : 0 ≤ ‖iteratedCovGrad (I := I) g₀ 0 (2 + 2) i₀
        (iteratedCovGrad (I := I) g₀ 0 2 2 P)‖ ^ 2 := sq_nonneg _
    have hmax_nn : 0 ≤ max Lam (max (Cgn i₀) 1) :=
      le_trans hLam_nn (le_max_left _ _)
    have hmax1 : (1 : ℝ) ≤ max Lam (max (Cgn i₀) 1) :=
      le_trans (le_max_right (Cgn i₀) 1) (le_max_right Lam _)
    have hmax_le : max Lam (max (Cgn i₀) 1) ≤ MBv := by
      apply max_le hMBv_Lam
      apply max_le (hMBv_Cgn i₀ (by omega)) hMBv1
    have hlowcard_le : low.card ≤ i + 2 :=
      le_trans (Finset.card_filter_le _ _) (le_trans (by simp) hn)
    have hLampow_nn : 0 ≤ Lam ^ (2 * low.card) := pow_nonneg hLam_nn _
    have hsplit : ∀ x : M, F x =
        (∏ m ∈ high, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) *
        (∏ m ∈ low, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) := by
      intro x
      rw [hF, hhigh, hlow]
      exact (Finset.prod_filter_mul_prod_filter_not Finset.univ (fun m => 3 ≤ e m)
        (fun m => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))).symm
    have hFbnd : ∀ x : M, F x ≤ Lam ^ (2 * low.card) *
        (∏ m ∈ high, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) := by
      intro x
      rw [hsplit x]
      have hhnn : 0 ≤ ∏ m ∈ high, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x) :=
        Finset.prod_nonneg (fun m _ => hfac_nn m x)
      calc (∏ m ∈ high, _) * (∏ m ∈ low, _)
          ≤ (∏ m ∈ high, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) * Lam ^ (2 * low.card) :=
            mul_le_mul_of_nonneg_left (hlowbnd x) hhnn
        _ = Lam ^ (2 * low.card) * (∏ m ∈ high, _) := by ring
    have hfinal : (∫ x, F x ∂μ) ≤ Lam ^ (2 * low.card) *
        ((i₀ : ℝ) * (max Lam (max (Cgn i₀) 1)) ^ (7 * i₀) *
          ‖iteratedCovGrad (I := I) g₀ 0 (2 + 2) i₀
            (iteratedCovGrad (I := I) g₀ 0 2 2 P)‖ ^ 2) := by
      calc (∫ x, F x ∂μ)
          ≤ ∫ x, Lam ^ (2 * low.card) *
              (∏ m ∈ high, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x)) ∂μ :=
            MeasureTheory.integral_mono hF_int (hhigh_int.const_mul _) hFbnd
        _ = Lam ^ (2 * low.card) * ∫ x, ∏ m ∈ high,
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x) ∂μ :=
            MeasureTheory.integral_const_mul _ _
        _ ≤ Lam ^ (2 * low.card) *
              ((i₀ : ℝ) * (max Lam (max (Cgn i₀) 1)) ^ (7 * i₀) *
                ‖iteratedCovGrad (I := I) g₀ 0 (2 + 2) i₀
                  (iteratedCovGrad (I := I) g₀ 0 2 2 P)‖ ^ 2) :=
            mul_le_mul_of_nonneg_left hhigh_le hLampow_nn
    refine le_trans hfinal ?_
    have hLL : Lam ^ (2 * low.card) ≤ MBv ^ (2 * (i + 2)) :=
      le_trans (pow_le_pow_left₀ hLam_nn hMBv_Lam _)
        (pow_le_pow_right₀ hMBv1 (by omega))
    have hMM : (max Lam (max (Cgn i₀) 1)) ^ (7 * i₀) ≤ MBv ^ (7 * (i + 2)) :=
      le_trans (pow_le_pow_left₀ hmax_nn hmax_le _)
        (pow_le_pow_right₀ hMBv1 (by omega))
    have hi₀R : (i₀ : ℝ) ≤ (i : ℝ) + 2 := by
      have : i₀ ≤ i + 2 := by omega
      exact_mod_cast le_trans this (by norm_num)
    have hpowsum : MBv ^ (2 * (i + 2)) * MBv ^ (7 * (i + 2)) = MBv ^ (9 * (i + 2)) := by
      rw [← pow_add]; congr 1; ring
    calc Lam ^ (2 * low.card) *
          ((i₀ : ℝ) * (max Lam (max (Cgn i₀) 1)) ^ (7 * i₀) *
            ‖iteratedCovGrad (I := I) g₀ 0 (2 + 2) i₀
              (iteratedCovGrad (I := I) g₀ 0 2 2 P)‖ ^ 2)
        ≤ MBv ^ (2 * (i + 2)) *
            (((i : ℝ) + 2) * MBv ^ (7 * (i + 2)) * Wsum) := by
          apply mul_le_mul hLL _ (by positivity) (by positivity)
          apply mul_le_mul (mul_le_mul hi₀R hMM (by positivity) (by positivity)) hRsq_le
            hRsq_nn (by positivity)
      _ = ((i : ℝ) + 2) * (MBv ^ (2 * (i + 2)) * MBv ^ (7 * (i + 2))) * Wsum := by ring
      _ = ((i : ℝ) + 2) * MBv ^ (9 * (i + 2)) * Wsum := by rw [hpowsum]
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    have hallow : ∀ m : Fin n, e m ≤ 2 := by
      intro m
      by_contra h
      have hm3 : 3 ≤ e m := by omega
      have hmem : m ∈ high := (hmem_high m).mpr hm3
      rw [hne] at hmem
      exact absurd hmem (by simp)
    have hFbnd : ∀ x : M, F x ≤ Lam ^ (2 * n) := by
      intro x
      rw [hF]
      calc (∏ m : Fin n, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (e m) P).toSection x))
          ≤ ∏ _m : Fin n, Lam ^ 2 := by
            apply Finset.prod_le_prod (fun m _ => hfac_nn m x)
            intro m _; exact hΛsup_low (e m) (hallow m) x
        _ = Lam ^ (2 * n) := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
            ← pow_mul, Nat.mul_comm]
    have hvol_int : (∫ x, F x ∂μ) ≤ Lam ^ (2 * n) *
        ((riemannianVolumeMeasure (I := I) (M := M) g₀) Set.univ).toReal := by
      calc (∫ x, F x ∂μ)
          ≤ ∫ _x, Lam ^ (2 * n) ∂μ :=
            MeasureTheory.integral_mono hF_int (MeasureTheory.integrable_const _) hFbnd
        _ = Lam ^ (2 * n) * ((riemannianVolumeMeasure (I := I) (M := M) g₀) Set.univ).toReal := by
            rw [MeasureTheory.integral_const, smul_eq_mul, hμ,
              MeasureTheory.measureReal_def, mul_comm]
    refine le_trans hvol_int ?_
    have hLampow_nn : 0 ≤ Lam ^ (2 * n) := pow_nonneg hLam_nn _
    have hLn : Lam ^ (2 * n) ≤ MBv ^ (2 * (i + 2)) :=
      le_trans (pow_le_pow_left₀ hLam_nn hMBv_Lam _)
        (pow_le_pow_right₀ hMBv1 (by omega))
    have hbase : Lam ^ (2 * n) *
        ((riemannianVolumeMeasure (I := I) (M := M) g₀) Set.univ).toReal ≤
        MBv ^ (2 * (i + 2)) * MBv := by
      apply mul_le_mul hLn hMBv_vol ENNReal.toReal_nonneg (pow_nonneg hMBv_nn _)
    have hpow_le : MBv ^ (2 * (i + 2)) * MBv ≤ MBv ^ (9 * (i + 2)) := by
      rw [← pow_succ]
      exact pow_le_pow_right₀ hMBv1 (by omega)
    have hfinal2 : Lam ^ (2 * n) *
        ((riemannianVolumeMeasure (I := I) (M := M) g₀) Set.univ).toReal ≤
        MBv ^ (9 * (i + 2)) := le_trans hbase hpow_le
    calc Lam ^ (2 * n) *
          ((riemannianVolumeMeasure (I := I) (M := M) g₀) Set.univ).toReal
        ≤ MBv ^ (9 * (i + 2)) := hfinal2
      _ = 1 * (MBv ^ (9 * (i + 2)) * 1) := by ring
      _ ≤ ((i : ℝ) + 2) * (MBv ^ (9 * (i + 2)) * Wsum) := by
          apply mul_le_mul (by have := Nat.cast_nonneg (α := ℝ) i; linarith) _
            (by positivity) (by positivity)
          apply mul_le_mul_of_nonneg_left hWsum1 (by positivity)
      _ = (((i : ℝ) + 2) * MBv ^ (9 * (i + 2))) * Wsum := by ring

set_option linter.unusedVariables false in
theorem boundedFactorGrid_cappedTopLayer_integral_flat
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R) :
    ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
      ∀ (P : SmoothCcTensor g₀ 0 2),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ (i : ℕ),
          MeasureTheory.Integrable
              (fun x => Combinatorics.boundedFactorGrid
                (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 2))
              (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
            (∫ x, Combinatorics.boundedFactorGrid
                  (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 2)
                ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
              Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  classical
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g₀
  obtain ⟨Cemb, hCemb_nn, hCemb⟩ :=
    DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.deTurckSmoothRemainderDiff_supercritical_pointwise_jet_le_fixedWindow
      (I := I) (M := M) g₀ a ha_super
  set Lam : ℝ := Cemb * Real.sqrt ((a + 1 + 1 : ℕ) : ℝ) * R with hLam
  have hLam_nn : 0 ≤ Lam := by rw [hLam]; positivity
  set Cgn : ℕ → ℝ := fun k =>
    if h : 1 ≤ k then
      (DifferentialGeometry.Analysis.Sobolev.Tensor.exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
        (I := I) (M := M) g₀ 0 (2 + 2) k h).choose
    else 0 with hCgn
  have hCgn_nn : ∀ k, 0 ≤ Cgn k := by
    intro k
    simp only [hCgn]
    split_ifs with h
    · exact (DifferentialGeometry.Analysis.Sobolev.Tensor.exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
        (I := I) (M := M) g₀ 0 (2 + 2) k h).choose_spec.1
    · exact le_refl 0
  set vol : ℝ := ((riemannianVolumeMeasure (I := I) (M := M) g₀) Set.univ).toReal with hvol
  have hvol_nn : 0 ≤ vol := ENNReal.toReal_nonneg
  set MB : ℕ → ℝ := fun i => 1 + vol + Lam + ∑ k ∈ Finset.range (i + 1), Cgn k with hMBdef
  have hsumCgn_nn : ∀ i, 0 ≤ ∑ k ∈ Finset.range (i + 1), Cgn k :=
    fun i => Finset.sum_nonneg (fun k _ => hCgn_nn k)
  have hMB1 : ∀ i, 1 ≤ MB i := by
    intro i; rw [hMBdef]
    have := hsumCgn_nn i; linarith
  have hMB_nn : ∀ i, 0 ≤ MB i := fun i => le_trans zero_le_one (hMB1 i)
  have hMB_Lam : ∀ i, Lam ≤ MB i := by
    intro i; rw [hMBdef]; have := hsumCgn_nn i; linarith
  have hMB_vol : ∀ i, vol ≤ MB i := by
    intro i; rw [hMBdef]; have := hsumCgn_nn i; linarith
  have hMB_Cgn : ∀ i k, k ≤ i → Cgn k ≤ MB i := by
    intro i k hk
    rw [hMBdef]
    have hmem : k ∈ Finset.range (i + 1) := Finset.mem_range.mpr (by omega)
    have hle : Cgn k ≤ ∑ k' ∈ Finset.range (i + 1), Cgn k' :=
      Finset.single_le_sum (fun k' _ => hCgn_nn k') hmem
    linarith
  set gcount : ℕ → ℝ := fun i =>
    ∑ n ∈ Finset.range (i + 2 + 1), ((Finset.Nat.antidiagonalTuple n (i + 2)).card : ℝ)
    with hgcount
  have hgcount_nn : ∀ i, 0 ≤ gcount i :=
    fun i => Finset.sum_nonneg (fun n _ => Nat.cast_nonneg _)
  refine ⟨fun i => gcount i * (((i : ℝ) + 2) * MB i ^ (9 * (i + 2))),
    fun i => mul_nonneg (hgcount_nn i)
      (mul_nonneg (by positivity) (pow_nonneg (hMB_nn i) _)), ?_⟩
  intro P hPball i
  have hΛsup_low : ∀ (m : ℕ), m ≤ 2 → ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m) x
        ((iteratedCovGrad (I := I) g₀ 0 2 m P).toSection x) ≤ Lam ^ 2 := by
    intro m hm x
    have hsum_le : ∑ j ∈ Finset.range (a + 1 + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 ≤ ((a + 1 + 1 : ℕ) : ℝ) * R ^ 2 := by
      calc ∑ j ∈ Finset.range (a + 1 + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2
          ≤ ∑ j ∈ Finset.range (a + 1 + 1), R ^ 2 := by
            apply Finset.sum_le_sum
            intro j hj
            have hjle : j ≤ a + 2 := by have := Finset.mem_range.mp hj; omega
            nlinarith [norm_nonneg (iteratedCovGrad (I := I) g₀ 0 2 j P), hPball j hjle, hR]
        _ = ((a + 1 + 1 : ℕ) : ℝ) * R ^ 2 := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hsingle : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m) x
          ((iteratedCovGrad (I := I) g₀ 0 2 m P).toSection x) ≤
        ∑ m' ∈ Finset.range 3, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m') x
          ((iteratedCovGrad (I := I) g₀ 0 2 m' P).toSection x) := by
      have hmmem : m ∈ Finset.range 3 := Finset.mem_range.mpr (by omega)
      exact Finset.single_le_sum
        (f := fun m' => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m') x
          ((iteratedCovGrad (I := I) g₀ 0 2 m' P).toSection x))
        (fun m' _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + m') x _) hmmem
    have hLam2 : Lam ^ 2 = Cemb ^ 2 * ((a + 1 + 1 : ℕ) : ℝ) * R ^ 2 := by
      rw [hLam, mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
    have hchain : ∑ m' ∈ Finset.range 3, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m') x
          ((iteratedCovGrad (I := I) g₀ 0 2 m' P).toSection x) ≤ Lam ^ 2 := by
      refine le_trans (hCemb P x) ?_
      rw [hLam2]
      calc Cemb ^ 2 * ∑ j ∈ Finset.range (a + 1 + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2
          ≤ Cemb ^ 2 * (((a + 1 + 1 : ℕ) : ℝ) * R ^ 2) :=
            mul_le_mul_of_nonneg_left hsum_le (by positivity)
        _ = Cemb ^ 2 * ((a + 1 + 1 : ℕ) : ℝ) * R ^ 2 := by ring
    exact le_trans hsingle hchain
  have hΛsup_v2 : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 2) x
        ((iteratedCovGrad (I := I) g₀ 0 2 2 P).toSection x) ≤ Lam ^ 2 :=
    hΛsup_low 2 (le_refl 2)
  have hGNv : ∀ (i₀ : ℕ), 1 ≤ i₀ → ∀ (j : ℕ), 0 < j → j < i₀ →
      (∫ x, (riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + 2) + j) x
              ((iteratedCovGrad (I := I) g₀ 0 (2 + 2) j
                (iteratedCovGrad (I := I) g₀ 0 2 2 P)).toSection x)) ^ ((i₀ : ℝ) / (j : ℝ))
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ^ ((j : ℝ) / (i₀ : ℝ)) ≤
        Cgn i₀ * Lam ^ (2 * (1 - (j : ℝ) / (i₀ : ℝ))) *
          ‖iteratedCovGrad (I := I) g₀ 0 (2 + 2) i₀
            (iteratedCovGrad (I := I) g₀ 0 2 2 P)‖ ^ (2 * (j : ℝ) / (i₀ : ℝ)) := by
    intro i₀ hi₀ j hj0 hji
    have hGNspec := (DifferentialGeometry.Analysis.Sobolev.Tensor.exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
      (I := I) (M := M) g₀ 0 (2 + 2) i₀ hi₀).choose_spec.2
    have hb := hGNspec (iteratedCovGrad (I := I) g₀ 0 2 2 P) Lam hLam_nn hΛsup_v2 j hj0 hji
    have hchoose : (DifferentialGeometry.Analysis.Sobolev.Tensor.exists_gagliardoNirenberg_iteratedCovGrad_lpFiberNorm_le_rs
        (I := I) (M := M) g₀ 0 (2 + 2) i₀ hi₀).choose = Cgn i₀ := by
      rw [hCgn]; simp only [dif_pos hi₀]
    rw [hchoose] at hb
    have hnorm : Integral.L2.tensorL2Norm (I := I) g₀ 0 ((2 + 2) + i₀)
        (iteratedCovGrad (I := I) g₀ 0 (2 + 2) i₀
          (iteratedCovGrad (I := I) g₀ 0 2 2 P)).toFun =
        ‖iteratedCovGrad (I := I) g₀ 0 (2 + 2) i₀ (iteratedCovGrad (I := I) g₀ 0 2 2 P)‖ :=
      (SmoothCcTensor.norm_def (iteratedCovGrad (I := I) g₀ 0 (2 + 2) i₀
        (iteratedCovGrad (I := I) g₀ 0 2 2 P))).symm
    rw [hnorm] at hb
    exact hb
  set b : M → ℕ → ℝ := fun x l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
    ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x) with hb_def
  have hb : ∀ (x : M) (l : ℕ), 0 ≤ b x l :=
    fun x l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
  have hcont : ∀ l : ℕ, Continuous (fun x => b x l) := by
    intro l
    have hc := Integral.L2.SmoothCcTensor.continuous_inner_self (I := I) (M := M)
      (iteratedCovGrad (I := I) g₀ 0 2 l P)
    refine hc.congr (fun x => ?_)
    change tensorInnerPointwise (I := I) (M := M) g₀ 0 (2 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 2 l P).toFun x)
        ((iteratedCovGrad (I := I) g₀ 0 2 l P).toFun x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)
    rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g₀ 0 (2 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x),
      ← Integral.L2.SmoothCcTensor.toFun_apply (I := I) (M := M)
        (iteratedCovGrad (I := I) g₀ 0 2 l P) x]
  have hcell_cont : ∀ (n : ℕ) (e : Fin n → ℕ),
      Continuous (fun x => ∏ m : Fin n, b x (e m)) := by
    intro n e
    exact continuous_finset_prod _ (fun m _ => hcont (e m))
  have hcell_int : ∀ (n : ℕ) (e : Fin n → ℕ),
      MeasureTheory.Integrable (fun x => ∏ m : Fin n, b x (e m))
        (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    fun n e => (hcell_cont n e).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hgrid_cont : Continuous (fun x =>
      Combinatorics.boundedFactorGrid (b x) (i + 1) (i + 2)) := by
    simp only [Combinatorics.boundedFactorGrid]
    refine continuous_finset_sum _ (fun n _ => ?_)
    refine continuous_finset_sum _ (fun e _ => ?_)
    exact continuous_finset_prod _ (fun m _ => hcont (e m))
  have hgrid_int : MeasureTheory.Integrable
      (fun x => Combinatorics.boundedFactorGrid (b x) (i + 1) (i + 2))
      (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    hgrid_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  refine ⟨hgrid_int, ?_⟩
  have hPT : ∀ n ∈ Finset.range (i + 2 + 1),
      ∀ e ∈ (Finset.Nat.antidiagonalTuple n (i + 2)).filter (fun e => ∀ m, e m ≤ i + 1),
      (∫ x, ∏ m : Fin n, b x (e m) ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
        (((i : ℝ) + 2) * MB i ^ (9 * (i + 2))) *
          (1 + ∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
    intro n hn e he
    have hnle : n ≤ i + 2 := by have := Finset.mem_range.mp hn; omega
    have he_sum : ∑ m, e m = i + 2 :=
      Finset.Nat.mem_antidiagonalTuple.mp (Finset.mem_filter.mp he).1
    have he_cap : ∀ m, e m ≤ i + 1 := (Finset.mem_filter.mp he).2
    exact cappedTopLayerCell_integral_le (I := I) (M := M) g₀ P hLam_nn hΛsup_low
      Cgn hCgn_nn hGNv i n e hnle he_sum he_cap (MB i) (hMB1 i) (hMB_Lam i)
      (hMB_vol i) (fun k hk => hMB_Cgn i k hk)
  have hgrid_eq : (∫ x, Combinatorics.boundedFactorGrid (b x) (i + 1) (i + 2)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) =
      ∑ n ∈ Finset.range (i + 2 + 1),
        ∑ e ∈ (Finset.Nat.antidiagonalTuple n (i + 2)).filter (fun e => ∀ m, e m ≤ i + 1),
          ∫ x, ∏ m : Fin n, b x (e m) ∂(riemannianVolumeMeasure (I := I) (M := M) g₀) := by
    have h1 : (fun x => Combinatorics.boundedFactorGrid (b x) (i + 1) (i + 2)) =
        (fun x => ∑ n ∈ Finset.range (i + 2 + 1),
          ∑ e ∈ (Finset.Nat.antidiagonalTuple n (i + 2)).filter (fun e => ∀ m, e m ≤ i + 1),
            ∏ m : Fin n, b x (e m)) := rfl
    rw [h1, MeasureTheory.integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro n _
      rw [MeasureTheory.integral_finset_sum]
      intro e _; exact hcell_int n e
    · intro n _
      apply MeasureTheory.integrable_finset_sum
      intro e _; exact hcell_int n e
  rw [hgrid_eq]
  have hKcell_nn : (0 : ℝ) ≤ ((i : ℝ) + 2) * MB i ^ (9 * (i + 2)) :=
    mul_nonneg (by positivity) (pow_nonneg (hMB_nn i) _)
  have hWsum_nn : (0 : ℝ) ≤ 1 + ∑ j ∈ Finset.range (i + 2),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 := by
    have := Finset.sum_nonneg (fun j (_ : j ∈ Finset.range (i + 2)) =>
      sq_nonneg (‖iteratedCovGrad (I := I) g₀ 0 2 j P‖))
    linarith
  calc ∑ n ∈ Finset.range (i + 2 + 1),
        ∑ e ∈ (Finset.Nat.antidiagonalTuple n (i + 2)).filter (fun e => ∀ m, e m ≤ i + 1),
          ∫ x, ∏ m : Fin n, b x (e m) ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)
      ≤ ∑ n ∈ Finset.range (i + 2 + 1),
          ∑ e ∈ (Finset.Nat.antidiagonalTuple n (i + 2)).filter (fun e => ∀ m, e m ≤ i + 1),
            (((i : ℝ) + 2) * MB i ^ (9 * (i + 2))) *
              (1 + ∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
        apply Finset.sum_le_sum; intro n hn
        apply Finset.sum_le_sum; intro e he
        exact hPT n hn e he
    _ = (∑ n ∈ Finset.range (i + 2 + 1),
          (((Finset.Nat.antidiagonalTuple n (i + 2)).filter (fun e => ∀ m, e m ≤ i + 1)).card : ℝ)) *
          ((((i : ℝ) + 2) * MB i ^ (9 * (i + 2))) *
            (1 + ∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2)) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro n _; rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ gcount i *
          ((((i : ℝ) + 2) * MB i ^ (9 * (i + 2))) *
            (1 + ∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2)) := by
        apply mul_le_mul_of_nonneg_right _ (mul_nonneg hKcell_nn hWsum_nn)
        rw [hgcount]
        apply Finset.sum_le_sum
        intro n _
        exact_mod_cast Finset.card_filter_le _ _
    _ = gcount i * (((i : ℝ) + 2) * MB i ^ (9 * (i + 2))) *
          (1 + ∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
        ring

set_option linter.unusedVariables false in
theorem boundedFactorGridWindow_integral_ballUniform_flat_allOrders
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R) :
    ∃ Kflat : ℕ → ℝ, (∀ i, 0 ≤ Kflat i) ∧
      ∀ (P : SmoothCcTensor g₀ 0 2),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ (i : ℕ),
          MeasureTheory.Integrable
              (fun x => Combinatorics.boundedFactorGridWindow
                (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3))
              (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
            (∫ x, Combinatorics.boundedFactorGridWindow
                  (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3)
                ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
              Kflat i * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  classical
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace M := borel M
  haveI : BorelSpace M := ⟨rfl⟩
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g₀
  obtain ⟨Kt, hKt_nn, hKt⟩ := antidiagonalTupleGrid_integral_ballUniform_tameWindow
    (I := I) (M := M) g₀ a ha_super hR
  obtain ⟨Kc, hKc_nn, hKc⟩ := boundedFactorGrid_cappedTopLayer_integral_flat
    (I := I) (M := M) g₀ a ha_super hR
  refine ⟨fun i => (∑ k ∈ Finset.range (i + 2), Kt k) + Kc i,
    fun i => add_nonneg (Finset.sum_nonneg fun k _ => hKt_nn k) (hKc_nn i), ?_⟩
  intro P hPball i
  set b : M → ℕ → ℝ := fun x l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
    ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x) with hb_def
  have hb : ∀ (x : M) (l : ℕ), 0 ≤ b x l :=
    fun x l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
  have hcont : ∀ l : ℕ, Continuous (fun x => b x l) := by
    intro l
    have hc := Integral.L2.SmoothCcTensor.continuous_inner_self (I := I) (M := M)
      (iteratedCovGrad (I := I) g₀ 0 2 l P)
    refine hc.congr (fun x => ?_)
    change tensorInnerPointwise (I := I) (M := M) g₀ 0 (2 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 2 l P).toFun x)
        ((iteratedCovGrad (I := I) g₀ 0 2 l P).toFun x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)
    rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g₀ 0 (2 + l) x
        ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x),
      ← Integral.L2.SmoothCcTensor.toFun_apply (I := I) (M := M)
        (iteratedCovGrad (I := I) g₀ 0 2 l P) x]
  have hbfg_cont : ∀ (K k : ℕ),
      Continuous (fun x => Combinatorics.boundedFactorGrid (b x) K k) := by
    intro K k
    simp only [Combinatorics.boundedFactorGrid]
    refine continuous_finset_sum _ (fun n _ => ?_)
    refine continuous_finset_sum _ (fun e _ => ?_)
    exact continuous_finset_prod _ (fun m _ => hcont (e m))
  have hbfg_int : ∀ (K k : ℕ), MeasureTheory.Integrable
      (fun x => Combinatorics.boundedFactorGrid (b x) K k)
      (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    fun K k => (hbfg_cont K k).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hWcont : Continuous (fun x =>
      Combinatorics.boundedFactorGridWindow (b x) (i + 1) (i + 3)) := by
    simp only [Combinatorics.boundedFactorGridWindow]
    exact continuous_finset_sum _ (fun k _ => hbfg_cont (i + 1) k)
  have hWint : MeasureTheory.Integrable
      (fun x => Combinatorics.boundedFactorGridWindow (b x) (i + 1) (i + 3))
      (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    hWcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  refine ⟨hWint, ?_⟩
  have hInt_eq : (∫ x, Combinatorics.boundedFactorGridWindow (b x) (i + 1) (i + 3)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) =
      (∑ k ∈ Finset.range (i + 2), ∫ x, Combinatorics.boundedFactorGrid (b x) (i + 1) k
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) +
        ∫ x, Combinatorics.boundedFactorGrid (b x) (i + 1) (i + 2)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀) := by
    have hEq : (fun x => Combinatorics.boundedFactorGridWindow (b x) (i + 1) (i + 3)) =
        (fun x => ∑ k ∈ Finset.range (i + 3),
          Combinatorics.boundedFactorGrid (b x) (i + 1) k) := rfl
    rw [hEq, MeasureTheory.integral_finset_sum _ (fun k _ => hbfg_int (i + 1) k),
      Finset.sum_range_succ]
  rw [hInt_eq]
  have hlayer_le : ∀ k ∈ Finset.range (i + 2),
      (∫ x, Combinatorics.boundedFactorGrid (b x) (i + 1) k
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
        Kt k * (1 + ∑ j ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
    intro k hk
    rw [Finset.mem_range] at hk
    have hAint : MeasureTheory.Integrable
        (fun x => Combinatorics.antidiagonalTupleGrid (b x) k)
        (riemannianVolumeMeasure (I := I) (M := M) g₀) := (hKt P hPball k).1
    have hAbound : (∫ x, Combinatorics.antidiagonalTupleGrid (b x) k
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
        Kt k * (1 + ∑ j ∈ Finset.range (k + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := (hKt P hPball k).2
    calc (∫ x, Combinatorics.boundedFactorGrid (b x) (i + 1) k
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀))
        ≤ ∫ x, Combinatorics.antidiagonalTupleGrid (b x) k
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀) :=
          MeasureTheory.integral_mono (hbfg_int (i + 1) k) hAint
            (fun x => Combinatorics.boundedFactorGrid_le_antidiagonalTupleGrid
              (b x) (hb x) (i + 1) k)
      _ ≤ Kt k * (1 + ∑ j ∈ Finset.range (k + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := hAbound
      _ ≤ Kt k * (1 + ∑ j ∈ Finset.range (i + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
          refine mul_le_mul_of_nonneg_left ?_ (hKt_nn k)
          have hsub : (∑ j ∈ Finset.range (k + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤
              ∑ j ∈ Finset.range (i + 2), ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 := by
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun j _ _ => sq_nonneg _)
            intro m hm
            rw [Finset.mem_range] at hm ⊢
            omega
          linarith
  have hleaf := (hKc P hPball i).2
  calc (∑ k ∈ Finset.range (i + 2), ∫ x, Combinatorics.boundedFactorGrid (b x) (i + 1) k
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) +
        ∫ x, Combinatorics.boundedFactorGrid (b x) (i + 1) (i + 2)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)
      ≤ (∑ k ∈ Finset.range (i + 2), Kt k * (1 + ∑ j ∈ Finset.range (i + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2)) +
          Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) :=
        add_le_add (Finset.sum_le_sum hlayer_le) hleaf
    _ = ((∑ k ∈ Finset.range (i + 2), Kt k) + Kc i) * (1 + ∑ j ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
        rw [← Finset.sum_mul, ← add_mul]

set_option linter.unusedVariables false in
theorem boundedFactorGridWindow_integral_ballUniform_tameWindow_allOrders
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R) :
    ∃ Kflat : ℕ → ℝ, (∀ i, 0 ≤ Kflat i) ∧ ∃ Kleak : ℝ, 0 ≤ Kleak ∧
      ∀ (P : SmoothCcTensor g₀ 0 2),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ (i : ℕ),
          MeasureTheory.Integrable
              (fun x => Combinatorics.boundedFactorGridWindow
                (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3))
              (riemannianVolumeMeasure (I := I) (M := M) g₀) ∧
            (∫ x, Combinatorics.boundedFactorGridWindow
                  (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3)
                ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) ≤
              Kflat i * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) +
                Kleak * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P‖ ^ 2 := by
  obtain ⟨Kflat, hKflat_nn, hK⟩ :=
    boundedFactorGridWindow_integral_ballUniform_flat_allOrders
      (I := I) (M := M) g₀ a ha_super hR
  refine ⟨Kflat, hKflat_nn, 0, le_refl 0, ?_⟩
  intro P hPball i
  obtain ⟨hint, hbound⟩ := hK P hPball i
  refine ⟨hint, ?_⟩
  rw [show (0 : ℝ) * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P‖ ^ 2 = 0 by ring, add_zero]
  exact hbound

set_option linter.unusedVariables false in
theorem ricciArmOrder0BaseCoeff_perOrder_l2_topSeparated_generic
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Ktop : ℝ, 0 ≤ Ktop ∧ ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a →
          ∃ Hd : SmoothCcTensor g₀ 2 (2 + i),
            (∀ x : M,
              riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x (Hd.toSection x) ≤
                Ktop * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x)) ∧
            ‖Hd‖ ^ 2 ≤ Ktop * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P‖ ^ 2 ∧
            ‖iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁) - Hd‖ ^ 2 ≤
              Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  classical
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g₀
  obtain ⟨KtCr, hKtCr_nn, KcCr, hKcCr_nn, hCr⟩ :=
    rfns_iteratedCovGrad_ricciArmOrder0RiemannCoeff_backgroundDifference_topSeparated_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨KtCu, hKtCu_nn, KcCu, hKcCu_nn, hCu⟩ :=
    rfns_iteratedCovGrad_ricciArmOrder0CurvCoeff_backgroundDifference_topSeparated_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨cbg, hcbg_nn, hcbg⟩ := exists_backgroundJet_rfns_bound (I := I) (M := M) g₀ 2 2
    (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
      ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)
  obtain ⟨KI, hKI_nn, hKI⟩ := boundedFactorGridWindow_integral_ballUniform_tameWindow
    (I := I) (M := M) g₀ a ha_super hR
  refine ⟨2 * KtCr + 2 * KtCu, by linarith, ?_⟩
  refine ⟨fun i => (2 * cbg i + 4 * KcCr i + 4 * KcCu i) * KI i,
    fun i => mul_nonneg
      (by have := hcbg_nn i; have := hKcCr_nn i; have := hKcCu_nn i; linarith)
      (hKI_nn i), ?_⟩
  intro g₁ P δ hδ_le hδ htie hPball i hia
  by_cases hM : Nonempty M
  · obtain ⟨x₀⟩ := hM
    have hδ0 : 0 ≤ δ := by
      obtain ⟨v, hv⟩ : ∃ v : TangentSpace I x₀, v ≠ 0 := by
        haveI : Nontrivial (TangentSpace I x₀) := by
          have hfr : 0 < Module.finrank ℝ (TangentSpace I x₀) := by
            have heq : Module.finrank ℝ (TangentSpace I x₀) = Module.finrank ℝ E := rfl
            rw [heq]; exact Nat.pos_of_ne_zero (NeZero.ne _)
          exact Module.nontrivial_of_finrank_pos hfr
        exact exists_ne 0
      have hpos : 0 < g₀.inner x₀ v v := g₀.pos x₀ v hv
      have hbound := hδ x₀ v v
      have hsqrt_pos : 0 < Real.sqrt (g₀.inner x₀ v v) := Real.sqrt_pos.mpr hpos
      have habs_nn : 0 ≤ |ccTensorBilinSymm (I := I) g₀ P x₀ v v| := abs_nonneg _
      by_contra hδc
      have hδc' : δ < 0 := lt_of_not_ge hδc
      have hrhs_neg : δ * Real.sqrt (g₀.inner x₀ v v) * Real.sqrt (g₀.inner x₀ v v) < 0 := by
        have h1 : δ * Real.sqrt (g₀.inner x₀ v v) < 0 :=
          mul_neg_of_neg_of_pos hδc' hsqrt_pos
        exact mul_neg_of_neg_of_pos h1 hsqrt_pos
      linarith [le_trans habs_nn hbound]
    obtain ⟨HdCr, hCr_head, hCr_res⟩ := hCr g₁ P htie hδ_le hδ0 hδ i
    obtain ⟨HdCu, hCu_head, hCu_res⟩ := hCu g₁ P htie hδ_le hδ0 hδ i
    refine ⟨HdCr - HdCu, ?_, ?_, ?_⟩
    · intro x
      rw [show ((HdCr - HdCu).toSection x) = HdCr.toSection x - HdCu.toSection x from by
        rw [SmoothCcTensor.toSection_sub]; rfl]
      refine le_trans (tsRfns_sub_le (I := I) (M := M) g₀ 2 (2 + i) x _ _) ?_
      have h1 := hCr_head x
      have h2 := hCu_head x
      calc 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x (HdCr.toSection x) +
          2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x (HdCu.toSection x)
          ≤ 2 * (KtCr * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x)) +
            2 * (KtCu * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x)) :=
            add_le_add (mul_le_mul_of_nonneg_left h1 (by norm_num))
              (mul_le_mul_of_nonneg_left h2 (by norm_num))
        _ = (2 * KtCr + 2 * KtCu) *
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x) := by ring
    · have hpt : ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
              ((HdCr - HdCu).toSection x) ≤
            (2 * KtCr + 2 * KtCu) *
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x) := by
        intro x
        rw [show ((HdCr - HdCu).toSection x) = HdCr.toSection x - HdCu.toSection x from by
          rw [SmoothCcTensor.toSection_sub]; rfl]
        refine le_trans (tsRfns_sub_le (I := I) (M := M) g₀ 2 (2 + i) x _ _) ?_
        have h1 := hCr_head x
        have h2 := hCu_head x
        calc 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
              (HdCr.toSection x) +
            2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x (HdCu.toSection x)
            ≤ 2 * (KtCr * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x)) +
              2 * (KtCu * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x)) :=
              add_le_add (mul_le_mul_of_nonneg_left h1 (by norm_num))
                (mul_le_mul_of_nonneg_left h2 (by norm_num))
          _ = (2 * KtCr + 2 * KtCu) *
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x) := by ring
      have hF_int : MeasureTheory.Integrable
          (fun x => (2 * KtCr + 2 * KtCu) *
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x))
          (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
        (integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 0 (2 + (i + 2))
          (iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P)).const_mul _
      have key := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M)
        g₀ 2 (2 + i) (HdCr - HdCu) _ hF_int hpt
      refine le_trans key ?_
      rw [MeasureTheory.integral_const_mul]
      rw [show (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) =
          ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P‖ ^ 2 from by
        rw [SmoothCcTensor.norm_def (I := I) (M := M)
            (iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P),
          tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M)
            g₀ 0 (2 + (i + 2)) (iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P)]]
    · have harm0 : ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
          ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ =
          (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
            ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) +
          ((ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
              ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) -
            (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
              ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)) := by abel
      have hdiff : iteratedCovGrad (I := I) g₀ 2 2 i
            (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
              ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁) - (HdCr - HdCu) =
          iteratedCovGrad (I := I) g₀ 2 2 i
              (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
                ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) +
            ((iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) - HdCr) -
              (iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) - HdCu)) := by
        rw [harm0]
        rw [show iteratedCovGrad (I := I) g₀ 2 2 i
              ((ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
                ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) +
              ((ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) -
                (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀))) =
            iteratedCovGrad (I := I) g₀ 2 2 i
              (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
                ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) +
            (iteratedCovGrad (I := I) g₀ 2 2 i
              (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) -
             iteratedCovGrad (I := I) g₀ 2 2 i
              (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
                ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)) from by
          rw [iteratedCovGrad_add (I := I) g₀ 2 2 i
            (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
              ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)
            ((ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) -
              (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
                ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀))]
          rw [iteratedCovGrad_sub (I := I) g₀ 2 2 i
            (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
              ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀)
            (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
              ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)]]
        abel
      have hpt : ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
              ((iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁) -
                (HdCr - HdCu)).toSection x) ≤
            (2 * cbg i + 4 * KcCr i + 4 * KcCu i) *
              Combinatorics.boundedFactorGridWindow
                (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3) := by
        intro x
        set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
          ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x) with hb_def
        have hb : ∀ l, 0 ≤ b l :=
          fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
        have hW_one : 1 ≤ Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) :=
          Combinatorics.one_le_boundedFactorGridWindow b hb (by omega)
        have hW_nn : 0 ≤ Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) := by
          linarith
        rw [hdiff]
        rw [show ((iteratedCovGrad (I := I) g₀ 2 2 i
              (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
                ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) +
            ((iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) - HdCr) -
              (iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) - HdCu))).toSection x) =
            (iteratedCovGrad (I := I) g₀ 2 2 i
              (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
                ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)).toSection x +
            ((iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) - HdCr) -
              (iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) - HdCu)).toSection x
            from by rw [SmoothCcTensor.toSection_add]; rfl]
        refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 2 (2 + i)
          x _ _) ?_
        have h1 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
                ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)).toSection x) ≤
            cbg i := hcbg i x
        have h2 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            (((iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) - HdCr) -
              (iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) - HdCu)).toSection x) ≤
            2 * (KcCr i * Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3)) +
              2 * (KcCu i * Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3)) := by
          rw [show (((iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) - HdCr) -
              (iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) - HdCu)).toSection x) =
              (iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) - HdCr).toSection x -
              (iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) - HdCu).toSection x
              from by rw [SmoothCcTensor.toSection_sub]; rfl]
          refine le_trans (tsRfns_sub_le (I := I) (M := M) g₀ 2 (2 + i) x _ _) ?_
          exact add_le_add (mul_le_mul_of_nonneg_left (hCr_res x) (by norm_num))
            (mul_le_mul_of_nonneg_left (hCu_res x) (by norm_num))
        calc 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
              ((iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
                  ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)).toSection x) +
            2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
              (((iteratedCovGrad (I := I) g₀ 2 2 i
                  (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                    ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) - HdCr) -
                (iteratedCovGrad (I := I) g₀ 2 2 i
                  (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
                    ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) - HdCu)).toSection x)
            ≤ 2 * cbg i +
              2 * (2 * (KcCr i * Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3)) +
                2 * (KcCu i * Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3))) := by
              refine add_le_add ?_ (mul_le_mul_of_nonneg_left h2 (by norm_num))
              have := mul_le_mul_of_nonneg_left h1 (show (0:ℝ) ≤ 2 by norm_num)
              linarith
          _ ≤ (2 * cbg i + 4 * KcCr i + 4 * KcCu i) *
                Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) := by
              have hc1 : 2 * cbg i ≤ 2 * cbg i *
                  Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) := by
                nlinarith [hcbg_nn i, hW_one]
              nlinarith [hKcCr_nn i, hKcCu_nn i, hW_nn]
      obtain ⟨hint, hbound_int⟩ := hKI P hPball i hia
      have hF_int : MeasureTheory.Integrable
          (fun x => (2 * cbg i + 4 * KcCr i + 4 * KcCu i) *
            Combinatorics.boundedFactorGridWindow
              (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3))
          (riemannianVolumeMeasure (I := I) (M := M) g₀) := hint.const_mul _
      have key := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M)
        g₀ 2 (2 + i)
        (iteratedCovGrad (I := I) g₀ 2 2 i
          (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
            ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁) - (HdCr - HdCu))
        _ hF_int hpt
      refine le_trans key ?_
      rw [MeasureTheory.integral_const_mul]
      calc (2 * cbg i + 4 * KcCr i + 4 * KcCu i) *
            ∫ x, Combinatorics.boundedFactorGridWindow
              (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3)
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)
          ≤ (2 * cbg i + 4 * KcCr i + 4 * KcCu i) *
            (KI i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2)) := by
            refine mul_le_mul_of_nonneg_left hbound_int ?_
            have := hcbg_nn i; have := hKcCr_nn i; have := hKcCu_nn i; linarith
        _ = (2 * cbg i + 4 * KcCr i + 4 * KcCu i) * KI i *
            (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by ring
  · haveI hM' : IsEmpty M := not_nonempty_iff.mp hM
    refine ⟨0, fun x => (IsEmpty.false x).elim, ?_, ?_⟩
    · have hz : ‖(0 : SmoothCcTensor g₀ 2 (2 + i))‖ = 0 := by
        rw [SmoothCcTensor.norm_def, tensorL2Norm_def, tensorL2Inner,
          MeasureTheory.integral_of_isEmpty, Real.sqrt_zero]
      rw [hz]
      have := sq_nonneg ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P‖
      nlinarith [hKtCr_nn, hKtCu_nn]
    · have hz : ‖iteratedCovGrad (I := I) g₀ 2 2 i
          (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
            ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁) -
          (0 : SmoothCcTensor g₀ 2 (2 + i))‖ = 0 := by
        rw [SmoothCcTensor.norm_def, tensorL2Norm_def, tensorL2Inner,
          MeasureTheory.integral_of_isEmpty, Real.sqrt_zero]
      rw [hz]
      have hsum_nn : (0 : ℝ) ≤ ∑ j ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 :=
        Finset.sum_nonneg fun j _ => sq_nonneg _
      have hKc_nn : (0 : ℝ) ≤ (2 * cbg i + 4 * KcCr i + 4 * KcCu i) * KI i :=
        mul_nonneg
          (by have := hcbg_nn i; have := hKcCr_nn i; have := hKcCu_nn i; linarith)
          (hKI_nn i)
      nlinarith

set_option linter.unusedVariables false in
theorem ricciArmOrder0BaseCoeff_perOrder_l2_topSeparated_generic_allOrders
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Ktop : ℝ, 0 ≤ Ktop ∧ ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ P) δ)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ P y v w),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ≤ R) →
        ∀ (i : ℕ),
          ∃ Hd : SmoothCcTensor g₀ 2 (2 + i),
            (∀ x : M,
              riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x (Hd.toSection x) ≤
                Ktop * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x)) ∧
            ‖Hd‖ ^ 2 ≤ Ktop * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P‖ ^ 2 ∧
            ‖iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁) - Hd‖ ^ 2 ≤
              Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by
  classical
  haveI : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g₀
  obtain ⟨KtCr, hKtCr_nn, KcCr, hKcCr_nn, hCr⟩ :=
    rfns_iteratedCovGrad_ricciArmOrder0RiemannCoeff_backgroundDifference_topSeparated_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨KtCu, hKtCu_nn, KcCu, hKcCu_nn, hCu⟩ :=
    rfns_iteratedCovGrad_ricciArmOrder0CurvCoeff_backgroundDifference_topSeparated_le
      (I := I) (M := M) g₀ hδ₀
  obtain ⟨cbg, hcbg_nn, hcbg⟩ := exists_backgroundJet_rfns_bound (I := I) (M := M) g₀ 2 2
    (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
      ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)
  obtain ⟨KI, hKI_nn, hKI⟩ := boundedFactorGridWindow_integral_ballUniform_flat_allOrders
    (I := I) (M := M) g₀ a ha_super hR
  refine ⟨2 * KtCr + 2 * KtCu, by linarith, ?_⟩
  refine ⟨fun i => (2 * cbg i + 4 * KcCr i + 4 * KcCu i) * KI i,
    fun i => mul_nonneg
      (by have := hcbg_nn i; have := hKcCr_nn i; have := hKcCu_nn i; linarith)
      (hKI_nn i), ?_⟩
  intro g₁ P δ hδ_le hδ htie hPball i
  by_cases hM : Nonempty M
  · obtain ⟨x₀⟩ := hM
    have hδ0 : 0 ≤ δ := by
      obtain ⟨v, hv⟩ : ∃ v : TangentSpace I x₀, v ≠ 0 := by
        haveI : Nontrivial (TangentSpace I x₀) := by
          have hfr : 0 < Module.finrank ℝ (TangentSpace I x₀) := by
            have heq : Module.finrank ℝ (TangentSpace I x₀) = Module.finrank ℝ E := rfl
            rw [heq]; exact Nat.pos_of_ne_zero (NeZero.ne _)
          exact Module.nontrivial_of_finrank_pos hfr
        exact exists_ne 0
      have hpos : 0 < g₀.inner x₀ v v := g₀.pos x₀ v hv
      have hbound := hδ x₀ v v
      have hsqrt_pos : 0 < Real.sqrt (g₀.inner x₀ v v) := Real.sqrt_pos.mpr hpos
      have habs_nn : 0 ≤ |ccTensorBilinSymm (I := I) g₀ P x₀ v v| := abs_nonneg _
      by_contra hδc
      have hδc' : δ < 0 := lt_of_not_ge hδc
      have hrhs_neg : δ * Real.sqrt (g₀.inner x₀ v v) * Real.sqrt (g₀.inner x₀ v v) < 0 := by
        have h1 : δ * Real.sqrt (g₀.inner x₀ v v) < 0 :=
          mul_neg_of_neg_of_pos hδc' hsqrt_pos
        exact mul_neg_of_neg_of_pos h1 hsqrt_pos
      linarith [le_trans habs_nn hbound]
    obtain ⟨HdCr, hCr_head, hCr_res⟩ := hCr g₁ P htie hδ_le hδ0 hδ i
    obtain ⟨HdCu, hCu_head, hCu_res⟩ := hCu g₁ P htie hδ_le hδ0 hδ i
    refine ⟨HdCr - HdCu, ?_, ?_, ?_⟩
    · intro x
      rw [show ((HdCr - HdCu).toSection x) = HdCr.toSection x - HdCu.toSection x from by
        rw [SmoothCcTensor.toSection_sub]; rfl]
      refine le_trans (tsRfns_sub_le (I := I) (M := M) g₀ 2 (2 + i) x _ _) ?_
      have h1 := hCr_head x
      have h2 := hCu_head x
      calc 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x (HdCr.toSection x) +
          2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x (HdCu.toSection x)
          ≤ 2 * (KtCr * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x)) +
            2 * (KtCu * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x)) :=
            add_le_add (mul_le_mul_of_nonneg_left h1 (by norm_num))
              (mul_le_mul_of_nonneg_left h2 (by norm_num))
        _ = (2 * KtCr + 2 * KtCu) *
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x) := by ring
    · have hpt : ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
              ((HdCr - HdCu).toSection x) ≤
            (2 * KtCr + 2 * KtCu) *
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x) := by
        intro x
        rw [show ((HdCr - HdCu).toSection x) = HdCr.toSection x - HdCu.toSection x from by
          rw [SmoothCcTensor.toSection_sub]; rfl]
        refine le_trans (tsRfns_sub_le (I := I) (M := M) g₀ 2 (2 + i) x _ _) ?_
        have h1 := hCr_head x
        have h2 := hCu_head x
        calc 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
              (HdCr.toSection x) +
            2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x (HdCu.toSection x)
            ≤ 2 * (KtCr * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x)) +
              2 * (KtCu * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x)) :=
              add_le_add (mul_le_mul_of_nonneg_left h1 (by norm_num))
                (mul_le_mul_of_nonneg_left h2 (by norm_num))
          _ = (2 * KtCr + 2 * KtCu) *
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x) := by ring
      have hF_int : MeasureTheory.Integrable
          (fun x => (2 * KtCr + 2 * KtCu) *
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x))
          (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
        (integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 0 (2 + (i + 2))
          (iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P)).const_mul _
      have key := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M)
        g₀ 2 (2 + i) (HdCr - HdCu) _ hF_int hpt
      refine le_trans key ?_
      rw [MeasureTheory.integral_const_mul]
      rw [show (∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P).toSection x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)) =
          ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P‖ ^ 2 from by
        rw [SmoothCcTensor.norm_def (I := I) (M := M)
            (iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P),
          tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M)
            g₀ 0 (2 + (i + 2)) (iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P)]]
    · have harm0 : ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
          ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ =
          (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
            ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) +
          ((ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
              ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) -
            (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
              ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)) := by abel
      have hdiff : iteratedCovGrad (I := I) g₀ 2 2 i
            (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
              ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁) - (HdCr - HdCu) =
          iteratedCovGrad (I := I) g₀ 2 2 i
              (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
                ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) +
            ((iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) - HdCr) -
              (iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) - HdCu)) := by
        rw [harm0]
        rw [show iteratedCovGrad (I := I) g₀ 2 2 i
              ((ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
                ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) +
              ((ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) -
                (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀))) =
            iteratedCovGrad (I := I) g₀ 2 2 i
              (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
                ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) +
            (iteratedCovGrad (I := I) g₀ 2 2 i
              (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) -
             iteratedCovGrad (I := I) g₀ 2 2 i
              (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
                ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)) from by
          rw [iteratedCovGrad_add (I := I) g₀ 2 2 i
            (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
              ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)
            ((ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) -
              (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
                ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀))]
          rw [iteratedCovGrad_sub (I := I) g₀ 2 2 i
            (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
              ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀)
            (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
              ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)]]
        abel
      have hpt : ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
              ((iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁) -
                (HdCr - HdCu)).toSection x) ≤
            (2 * cbg i + 4 * KcCr i + 4 * KcCu i) *
              Combinatorics.boundedFactorGridWindow
                (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3) := by
        intro x
        set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
          ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x) with hb_def
        have hb : ∀ l, 0 ≤ b l :=
          fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
        have hW_one : 1 ≤ Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) :=
          Combinatorics.one_le_boundedFactorGridWindow b hb (by omega)
        have hW_nn : 0 ≤ Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) := by
          linarith
        rw [hdiff]
        rw [show ((iteratedCovGrad (I := I) g₀ 2 2 i
              (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
                ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) +
            ((iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) - HdCr) -
              (iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) - HdCu))).toSection x) =
            (iteratedCovGrad (I := I) g₀ 2 2 i
              (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
                ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)).toSection x +
            ((iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) - HdCr) -
              (iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) - HdCu)).toSection x
            from by rw [SmoothCcTensor.toSection_add]; rfl]
        refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 2 (2 + i)
          x _ _) ?_
        have h1 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            ((iteratedCovGrad (I := I) g₀ 2 2 i
              (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
                ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)).toSection x) ≤
            cbg i := hcbg i x
        have h2 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
            (((iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) - HdCr) -
              (iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) - HdCu)).toSection x) ≤
            2 * (KcCr i * Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3)) +
              2 * (KcCu i * Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3)) := by
          rw [show (((iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) - HdCr) -
              (iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) - HdCu)).toSection x) =
              (iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) - HdCr).toSection x -
              (iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
                  ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) - HdCu).toSection x
              from by rw [SmoothCcTensor.toSection_sub]; rfl]
          refine le_trans (tsRfns_sub_le (I := I) (M := M) g₀ 2 (2 + i) x _ _) ?_
          exact add_le_add (mul_le_mul_of_nonneg_left (hCr_res x) (by norm_num))
            (mul_le_mul_of_nonneg_left (hCu_res x) (by norm_num))
        calc 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
              ((iteratedCovGrad (I := I) g₀ 2 2 i
                (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀ -
                  ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀)).toSection x) +
            2 * riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
              (((iteratedCovGrad (I := I) g₀ 2 2 i
                  (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
                    ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₀) - HdCr) -
                (iteratedCovGrad (I := I) g₀ 2 2 i
                  (ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁ -
                    ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₀) - HdCu)).toSection x)
            ≤ 2 * cbg i +
              2 * (2 * (KcCr i * Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3)) +
                2 * (KcCu i * Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3))) := by
              refine add_le_add ?_ (mul_le_mul_of_nonneg_left h2 (by norm_num))
              have := mul_le_mul_of_nonneg_left h1 (show (0:ℝ) ≤ 2 by norm_num)
              linarith
          _ ≤ (2 * cbg i + 4 * KcCr i + 4 * KcCu i) *
                Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) := by
              have hc1 : 2 * cbg i ≤ 2 * cbg i *
                  Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) := by
                nlinarith [hcbg_nn i, hW_one]
              nlinarith [hKcCr_nn i, hKcCu_nn i, hW_nn]
      obtain ⟨hint, hbound_int⟩ := hKI P hPball i
      have hF_int : MeasureTheory.Integrable
          (fun x => (2 * cbg i + 4 * KcCr i + 4 * KcCu i) *
            Combinatorics.boundedFactorGridWindow
              (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3))
          (riemannianVolumeMeasure (I := I) (M := M) g₀) := hint.const_mul _
      have key := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M)
        g₀ 2 (2 + i)
        (iteratedCovGrad (I := I) g₀ 2 2 i
          (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
            ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁) - (HdCr - HdCu))
        _ hF_int hpt
      refine le_trans key ?_
      rw [MeasureTheory.integral_const_mul]
      calc (2 * cbg i + 4 * KcCr i + 4 * KcCu i) *
            ∫ x, Combinatorics.boundedFactorGridWindow
              (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                ((iteratedCovGrad (I := I) g₀ 0 2 l P).toSection x)) (i + 1) (i + 3)
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀)
          ≤ (2 * cbg i + 4 * KcCr i + 4 * KcCu i) *
            (KI i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2)) := by
            refine mul_le_mul_of_nonneg_left hbound_int ?_
            have := hcbg_nn i; have := hKcCr_nn i; have := hKcCu_nn i; linarith
        _ = (2 * cbg i + 4 * KcCr i + 4 * KcCu i) * KI i *
            (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) := by ring
  · haveI hM' : IsEmpty M := not_nonempty_iff.mp hM
    refine ⟨0, fun x => (IsEmpty.false x).elim, ?_, ?_⟩
    · have hz : ‖(0 : SmoothCcTensor g₀ 2 (2 + i))‖ = 0 := by
        rw [SmoothCcTensor.norm_def, tensorL2Norm_def, tensorL2Inner,
          MeasureTheory.integral_of_isEmpty, Real.sqrt_zero]
      rw [hz]
      have := sq_nonneg ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) P‖
      nlinarith [hKtCr_nn, hKtCu_nn]
    · have hz : ‖iteratedCovGrad (I := I) g₀ 2 2 i
          (ricciArmOrder0RiemannCoeff (I := I) (M := M) g₀ g₁ -
            ricciArmOrder0CurvCoeff (I := I) (M := M) g₀ g₁) -
          (0 : SmoothCcTensor g₀ 2 (2 + i))‖ = 0 := by
        rw [SmoothCcTensor.norm_def, tensorL2Norm_def, tensorL2Inner,
          MeasureTheory.integral_of_isEmpty, Real.sqrt_zero]
      rw [hz]
      have hsum_nn : (0 : ℝ) ≤ ∑ j ∈ Finset.range (i + 2),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2 :=
        Finset.sum_nonneg fun j _ => sq_nonneg _
      have hKc_nn : (0 : ℝ) ≤ (2 * cbg i + 4 * KcCr i + 4 * KcCu i) * KI i :=
        mul_nonneg
          (by have := hcbg_nn i; have := hKcCr_nn i; have := hKcCu_nn i; linarith)
          (hKI_nn i)
      nlinarith

section TopSeparatedKoszulExport

set_option linter.unusedSectionVars false in
theorem rfns_iteratedCovGrad_raisedKoszul_pointwise_le
    (g₀ g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
    (i : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 2 i (raisedKoszul (I := I) g₀ g₁)).toSection x) ≤
      10 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 1)) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (i + 1) T).toSection x) :=
  rfns_iteratedCovGrad_raisedKoszul_pointwise (I := I) (M := M) g₀ g₁ T htie i x

/-- The lowered Koszul covector costs exactly one metric derivative in `L2`.
This is the low-regularity form used after the moving lowering metric cancels
the inverse metric in a self-background connection difference. -/
theorem koszul_l2_succ
    (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    (n : ℕ) :
    ‖iteratedCovGrad (I := I) g₀ 0 3 n (koszulCovecCc (I := I) g₀ T)‖ ^ 2 ≤
      10 * ‖iteratedCovGrad (I := I) g₀ 0 2 (n + 1) T‖ ^ 2 := by
  have hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (3 + n) x
          ((iteratedCovGrad (I := I) g₀ 0 3 n
            (koszulCovecCc (I := I) g₀ T)).toSection x) ≤
        10 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (n + 1)) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (n + 1) T).toSection x) := by
    intro x
    exact rfns_iteratedCovGrad_koszulCovecCc_pointwise
      (I := I) (M := M) g₀ T n x
  have hF_int : MeasureTheory.Integrable
      (fun x => 10 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (n + 1)) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (n + 1) T).toSection x))
      (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    (integrable_riemannianFiberNormSq_toSection
      (I := I) (M := M) g₀ 0 (2 + (n + 1))
      (iteratedCovGrad (I := I) g₀ 0 2 (n + 1) T)).const_mul _
  have key := normSq_le_integral_of_pointwise_fiberNormSq_le_rs
    (I := I) (M := M) g₀ 0 (3 + n)
    (iteratedCovGrad (I := I) g₀ 0 3 n (koszulCovecCc (I := I) g₀ T))
    (fun x => 10 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (n + 1)) x
      ((iteratedCovGrad (I := I) g₀ 0 2 (n + 1) T).toSection x))
    hF_int hpt
  refine key.trans ?_
  rw [MeasureTheory.integral_const_mul]
  rw [← tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs
    (I := I) (M := M) g₀ 0 (2 + (n + 1))
    (iteratedCovGrad (I := I) g₀ 0 2 (n + 1) T)]
  rw [← SmoothCcTensor.norm_def]

end TopSeparatedKoszulExport

end TopSeparatedResidualIntegrator

end Connection
end Integral
end DifferentialGeometry

end
