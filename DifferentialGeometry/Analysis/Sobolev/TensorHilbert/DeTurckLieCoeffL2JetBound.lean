import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckVectorFieldL2JetBound
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLieKernelL2JetBound
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricArmCoeffJetTower
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurckSectionDifference
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorFieldFibreNormJet
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedCovGradLinear
import DifferentialGeometry.Geometry.Connection.TensorNabla.SlotInsertCovariantNaturality
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.FiberNormSubadditivity

noncomputable section

set_option linter.style.setOption false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open MeasureTheory Set Filter Topology Bundle Manifold Tensor0SBundle ContinuousLinearMap
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.Integral.Connection

open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
  (deTurckLieCoeffField deTurckLieCoeffField_toSection deTurckLieDLbFib deTurckLieDLbFib_toModel
    deTurckLieWEndo reindexCoeffGen reindexCoeffGen_toSection reindexCoeffFibGen
    reindexCoeffFibGen_apply)
open DifferentialGeometry.PDE.DeTurck.RicciLinearization (realizedFam)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private theorem sq_le_two_add (t u v c1 c2 : ℝ) (ht : 0 ≤ t) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (htri : t ≤ u + v) (h1 : u ^ 2 ≤ c1) (h2 : v ^ 2 ≤ c2) : t ^ 2 ≤ 2 * (c1 + c2) := by
  have huv : 0 ≤ u + v := by linarith
  nlinarith [mul_le_mul htri htri ht huv, sq_nonneg (u - v), h1, h2, hu, hv]

set_option linter.unusedSectionVars false in
private theorem deTurckLieDLbCoeffField_eq_slotInsert_sum
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    deTurckLieDLbCoeffField (I := I) (M := M) g₀ g₁ g_bg =
      slotInsertEndoCc (I := I) (M := M) g₀ 1
          (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg)
        + reindexCoeffGen (I := I) (M := M) g₀ 2 2
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
              (slotInsertEndoCc (I := I) (M := M) g₀ 1
                (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg)))
            (Equiv.swap (0 : Fin 2) 1) := by
  classical
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply]
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  have hsum : (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (slotInsertEndoCc (I := I) (M := M) g₀ 1
            (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg)).toSection x
          + (reindexCoeffGen (I := I) (M := M) g₀ 2 2
              (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
                (slotInsertEndoCc (I := I) (M := M) g₀ 1
                  (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg)))
              (Equiv.swap (0 : Fin 2) 1)).toSection x) D
      = (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
          (slotInsertEndoCc (I := I) (M := M) g₀ 1
            (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg)).toSection x) D
        + (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
          (reindexCoeffGen (I := I) (M := M) g₀ 2 2
              (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
                (slotInsertEndoCc (I := I) (M := M) g₀ 1
                  (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg)))
              (Equiv.swap (0 : Fin 2) 1)).toSection x) D := rfl
  change Tensor0SSpace.toModel
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (deTurckLieDLbCoeffField (I := I) (M := M) g₀ g₁ g_bg).toSection x) D) m =
    Tensor0SSpace.toModel
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (slotInsertEndoCc (I := I) (M := M) g₀ 1
            (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg)).toSection x
          + (reindexCoeffGen (I := I) (M := M) g₀ 2 2
              (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
                (slotInsertEndoCc (I := I) (M := M) g₀ 1
                  (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg)))
              (Equiv.swap (0 : Fin 2) 1)).toSection x) D) m
  rw [hsum, Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply]
  rw [show (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (deTurckLieDLbCoeffField (I := I) (M := M) g₀ g₁ g_bg).toSection x) D
      = deTurckLieDLbFib (I := I) g₁ g_bg x D from rfl]
  rw [deTurckLieDLbFib_toModel (I := I) g₁ g_bg x D m]
  rw [show (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (slotInsertEndoCc (I := I) (M := M) g₀ 1
          (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg)).toSection x) D
      = slotInsertEndoFib (I := I) (M := M) 2 0 x
          (deTurckLieWEndo (I := I) g₁ g_bg x) D from rfl]
  rw [slotInsertEndoFib_apply_eval (I := I) (M := M) 2 0 x
    (deTurckLieWEndo (I := I) g₁ g_bg x) D m]
  rw [show (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (reindexCoeffGen (I := I) (M := M) g₀ 2 2
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
              (slotInsertEndoCc (I := I) (M := M) g₀ 1
                (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg)))
            (Equiv.swap (0 : Fin 2) 1)).toSection x) D
      = reindexCoeffFibGen (I := I) 2 2 (Equiv.swap (0 : Fin 2) 1) x
          (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
              (slotInsertEndoCc (I := I) (M := M) g₀ 1
                (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg))).toSection x) D from rfl]
  rw [reindexCoeffFibGen_apply (I := I) 2 2 (Equiv.swap (0 : Fin 2) 1) x
    (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
        (slotInsertEndoCc (I := I) (M := M) g₀ 1
          (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg))).toSection x) D]
  rw [show (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
          (slotInsertEndoCc (I := I) (M := M) g₀ 1
            (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg))).toSection x)
      = (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
          rsDomDomCongr (I := I) (M := M) (Equiv.swap (0 : Fin 2) 1)
            ((slotInsertEndoCc (I := I) (M := M) g₀ 1
              (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg)).toSection x)) from rfl]
  rw [toModel_rsDomDomCongr_apply (I := I) (M := M) (Equiv.swap (0 : Fin 2) 1)
    ((slotInsertEndoCc (I := I) (M := M) g₀ 1
      (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg)).toSection x)
    (Tensor0SSpace.ofModel
      (ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
        (Tensor0SSpace.toModel D)))]
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  rw [show (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        (slotInsertEndoCc (I := I) (M := M) g₀ 1
          (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg)).toSection x)
        (Tensor0SSpace.ofModel
          (ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
            (Tensor0SSpace.toModel D)))
      = slotInsertEndoFib (I := I) (M := M) 2 0 x
          (deTurckLieWEndo (I := I) g₁ g_bg x)
          (Tensor0SSpace.ofModel
            (ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
              (Tensor0SSpace.toModel D))) from rfl]
  rw [slotInsertEndoFib_apply_eval (I := I) (M := M) 2 0 x
    (deTurckLieWEndo (I := I) g₁ g_bg x)
    (Tensor0SSpace.ofModel
      (ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
        (Tensor0SSpace.toModel D)))
    (fun i => m ((Equiv.swap (0 : Fin 2) 1) i))]
  rw [Tensor0SSpace.toModel_ofModel, ContinuousMultilinearMap.domDomCongr_apply]
  have harg : (fun k => Function.update (fun i => m ((Equiv.swap (0 : Fin 2) 1) i)) 0
        (deTurckLieWEndo (I := I) g₁ g_bg x
          ((fun i => m ((Equiv.swap (0 : Fin 2) 1) i)) 0))
        ((Equiv.swap (0 : Fin 2) 1) k))
      = Function.update m 1 (deTurckLieWEndo (I := I) g₁ g_bg x (m 1)) := by
    funext k
    have hswap0 : (Equiv.swap (0 : Fin 2) 1) 0 = 1 := Equiv.swap_apply_left 0 1
    have hswap1 : (Equiv.swap (0 : Fin 2) 1) 1 = 0 := Equiv.swap_apply_right 0 1
    simp only [Function.update_apply]
    rw [hswap0, Equiv.swap_apply_self]
    have hcond : ((Equiv.swap (0 : Fin 2) 1) k = 0) = (k = 1) := by
      apply propext
      constructor
      · intro h
        have h2 := congrArg (Equiv.swap (0 : Fin 2) 1) h
        rwa [Equiv.swap_apply_self, hswap0] at h2
      · intro h
        rw [h, hswap1]
    simp only [hcond]
  rw [harg]

set_option linter.unusedSectionVars false in
private theorem normSq_iteratedCovGrad_le_scaled_of_pointwise
    (g₀ : SmoothRiemannianMetric I M) (X : SmoothCcTensor g₀ 2 2) (Y : SmoothCcTensor g₀ 1 1)
    (i : ℕ) (c : ℝ)
    (hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
          ((iteratedCovGrad (I := I) g₀ 2 2 i X).toSection x) ≤
        c * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
          ((iteratedCovGrad (I := I) g₀ 1 1 i Y).toSection x)) :
    ‖iteratedCovGrad (I := I) g₀ 2 2 i X‖ ^ 2 ≤
      c * ‖iteratedCovGrad (I := I) g₀ 1 1 i Y‖ ^ 2 := by
  have hF_int : MeasureTheory.Integrable
      (fun x => c * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 1 i Y).toSection x))
      (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    (integrable_riemannianFiberNormSq_toSection (I := I) (M := M) g₀ 1 (1 + i)
      (iteratedCovGrad (I := I) g₀ 1 1 i Y)).const_mul c
  have key := normSq_le_integral_of_pointwise_fiberNormSq_le_rs (I := I) (M := M) g₀ 2 (2 + i)
    (iteratedCovGrad (I := I) g₀ 2 2 i X)
    (fun x => c * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
      ((iteratedCovGrad (I := I) g₀ 1 1 i Y).toSection x))
    hF_int (fun x => hpt x)
  refine le_trans key (le_of_eq ?_)
  rw [MeasureTheory.integral_const_mul]
  congr 1
  rw [SmoothCcTensor.norm_def (I := I) (M := M) (iteratedCovGrad (I := I) g₀ 1 1 i Y)]
  exact (tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g₀ 1 (1 + i)
    (iteratedCovGrad (I := I) g₀ 1 1 i Y)).symm

set_option linter.unusedSectionVars false in
private theorem rfns_iteratedCovGrad_dlbSlotZero_le
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (i : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 2 2 i
          (slotInsertEndoCc (I := I) (M := M) g₀ 1
            (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg))).toSection x) ≤
      (Module.finrank ℝ E : ℝ) *
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
          ((iteratedCovGrad (I := I) g₀ 1 1 i
            (deTurckLieWEndoInsert (I := I) (M := M) g₀ g₁ g_bg)).toSection x) := by
  have h := rfns_iteratedCovGrad_slotInsertEndoCc_le_endo (I := I) (M := M) g₀ 1
    (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg) i x
  rw [pow_one] at h
  exact h

set_option linter.unusedSectionVars false in
private theorem rfns_iteratedCovGrad_dlbSlotOne_le
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (i : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 2 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 2 2 i
          (reindexCoeffGen (I := I) (M := M) g₀ 2 2
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
              (slotInsertEndoCc (I := I) (M := M) g₀ 1
                (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg)))
            (Equiv.swap (0 : Fin 2) 1))).toSection x) ≤
      (Module.finrank ℝ E : ℝ) *
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
          ((iteratedCovGrad (I := I) g₀ 1 1 i
            (deTurckLieWEndoInsert (I := I) (M := M) g₀ g₁ g_bg)).toSection x) := by
  have heq := rfns_iteratedCovGrad_rsDomDomCongr_both_eq (I := I) (M := M) g₀ 2 2
    (Equiv.swap (0 : Fin 2) 1) (Equiv.swap (0 : Fin 2) 1)
    (slotInsertEndoCc (I := I) (M := M) g₀ 1
      (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg)) i x
  exact heq.trans_le (rfns_iteratedCovGrad_dlbSlotZero_le (I := I) (M := M) g₀ g₁ g_bg i x)

set_option linter.unusedVariables false in
theorem deTurckLieDLbCoeffField_realizedFam_jetL2_perOrder_ballUniform
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ P : ℕ → ℝ, (∀ i, 0 ≤ P i) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a → ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
              (deTurckLieDLbCoeffField (I := I) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)‖ ^ 2 ≤ P i := by
  obtain ⟨F, hF_nn, hF⟩ :=
    deTurckLieWEndoInsert_realizedFam_jetL2_perOrder_ballUniform (I := I) (M := M) g₀ g_bg a
      ha_super hR hδ₀
  have hfr_nn : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
  refine ⟨fun i => 2 * ((Module.finrank ℝ E : ℝ) * F i + (Module.finrank ℝ E : ℝ) * F i),
    fun i => by
      have h1 := hF_nn i
      have h2 : 0 ≤ (Module.finrank ℝ E : ℝ) * F i := mul_nonneg hfr_nn h1
      linarith, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball i hi s hs
  have hWE : ‖iteratedCovGrad (I := I) g₀ 1 1 i
      (deTurckLieWEndoInsert (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)‖ ^ 2 ≤ F i :=
    hF T T' hδ_le hδ hδ'_le hδ' hTball hT'ball i hi s hs
  have hL2A : ‖iteratedCovGrad (I := I) g₀ 2 2 i
      (slotInsertEndoCc (I := I) (M := M) g₀ 1
        (deTurckLieWEndoSection (I := I) (M := M)
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg))‖ ^ 2 ≤
      (Module.finrank ℝ E : ℝ) * F i := by
    refine le_trans (normSq_iteratedCovGrad_le_scaled_of_pointwise (I := I) (M := M) g₀
      (slotInsertEndoCc (I := I) (M := M) g₀ 1
        (deTurckLieWEndoSection (I := I) (M := M)
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg))
      (deTurckLieWEndoInsert (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
      i (Module.finrank ℝ E : ℝ)
      (fun x => rfns_iteratedCovGrad_dlbSlotZero_le (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg i x)) ?_
    exact mul_le_mul_of_nonneg_left hWE hfr_nn
  have hL2B : ‖iteratedCovGrad (I := I) g₀ 2 2 i
      (reindexCoeffGen (I := I) (M := M) g₀ 2 2
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
          (slotInsertEndoCc (I := I) (M := M) g₀ 1
            (deTurckLieWEndoSection (I := I) (M := M)
              (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)))
        (Equiv.swap (0 : Fin 2) 1))‖ ^ 2 ≤
      (Module.finrank ℝ E : ℝ) * F i := by
    refine le_trans (normSq_iteratedCovGrad_le_scaled_of_pointwise (I := I) (M := M) g₀
      (reindexCoeffGen (I := I) (M := M) g₀ 2 2
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
          (slotInsertEndoCc (I := I) (M := M) g₀ 1
            (deTurckLieWEndoSection (I := I) (M := M)
              (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)))
        (Equiv.swap (0 : Fin 2) 1))
      (deTurckLieWEndoInsert (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
      i (Module.finrank ℝ E : ℝ)
      (fun x => rfns_iteratedCovGrad_dlbSlotOne_le (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg i x)) ?_
    exact mul_le_mul_of_nonneg_left hWE hfr_nn
  have hgrad : iteratedCovGrad (I := I) g₀ 2 2 i
      (deTurckLieDLbCoeffField (I := I) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
      = iteratedCovGrad (I := I) g₀ 2 2 i
          (slotInsertEndoCc (I := I) (M := M) g₀ 1
            (deTurckLieWEndoSection (I := I) (M := M)
              (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg))
        + iteratedCovGrad (I := I) g₀ 2 2 i
            (reindexCoeffGen (I := I) (M := M) g₀ 2 2
              (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
                (slotInsertEndoCc (I := I) (M := M) g₀ 1
                  (deTurckLieWEndoSection (I := I) (M := M)
                    (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)))
              (Equiv.swap (0 : Fin 2) 1)) := by
    rw [deTurckLieDLbCoeffField_eq_slotInsert_sum (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg, iteratedCovGrad_add]
  rw [hgrad]
  exact sq_le_two_add
    ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (slotInsertEndoCc (I := I) (M := M) g₀ 1
          (deTurckLieWEndoSection (I := I) (M := M)
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg))
      + iteratedCovGrad (I := I) g₀ 2 2 i
          (reindexCoeffGen (I := I) (M := M) g₀ 2 2
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
              (slotInsertEndoCc (I := I) (M := M) g₀ 1
                (deTurckLieWEndoSection (I := I) (M := M)
                  (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)))
            (Equiv.swap (0 : Fin 2) 1))‖
    ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (slotInsertEndoCc (I := I) (M := M) g₀ 1
          (deTurckLieWEndoSection (I := I) (M := M)
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg))‖
    ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (reindexCoeffGen (I := I) (M := M) g₀ 2 2
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
            (slotInsertEndoCc (I := I) (M := M) g₀ 1
              (deTurckLieWEndoSection (I := I) (M := M)
                (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)))
          (Equiv.swap (0 : Fin 2) 1))‖
    ((Module.finrank ℝ E : ℝ) * F i) ((Module.finrank ℝ E : ℝ) * F i)
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    (norm_add_le _ _) hL2A hL2B

set_option linter.unusedSectionVars false in
/-- Per-order `×4·finrank` transport of the `(2,2)` field jet to the `(1,1)` insert jet, via the
slotInsert/reindex decomposition (`deTurckLieDLbCoeffField_eq_slotInsert_sum`); each summand is
`≤ finrank·‖∇ⁱ wEndoInsert‖²` (`rfns_iteratedCovGrad_dlbSlotZero_le`/`dlbSlotOne_le`), and
`sq_le_two_add` yields the factor `4·finrank`.  `R`-free bounded factor. -/
private theorem normSq_iCG_dlbField_le (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (i : ℕ) :
    ‖iteratedCovGrad (I := I) g₀ 2 2 i (deTurckLieDLbCoeffField (I := I) g₀ g₁ g_bg)‖ ^ 2 ≤
      4 * (Module.finrank ℝ E : ℝ) *
        ‖iteratedCovGrad (I := I) g₀ 1 1 i
          (deTurckLieWEndoInsert (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2 := by
  have hL2A : ‖iteratedCovGrad (I := I) g₀ 2 2 i
      (slotInsertEndoCc (I := I) (M := M) g₀ 1
        (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg))‖ ^ 2 ≤
      (Module.finrank ℝ E : ℝ) *
        ‖iteratedCovGrad (I := I) g₀ 1 1 i
          (deTurckLieWEndoInsert (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2 :=
    normSq_iteratedCovGrad_le_scaled_of_pointwise (I := I) (M := M) g₀
      (slotInsertEndoCc (I := I) (M := M) g₀ 1 (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg))
      (deTurckLieWEndoInsert (I := I) (M := M) g₀ g₁ g_bg) i (Module.finrank ℝ E : ℝ)
      (fun x => rfns_iteratedCovGrad_dlbSlotZero_le (I := I) (M := M) g₀ g₁ g_bg i x)
  have hL2B : ‖iteratedCovGrad (I := I) g₀ 2 2 i
      (reindexCoeffGen (I := I) (M := M) g₀ 2 2
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
          (slotInsertEndoCc (I := I) (M := M) g₀ 1
            (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg)))
        (Equiv.swap (0 : Fin 2) 1))‖ ^ 2 ≤
      (Module.finrank ℝ E : ℝ) *
        ‖iteratedCovGrad (I := I) g₀ 1 1 i
          (deTurckLieWEndoInsert (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2 :=
    normSq_iteratedCovGrad_le_scaled_of_pointwise (I := I) (M := M) g₀
      (reindexCoeffGen (I := I) (M := M) g₀ 2 2
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
          (slotInsertEndoCc (I := I) (M := M) g₀ 1
            (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg)))
        (Equiv.swap (0 : Fin 2) 1))
      (deTurckLieWEndoInsert (I := I) (M := M) g₀ g₁ g_bg) i (Module.finrank ℝ E : ℝ)
      (fun x => rfns_iteratedCovGrad_dlbSlotOne_le (I := I) (M := M) g₀ g₁ g_bg i x)
  have hgrad : iteratedCovGrad (I := I) g₀ 2 2 i (deTurckLieDLbCoeffField (I := I) g₀ g₁ g_bg)
      = iteratedCovGrad (I := I) g₀ 2 2 i
          (slotInsertEndoCc (I := I) (M := M) g₀ 1
            (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg))
        + iteratedCovGrad (I := I) g₀ 2 2 i
            (reindexCoeffGen (I := I) (M := M) g₀ 2 2
              (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
                (slotInsertEndoCc (I := I) (M := M) g₀ 1
                  (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg)))
              (Equiv.swap (0 : Fin 2) 1)) := by
    rw [deTurckLieDLbCoeffField_eq_slotInsert_sum (I := I) (M := M) g₀ g₁ g_bg, iteratedCovGrad_add]
  rw [hgrad]
  refine le_trans (sq_le_two_add
    ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (slotInsertEndoCc (I := I) (M := M) g₀ 1
          (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg))
      + iteratedCovGrad (I := I) g₀ 2 2 i
          (reindexCoeffGen (I := I) (M := M) g₀ 2 2
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
              (slotInsertEndoCc (I := I) (M := M) g₀ 1
                (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg)))
            (Equiv.swap (0 : Fin 2) 1))‖
    ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (slotInsertEndoCc (I := I) (M := M) g₀ 1
          (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg))‖
    ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (reindexCoeffGen (I := I) (M := M) g₀ 2 2
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
            (slotInsertEndoCc (I := I) (M := M) g₀ 1
              (deTurckLieWEndoSection (I := I) (M := M) g₁ g_bg)))
          (Equiv.swap (0 : Fin 2) 1))‖
    ((Module.finrank ℝ E : ℝ) *
      ‖iteratedCovGrad (I := I) g₀ 1 1 i (deTurckLieWEndoInsert (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2)
    ((Module.finrank ℝ E : ℝ) *
      ‖iteratedCovGrad (I := I) g₀ 1 1 i (deTurckLieWEndoInsert (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2)
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    (norm_add_le _ _) hL2A hL2B) (le_of_eq (by ring))

set_option linter.unusedVariables false in
/-- **`realizedFam` per-order top-separated jet-L2 bound** for the DLb coefficient field.  Thin
`×4·finrank` transport of `deTurckLieWEndoInsert_realizedFam_jetL2_perOrder_topSeparated` through
`normSq_iCG_dlbField_le`; `Ktop = 4·finrank·Ktop_insert` stays `R`-free. -/
theorem deTurckLieDLbCoeffField_realizedFam_jetL2_perOrder_topSeparated
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Ktop : ℝ, 0 ≤ Ktop ∧ ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
        ∀ (i : ℕ), i ≤ a →
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
              (deTurckLieDLbCoeffField (I := I) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)‖ ^ 2 ≤
            Ktop * (‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T‖ ^ 2 +
              ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T'‖ ^ 2) +
            Kc i * (1 + ∑ j ∈ Finset.range (i + 3),
              (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) := by
  obtain ⟨Ktop, hKtop_nn, Kc, hKc_nn, hins⟩ :=
    deTurckLieWEndoInsert_realizedFam_jetL2_perOrder_topSeparated (I := I) (M := M) g₀ g_bg a
      ha_super hR hδ₀
  have hfr_nn : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
  refine ⟨4 * (Module.finrank ℝ E : ℝ) * Ktop,
      mul_nonneg (mul_nonneg (by norm_num) hfr_nn) hKtop_nn,
    fun i => 4 * (Module.finrank ℝ E : ℝ) * Kc i,
    fun i => mul_nonneg (mul_nonneg (by norm_num) hfr_nn) (hKc_nn i), ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball s hs i hi
  have hins_i := hins T T' hδ_le hδ hδ'_le hδ' hTball hT'ball s hs i hi
  have hstep : 4 * (Module.finrank ℝ E : ℝ) *
        ‖iteratedCovGrad (I := I) g₀ 1 1 i
          (deTurckLieWEndoInsert (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)‖ ^ 2 ≤
      4 * (Module.finrank ℝ E : ℝ) *
        (Ktop * (‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T‖ ^ 2 +
            ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T'‖ ^ 2) +
          Kc i * (1 + ∑ j ∈ Finset.range (i + 3),
            (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2))) :=
    mul_le_mul_of_nonneg_left hins_i (mul_nonneg (by norm_num) hfr_nn)
  refine le_trans (normSq_iCG_dlbField_le (I := I) (M := M) g₀
    (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg i) ?_
  refine le_trans hstep (le_of_eq ?_)
  ring

set_option linter.unusedVariables false in
/-- **Summed** `realizedFam` top-separated jet-L2 bound for the DLb coefficient field.  Thin
`×4·finrank` transport of the summed insert bound; both windows `a+3`, `Ktop` `R`-free. -/
theorem deTurckLieDLbCoeffField_realizedFam_jetL2_summed_topSeparated
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Ktop : ℝ, 0 ≤ Ktop ∧ ∃ Kc : ℝ, 0 ≤ Kc ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
          ∑ i ∈ Finset.range (a + 1),
              ‖iteratedCovGrad (I := I) g₀ 2 2 i
                (deTurckLieDLbCoeffField (I := I) g₀
                  (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)‖ ^ 2 ≤
            Ktop * (∑ j ∈ Finset.range (a + 3),
                (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
                  ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) +
            Kc * (1 + ∑ j ∈ Finset.range (a + 3),
                (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
                  ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) := by
  obtain ⟨Ktop, hKtop_nn, Kc, hKc_nn, hins⟩ :=
    deTurckLieWEndoInsert_realizedFam_jetL2_summed_topSeparated (I := I) (M := M) g₀ g_bg a
      ha_super hR hδ₀
  have hfr_nn : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
  refine ⟨4 * (Module.finrank ℝ E : ℝ) * Ktop,
      mul_nonneg (mul_nonneg (by norm_num) hfr_nn) hKtop_nn,
    4 * (Module.finrank ℝ E : ℝ) * Kc,
    mul_nonneg (mul_nonneg (by norm_num) hfr_nn) hKc_nn, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball s hs
  have hsum_field : ∑ i ∈ Finset.range (a + 1),
        ‖iteratedCovGrad (I := I) g₀ 2 2 i
          (deTurckLieDLbCoeffField (I := I) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)‖ ^ 2 ≤
      4 * (Module.finrank ℝ E : ℝ) *
        ∑ i ∈ Finset.range (a + 1),
          ‖iteratedCovGrad (I := I) g₀ 1 1 i
            (deTurckLieWEndoInsert (I := I) (M := M) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun i _ => ?_)
    exact normSq_iCG_dlbField_le (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg i
  have hins_s := hins T T' hδ_le hδ hδ'_le hδ' hTball hT'ball s hs
  refine le_trans hsum_field ?_
  refine le_trans (mul_le_mul_of_nonneg_left hins_s (mul_nonneg (by norm_num) hfr_nn))
    (le_of_eq ?_)
  ring

set_option linter.unusedVariables false in
theorem deTurckLieDLbCoeffField_realizedFam_rfns_order0_ballUniform
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 → ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
              ((deTurckLieDLbCoeffField (I := I) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg).toSection x) ≤ Λ := by
  obtain ⟨Λ0, hΛ0_nn, hΛ0⟩ :=
    deTurckLieWEndoInsert_realizedFam_rfns_order0_ballUniform (I := I) (M := M) g₀ g_bg a
      ha_super hR hδ₀
  have hfr_nn : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
  refine ⟨2 * ((Module.finrank ℝ E : ℝ) * Λ0) + 2 * ((Module.finrank ℝ E : ℝ) * Λ0), by
    have h2 : 0 ≤ (Module.finrank ℝ E : ℝ) * Λ0 := mul_nonneg hfr_nn hΛ0_nn
    linarith, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball s hs x
  have hWE : riemannianFiberNormSq (I := I) (M := M) g₀ 1 1 x
      ((deTurckLieWEndoInsert (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg).toSection x) ≤ Λ0 :=
    hΛ0 T T' hδ_le hδ hδ'_le hδ' hTball hT'ball s hs x
  have hA0 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
      ((slotInsertEndoCc (I := I) (M := M) g₀ 1
        (deTurckLieWEndoSection (I := I) (M := M)
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)).toSection x) ≤
      (Module.finrank ℝ E : ℝ) * Λ0 := by
    have h := rfns_iteratedCovGrad_dlbSlotZero_le (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg 0 x
    exact le_trans h (mul_le_mul_of_nonneg_left hWE hfr_nn)
  have hB0 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
      ((reindexCoeffGen (I := I) (M := M) g₀ 2 2
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
          (slotInsertEndoCc (I := I) (M := M) g₀ 1
            (deTurckLieWEndoSection (I := I) (M := M)
              (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)))
        (Equiv.swap (0 : Fin 2) 1)).toSection x) ≤
      (Module.finrank ℝ E : ℝ) * Λ0 := by
    have h := rfns_iteratedCovGrad_dlbSlotOne_le (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg 0 x
    exact le_trans h (mul_le_mul_of_nonneg_left hWE hfr_nn)
  have hsec : (deTurckLieDLbCoeffField (I := I) g₀
      (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg).toSection x
      = (slotInsertEndoCc (I := I) (M := M) g₀ 1
          (deTurckLieWEndoSection (I := I) (M := M)
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)).toSection x
        + (reindexCoeffGen (I := I) (M := M) g₀ 2 2
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
              (slotInsertEndoCc (I := I) (M := M) g₀ 1
                (deTurckLieWEndoSection (I := I) (M := M)
                  (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)))
            (Equiv.swap (0 : Fin 2) 1)).toSection x := by
    rw [deTurckLieDLbCoeffField_eq_slotInsert_sum (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg,
      SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply]
  rw [hsec]
  have hadd := riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 2 2 x
    ((slotInsertEndoCc (I := I) (M := M) g₀ 1
      (deTurckLieWEndoSection (I := I) (M := M)
        (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)).toSection x)
    ((reindexCoeffGen (I := I) (M := M) g₀ 2 2
      (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 (Equiv.swap (0 : Fin 2) 1)
        (slotInsertEndoCc (I := I) (M := M) g₀ 1
          (deTurckLieWEndoSection (I := I) (M := M)
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)))
      (Equiv.swap (0 : Fin 2) 1)).toSection x)
  linarith [hadd, hA0, hB0]

set_option linter.unusedVariables false in
theorem deTurckLieCoeffField_realizedFam_jetL2_perOrder_ballUniform
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ P : ℕ → ℝ, (∀ i, 0 ≤ P i) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (i : ℕ), i ≤ a → ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
              (deTurckLieCoeffField (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)‖ ^ 2 ≤ P i := by
  obtain ⟨Pa, hPa_nn, hPa⟩ :=
    deTurckLieDLaCoeffField_realizedFam_jetL2_perOrder_ballUniform (I := I) (M := M) g₀ g_bg a
      ha_super hR hδ₀
  obtain ⟨Pb, hPb_nn, hPb⟩ :=
    deTurckLieDLbCoeffField_realizedFam_jetL2_perOrder_ballUniform (I := I) (M := M) g₀ g_bg a
      ha_super hR hδ₀
  refine ⟨fun i => 2 * (Pa i + Pb i),
    fun i => by linarith [hPa_nn i, hPb_nn i], ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball i hi s hs
  have ha := hPa T T' hδ_le hδ hδ'_le hδ' hTball hT'ball i hi s hs
  have hb := hPb T T' hδ_le hδ hδ'_le hδ' hTball hT'ball i hi s hs
  have hgrad : iteratedCovGrad (I := I) g₀ 2 2 i
      (deTurckLieCoeffField (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
      = iteratedCovGrad (I := I) g₀ 2 2 i
          (deTurckLieDLaCoeffField (I := I) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
        + iteratedCovGrad (I := I) g₀ 2 2 i
            (deTurckLieDLbCoeffField (I := I) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg) := by
    rw [← deTurckLieDLaCoeffField_add_deTurckLieDLbCoeffField (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg, iteratedCovGrad_add]
  rw [hgrad]
  exact sq_le_two_add
    ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (deTurckLieDLaCoeffField (I := I) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)
      + iteratedCovGrad (I := I) g₀ 2 2 i
          (deTurckLieDLbCoeffField (I := I) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)‖
    ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (deTurckLieDLaCoeffField (I := I) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)‖
    ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (deTurckLieDLbCoeffField (I := I) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)‖
    (Pa i) (Pb i)
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    (norm_add_le _ _) ha hb

set_option linter.unusedVariables false in
theorem deTurckLieCoeffField_realizedFam_rfns_order0_ballUniform
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 → ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x
              ((deTurckLieCoeffField (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg).toSection x) ≤ Λ := by
  obtain ⟨Λa, hΛa_nn, hΛa⟩ :=
    deTurckLieDLaCoeffField_realizedFam_rfns_order0_ballUniform (I := I) (M := M) g₀ g_bg a
      ha_super hR hδ₀
  obtain ⟨Λb, hΛb_nn, hΛb⟩ :=
    deTurckLieDLbCoeffField_realizedFam_rfns_order0_ballUniform (I := I) (M := M) g₀ g_bg a
      ha_super hR hδ₀
  refine ⟨2 * Λa + 2 * Λb, by linarith, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball s hs x
  have ha := hΛa T T' hδ_le hδ hδ'_le hδ' hTball hT'ball s hs x
  have hb := hΛb T T' hδ_le hδ hδ'_le hδ' hTball hT'ball s hs x
  have hsec : (deTurckLieCoeffField (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg).toSection x
      = (deTurckLieDLaCoeffField (I := I) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg).toSection x
        + (deTurckLieDLbCoeffField (I := I) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg).toSection x := by
    rw [← deTurckLieDLaCoeffField_add_deTurckLieDLbCoeffField (I := I) (M := M) g₀
      (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg,
      SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply]
  rw [hsec]
  have hadd := riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 2 2 x
    ((deTurckLieDLaCoeffField (I := I) g₀
      (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg).toSection x)
    ((deTurckLieDLbCoeffField (I := I) g₀
      (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg).toSection x)
  linarith [hadd, ha, hb]

set_option linter.unusedSectionVars false in
/-- Pointwise combined triangle `‖∇ⁱ deTurckLieCoeffField‖² ≤ 2‖∇ⁱ DLa‖² + 2‖∇ⁱ DLb‖²`, from the
committed additive split `deTurckLieDLaCoeffField_add_deTurckLieDLbCoeffField` + `sq_le_two_add`.
Generic over `g₁`, so both combined endpoints reuse it. -/
private theorem normSq_iCG_deTurckLieCoeff_le (g₀ g₁ g_bg : SmoothRiemannianMetric I M) (i : ℕ) :
    ‖iteratedCovGrad (I := I) g₀ 2 2 i (deTurckLieCoeffField (I := I) (M := M) g₀ g₁ g_bg)‖ ^ 2 ≤
      2 * ‖iteratedCovGrad (I := I) g₀ 2 2 i (deTurckLieDLaCoeffField (I := I) g₀ g₁ g_bg)‖ ^ 2
      + 2 * ‖iteratedCovGrad (I := I) g₀ 2 2 i (deTurckLieDLbCoeffField (I := I) g₀ g₁ g_bg)‖ ^ 2 := by
  have hgrad : iteratedCovGrad (I := I) g₀ 2 2 i (deTurckLieCoeffField (I := I) (M := M) g₀ g₁ g_bg)
      = iteratedCovGrad (I := I) g₀ 2 2 i (deTurckLieDLaCoeffField (I := I) g₀ g₁ g_bg)
        + iteratedCovGrad (I := I) g₀ 2 2 i (deTurckLieDLbCoeffField (I := I) g₀ g₁ g_bg) := by
    rw [← deTurckLieDLaCoeffField_add_deTurckLieDLbCoeffField (I := I) (M := M) g₀ g₁ g_bg,
      iteratedCovGrad_add]
  rw [hgrad]
  refine le_trans (sq_le_two_add
    ‖iteratedCovGrad (I := I) g₀ 2 2 i (deTurckLieDLaCoeffField (I := I) g₀ g₁ g_bg)
      + iteratedCovGrad (I := I) g₀ 2 2 i (deTurckLieDLbCoeffField (I := I) g₀ g₁ g_bg)‖
    ‖iteratedCovGrad (I := I) g₀ 2 2 i (deTurckLieDLaCoeffField (I := I) g₀ g₁ g_bg)‖
    ‖iteratedCovGrad (I := I) g₀ 2 2 i (deTurckLieDLbCoeffField (I := I) g₀ g₁ g_bg)‖
    (‖iteratedCovGrad (I := I) g₀ 2 2 i (deTurckLieDLaCoeffField (I := I) g₀ g₁ g_bg)‖ ^ 2)
    (‖iteratedCovGrad (I := I) g₀ 2 2 i (deTurckLieDLbCoeffField (I := I) g₀ g₁ g_bg)‖ ^ 2)
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    (norm_add_le _ _) (le_refl _) (le_refl _)) (le_of_eq (by ring))

set_option linter.unusedVariables false in
/-- **`realizedFam` per-order top-separated jet-L2 bound** for the full DeTurck-Lie coefficient field
`deTurckLieCoeffField = deTurckLieDLaCoeffField + deTurckLieDLbCoeffField`.  Combines the DLa and DLb
field endpoints by the pointwise triangle; `Ktop = 2·(Ktop_DLa + Ktop_DLb)` stays `R`-free, single
combined `Kc`.  This CLOSES the `deTurckLieCoeffField` constituent. -/
theorem deTurckLieCoeffField_realizedFam_jetL2_perOrder_topSeparated
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Ktop : ℝ, 0 ≤ Ktop ∧ ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
        ∀ (i : ℕ), i ≤ a →
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
              (deTurckLieCoeffField (I := I) (M := M) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)‖ ^ 2 ≤
            Ktop * (‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T‖ ^ 2 +
              ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T'‖ ^ 2) +
            Kc i * (1 + ∑ j ∈ Finset.range (i + 3),
              (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) := by
  obtain ⟨Ktop_a, hKtop_a_nn, Kc_a, hKc_a_nn, ha⟩ :=
    deTurckLieDLaCoeffField_realizedFam_jetL2_perOrder_topSeparated (I := I) (M := M) g₀ g_bg a
      ha_super hR hδ₀
  obtain ⟨Ktop_b, hKtop_b_nn, Kc_b, hKc_b_nn, hb⟩ :=
    deTurckLieDLbCoeffField_realizedFam_jetL2_perOrder_topSeparated (I := I) (M := M) g₀ g_bg a
      ha_super hR hδ₀
  refine ⟨2 * (Ktop_a + Ktop_b), by linarith [hKtop_a_nn, hKtop_b_nn],
    fun i => 2 * (Kc_a i + Kc_b i),
    fun i => by linarith [hKc_a_nn i, hKc_b_nn i], ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball s hs i hi
  have ha_i := ha T T' hδ_le hδ hδ'_le hδ' hTball hT'ball s hs i hi
  have hb_i := hb T T' hδ_le hδ hδ'_le hδ' hTball hT'ball s hs i hi
  refine le_trans (normSq_iCG_deTurckLieCoeff_le (I := I) (M := M) g₀
    (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg i) ?_
  have h1 : 2 * ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (deTurckLieDLaCoeffField (I := I) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)‖ ^ 2 ≤
      2 * (Ktop_a * (‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T‖ ^ 2 +
          ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T'‖ ^ 2) +
        Kc_a i * (1 + ∑ j ∈ Finset.range (i + 3),
          (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
            ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2))) :=
    mul_le_mul_of_nonneg_left ha_i (by norm_num)
  have h2 : 2 * ‖iteratedCovGrad (I := I) g₀ 2 2 i
        (deTurckLieDLbCoeffField (I := I) g₀
          (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)‖ ^ 2 ≤
      2 * (Ktop_b * (‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T‖ ^ 2 +
          ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T'‖ ^ 2) +
        Kc_b i * (1 + ∑ j ∈ Finset.range (i + 3),
          (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
            ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2))) :=
    mul_le_mul_of_nonneg_left hb_i (by norm_num)
  refine le_trans (add_le_add h1 h2) (le_of_eq ?_)
  ring

set_option linter.unusedVariables false in
/-- **Summed** `realizedFam` top-separated jet-L2 bound for the full DeTurck-Lie coefficient field.
Both windows `a+3`, `Ktop = 2·(Ktop_DLa + Ktop_DLb)` `R`-free, single combined `Kc`. -/
theorem deTurckLieCoeffField_realizedFam_jetL2_summed_topSeparated
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Ktop : ℝ, 0 ≤ Ktop ∧ ∃ Kc : ℝ, 0 ≤ Kc ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
          ∑ i ∈ Finset.range (a + 1),
              ‖iteratedCovGrad (I := I) g₀ 2 2 i
                (deTurckLieCoeffField (I := I) (M := M) g₀
                  (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)‖ ^ 2 ≤
            Ktop * (∑ j ∈ Finset.range (a + 3),
                (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
                  ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) +
            Kc * (1 + ∑ j ∈ Finset.range (a + 3),
                (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
                  ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) := by
  obtain ⟨Ktop_a, hKtop_a_nn, Kc_a, hKc_a_nn, ha⟩ :=
    deTurckLieDLaCoeffField_realizedFam_jetL2_summed_topSeparated (I := I) (M := M) g₀ g_bg a
      ha_super hR hδ₀
  obtain ⟨Ktop_b, hKtop_b_nn, Kc_b, hKc_b_nn, hb⟩ :=
    deTurckLieDLbCoeffField_realizedFam_jetL2_summed_topSeparated (I := I) (M := M) g₀ g_bg a
      ha_super hR hδ₀
  refine ⟨2 * (Ktop_a + Ktop_b), by linarith [hKtop_a_nn, hKtop_b_nn],
    2 * (Kc_a + Kc_b), by linarith [hKc_a_nn, hKc_b_nn], ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball s hs
  have ha_s := ha T T' hδ_le hδ hδ'_le hδ' hTball hT'ball s hs
  have hb_s := hb T T' hδ_le hδ hδ'_le hδ' hTball hT'ball s hs
  have htri_sum : ∑ i ∈ Finset.range (a + 1),
        ‖iteratedCovGrad (I := I) g₀ 2 2 i
          (deTurckLieCoeffField (I := I) (M := M) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)‖ ^ 2 ≤
      2 * (∑ i ∈ Finset.range (a + 1),
          ‖iteratedCovGrad (I := I) g₀ 2 2 i
            (deTurckLieDLaCoeffField (I := I) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)‖ ^ 2)
        + 2 * (∑ i ∈ Finset.range (a + 1),
            ‖iteratedCovGrad (I := I) g₀ 2 2 i
              (deTurckLieDLbCoeffField (I := I) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg)‖ ^ 2) := by
    have hstep := Finset.sum_le_sum (fun i (_ : i ∈ Finset.range (a + 1)) =>
      normSq_iCG_deTurckLieCoeff_le (I := I) (M := M) g₀
        (realizedFam (I := I) g₀ T T' hδ hδ' s) g_bg i)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hstep
    exact hstep
  refine le_trans htri_sum ?_
  have h1 := mul_le_mul_of_nonneg_left ha_s (show (0 : ℝ) ≤ 2 by norm_num)
  have h2 := mul_le_mul_of_nonneg_left hb_s (show (0 : ℝ) ≤ 2 by norm_num)
  refine le_trans (add_le_add h1 h2) (le_of_eq ?_)
  ring

end DifferentialGeometry.Integral.Connection

end
