import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.DeTurckLieKernelL2JetBoundLoweredRepresentation
open DifferentialGeometry.Tensor.Auxiliary
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection

noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set Filter Topology Bundle Manifold DifferentialGeometry.Tensor0SBundle ContinuousLinearMap
open scoped ENNReal NNReal BigOperators Manifold ContDiff

namespace DifferentialGeometry.Analysis.Sobolev

open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
  (connDiffCovDerivBiContrFib dLaBiContrFib_contMDiff deTurckLieDLbFib deTurckLieDLbFib_contMDiff
    deTurckLieFib deTurckLieCoeffField deTurckLieCoeffField_toSection
    deTurckConnDiffCovDeriv connDiff_pairing_mdiffAt connDiffCovDerivOp dLaCovKernel_apply_extend)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
  (realizedFam convexPerturbation realizedFam_inner_of_mem convexPerturbation_gFibreOpBound_abs
    abs_convex_smallConstant_lt_one realizedSmallSet)
open DifferentialGeometry.Analysis.Laplacian
  (metric_inner_self_nonneg metric_inner_cauchy_schwarz_sq)
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
  (covGrad connDiff_gFibreNorm_le_iteratedCovGrad_of_lt_one dLaBiContrFibFixedFrame_toModel)
open DifferentialGeometry.Geometry.Curvature
  (exists_covDerivConnDiff_gQuadratic_le_of_jetEnvelope
    abs_tensor_one_three_flat_eval_le_fibreNorm_mul_sqrt)
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
  (g0FlatCLM cotangentToDual_g0FlatCLM g0FlatCLM_apply)

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

section DLaGridBrick

open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Spectral.DeTurck
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma connDiffSection_eq_armSlotEndoCc_zero_dla (g₀ gc : SmoothRiemannianMetric I M) :
    connDiffSection (I := I) gc g₀ =
      armSlotEndoCc (I := I) (M := M) g₀ 0 (dLaConnArmPt (I := I) (M := M) g₀ gc) := by
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
          (dLaConnArmPt (I := I) (M := M) g₀ gc)).toSection x) om) =
      bilinearSlotInsertCLM (I := I) (M := M) 0 x (dLaConnArmPt (I := I) (M := M) g₀ gc x) om
      from rfl]
  rw [armSlotFib_apply_eval (I := I) (M := M) 0 x
    (dLaConnArmPt (I := I) (M := M) g₀ gc x) om v]
  rw [slotInsertEndoFib_apply_eval]
  rw [show (Function.update (Matrix.vecTail (fun k : Fin 2 => (v k : E))) 0
        (dLaConnArmPt (I := I) (M := M) g₀ gc x (v 0)
          (Matrix.vecTail (fun k : Fin 2 => (v k : E)) 0))) =
      (fun _ : Fin 1 => (show E from
        PDE.DeTurck.connDiff (I := I) gc g₀ x (v 0) (v 1))) from by
    funext k
    rw [show k = (0 : Fin 1) from Subsingleton.elim k 0]
    rw [Function.update_self]
    rfl]
  rw [show ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
        (connDiffSection (I := I) gc g₀).toSection x) om) =
      connDiffPairing (I := I) gc g₀ x om from rfl]
  change connDiffPairing (I := I) gc g₀ x om v = _
  rw [connDiffPairing_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M]
    in
private lemma armSlotEndoCc_one_eq_reindex_slotExtend_dla (g₀ : SmoothRiemannianMetric I M)
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
        bilinearSlotInsertCLM (I := I) (M := M) 1 x (Arm x) D from rfl]
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
          tensorRS_domDomCongr (finRotate 3).symm
            ((slotExtend (I := I) (M := M) g₀ 1 2
              (armSlotEndoCc (I := I) (M := M) g₀ 0 Arm)).toSection x)) D') w := by
    have h1 : ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
        (reindexCoeffGen (I := I) (M := M) g₀ 2 3
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 3 (finRotate 3).symm
            (slotExtend (I := I) (M := M) g₀ 1 2 (armSlotEndoCc (I := I) (M := M) g₀ 0 Arm)))
          (Equiv.swap (0 : Fin 2) 1)).toSection x) D) =
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
          tensorRS_domDomCongr (finRotate 3).symm
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
        tensorRS_domDomCongr (finRotate 3).symm
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
        (bilinearSlotInsertCLM (I := I) (M := M) 0 x (Arm x)
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
      (bilinearSlotInsertCLM (I := I) (M := M) 0 x (Arm x)
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

private lemma rfns_iteratedCovGrad_armSlotPass_connArm_le_dla
    (g₀ gc : SmoothRiemannianMetric I M) (j : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 2 (3 + j) x
        ((iteratedCovGrad (I := I) g₀ 2 3 j
          (armSlotEndoPassZeroCc (I := I) (M := M) g₀
            (dLaConnArmPt (I := I) (M := M) g₀ gc))).toSection x) ≤
      (Module.finrank ℝ E : ℝ) *
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 1 2 j (connDiffSection (I := I) gc g₀)).toSection x) := by
  rw [riemannianFiberNormSq_iteratedCovGrad_armSlotEndoPassZeroCc_eq (I := I) (M := M) g₀
    (dLaConnArmPt (I := I) (M := M) g₀ gc) j x]
  rw [armSlotEndoCc_one_eq_reindex_slotExtend_dla (I := I) (M := M) g₀
    (dLaConnArmPt (I := I) (M := M) g₀ gc)]
  rw [rfns_iteratedCovGrad_rsDomDomCongr_both_eq (I := I) (M := M) g₀ 2 3
    (Equiv.swap (0 : Fin 2) 1) (finRotate 3).symm
    (slotExtend (I := I) (M := M) g₀ 1 2
      (armSlotEndoCc (I := I) (M := M) g₀ 0 (dLaConnArmPt (I := I) (M := M) g₀ gc))) j x]
  refine le_trans (rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 1 2
    (armSlotEndoCc (I := I) (M := M) g₀ 0 (dLaConnArmPt (I := I) (M := M) g₀ gc)) j x) ?_
  rw [← connDiffSection_eq_armSlotEndoCc_zero_dla (I := I) (M := M) g₀ gc]

lemma dLaQuad_tower_of_factors (g₀ ga gb : SmoothRiemannianMetric I M)
    (j : ℕ) (x : M) (b : ℕ → ℝ) (hb : ∀ l, 0 ≤ b l)
    (Ba Bb : ℕ → ℝ) (hBa_nn : ∀ i, 0 ≤ Ba i) (hBb_nn : ∀ l, 0 ≤ Bb l)
    (harm : ∀ i, i ≤ j →
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 2 i (connDiffSection (I := I) ga g₀)).toSection x) ≤
      Ba i * antidiagonalTupleGridPartialSum b (i + 2))
    (hin : ∀ l, l ≤ j →
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + l) x
        ((iteratedCovGrad (I := I) g₀ 1 2 l (connDiffSection (I := I) gb g₀)).toSection x) ≤
      Bb l * antidiagonalTupleGridPartialSum b (l + 2)) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + j) x
        ((iteratedCovGrad (I := I) g₀ 1 3 j
          (dLaQuadCc (I := I) (M := M) g₀ ga gb)).toSection x) ≤
      (diagonalGridGrowthFactor (E := E) j * ∑ i ∈ Finset.range (j + 1),
        (Module.finrank ℝ E : ℝ) * Ba i *
          ∑ l ∈ Finset.range (j + 1 - i), Bb l * antidiagonalTuplePairCount (i + 2) (l + 2)) *
        antidiagonalTupleGridPartialSum b (j + 3) := by
  have hWnn : 0 ≤ antidiagonalTupleGridPartialSum b (j + 3) := dLaGridWin_nonneg b hb (j + 3)
  have hfr_nn : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
  refine le_trans
    (riemannianFiberNormSq_iteratedCovGrad_ccTensorCompose_diagonalProductGrid_leftFactor_le
    (I := I) (M := M) g₀ j 1 2 3
    (armSlotEndoPassZeroCc (I := I) (M := M) g₀ (dLaConnArmPt (I := I) (M := M) g₀ ga))
    (connDiffSection (I := I) gb g₀) x) ?_
  have hcell : ∀ i ∈ Finset.range (j + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (3 + i) x
          ((iteratedCovGrad (I := I) g₀ 2 3 i
            (armSlotEndoPassZeroCc (I := I) (M := M) g₀
              (dLaConnArmPt (I := I) (M := M) g₀ ga))).toSection x) *
        ∑ l ∈ Finset.range (j + 1 - i),
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + l) x
            ((iteratedCovGrad (I := I) g₀ 1 2 l
              (connDiffSection (I := I) gb g₀)).toSection x) ≤
      ((Module.finrank ℝ E : ℝ) * Ba i *
        ∑ l ∈ Finset.range (j + 1 - i), Bb l * antidiagonalTuplePairCount (i + 2) (l + 2)) *
        antidiagonalTupleGridPartialSum b (j + 3) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hi_le : i ≤ j := by omega
    have hA1 : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (3 + i) x
        ((iteratedCovGrad (I := I) g₀ 2 3 i
          (armSlotEndoPassZeroCc (I := I) (M := M) g₀
            (dLaConnArmPt (I := I) (M := M) g₀ ga))).toSection x) ≤
        (Module.finrank ℝ E : ℝ) * (Ba i * antidiagonalTupleGridPartialSum b (i + 2)) := by
      refine le_trans (rfns_iteratedCovGrad_armSlotPass_connArm_le_dla
        (I := I) (M := M) g₀ ga i x) ?_
      exact mul_le_mul_of_nonneg_left (harm i hi_le) hfr_nn
    have hA2 : (∑ l ∈ Finset.range (j + 1 - i),
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + l) x
          ((iteratedCovGrad (I := I) g₀ 1 2 l
            (connDiffSection (I := I) gb g₀)).toSection x)) ≤
        ∑ l ∈ Finset.range (j + 1 - i), Bb l * antidiagonalTupleGridPartialSum b (l + 2) := by
      refine Finset.sum_le_sum fun l hl => ?_
      rw [Finset.mem_range] at hl
      exact hin l (by omega)
    have hsum_nn : 0 ≤ ∑ l ∈ Finset.range (j + 1 - i),
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + l) x
          ((iteratedCovGrad (I := I) g₀ 1 2 l
            (connDiffSection (I := I) gb g₀)).toSection x) :=
      Finset.sum_nonneg fun l _ =>
        riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 (2 + l) x _
    have hA1_rhs_nn : 0 ≤ (Module.finrank ℝ E : ℝ) *
      (Ba i * antidiagonalTupleGridPartialSum b (i + 2)) :=
      mul_nonneg hfr_nn (mul_nonneg (hBa_nn i) (dLaGridWin_nonneg b hb (i + 2)))
    refine le_trans (mul_le_mul hA1 hA2 hsum_nn hA1_rhs_nn) ?_
    rw [Finset.mul_sum]
    rw [show ((Module.finrank ℝ E : ℝ) * Ba i *
        ∑ l ∈ Finset.range (j + 1 - i), Bb l * antidiagonalTuplePairCount (i + 2) (l + 2)) *
        antidiagonalTupleGridPartialSum b (j + 3) =
        ∑ l ∈ Finset.range (j + 1 - i),
          ((Module.finrank ℝ E : ℝ) * Ba i * (Bb l * antidiagonalTuplePairCount (i + 2) (l + 2))) *
            antidiagonalTupleGridPartialSum b (j + 3) from by
      rw [Finset.mul_sum, Finset.sum_mul]]
    refine Finset.sum_le_sum fun l hl => ?_
    rw [Finset.mem_range] at hl
    have hpair : antidiagonalTupleGridPartialSum b (i + 2) * antidiagonalTupleGridPartialSum b
      (l + 2) ≤
        antidiagonalTuplePairCount (i + 2) (l + 2) * antidiagonalTupleGridPartialSum b (j + 3) :=
      dLaGridWin_mul_le b hb (i + 2) (l + 2) (j + 3) (by omega)
    calc (Module.finrank ℝ E : ℝ) * (Ba i * antidiagonalTupleGridPartialSum b (i + 2)) *
          (Bb l * antidiagonalTupleGridPartialSum b (l + 2))
        = ((Module.finrank ℝ E : ℝ) * Ba i * Bb l) *
            (antidiagonalTupleGridPartialSum b (i + 2) * antidiagonalTupleGridPartialSum b (l + 2))
              := by ring
      _ ≤ ((Module.finrank ℝ E : ℝ) * Ba i * Bb l) *
            (antidiagonalTuplePairCount (i + 2) (l + 2) * antidiagonalTupleGridPartialSum b
              (j + 3)) := by
          refine mul_le_mul_of_nonneg_left hpair ?_
          exact mul_nonneg (mul_nonneg hfr_nn (hBa_nn i)) (hBb_nn l)
      _ = (Module.finrank ℝ E : ℝ) * Ba i * (Bb l * antidiagonalTuplePairCount (i + 2) (l + 2)) *
            antidiagonalTupleGridPartialSum b (j + 3) := by ring
  calc diagonalGridGrowthFactor (E := E) j *
        ∑ i ∈ Finset.range (j + 1),
          riemannianFiberNormSq (I := I) (M := M) g₀ 2 (3 + i) x
              ((iteratedCovGrad (I := I) g₀ 2 3 i
                (armSlotEndoPassZeroCc (I := I) (M := M) g₀
                  (dLaConnArmPt (I := I) (M := M) g₀ ga))).toSection x) *
            ∑ l ∈ Finset.range (j + 1 - i),
              riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + l) x
                ((iteratedCovGrad (I := I) g₀ 1 2 l
                  (connDiffSection (I := I) gb g₀)).toSection x)
      ≤ diagonalGridGrowthFactor (E := E) j *
          ∑ i ∈ Finset.range (j + 1),
            ((Module.finrank ℝ E : ℝ) * Ba i *
              ∑ l ∈ Finset.range (j + 1 - i), Bb l * antidiagonalTuplePairCount (i + 2) (l + 2)) *
              antidiagonalTupleGridPartialSum b (j + 3) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hcell) (appCcGdiag_nonneg (E := E) j)
    _ = (diagonalGridGrowthFactor (E := E) j * ∑ i ∈ Finset.range (j + 1),
          (Module.finrank ℝ E : ℝ) * Ba i *
            ∑ l ∈ Finset.range (j + 1 - i), Bb l * antidiagonalTuplePairCount (i + 2) (l + 2)) *
          antidiagonalTupleGridPartialSum b (j + 3) := by
        rw [← Finset.sum_mul, ← mul_assoc]

private theorem exists_rfns_dLaKernelRaised_tgrid (g₀ g_bg : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T)
          δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
            ((iteratedCovGrad (I := I) g₀ 1 3 i
              (dLaKernelRaisedCc (I := I) (M := M) g₀ g₁ g_bg)).toSection x) ≤
          C i * antidiagonalTupleGridPartialSum
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x)) (i + 3) := by
  classical
  obtain ⟨CA, hCA_nn, hCA⟩ := exists_rfns_iteratedCovGrad_connDiffSection_tgrid_dla
    (I := I) (M := M) g₀ hδ₀
  obtain ⟨cbg, hcbg_nn, hcbg⟩ := exists_fixedField_rfns_jet_dla (I := I) (M := M) g₀ 1 3
    (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g_bg g₀))
  obtain ⟨cc, hcc_nn, hcc⟩ := exists_fixedField_rfns_jet_dla (I := I) (M := M) g₀ 1 2
    (connDiffSection (I := I) g_bg g₀)
  set CQ1 : ℕ → ℝ := fun j => diagonalGridGrowthFactor (E := E) j * ∑ i' ∈ Finset.range (j + 1),
    (Module.finrank ℝ E : ℝ) * CA i' *
      ∑ l ∈ Finset.range (j + 1 - i'), CA l * antidiagonalTuplePairCount (i' + 2) (l + 2) with
        hCQ1_def
  set CQ2 : ℕ → ℝ := fun j => diagonalGridGrowthFactor (E := E) j * ∑ i' ∈ Finset.range (j + 1),
    (Module.finrank ℝ E : ℝ) * cc i' *
      ∑ l ∈ Finset.range (j + 1 - i'), CA l * antidiagonalTuplePairCount (i' + 2) (l + 2) with
        hCQ2_def
  set CQ3 : ℕ → ℝ := fun j => diagonalGridGrowthFactor (E := E) j * ∑ i' ∈ Finset.range (j + 1),
    (Module.finrank ℝ E : ℝ) * CA i' *
      ∑ l ∈ Finset.range (j + 1 - i'), cc l * antidiagonalTuplePairCount (i' + 2) (l + 2) with
        hCQ3_def
  have hCQ1_nn : ∀ j, 0 ≤ CQ1 j := by
    intro j
    refine mul_nonneg (appCcGdiag_nonneg (E := E) j) (Finset.sum_nonneg fun i' _ => ?_)
    refine mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hCA_nn i'))
      (Finset.sum_nonneg fun l _ => mul_nonneg (hCA_nn l) (dLaPairCount_nonneg _ _))
  have hCQ2_nn : ∀ j, 0 ≤ CQ2 j := by
    intro j
    refine mul_nonneg (appCcGdiag_nonneg (E := E) j) (Finset.sum_nonneg fun i' _ => ?_)
    refine mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hcc_nn i'))
      (Finset.sum_nonneg fun l _ => mul_nonneg (hCA_nn l) (dLaPairCount_nonneg _ _))
  have hCQ3_nn : ∀ j, 0 ≤ CQ3 j := by
    intro j
    refine mul_nonneg (appCcGdiag_nonneg (E := E) j) (Finset.sum_nonneg fun i' _ => ?_)
    refine mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hCA_nn i'))
      (Finset.sum_nonneg fun l _ => mul_nonneg (hcc_nn l) (dLaPairCount_nonneg _ _))
  refine ⟨fun i => 2 * (2 * (2 * (2 * (2 * (2 * (2 * CA (i + 1) + 2 * cbg i) + 2 * CQ1 i)
      + 2 * CQ2 i) + 2 * CQ1 i) + 2 * CQ3 i) + 2 * CQ1 i) + 2 * CQ3 i,
    fun i => by
      have h1 := hCA_nn (i + 1)
      have h2 := hcbg_nn i
      have h3 := hCQ1_nn i
      have h4 := hCQ2_nn i
      have h5 := hCQ3_nn i
      positivity, ?_⟩
  intro g₁ T htie δ hδ_le hδ0 hbound i x
  set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
    ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x) with hb_def
  have hb : ∀ l, 0 ≤ b l :=
    fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
  set W : ℝ := antidiagonalTupleGridPartialSum b (i + 3) with hW_def
  have hW_nn : 0 ≤ W := dLaGridWin_nonneg b hb (i + 3)
  have hW_ge1 : 1 ≤ W := one_le_dLaGridWin b hb (by omega)
  have harm : ∀ i', i' ≤ i →
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i') x
        ((iteratedCovGrad (I := I) g₀ 1 2 i' (connDiffSection (I := I) g₁ g₀)).toSection x) ≤
      CA i' * antidiagonalTupleGridPartialSum b (i' + 2) :=
    fun i' _ => hCA g₁ T htie hδ_le hδ0 hbound i' x
  have hfix : ∀ i', i' ≤ i →
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + i') x
        ((iteratedCovGrad (I := I) g₀ 1 2 i' (connDiffSection (I := I) g_bg g₀)).toSection x) ≤
      cc i' * antidiagonalTupleGridPartialSum b (i' + 2) := by
    intro i' _
    refine le_trans (hcc i' x) ?_
    have h1 : (1 : ℝ) ≤ antidiagonalTupleGridPartialSum b (i' + 2) := one_le_dLaGridWin b hb
      (by omega)
    nlinarith [hcc_nn i']
  have hQ1 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
      ((iteratedCovGrad (I := I) g₀ 1 3 i
        (dLaQuadCc (I := I) (M := M) g₀ g₁ g₁)).toSection x) ≤ CQ1 i * W :=
    dLaQuad_tower_of_factors (I := I) (M := M) g₀ g₁ g₁ i x b hb CA CA hCA_nn hCA_nn harm harm
  have hQ2 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
      ((iteratedCovGrad (I := I) g₀ 1 3 i
        (dLaQuadCc (I := I) (M := M) g₀ g_bg g₁)).toSection x) ≤ CQ2 i * W :=
    dLaQuad_tower_of_factors (I := I) (M := M) g₀ g_bg g₁ i x b hb cc CA hcc_nn hCA_nn hfix harm
  have hQ3 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
      ((iteratedCovGrad (I := I) g₀ 1 3 i
        (dLaQuadCc (I := I) (M := M) g₀ g₁ g_bg)).toSection x) ≤ CQ3 i * W :=
    dLaQuad_tower_of_factors (I := I) (M := M) g₀ g₁ g_bg i x b hb CA cc hCA_nn hcc_nn harm hfix
  have hrs_eq : ∀ (σ : Equiv.Perm (Fin 3)) (F : SmoothCcTensor g₀ 1 3),
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 3 i
          (rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 σ F)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 3 i F).toSection x) := by
    intro σ F
    exact riemannianFiberNormSq_iteratedCovGrad_rs_eq_of_section_domDomCongr (I := I) (M := M) g₀ 1
      3 σ F
      (rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 σ F)
      (fun y d => by
        rw [rsDomDomCongrSection_toSection, toModel_rsDomDomCongr_apply]) i x
  have hA1 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
      ((iteratedCovGrad (I := I) g₀ 1 3 i
        (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀))).toSection x) ≤
      CA (i + 1) * W := by
    rw [rfns_iteratedCovGrad_covGrad_comm_rs (I := I) (M := M) g₀ 1 2 i
      (connDiffSection (I := I) g₁ g₀) x]
    exact hCA g₁ T htie hδ_le hδ0 hbound (i + 1) x
  have hA2 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
      ((iteratedCovGrad (I := I) g₀ 1 3 i
        (covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g_bg g₀))).toSection x) ≤
      cbg i * W := by
    refine le_trans (hcbg i x) ?_
    nlinarith [hcbg_nn i]
  set A1 := covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g₁ g₀) with hA1_def
  set A2 := covGrad (I := I) (M := M) g₀ 1 2 (connDiffSection (I := I) g_bg g₀) with hA2_def
  set Q11 := dLaQuadCc (I := I) (M := M) g₀ g₁ g₁ with hQ11_def
  set Qbg1 := dLaQuadCc (I := I) (M := M) g₀ g_bg g₁ with hQbg1_def
  set Q1bg := dLaQuadCc (I := I) (M := M) g₀ g₁ g_bg with hQ1bg_def
  set P1 := rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (Equiv.swap (0 : Fin 3) 2) Q11
    with hP1_def
  set P2 := rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (Equiv.swap (0 : Fin 3) 2) Q1bg
    with hP2_def
  set P3 := rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (finRotate 3) Q11 with hP3_def
  set P4 := rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (finRotate 3) Q1bg with hP4_def
  have hP1_le : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
      ((iteratedCovGrad (I := I) g₀ 1 3 i P1).toSection x) ≤ CQ1 i * W :=
    le_of_eq_of_le (hrs_eq (Equiv.swap (0 : Fin 3) 2) Q11) hQ1
  have hP2_le : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
      ((iteratedCovGrad (I := I) g₀ 1 3 i P2).toSection x) ≤ CQ3 i * W :=
    le_of_eq_of_le (hrs_eq (Equiv.swap (0 : Fin 3) 2) Q1bg) hQ3
  have hP3_le : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
      ((iteratedCovGrad (I := I) g₀ 1 3 i P3).toSection x) ≤ CQ1 i * W :=
    le_of_eq_of_le (hrs_eq (finRotate 3) Q11) hQ1
  have hP4_le : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
      ((iteratedCovGrad (I := I) g₀ 1 3 i P4).toSection x) ≤ CQ3 i * W :=
    le_of_eq_of_le (hrs_eq (finRotate 3) Q1bg) hQ3
  have t1 := rfns_iCG_sub_le_dla (I := I) (M := M) g₀ 1 3 i A1 A2 x
  have t2 := rfns_iCG_add_le_dla (I := I) (M := M) g₀ 1 3 i (A1 - A2) Q11 x
  have t3 := rfns_iCG_sub_le_dla (I := I) (M := M) g₀ 1 3 i (A1 - A2 + Q11) Qbg1 x
  have t4 := rfns_iCG_sub_le_dla (I := I) (M := M) g₀ 1 3 i (A1 - A2 + Q11 - Qbg1) P1 x
  have t5 := rfns_iCG_add_le_dla (I := I) (M := M) g₀ 1 3 i (A1 - A2 + Q11 - Qbg1 - P1) P2 x
  have t6 := rfns_iCG_sub_le_dla (I := I) (M := M) g₀ 1 3 i
    (A1 - A2 + Q11 - Qbg1 - P1 + P2) P3 x
  have t7 := rfns_iCG_add_le_dla (I := I) (M := M) g₀ 1 3 i
    (A1 - A2 + Q11 - Qbg1 - P1 + P2 - P3) P4 x
  have hKK : dLaKernelRaisedCc (I := I) (M := M) g₀ g₁ g_bg =
      A1 - A2 + Q11 - Qbg1 - P1 + P2 - P3 + P4 := rfl
  rw [hKK]
  linarith [t1, t2, t3, t4, t5, t6, t7, hA1, hA2, hQ1, hQ2, hQ3,
    hP1_le, hP2_le, hP3_le, hP4_le]

theorem exists_rfns_dLaLowered_tgrid (g₀ g_bg : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T)
          δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 4 i
              (dLaLoweredCc (I := I) (M := M) g₀ g₁ g_bg)).toSection x) ≤
          C i * antidiagonalTupleGridPartialSum
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x)) (i + 3) := by
  obtain ⟨C, hC_nn, hC⟩ := exists_rfns_dLaKernelRaised_tgrid (I := I) (M := M) g₀ g_bg hδ₀
  refine ⟨C, hC_nn, ?_⟩
  intro g₁ T htie δ hδ_le hδ0 hbound i x
  have hbridge : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
      ((iteratedCovGrad (I := I) g₀ 0 4 i
        (dLaLoweredCc (I := I) (M := M) g₀ g₁ g_bg)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 3 i
          (dLaKernelRaisedCc (I := I) (M := M) g₀ g₁ g_bg)).toSection x) := by
    have h := riemannianFiberNormSq_iteratedCovGrad_cometricRaiseSlot0Field_eq (I := I) (M := M) g₀
      2
      (dLaLoweredCc (I := I) (M := M) g₀ g₁ g_bg) i x
    rw [dLaLoweredCc_raise_repr (I := I) (M := M) g₀ g₁ g_bg] at h
    exact h.symm
  rw [hbridge]
  exact hC g₁ T htie hδ_le hδ0 hbound i x

omit [NeZero (Module.finrank ℝ E)] in
lemma rfns_iCG_symmS_le_dla (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (j : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j (ccTensor02Symm (I := I) (M := M) g₀ T)).toSection x) ≤
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
        ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x) := by
  have hsec : (iteratedCovGrad (I := I) g₀ 0 2 j (ccTensor02Symm (I := I) (M := M) g₀ T)).toSection
    x =
      (1 / 2 : ℝ) • (iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x +
        (1 / 2 : ℝ) • (iteratedCovGrad (I := I) g₀ 0 2 j
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) T)).toSection x := by
    rw [iteratedCovGrad_symmS_eq (I := I) (M := M) g₀ T j, SmoothCcTensor.toSection_add]
    rw [show (((1 / 2 : ℝ) • iteratedCovGrad (I := I) g₀ 0 2 j T).toSection +
        ((1 / 2 : ℝ) • iteratedCovGrad (I := I) g₀ 0 2 j
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) T)).toSection) x =
        ((1 / 2 : ℝ) • iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x +
          ((1 / 2 : ℝ) • iteratedCovGrad (I := I) g₀ 0 2 j
            (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) T)).toSection x from rfl]
    rw [SmoothCcTensor.toSection_smul, SmoothCcTensor.toSection_smul]
    rfl
  rw [hsec]
  refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 (2 + j) x _ _) ?_
  rw [rfns_smul_dla (I := I) (M := M) g₀ 0 (2 + j) x, rfns_smul_dla (I := I) (M := M) g₀ 0 (2 + j)
    x]
  have hperm := riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
    (Equiv.swap (0 : Fin 2) 1) T j x
  rw [hperm]
  ring_nf
  nlinarith [riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + j) x
    ((iteratedCovGrad (I := I) g₀ 0 2 j T).toSection x)]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] in
lemma rfns_symmS_zero_le_dla (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
        ((ccTensor02Symm (I := I) (M := M) g₀ T).toSection x) ≤
      (Module.finrank ℝ E : ℝ) ^ 2 * δ ^ 2 := by
  classical
  obtain ⟨n, e, bse, hn, hbse, horth, _hpars, _hrepr, _hsum⟩ :=
    tangent_orthonormalBasis_witness (I := I) (M := M) g₀ x
  have hnE : n = Module.finrank ℝ E := by rw [hn]; rfl
  rw [riemannianFiberNormSq_eq_sum_componentSq_of_basis (I := I) (M := M) g₀ 0 2 x
    ((ccTensor02Symm (I := I) (M := M) g₀ T).toSection x) e bse hnE hbse horth]
  have hcof : coframeS (I := I) (M := M) g₀ x 0 e = fun _ : Fin 0 → Fin n =>
      unitTensor (I := I) (M := M) x := by
    funext K
    apply Tensor0SSpace.toModel_injective
    apply ContinuousMultilinearMap.ext
    intro v
    rw [show Tensor0SSpace.toModel (coframeS (I := I) (M := M) g₀ x 0 e K) v =
        coframeS (I := I) (M := M) g₀ x 0 e K v from rfl]
    rw [coframeS_apply (I := I) (M := M) g₀ x 0 e K v]
    rw [show Tensor0SSpace.toModel (unitTensor (I := I) (M := M) x) v =
        unitTensor (I := I) (M := M) x v from rfl]
    rw [Fin.prod_univ_zero]
    rw [unitTensor, Tensor0SSpace.ofModel]
    rfl
  have hcomp : ∀ (K : Fin 0 → Fin n) (J : Fin 2 → Fin n),
      (fiberNormSqComponent (I := I) (M := M) g₀ x 0 2
        ((ccTensor02Symm (I := I) (M := M) g₀ T).toSection x) n e K J) ^ 2 ≤ δ ^ 2 := by
    intro K J
    have hval : fiberNormSqComponent (I := I) (M := M) g₀ x 0 2
        ((ccTensor02Symm (I := I) (M := M) g₀ T).toSection x) n e K J =
        ccTensorBilinSymm (I := I) g₀ T x (e (J 0)) (e (J 1)) := by
      rw [show fiberNormSqComponent (I := I) (M := M) g₀ x 0 2
          ((ccTensor02Symm (I := I) (M := M) g₀ T).toSection x) n e K J =
          Tensor0SSpace.toModel
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
              (ccTensor02Symm (I := I) (M := M) g₀ T).toSection x)
              (coframeS (I := I) (M := M) g₀ x 0 e K))
            (fun i : Fin 2 => (e (J i) : E)) from rfl]
      rw [hcof]
      rw [show Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
            (ccTensor02Symm (I := I) (M := M) g₀ T).toSection x)
            (unitTensor (I := I) (M := M) x))
          (fun i : Fin 2 => (e (J i) : E)) =
          unitModel (I := I) (M := M) g₀ 2 (ccTensor02Symm (I := I) (M := M) g₀ T) x
            ![e (J 0), e (J 1)] from by
        rw [unitModel]
        refine congrArg _ ?_
        funext k
        fin_cases k <;> rfl]
      rw [unitModel_eq_ccTensorBilin_dla (I := I) (M := M) g₀
        (ccTensor02Symm (I := I) (M := M) g₀ T) x (e (J 0)) (e (J 1))]
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
          ((ccTensor02Symm (I := I) (M := M) g₀ T).toSection x) n e K J) ^ 2)
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

lemma rfns_iCG_slotInsert3_dLaPerturb_le (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (j : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 4 (4 + j) x
        ((iteratedCovGrad (I := I) g₀ 4 4 j
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ 3
            (dLaPerturbSharpEndoField (I := I) (M := M) g₀ T))).toSection x) ≤
      (Module.finrank ℝ E : ℝ) ^ 3 *
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + j) x
          ((iteratedCovGrad (I := I) g₀ 0 2 j (ccTensor02Symm (I := I) (M := M) g₀ T)).toSection
            x) := by
  refine le_trans (rfns_iteratedCovGrad_slotInsertEndoCc_le_endo (I := I) (M := M) g₀ 3
    (dLaPerturbSharpEndoField (I := I) (M := M) g₀ T) j x) ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [dLaSlotInsert_perturbSharp_eq_raise_symmS (I := I) (M := M) g₀ T]
  rw [riemannianFiberNormSq_iteratedCovGrad_cometricRaiseSlot0Field_eq (I := I) (M := M) g₀ 0
    (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1)
      (ccTensor02Symm (I := I) (M := M) g₀ T)) j x]
  rw [riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
    (Equiv.swap (0 : Fin 2) 1) (ccTensor02Symm (I := I) (M := M) g₀ T) j x]

theorem exists_rfns_dLaSym_tgrid (g₀ g_bg : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T)
          δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
            ((iteratedCovGrad (I := I) g₀ 0 4 i
              (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
                  (dLaLoweredG1Cc (I := I) (M := M) g₀ T g₁ g_bg) +
                dLaLoweredG1Cc (I := I) (M := M) g₀ T g₁ g_bg)).toSection x) ≤
          C i * antidiagonalTupleGridPartialSum
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x)) (i + 3) := by
  classical
  obtain ⟨CL, hCL_nn, hCL⟩ := exists_rfns_dLaLowered_tgrid (I := I) (M := M) g₀ g_bg hδ₀
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfr_def
  have hfr_nn : 0 ≤ fr := Nat.cast_nonneg _
  set CP : ℕ → ℝ := fun i' => fr ^ 3 * (fr ^ 2 * δ₀ ^ 2 + 1) with hCP_def
  have hCP_nn : ∀ i', 0 ≤ CP i' := fun i' => by rw [hCP_def]; positivity
  set CLT : ℕ → ℝ := fun i => diagonalGridGrowthFactor (E := E) i * ∑ i' ∈ Finset.range (i + 1),
    CP i' * ∑ l ∈ Finset.range (i + 1 - i'), CL l * antidiagonalTuplePairCount (i' + 1) (l + 3) with
      hCLT_def
  have hCLT_nn : ∀ i, 0 ≤ CLT i := by
    intro i
    refine mul_nonneg (appCcGdiag_nonneg (E := E) i) (Finset.sum_nonneg fun i' _ => ?_)
    exact mul_nonneg (hCP_nn i') (Finset.sum_nonneg fun l _ =>
      mul_nonneg (hCL_nn l) (dLaPairCount_nonneg _ _))
  refine ⟨fun i => 4 * (2 * CL i + 2 * CLT i),
    fun i => by have := hCL_nn i; have := hCLT_nn i; positivity, ?_⟩
  intro g₁ T htie δ hδ_le hδ0 hbound i x
  set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
    ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x) with hb_def
  have hb : ∀ l, 0 ≤ b l :=
    fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
  set W : ℝ := antidiagonalTupleGridPartialSum b (i + 3) with hW_def
  have hW_nn : 0 ≤ W := dLaGridWin_nonneg b hb (i + 3)
  have hδ₀_nn : 0 ≤ δ₀ := le_trans hδ0 hδ_le
  have hPfac : ∀ i', i' ≤ i →
      riemannianFiberNormSq (I := I) (M := M) g₀ 4 (4 + i') x
        ((iteratedCovGrad (I := I) g₀ 4 4 i'
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ 3
            (dLaPerturbSharpEndoField (I := I) (M := M) g₀ T))).toSection x) ≤
      CP i' * antidiagonalTupleGridPartialSum b (i' + 1) := by
    intro i' _
    refine le_trans (rfns_iCG_slotInsert3_dLaPerturb_le (I := I) (M := M) g₀ T i' x) ?_
    have hfr3_nn : (0 : ℝ) ≤ fr ^ 3 := by positivity
    match i' with
    | 0 =>
        have h0 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 0) x
            ((iteratedCovGrad (I := I) g₀ 0 2 0
              (ccTensor02Symm (I := I) (M := M) g₀ T)).toSection x) ≤ fr ^ 2 * δ ^ 2 := by
          rw [iteratedCovGrad_zero]
          exact rfns_symmS_zero_le_dla (I := I) (M := M) g₀ T hδ0 hbound x
        have hδsq : δ ^ 2 ≤ δ₀ ^ 2 := by nlinarith [hδ0, hδ_le]
        have hwin1 : (1 : ℝ) ≤ antidiagonalTupleGridPartialSum b (0 + 1) := one_le_dLaGridWin b hb
          (by omega)
        have hle1 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 0) x
            ((iteratedCovGrad (I := I) g₀ 0 2 0
              (ccTensor02Symm (I := I) (M := M) g₀ T)).toSection x) ≤ fr ^ 2 * δ₀ ^ 2 := by
          refine le_trans h0 (mul_le_mul_of_nonneg_left hδsq (by positivity))
        calc fr ^ 3 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + 0) x
              ((iteratedCovGrad (I := I) g₀ 0 2 0
                (ccTensor02Symm (I := I) (M := M) g₀ T)).toSection x)
            ≤ fr ^ 3 * (fr ^ 2 * δ₀ ^ 2) := mul_le_mul_of_nonneg_left hle1 hfr3_nn
          _ ≤ fr ^ 3 * (fr ^ 2 * δ₀ ^ 2 + 1) := by
              refine mul_le_mul_of_nonneg_left ?_ hfr3_nn
              linarith
          _ ≤ (fr ^ 3 * (fr ^ 2 * δ₀ ^ 2 + 1)) * antidiagonalTupleGridPartialSum b (0 + 1) := by
              refine le_mul_of_one_le_right ?_ hwin1
              positivity
          _ = CP 0 * antidiagonalTupleGridPartialSum b (0 + 1) := by rw [hCP_def]
    | (m + 1) =>
        have h1 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (m + 1)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (m + 1)
              (ccTensor02Symm (I := I) (M := M) g₀ T)).toSection x) ≤ b (m + 1) :=
          rfns_iCG_symmS_le_dla (I := I) (M := M) g₀ T (m + 1) x
        have h2 : b (m + 1) ≤ Combinatorics.antidiagonalTupleGrid b (m + 1) :=
          single_le_grid_dla b hb (m + 1) (by omega)
        have h3 : Combinatorics.antidiagonalTupleGrid b (m + 1) ≤
            antidiagonalTupleGridPartialSum b ((m + 1) + 1) := grid_le_dLaGridWin b hb (by omega)
        have hfac1 : (1 : ℝ) ≤ fr ^ 2 * δ₀ ^ 2 + 1 :=
          le_add_of_nonneg_left (by positivity)
        have hwin_nn : 0 ≤ antidiagonalTupleGridPartialSum b ((m + 1) + 1) := dLaGridWin_nonneg b hb
          _
        calc fr ^ 3 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (m + 1)) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (m + 1)
                (ccTensor02Symm (I := I) (M := M) g₀ T)).toSection x)
            ≤ fr ^ 3 * antidiagonalTupleGridPartialSum b ((m + 1) + 1) := by
              refine mul_le_mul_of_nonneg_left ?_ hfr3_nn
              exact le_trans h1 (le_trans h2 h3)
          _ ≤ CP (m + 1) * antidiagonalTupleGridPartialSum b ((m + 1) + 1) := by
              rw [hCP_def]
              refine mul_le_mul_of_nonneg_right ?_ hwin_nn
              calc fr ^ 3 = fr ^ 3 * 1 := by ring
                _ ≤ fr ^ 3 * (fr ^ 2 * δ₀ ^ 2 + 1) :=
                    mul_le_mul_of_nonneg_left hfac1 hfr3_nn
  have hLT : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
      ((iteratedCovGrad (I := I) g₀ 0 4 i
        (dLaLoweredPerturbCc (I := I) (M := M) g₀ T g₁ g_bg)).toSection x) ≤
      CLT i * W := by
    refine le_trans
      (riemannianFiberNormSq_iteratedCovGrad_ccTensorCompose_diagonalProductGrid_leftFactor_le
      (I := I) (M := M) g₀ i 0 4 4
      (endoSlotZeroCcTensor (I := I) (M := M) g₀ 3
        (dLaPerturbSharpEndoField (I := I) (M := M) g₀ T))
      (dLaLoweredCc (I := I) (M := M) g₀ g₁ g_bg) x) ?_
    have hcell : ∀ i' ∈ Finset.range (i + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 4 (4 + i') x
            ((iteratedCovGrad (I := I) g₀ 4 4 i'
              (endoSlotZeroCcTensor (I := I) (M := M) g₀ 3
                (dLaPerturbSharpEndoField (I := I) (M := M) g₀ T))).toSection x) *
          ∑ l ∈ Finset.range (i + 1 - i'),
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 4 l
                (dLaLoweredCc (I := I) (M := M) g₀ g₁ g_bg)).toSection x) ≤
        (CP i' * ∑ l ∈ Finset.range (i + 1 - i'), CL l * antidiagonalTuplePairCount (i' + 1)
          (l + 3)) * W := by
      intro i' hi'
      rw [Finset.mem_range] at hi'
      have hi'_le : i' ≤ i := by omega
      have hA1 := hPfac i' hi'_le
      have hA2 : (∑ l ∈ Finset.range (i + 1 - i'),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 4 l
              (dLaLoweredCc (I := I) (M := M) g₀ g₁ g_bg)).toSection x)) ≤
          ∑ l ∈ Finset.range (i + 1 - i'), CL l * antidiagonalTupleGridPartialSum b (l + 3) :=
        Finset.sum_le_sum fun l _ => hCL g₁ T htie hδ_le hδ0 hbound l x
      have hsum_nn : 0 ≤ ∑ l ∈ Finset.range (i + 1 - i'),
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
            ((iteratedCovGrad (I := I) g₀ 0 4 l
              (dLaLoweredCc (I := I) (M := M) g₀ g₁ g_bg)).toSection x) :=
        Finset.sum_nonneg fun l _ =>
          riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (4 + l) x _
      have hA1_rhs_nn : 0 ≤ CP i' * antidiagonalTupleGridPartialSum b (i' + 1) :=
        mul_nonneg (hCP_nn i') (dLaGridWin_nonneg b hb (i' + 1))
      refine le_trans (mul_le_mul hA1 hA2 hsum_nn hA1_rhs_nn) ?_
      rw [Finset.mul_sum]
      rw [show (CP i' * ∑ l ∈ Finset.range (i + 1 - i'),
          CL l * antidiagonalTuplePairCount (i' + 1) (l + 3)) * W =
          ∑ l ∈ Finset.range (i + 1 - i'),
            (CP i' * (CL l * antidiagonalTuplePairCount (i' + 1) (l + 3))) * W from by
        rw [Finset.mul_sum, Finset.sum_mul]]
      refine Finset.sum_le_sum fun l hl => ?_
      rw [Finset.mem_range] at hl
      have hpair : antidiagonalTupleGridPartialSum b (i' + 1) * antidiagonalTupleGridPartialSum b
        (l + 3) ≤
          antidiagonalTuplePairCount (i' + 1) (l + 3) * antidiagonalTupleGridPartialSum b (i + 3) :=
        dLaGridWin_mul_le b hb (i' + 1) (l + 3) (i + 3) (by omega)
      calc CP i' * antidiagonalTupleGridPartialSum b (i' + 1) *
             (CL l * antidiagonalTupleGridPartialSum b (l + 3))
          = (CP i' * CL l) * (antidiagonalTupleGridPartialSum b (i' + 1) *
            antidiagonalTupleGridPartialSum b (l + 3)) := by ring
        _ ≤ (CP i' * CL l) * (antidiagonalTuplePairCount (i' + 1) (l + 3) *
          antidiagonalTupleGridPartialSum b (i + 3)) := by
            refine mul_le_mul_of_nonneg_left hpair ?_
            exact mul_nonneg (hCP_nn i') (hCL_nn l)
        _ = (CP i' * (CL l * antidiagonalTuplePairCount (i' + 1) (l + 3))) * W := by
            rw [hW_def]
            ring
    calc diagonalGridGrowthFactor (E := E) i *
          ∑ i' ∈ Finset.range (i + 1),
            riemannianFiberNormSq (I := I) (M := M) g₀ 4 (4 + i') x
                ((iteratedCovGrad (I := I) g₀ 4 4 i'
                  (endoSlotZeroCcTensor (I := I) (M := M) g₀ 3
                    (dLaPerturbSharpEndoField (I := I) (M := M) g₀ T))).toSection x) *
              ∑ l ∈ Finset.range (i + 1 - i'),
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + l) x
                  ((iteratedCovGrad (I := I) g₀ 0 4 l
                    (dLaLoweredCc (I := I) (M := M) g₀ g₁ g_bg)).toSection x)
        ≤ diagonalGridGrowthFactor (E := E) i *
            ∑ i' ∈ Finset.range (i + 1),
              (CP i' * ∑ l ∈ Finset.range (i + 1 - i'),
                CL l * antidiagonalTuplePairCount (i' + 1) (l + 3)) * W :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum hcell) (appCcGdiag_nonneg (E := E) i)
      _ = CLT i * W := by
          rw [hCLT_def, ← Finset.sum_mul, ← mul_assoc]
  have hL0 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
      ((iteratedCovGrad (I := I) g₀ 0 4 i
        (dLaLoweredCc (I := I) (M := M) g₀ g₁ g_bg)).toSection x) ≤ CL i * W :=
    hCL g₁ T htie hδ_le hδ0 hbound i x
  have hLG1 : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
      ((iteratedCovGrad (I := I) g₀ 0 4 i
        (dLaLoweredG1Cc (I := I) (M := M) g₀ T g₁ g_bg)).toSection x) ≤
      2 * (CL i * W) + 2 * (CLT i * W) := by
    refine le_trans (rfns_iCG_add_le_dla (I := I) (M := M) g₀ 0 4 i
      (dLaLoweredCc (I := I) (M := M) g₀ g₁ g_bg)
      (dLaLoweredPerturbCc (I := I) (M := M) g₀ T g₁ g_bg) x) ?_
    linarith [hL0, hLT]
  have hperm : riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
      ((iteratedCovGrad (I := I) g₀ 0 4 i
        (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
          (dLaLoweredG1Cc (I := I) (M := M) g₀ T g₁ g_bg))).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
        ((iteratedCovGrad (I := I) g₀ 0 4 i
          (dLaLoweredG1Cc (I := I) (M := M) g₀ T g₁ g_bg)).toSection x) :=
    riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀
      (Equiv.swap (0 : Fin 4) 1) (dLaLoweredG1Cc (I := I) (M := M) g₀ T g₁ g_bg) i x
  refine le_trans (rfns_iCG_add_le_dla (I := I) (M := M) g₀ 0 4 i
    (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
      (dLaLoweredG1Cc (I := I) (M := M) g₀ T g₁ g_bg))
    (dLaLoweredG1Cc (I := I) (M := M) g₀ T g₁ g_bg) x) ?_
  rw [hperm]
  linarith [hLG1]

end DLaGridBrick

end DifferentialGeometry.Analysis.Sobolev

end
