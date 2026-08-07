import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderTameLipschitzLieCorrectionTensorTransferBounds
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.AppCcDropIteratedGrid
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection

/-!
# Background differences of the zeroth-order DeTurck correction

The vector, insertion, and connection pieces share the same moving trace and
connection passengers.  Their background differences therefore refold into
linear operator-field expressions with the cancellation exposed.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Manifold DifferentialGeometry.Tensor0SBundle ContinuousLinearMap
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.Analysis.Spectral

open LieCorr0Core
open DifferentialGeometry
open DifferentialGeometry.Integral.L2

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M]
    in
private lemma endoSlotZeroCcTensor_sub (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (A B : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)) :
    endoSlotZeroCcTensor (I := I) (M := M) g₀ s (A - B) =
      endoSlotZeroCcTensor (I := I) (M := M) g₀ s A -
        endoSlotZeroCcTensor (I := I) (M := M) g₀ s B := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  rw [show ((endoSlotZeroCcTensor (I := I) (M := M) g₀ s A -
        endoSlotZeroCcTensor (I := I) (M := M) g₀ s B).toSection x) =
      (endoSlotZeroCcTensor (I := I) (M := M) g₀ s A).toSection x -
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ s B).toSection x from by
    rw [SmoothCcTensor.toSection_sub]
    rfl]
  rw [ContinuousLinearMap.sub_apply]
  simp only [slotInsertEndoCc_toSection]
  rw [show ((A - B) x) = A x - B x from by
    rw [ContMDiffSection.coe_sub]
    rfl]
  rw [slotInsertEndoFib_sub_left, ContinuousLinearMap.sub_apply]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M]
    in
private lemma rsDomDomCongrSection_sub (g₀ : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 2)) (X Y : SmoothCcTensor g₀ 2 2) :
    rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 σ (X - Y) =
      rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 σ X -
        rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 σ Y := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun m => ?_)
  have hsub : (X - Y).toSection x = X.toSection x - Y.toSection x := by
    rw [SmoothCcTensor.toSection_sub]
    rfl
  have hsub2 :
      (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 σ X -
          rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 σ Y).toSection x =
        (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 σ X).toSection x -
          (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 σ Y).toSection x := by
    rw [SmoothCcTensor.toSection_sub]
    rfl
  rw [rsDomDomCongrSection_toSection, hsub, hsub2]
  rw [rsDomDomCongrSection_toSection, rsDomDomCongrSection_toSection]
  have hfib : ∀ (y : Tensor0SSpace 2 I x) (w : Fin 2 → TangentSpace I x),
      Tensor0SSpace.toModel y w = (y : Tensor0SSpace 2 I x) w := fun _ _ => rfl
  rw [hfib, hfib]
  rw [rsDomDomCongr_apply_eval (I := I) (M := M) σ (X.toSection x - Y.toSection x) D m]
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      tensorRS_domDomCongr σ (X.toSection x) - tensorRS_domDomCongr σ (Y.toSection x)) D) =
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        tensorRS_domDomCongr σ (X.toSection x)) D -
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        tensorRS_domDomCongr σ (Y.toSection x)) D from rfl]
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
      (X.toSection x - Y.toSection x : TensorRSSpace 2 2 I x)) D) =
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from X.toSection x) D -
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from Y.toSection x) D from rfl]
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        tensorRS_domDomCongr σ (X.toSection x)) D -
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        tensorRS_domDomCongr σ (Y.toSection x)) D : Tensor0SSpace 2 I x) m =
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        tensorRS_domDomCongr σ (X.toSection x)) D : Tensor0SSpace 2 I x) m -
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 2 I x from
        tensorRS_domDomCongr σ (Y.toSection x)) D : Tensor0SSpace 2 I x) m from rfl]
  rw [rsDomDomCongr_apply_eval (I := I) (M := M) σ (X.toSection x) D m]
  rw [rsDomDomCongr_apply_eval (I := I) (M := M) σ (Y.toSection x) D m]
  rfl

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M]
    in
private lemma reindexCoeffGen_sub (g₀ : SmoothRiemannianMetric I M)
    (A B : SmoothCcTensor g₀ 2 2) (ρ : Equiv.Perm (Fin 2)) :
    reindexCoeffGen (I := I) (M := M) g₀ 2 2 (A - B) ρ =
      reindexCoeffGen (I := I) (M := M) g₀ 2 2 A ρ -
        reindexCoeffGen (I := I) (M := M) g₀ 2 2 B ρ := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
    reindexCoeffGen_toSection, reindexCoeffGen_toSection, reindexCoeffGen_toSection,
    SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply]
  apply ContinuousLinearMap.ext
  intro D
  rw [ContinuousLinearMap.sub_apply, reindexCoeffFibGen_apply, reindexCoeffFibGen_apply,
    reindexCoeffFibGen_apply, ContinuousLinearMap.sub_apply]

/-- Inserting the difference of the correction endomorphisms is exactly the
difference of the two connection-after-vector-field operators. -/
theorem lc0NEndoSec_sub_insert_eq_lc0CdVField_sub
    (g₀ g₁ gB : SmoothRiemannianMetric I M) :
    endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
        (lc0NEndoSec (I := I) (M := M) g₀ g₁ gB -
          lc0NEndoSec (I := I) (M := M) g₀ g₁ g₀) =
      lc0CdVField (I := I) (M := M) g₀ g₁ g₀ -
        lc0CdVField (I := I) (M := M) g₀ g₁ gB := by
  rw [endoSlotZeroCcTensor_sub (I := I) (M := M) g₀ 0,
    lc0b_NEndoIns_decomp (I := I) (M := M) g₀ g₁ gB,
    lc0b_NEndoIns_decomp (I := I) (M := M) g₀ g₁ g₀]
  abel

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
/-- The insertion-field background difference is the symmetrized insertion
of the single endomorphism-section difference. -/
theorem lc0InsertField_sub_eq_nEndoInsert
    (g₀ g₁ gB : SmoothRiemannianMetric I M) :
    lc0InsertField (I := I) (M := M) g₀ g₁ gB -
        lc0InsertField (I := I) (M := M) g₀ g₁ g₀ =
      endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
          (lc0NEndoSec (I := I) (M := M) g₀ g₁ gB -
            lc0NEndoSec (I := I) (M := M) g₀ g₁ g₀)
        + reindexCoeffGen (I := I) (M := M) g₀ 2 2
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2
              (Equiv.swap (0 : Fin 2) 1)
              (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
                (lc0NEndoSec (I := I) (M := M) g₀ g₁ gB -
                  lc0NEndoSec (I := I) (M := M) g₀ g₁ g₀)))
            (Equiv.swap (0 : Fin 2) 1) := by
  rw [endoSlotZeroCcTensor_sub (I := I) (M := M) g₀ 1,
    rsDomDomCongrSection_sub (I := I) (M := M) g₀ (Equiv.swap (0 : Fin 2) 1),
    reindexCoeffGen_sub (I := I) (M := M) g₀]
  change (_ + _) - (_ + _) = _
  abel

omit [NeZero (Module.finrank ℝ E)] in
/-- The DeTurck covector background difference is the common moving trace
applied to the lowered-connection background difference. -/
theorem lc0VFlat_sub_eq_trace_comp_kappa_sub
    (g₀ g₁ gB : SmoothRiemannianMetric I M) :
    lc0VFlat (I := I) (M := M) g₀ g₁ g₀ -
        lc0VFlat (I := I) (M := M) g₀ g₁ gB =
      ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 1
        (lc0PureDT (I := I) (M := M) g₀ g₁ 1)
        (lc0Kappa (I := I) (M := M) g₀ g₁ g₀ -
          lc0Kappa (I := I) (M := M) g₀ g₁ gB) := by
  rw [ccOperatorFieldComp_sub_right]
  rfl

omit [NeZero (Module.finrank ℝ E)] in
/-- The vector-insertion background difference is the common moving trace
applied to the slot extension of the DeTurck-covector difference. -/
theorem lc0IVField_sub_eq_trace_comp_slotExtend_vflat_sub
    (g₀ g₁ gB : SmoothRiemannianMetric I M) :
    lc0IVField (I := I) (M := M) g₀ g₁ g₀ -
        lc0IVField (I := I) (M := M) g₀ g₁ gB =
      ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 1
        (lc0Tr (I := I) (M := M) g₀ g₁ 1 lc0IVPerm)
        (slotExtendIter (I := I) (M := M) g₀ 0 1 2
          (lc0VFlat (I := I) (M := M) g₀ g₁ g₀ -
            lc0VFlat (I := I) (M := M) g₀ g₁ gB)) := by
  rw [slotExtendIter_sub, ccOperatorFieldComp_sub_right]
  rfl

omit [NeZero (Module.finrank ℝ E)] in
/-- The connection-after-vector-field background difference is the common
connection-difference passenger acted on by the vector-insertion difference. -/
theorem lc0CdVField_sub_eq_comp_connDiff
    (g₀ g₁ gB : SmoothRiemannianMetric I M) :
    lc0CdVField (I := I) (M := M) g₀ g₁ g₀ -
        lc0CdVField (I := I) (M := M) g₀ g₁ gB =
      ccOperatorFieldComp (I := I) (M := M) g₀ 1 2 1
        (lc0IVField (I := I) (M := M) g₀ g₁ g₀ -
          lc0IVField (I := I) (M := M) g₀ g₁ gB)
        (connDiffSection (I := I) g₁ g₀) := by
  rw [appCcRS_sub_left]
  rfl

end DifferentialGeometry.Analysis.Spectral

end
