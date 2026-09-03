import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.LieCorrection.TameBounds
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorFieldApplicationDropIteratedGrid
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection

noncomputable section


open Bundle Manifold DifferentialGeometry.Tensor0SBundle ContinuousLinearMap
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.Analysis.Spectral

open LieCorrectionZeroCore
open DifferentialGeometry.Integral.L2

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M]
    [SigmaCompactSpace M] in
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
  rw [sub_apply]
  simp only [slotInsertEndoCc_toSection]
  rw [show ((A - B) x) = A x - B x from by
    rw [ContMDiffSection.coe_sub]
    rfl]
  rw [slotInsertEndoFib_sub_left, sub_apply]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M]
    [SigmaCompactSpace M] in
private lemma rsDomDomCongrSection_sub (g₀ : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 2)) (X Y : SmoothCcTensor g₀ 2 2) :
    rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 σ (X - Y) =
      rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 σ X -
        rsDomDomCongrSection (I := I) (M := M) g₀ 2 2 σ Y := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  change tensorRSDomDomCongr σ ((X - Y).toSection x) =
    tensorRSDomDomCongr σ (X.toSection x) - tensorRSDomDomCongr σ (Y.toSection x)
  rw [SmoothCcTensor.toSection_sub]
  rfl

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M]
    [SigmaCompactSpace M] in
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
  rw [sub_apply, reindexCoeffFibGen_apply, reindexCoeffFibGen_apply,
    reindexCoeffFibGen_apply, sub_apply]

omit [I.Boundaryless] [SigmaCompactSpace M] in
theorem lieCorrectionZeroNEndoSec_sub_insert_eq_lieCorrectionZeroCdVField_sub
    (g₀ g₁ gB : SmoothRiemannianMetric I M) :
    endoSlotZeroCcTensor (I := I) (M := M) g₀ 0
        (lieCorrectionZeroNEndoSec (I := I) (M := M) g₀ g₁ gB -
          lieCorrectionZeroNEndoSec (I := I) (M := M) g₀ g₁ g₀) =
      lieCorrectionZeroCdVField (I := I) (M := M) g₀ g₁ g₀ -
        lieCorrectionZeroCdVField (I := I) (M := M) g₀ g₁ gB := by
  rw [endoSlotZeroCcTensor_sub (I := I) (M := M) g₀ 0,
    lieCorrectionZerob_NEndoIns_decomp (I := I) (M := M) g₀ g₁ gB,
    lieCorrectionZerob_NEndoIns_decomp (I := I) (M := M) g₀ g₁ g₀]
  abel

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] in
theorem lieCorrectionZeroInsertionField_sub_eq_nEndoInsert
    (g₀ g₁ gB : SmoothRiemannianMetric I M) :
    lieCorrectionZeroInsertionField (I := I) (M := M) g₀ g₁ gB -
        lieCorrectionZeroInsertionField (I := I) (M := M) g₀ g₁ g₀ =
      endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
          (lieCorrectionZeroNEndoSec (I := I) (M := M) g₀ g₁ gB -
            lieCorrectionZeroNEndoSec (I := I) (M := M) g₀ g₁ g₀)
        + reindexCoeffGen (I := I) (M := M) g₀ 2 2
            (rsDomDomCongrSection (I := I) (M := M) g₀ 2 2
              (Equiv.swap (0 : Fin 2) 1)
              (endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
                (lieCorrectionZeroNEndoSec (I := I) (M := M) g₀ g₁ gB -
                  lieCorrectionZeroNEndoSec (I := I) (M := M) g₀ g₁ g₀)))
            (Equiv.swap (0 : Fin 2) 1) := by
  rw [endoSlotZeroCcTensor_sub (I := I) (M := M) g₀ 1,
    rsDomDomCongrSection_sub (I := I) (M := M) g₀ (Equiv.swap (0 : Fin 2) 1),
    reindexCoeffGen_sub (I := I) (M := M) g₀]
  change (_ + _) - (_ + _) = _
  abel

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [I.Boundaryless] in
theorem lieCorrectionZeroVFlat_sub_eq_trace_comp_kappa_sub
    (g₀ g₁ gB : SmoothRiemannianMetric I M) :
    lieCorrectionZeroVFlat (I := I) (M := M) g₀ g₁ g₀ -
        lieCorrectionZeroVFlat (I := I) (M := M) g₀ g₁ gB =
      ccOperatorFieldComp (I := I) (M := M) g₀ 0 3 1
        (lieCorrectionZeroPureDT (I := I) (M := M) g₀ g₁ 1)
        (lieCorrectionZeroKappa (I := I) (M := M) g₀ g₁ g₀ -
          lieCorrectionZeroKappa (I := I) (M := M) g₀ g₁ gB) := by
  rw [ccOperatorFieldComp_sub_right]
  rfl

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [I.Boundaryless] in
theorem lieCorrectionZeroIVField_sub_eq_trace_comp_slotExtend_vflat_sub
    (g₀ g₁ gB : SmoothRiemannianMetric I M) :
    lieCorrectionZeroIVField (I := I) (M := M) g₀ g₁ g₀ -
        lieCorrectionZeroIVField (I := I) (M := M) g₀ g₁ gB =
      ccOperatorFieldComp (I := I) (M := M) g₀ 2 3 1
        (lieCorrectionZeroTr (I := I) (M := M) g₀ g₁ 1 lieCorrectionZeroIVPerm)
        (slotExtendIter (I := I) (M := M) g₀ 0 1 2
          (lieCorrectionZeroVFlat (I := I) (M := M) g₀ g₁ g₀ -
            lieCorrectionZeroVFlat (I := I) (M := M) g₀ g₁ gB)) := by
  rw [slotExtendIter_sub, ccOperatorFieldComp_sub_right]
  rfl

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [I.Boundaryless] in
theorem lieCorrectionZeroCdVField_sub_eq_comp_connectionDifference
    (g₀ g₁ gB : SmoothRiemannianMetric I M) :
    lieCorrectionZeroCdVField (I := I) (M := M) g₀ g₁ g₀ -
        lieCorrectionZeroCdVField (I := I) (M := M) g₀ g₁ gB =
      ccOperatorFieldComp (I := I) (M := M) g₀ 1 2 1
        (lieCorrectionZeroIVField (I := I) (M := M) g₀ g₁ g₀ -
          lieCorrectionZeroIVField (I := I) (M := M) g₀ g₁ gB)
        (connectionDifferenceSection (I := I) g₁ g₀) := by
  rw [operatorFieldComposition_sub_left]
  rfl

end DifferentialGeometry.Analysis.Spectral

end
