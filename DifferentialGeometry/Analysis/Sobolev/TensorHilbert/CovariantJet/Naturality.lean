import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.CovariantJet.Basic
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricPerturbation.CovariantOrderCoefficient.SlotIdentities
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricPerturbation.InverseMetricSlotCoefficient
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorField.Bounds.FiberNormJets
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorField.Algebra.CoefficientReindexing
import Mathlib.Algebra.Order.GroupWithZero.Basic
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifference.RecoveryEndomorphismJetBounds

open DifferentialGeometry.TensorMetric
  (riemannianFiberNormSq)

noncomputable section


open Bundle Manifold MeasureTheory DifferentialGeometry.Tensor0SBundle
open scoped BigOperators Manifold ContDiff

namespace DifferentialGeometry.Analysis.Sobolev

open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor.RSTensor

variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

theorem iteratedCovGrad_slotExtend_norm_sq_le
    (g : SmoothRiemannianMetric I M) (r s i : ℕ)
    (Φ : SmoothCcTensor g r s) :
    ‖iteratedCovGrad (I := I) g (r + 1) (s + 1) i
        (slotExtend (I := I) (M := M) g r s Φ)‖ ^ 2 ≤
      (Module.finrank ℝ E : ℝ) *
        ‖iteratedCovGrad (I := I) g r s i Φ‖ ^ 2 := by
  let F : M → ℝ := fun x => (Module.finrank ℝ E : ℝ) *
    riemannianFiberNormSq (I := I) (M := M) g r (s + i) x
      ((iteratedCovGrad (I := I) g r s i Φ).toSection x)
  have hF : Integrable F (riemannianVolumeMeasure (I := I) (M := M) g) := by
    dsimp only [F]
    exact (integrable_riemannianFiberNormSq_toSection
      (I := I) (M := M) g r (s + i)
      (iteratedCovGrad (I := I) g r s i Φ)).const_mul _
  have hsq := normSq_le_integral_of_pointwise_fiberNormSq_le_rs
    (I := I) (M := M) g (r + 1) ((s + 1) + i)
    (iteratedCovGrad (I := I) g (r + 1) (s + 1) i
      (slotExtend (I := I) (M := M) g r s Φ))
    F hF (fun x =>
      riemannianFiberNormSq_iteratedCovGrad_slotExtend_le
        (I := I) (M := M) g r s Φ i x)
  have hint : (∫ x,
      riemannianFiberNormSq (I := I) (M := M) g r (s + i) x
        ((iteratedCovGrad (I := I) g r s i Φ).toSection x)
      ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      ‖iteratedCovGrad (I := I) g r s i Φ‖ ^ 2 := by
    rw [SmoothCcTensor.norm_def,
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs
        (I := I) (M := M) g r (s + i)]
  dsimp only [F] at hsq
  rw [integral_const_mul, hint] at hsq
  exact hsq

theorem covariantJetNormSq_slotExtend_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ) {m : ℕ}
    (Φ : SmoothCcTensor g r s) :
    covariantJetNormSq (I := I) (M := M) g m
        (slotExtend (I := I) (M := M) g r s Φ) ≤
      (Module.finrank ℝ E : ℝ) *
        covariantJetNormSq (I := I) (M := M) g m Φ := by
  unfold covariantJetNormSq
  calc
    ∑ i ∈ Finset.range (m + 1),
        ‖iteratedCovGrad (I := I) g (r + 1) (s + 1) i
          (slotExtend (I := I) (M := M) g r s Φ)‖ ^ 2 ≤
      ∑ i ∈ Finset.range (m + 1), (Module.finrank ℝ E : ℝ) *
        ‖iteratedCovGrad (I := I) g r s i Φ‖ ^ 2 :=
      Finset.sum_le_sum fun i _ =>
        iteratedCovGrad_slotExtend_norm_sq_le (I := I) (M := M) g r s i Φ
    _ = (Module.finrank ℝ E : ℝ) *
        ∑ i ∈ Finset.range (m + 1),
          ‖iteratedCovGrad (I := I) g r s i Φ‖ ^ 2 := by
      rw [Finset.mul_sum]

omit [NeZero (Module.finrank ℝ E)] in
theorem covariantJetNormSq_reindexCoefficientInputSlots
    (g : SmoothRiemannianMetric I M) {r s m : ℕ}
    (R : SmoothCcTensor g r s) (σ : Equiv.Perm (Fin r)) :
    covariantJetNormSq (I := I) (M := M) g m
        (reindexCoefficientInputSlots (I := I) (M := M) g r s R σ) =
      covariantJetNormSq (I := I) (M := M) g m R := by
  unfold covariantJetNormSq
  apply Finset.sum_congr rfl
  intro q _
  rw [SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs,
    SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x =>
    riemannianFiberNormSq_iteratedCovGrad_reindexCoefficientInputSlots_eq
      (I := I) (M := M) g r s R σ q x

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
    [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem reindexCoefficientInputSlots_sub
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (A B : SmoothCcTensor g r s) (σ : Equiv.Perm (Fin r)) :
    reindexCoefficientInputSlots (I := I) (M := M) g r s (A - B) σ =
      reindexCoefficientInputSlots (I := I) (M := M) g r s A σ -
        reindexCoefficientInputSlots (I := I) (M := M) g r s B σ := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
    reindexCoefficientInputSlots_toSection, reindexCoefficientInputSlots_toSection,
    reindexCoefficientInputSlots_toSection,
    SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply]
  apply ContinuousLinearMap.ext
  intro D
  rw [sub_apply, reindexCoefficientInputSlotsFiber_apply,
    reindexCoefficientInputSlotsFiber_apply, reindexCoefficientInputSlotsFiber_apply,
    sub_apply]

theorem iteratedCovGrad_rsDomDomCongrSection_norm_sq
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (σ : Equiv.Perm (Fin s)) (S : SmoothCcTensor g r s) (i : ℕ) :
    ‖iteratedCovGrad (I := I) g r s i
        (rsDomDomCongrSection (I := I) (M := M) g r s σ S)‖ ^ 2 =
      ‖iteratedCovGrad (I := I) g r s i S‖ ^ 2 := by
  rw [SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs,
    SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  exact riemannianFiberNormSq_iteratedCovGrad_rs_eq_of_section_domDomCongr
    (I := I) (M := M) g r s σ S
      (rsDomDomCongrSection (I := I) (M := M) g r s σ S)
      (fun y d => by
        rw [rsDomDomCongrSection_toSection,
          toModel_rsDomDomCongr_apply]) i x

theorem covariantJetNormSq_rsDomDomCongrSection
    (g : SmoothRiemannianMetric I M) {r s m : ℕ}
    (σ : Equiv.Perm (Fin s)) (S : SmoothCcTensor g r s) :
    covariantJetNormSq (I := I) (M := M) g m
        (rsDomDomCongrSection (I := I) (M := M) g r s σ S) =
      covariantJetNormSq (I := I) (M := M) g m S := by
  unfold covariantJetNormSq
  apply Finset.sum_congr rfl
  intro i _
  exact iteratedCovGrad_rsDomDomCongrSection_norm_sq
    (I := I) (M := M) g σ S i

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
    [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem rsDomDomCongrSection_sub
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (σ : Equiv.Perm (Fin s)) (A B : SmoothCcTensor g r s) :
    rsDomDomCongrSection (I := I) (M := M) g r s σ (A - B) =
      rsDomDomCongrSection (I := I) (M := M) g r s σ A -
        rsDomDomCongrSection (I := I) (M := M) g r s σ B := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  change rsDomDomCongr σ ((A - B).toSection x) =
    rsDomDomCongr σ (A.toSection x) - rsDomDomCongr σ (B.toSection x)
  rw [SmoothCcTensor.toSection_sub]
  rfl

omit [NeZero (Module.finrank ℝ E)] in
theorem covariantJetNormSq_domDomCongrSection
    (g : SmoothRiemannianMetric I M) {s m : ℕ}
    (σ : Equiv.Perm (Fin s)) (S : SmoothCcTensor g 0 s) :
    covariantJetNormSq (I := I) (M := M) g m
        (domDomCongrSection (I := I) g σ S) =
      covariantJetNormSq (I := I) (M := M) g m S := by
  unfold covariantJetNormSq
  apply Finset.sum_congr rfl
  intro q _
  rw [SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs,
    SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x =>
    riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection
      (I := I) (M := M) g σ S q x

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
    [BoundarylessManifold I M] [SigmaCompactSpace M] [T2Space M] in
theorem domDomCongrSection_sub
    (g : SmoothRiemannianMetric I M) {s : ℕ}
    (σ : Equiv.Perm (Fin s)) (A B : SmoothCcTensor g 0 s) :
    domDomCongrSection (I := I) g σ (A - B) =
      domDomCongrSection (I := I) g σ A -
        domDomCongrSection (I := I) g σ B := by
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g
  intro x
  have hsub : ∀ (P Q : SmoothCcTensor g 0 s),
      unitModel (I := I) (M := M) g s (P - Q) x =
        unitModel (I := I) (M := M) g s P x -
          unitModel (I := I) (M := M) g s Q x := by
    intro P Q
    simp only [unitModel]
    rw [SmoothCcTensor.toSection_sub]
    rfl
  rw [domDomCongrSection_unitModel, hsub A B]
  rw [hsub
    (domDomCongrSection (I := I) g σ A)
    (domDomCongrSection (I := I) g σ B)]
  rw [domDomCongrSection_unitModel, domDomCongrSection_unitModel]
  apply ContinuousMultilinearMap.ext
  intro v
  simp only [sub_apply,
    ContinuousMultilinearMap.domDomCongr_apply]

theorem covariantJetNormSq_bilinearSlotInsertionCoefficient_succ_le
    (g : SmoothRiemannianMetric I M) (s : ℕ) {m : ℕ}
    (A : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ]
        (TangentSpace I x →L[ℝ] TangentSpace I x))) :
    covariantJetNormSq (I := I) (M := M) g m
        (bilinearSlotInsertionCoefficient (I := I) (M := M) g (s + 1) A) ≤
      (Module.finrank ℝ E : ℝ) *
        covariantJetNormSq (I := I) (M := M) g m
          (bilinearSlotInsertionCoefficient (I := I) (M := M) g s A) := by
  rw [termSlotEndoCc_succ (I := I) (M := M) g s A,
    covariantJetNormSq_reindexCoefficientInputSlots,
    covariantJetNormSq_rsDomDomCongrSection]
  exact covariantJetNormSq_slotExtend_le
    (I := I) (M := M) g (s + 1) (s + 1 + 1) _

theorem covariantJetNormSq_bilinearSlotInsertionCoefficient_two_le
    (g : SmoothRiemannianMetric I M) {m : ℕ}
    (A : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ]
        (TangentSpace I x →L[ℝ] TangentSpace I x))) :
    covariantJetNormSq (I := I) (M := M) g m
        (bilinearSlotInsertionCoefficient (I := I) (M := M) g 2 A) ≤
      (Module.finrank ℝ E : ℝ) ^ 2 *
        covariantJetNormSq (I := I) (M := M) g m
          (bilinearSlotInsertionCoefficient (I := I) (M := M) g 0 A) := by
  have hfr : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
  calc
    covariantJetNormSq (I := I) (M := M) g m
        (bilinearSlotInsertionCoefficient (I := I) (M := M) g 2 A) ≤
      (Module.finrank ℝ E : ℝ) *
        covariantJetNormSq (I := I) (M := M) g m
          (bilinearSlotInsertionCoefficient (I := I) (M := M) g 1 A) :=
      covariantJetNormSq_bilinearSlotInsertionCoefficient_succ_le
        (I := I) (M := M) g 1 A
    _ ≤ (Module.finrank ℝ E : ℝ) *
        ((Module.finrank ℝ E : ℝ) *
          covariantJetNormSq (I := I) (M := M) g m
            (bilinearSlotInsertionCoefficient (I := I) (M := M) g 0 A)) :=
      mul_le_mul_of_nonneg_left
        (covariantJetNormSq_bilinearSlotInsertionCoefficient_succ_le
          (I := I) (M := M) g 0 A) hfr
    _ = (Module.finrank ℝ E : ℝ) ^ 2 *
        covariantJetNormSq (I := I) (M := M) g m
          (bilinearSlotInsertionCoefficient (I := I) (M := M) g 0 A) := by ring

end DifferentialGeometry.Analysis.Sobolev

section

namespace DifferentialGeometry.Integral.Connection

open DifferentialGeometry.Integral.L2 (SmoothCcTensor)
open DifferentialGeometry.Analysis.Sobolev
  (iteratedCovGrad tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs)
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
  (cometricRaiseSlot0Field riemannianFiberNormSq_iteratedCovGrad_cometricRaiseSlot0Field_eq)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] in
lemma norm_iteratedCovGrad_cometricRaiseSlot0Field_eq (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (W : SmoothCcTensor g₀ 0 (s + 2)) (i : ℕ) :
    ‖iteratedCovGrad (I := I) g₀ 1 (s + 1) i
        (cometricRaiseSlot0Field (I := I) (M := M) g₀ s W)‖ =
      ‖iteratedCovGrad (I := I) g₀ 0 (s + 2) i W‖ := by
  refine (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) (by decide : (2 : ℕ) ≠ 0)).mp ?_
  rw [SmoothCcTensor.norm_def, SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  exact riemannianFiberNormSq_iteratedCovGrad_cometricRaiseSlot0Field_eq (I := I) (M := M) g₀ s W i x

end DifferentialGeometry.Integral.Connection

end

section

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.RicciDeTurckPairing

open DifferentialGeometry.Integral.L2 (SmoothCcTensor)
open DifferentialGeometry.Integral.Measure (riemannianVolumeMeasure)
open DifferentialGeometry.Integral.Connection (norm_iteratedCovGrad_cometricRaiseSlot0Field_eq)
open DifferentialGeometry.Analysis.Elliptic (integrable_riemannianFiberNormSq_toSection)
open DifferentialGeometry.Analysis.Sobolev
  (iteratedCovGrad covariantJetNormSq covariantJetNormSq_slotExtend_le
    normSq_le_integral_of_pointwise_fiberNormSq_le_rs
    riemannianFiberNormSq_iteratedCovGrad_slotInsertEndoCc_le_endo
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs)
open DifferentialGeometry.Analysis.Spectral (slotExtend slotExtendIter)
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (cometricRaiseSlot0Field)
open DifferentialGeometry.Geometry.Connection (slotInsertEndoCc)

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

theorem iteratedCovGrad_slotInsertEndoCc_normSq_le
    (g : SmoothRiemannianMetric I M) (s i : ℕ)
    (Λ : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)) :
    ‖iteratedCovGrad (I := I) g (s + 1) (s + 1) i
        (slotInsertEndoCc (I := I) (M := M) g s Λ)‖ ^ 2 ≤
      (Module.finrank ℝ E : ℝ) ^ s *
        ‖iteratedCovGrad (I := I) g 1 1 i
          (slotInsertEndoCc (I := I) (M := M) g 0 Λ)‖ ^ 2 := by
  let F : M → ℝ := fun x => (Module.finrank ℝ E : ℝ) ^ s *
    riemannianFiberNormSq (I := I) (M := M) g 1 (1 + i) x
      ((iteratedCovGrad (I := I) g 1 1 i
        (slotInsertEndoCc (I := I) (M := M) g 0 Λ)).toSection x)
  have hF : MeasureTheory.Integrable F
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    dsimp only [F]
    exact (integrable_riemannianFiberNormSq_toSection
      (I := I) (M := M) g 1 (1 + i)
      (iteratedCovGrad (I := I) g 1 1 i
        (slotInsertEndoCc (I := I) (M := M) g 0 Λ))).const_mul _
  have hsq := normSq_le_integral_of_pointwise_fiberNormSq_le_rs
    (I := I) (M := M) g (s + 1) ((s + 1) + i)
    (iteratedCovGrad (I := I) g (s + 1) (s + 1) i
      (slotInsertEndoCc (I := I) (M := M) g s Λ))
    F hF (fun x =>
      riemannianFiberNormSq_iteratedCovGrad_slotInsertEndoCc_le_endo
        (I := I) (M := M) g s Λ i x)
  have hint :
      (∫ x, riemannianFiberNormSq (I := I) (M := M) g 1 (1 + i) x
          ((iteratedCovGrad (I := I) g 1 1 i
            (slotInsertEndoCc (I := I) (M := M) g 0 Λ)).toSection x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
        ‖iteratedCovGrad (I := I) g 1 1 i
          (slotInsertEndoCc (I := I) (M := M) g 0 Λ)‖ ^ 2 := by
    rw [SmoothCcTensor.norm_def,
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs]
  dsimp only [F] at hsq
  rw [MeasureTheory.integral_const_mul, hint] at hsq
  exact hsq

theorem covariantJetNormSq_slotInsertEndoCc_le
    (g : SmoothRiemannianMetric I M) (s m : ℕ)
    (Λ : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)) :
    covariantJetNormSq (I := I) (M := M) g m
        (slotInsertEndoCc (I := I) (M := M) g s Λ) ≤
      (Module.finrank ℝ E : ℝ) ^ s *
        covariantJetNormSq (I := I) (M := M) g m
          (slotInsertEndoCc (I := I) (M := M) g 0 Λ) := by
  unfold covariantJetNormSq
  calc
    ∑ i ∈ Finset.range (m + 1),
        ‖iteratedCovGrad (I := I) g (s + 1) (s + 1) i
          (slotInsertEndoCc (I := I) (M := M) g s Λ)‖ ^ 2 ≤
      ∑ i ∈ Finset.range (m + 1), (Module.finrank ℝ E : ℝ) ^ s *
        ‖iteratedCovGrad (I := I) g 1 1 i
          (slotInsertEndoCc (I := I) (M := M) g 0 Λ)‖ ^ 2 :=
      Finset.sum_le_sum fun i _ =>
        iteratedCovGrad_slotInsertEndoCc_normSq_le (I := I) (M := M) g s i Λ
    _ = (Module.finrank ℝ E : ℝ) ^ s *
        ∑ i ∈ Finset.range (m + 1),
          ‖iteratedCovGrad (I := I) g 1 1 i
            (slotInsertEndoCc (I := I) (M := M) g 0 Λ)‖ ^ 2 := by
      rw [Finset.mul_sum]

omit [NeZero (Module.finrank ℝ E)] in
theorem covariantJetNormSq_cometricRaiseSlot0Field
    (g : SmoothRiemannianMetric I M) (s m : ℕ)
    (W : SmoothCcTensor g 0 (s + 2)) :
    covariantJetNormSq (I := I) (M := M) g m
        (cometricRaiseSlot0Field (I := I) (M := M) g s W) =
      covariantJetNormSq (I := I) (M := M) g m W := by
  unfold covariantJetNormSq
  apply Finset.sum_congr rfl
  intro q _
  rw [norm_iteratedCovGrad_cometricRaiseSlot0Field_eq
    (I := I) (M := M) g s W q]

theorem covariantJetNormSq_slotExtendIter_two_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (F : SmoothCcTensor g r s) :
    covariantJetNormSq (I := I) (M := M) g 2
        (slotExtendIter (I := I) (M := M) g r s 2 F) ≤
      (Module.finrank ℝ E : ℝ) ^ 2 *
        covariantJetNormSq (I := I) (M := M) g 2 F := by
  let fr : ℝ := Module.finrank ℝ E
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  simp only [slotExtendIter, Nat.add_zero]
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (slotExtend (I := I) (M := M) g (r + 1) (s + 1)
          (slotExtend (I := I) (M := M) g r s F)) ≤
      fr * covariantJetNormSq (I := I) (M := M) g 2
        (slotExtend (I := I) (M := M) g r s F) :=
      covariantJetNormSq_slotExtend_le (I := I) (M := M) g (r + 1) (s + 1) _
    _ ≤ fr * (fr * covariantJetNormSq (I := I) (M := M) g 2 F) :=
      mul_le_mul_of_nonneg_left
        (covariantJetNormSq_slotExtend_le (I := I) (M := M) g r s F) hfr
    _ = fr ^ 2 * covariantJetNormSq (I := I) (M := M) g 2 F := by ring

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.RicciDeTurckPairing

end
