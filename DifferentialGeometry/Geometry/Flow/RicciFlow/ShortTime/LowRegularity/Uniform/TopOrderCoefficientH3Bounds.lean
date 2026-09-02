import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.AlgebraicCoefficientThirdOrderBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.MixedTensorApplicationThirdOrderBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.CoefficientDeviationThirdOrderBounds
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorFieldFibreNormJet
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureCoefficientDifferenceJetTower.TopOrderSeparatedCurvatureBounds
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureCoefficientDifferenceJetTower.PairTrace
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.RicciTopOrderCoefficientBounds
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.AllOrderGardingConstant
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.H2PointwiseUnif
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Uniform.Morrey

set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory Set DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

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
open DifferentialGeometry.Analysis.Spectral.CurvatureCoefficientDifferenceJetTower
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.PDE.DeTurck.RicciLinearization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem symm_self
    (g : SmoothRiemannianMetric I M) (S : SmoothCcTensor g 0 2)
    (hS : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g S x u v =
        ccTensorBilin (I := I) g S x v u) :
    ccTensor02Symm (I := I) (M := M) g S = S := by
  have hswap :
      domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1) S = S := by
    refine smoothCcTensor_ext_of_unitModel (I := I) (M := M) g fun x => ?_
    rw [domDomCongrSection_unitModel]
    refine ContinuousMultilinearMap.ext fun v => ?_
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    have hv : ∀ u w : TangentSpace I x,
        unitModel (I := I) (M := M) g 2 S x ![u, w] =
          unitModel (I := I) (M := M) g 2 S x ![w, u] := by
      intro u w
      rw [unitModel_eq_ccTensorBilin_local (I := I) (M := M) g S x u w,
        unitModel_eq_ccTensorBilin_local (I := I) (M := M) g S x w u]
      exact hS x u w
    have hveta :
        (fun i => v ((Equiv.swap (0 : Fin 2) 1) i)) = ![v 1, v 0] := by
      funext i
      fin_cases i <;> rfl
    have hveta' : v = ![v 0, v 1] := by
      funext i
      fin_cases i <;> rfl
    rw [hveta]
    conv_rhs => rw [hveta']
    exact hv (v 1) (v 0)
  have htwo : S + S = (2 : ℝ) • S := (two_smul ℝ S).symm
  unfold ccTensor02Symm
  rw [hswap, htwo, smul_smul,
    show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_smul]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem endo_slot_succ_eq
    (g : SmoothRiemannianMetric I M) (q : ℕ)
    (P : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)) :
    endoSlotZeroCcTensor (I := I) (M := M) g (q + 1) P =
      reindexCoeffGen (I := I) (M := M) g (q + 2) (q + 2)
        (rsDomDomCongrSection (I := I) (M := M) g (q + 2) (q + 2)
          (Equiv.swap (0 : Fin (q + 2)) 1)
          (slotExtend (I := I) (M := M) g (q + 1) (q + 1)
            (endoSlotZeroCcTensor (I := I) (M := M) g q P)))
        (Equiv.swap (0 : Fin (q + 2)) 1) := by
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    slotInsertEndoCc_succ_eq_reindex_slotExtend (I := I) (M := M) g q P

omit [SigmaCompactSpace M] in
private theorem endo_slot_succ_pointwise
    (g : SmoothRiemannianMetric I M) (q i : ℕ)
    (P : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x))
    (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g (q + 2) (q + 2 + i) x
        ((iteratedCovGrad (I := I) g (q + 2) (q + 2) i
          (endoSlotZeroCcTensor (I := I) (M := M) g (q + 1) P)).toSection x) ≤
      (Module.finrank ℝ E : ℝ) *
        riemannianFiberNormSq (I := I) (M := M) g (q + 1) (q + 1 + i) x
          ((iteratedCovGrad (I := I) g (q + 1) (q + 1) i
            (endoSlotZeroCcTensor (I := I) (M := M) g q P)).toSection x) := by
  have hA :
      riemannianFiberNormSq (I := I) (M := M) g (q + 2) (q + 2 + i) x
          ((iteratedCovGrad (I := I) g (q + 2) (q + 2) i
            (endoSlotZeroCcTensor (I := I) (M := M) g (q + 1) P)).toSection x) =
        riemannianFiberNormSq (I := I) (M := M) g (q + 2) (q + 2 + i) x
          ((iteratedCovGrad (I := I) g (q + 2) (q + 2) i
            (slotExtend (I := I) (M := M) g (q + 1) (q + 1)
              (endoSlotZeroCcTensor (I := I) (M := M) g q P))).toSection x) := by
    rw [endo_slot_succ_eq (I := I) (M := M) g q P]
    exact riemannianFiberNormSq_iteratedCovGrad_rsDomDomCongr_both_eq (I := I) (M := M) g
      (q + 2) (q + 2) (Equiv.swap (0 : Fin (q + 2)) 1)
      (Equiv.swap (0 : Fin (q + 2)) 1)
      (slotExtend (I := I) (M := M) g (q + 1) (q + 1)
        (endoSlotZeroCcTensor (I := I) (M := M) g q P)) i x
  rw [hA]
  exact riemannianFiberNormSq_iteratedCovGrad_slotExtend_le (I := I) (M := M) g (q + 1) (q + 1)
    (endoSlotZeroCcTensor (I := I) (M := M) g q P) i x

private theorem endo_slot_succ_sq
    (g : SmoothRiemannianMetric I M) (q i : ℕ)
    (P : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)) :
    ‖iteratedCovGrad (I := I) g (q + 2) (q + 2) i
        (endoSlotZeroCcTensor (I := I) (M := M) g (q + 1) P)‖ ^ 2 ≤
      (Module.finrank ℝ E : ℝ) *
        ‖iteratedCovGrad (I := I) g (q + 1) (q + 1) i
          (endoSlotZeroCcTensor (I := I) (M := M) g q P)‖ ^ 2 := by
  classical
  let F : M → ℝ := fun x => (Module.finrank ℝ E : ℝ) *
    riemannianFiberNormSq (I := I) (M := M) g (q + 1) (q + 1 + i) x
      ((iteratedCovGrad (I := I) g (q + 1) (q + 1) i
        (endoSlotZeroCcTensor (I := I) (M := M) g q P)).toSection x)
  have hFint : Integrable F (riemannianVolumeMeasure (I := I) (M := M) g) := by
    dsimp only [F]
    exact (integrable_riemannianFiberNormSq_toSection
      (I := I) (M := M) g (q + 1) (q + 1 + i)
        (iteratedCovGrad (I := I) g (q + 1) (q + 1) i
          (endoSlotZeroCcTensor (I := I) (M := M) g q P))).const_mul _
  have hsq := normSq_le_integral_of_pointwise_fiberNormSq_le_rs
    (I := I) (M := M) g (q + 2) (q + 2 + i)
      (iteratedCovGrad (I := I) g (q + 2) (q + 2) i
        (endoSlotZeroCcTensor (I := I) (M := M) g (q + 1) P)) F hFint
      (endo_slot_succ_pointwise (I := I) (M := M) g q i P)
  have hint :
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g (q + 1) (q + 1 + i) x
          ((iteratedCovGrad (I := I) g (q + 1) (q + 1) i
            (endoSlotZeroCcTensor (I := I) (M := M) g q P)).toSection x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        ‖iteratedCovGrad (I := I) g (q + 1) (q + 1) i
          (endoSlotZeroCcTensor (I := I) (M := M) g q P)‖ ^ 2 := by
    rw [SmoothCcTensor.norm_def,
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs
        (I := I) (M := M) g (q + 1) (q + 1 + i)]
  dsimp only [F] at hsq
  rw [MeasureTheory.integral_const_mul, hint] at hsq
  exact hsq

private theorem endo_slot_succ_jet
    (g : SmoothRiemannianMetric I M) (q n : ℕ)
    (P : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)) :
    (∑ j ∈ Finset.range n,
      ‖iteratedCovGrad (I := I) g (q + 2) (q + 2) j
        (endoSlotZeroCcTensor (I := I) (M := M) g (q + 1) P)‖ ^ 2) ≤
      (Module.finrank ℝ E : ℝ) *
        ∑ j ∈ Finset.range n,
          ‖iteratedCovGrad (I := I) g (q + 1) (q + 1) j
            (endoSlotZeroCcTensor (I := I) (M := M) g q P)‖ ^ 2 := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun j _ =>
    endo_slot_succ_sq (I := I) (M := M) g q j P

omit [SigmaCompactSpace M] in
private theorem endo_slot_three_pointwise
    (g : SmoothRiemannianMetric I M)
    (P : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x))
    (i : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 4 (4 + i) x
        ((iteratedCovGrad (I := I) g 4 4 i
          (endoSlotZeroCcTensor (I := I) (M := M) g 3 P)).toSection x) ≤
      (Module.finrank ℝ E : ℝ) ^ 2 *
        riemannianFiberNormSq (I := I) (M := M) g 2 (2 + i) x
          ((iteratedCovGrad (I := I) g 2 2 i
            (endoSlotZeroCcTensor (I := I) (M := M) g 1 P)).toSection x) := by
  have hfr : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
  calc
    _ ≤ (Module.finrank ℝ E : ℝ) *
        riemannianFiberNormSq (I := I) (M := M) g 3 (3 + i) x
          ((iteratedCovGrad (I := I) g 3 3 i
            (endoSlotZeroCcTensor (I := I) (M := M) g 2 P)).toSection x) :=
      endo_slot_succ_pointwise (I := I) (M := M) g 2 i P x
    _ ≤ (Module.finrank ℝ E : ℝ) *
        ((Module.finrank ℝ E : ℝ) *
          riemannianFiberNormSq (I := I) (M := M) g 2 (2 + i) x
            ((iteratedCovGrad (I := I) g 2 2 i
              (endoSlotZeroCcTensor (I := I) (M := M) g 1 P)).toSection x)) :=
      mul_le_mul_of_nonneg_left
        (endo_slot_succ_pointwise (I := I) (M := M) g 1 i P x) hfr
    _ = _ := by ring

private theorem endo_slot_three_jet
    (g : SmoothRiemannianMetric I M)
    (P : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x))
    (n : ℕ) :
    (∑ j ∈ Finset.range n,
      ‖iteratedCovGrad (I := I) g 4 4 j
        (endoSlotZeroCcTensor (I := I) (M := M) g 3 P)‖ ^ 2) ≤
      (Module.finrank ℝ E : ℝ) ^ 2 *
        ∑ j ∈ Finset.range n,
          ‖iteratedCovGrad (I := I) g 2 2 j
            (endoSlotZeroCcTensor (I := I) (M := M) g 1 P)‖ ^ 2 := by
  have hfr : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
  calc
    _ ≤ (Module.finrank ℝ E : ℝ) *
        ∑ j ∈ Finset.range n,
          ‖iteratedCovGrad (I := I) g 3 3 j
            (endoSlotZeroCcTensor (I := I) (M := M) g 2 P)‖ ^ 2 :=
      endo_slot_succ_jet (I := I) (M := M) g 2 n P
    _ ≤ (Module.finrank ℝ E : ℝ) *
        ((Module.finrank ℝ E : ℝ) *
          ∑ j ∈ Finset.range n,
            ‖iteratedCovGrad (I := I) g 2 2 j
              (endoSlotZeroCcTensor (I := I) (M := M) g 1 P)‖ ^ 2) :=
      mul_le_mul_of_nonneg_left
        (endo_slot_succ_jet (I := I) (M := M) g 1 n P) hfr
    _ = _ := by ring

omit [SigmaCompactSpace M] in
private theorem endo_slot_five_pointwise
    (g : SmoothRiemannianMetric I M)
    (P : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x))
    (i : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 6 (6 + i) x
        ((iteratedCovGrad (I := I) g 6 6 i
          (endoSlotZeroCcTensor (I := I) (M := M) g 5 P)).toSection x) ≤
      (Module.finrank ℝ E : ℝ) ^ 4 *
        riemannianFiberNormSq (I := I) (M := M) g 2 (2 + i) x
          ((iteratedCovGrad (I := I) g 2 2 i
            (endoSlotZeroCcTensor (I := I) (M := M) g 1 P)).toSection x) := by
  have hfr : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
  calc
    _ ≤ (Module.finrank ℝ E : ℝ) *
        riemannianFiberNormSq (I := I) (M := M) g 5 (5 + i) x
          ((iteratedCovGrad (I := I) g 5 5 i
            (endoSlotZeroCcTensor (I := I) (M := M) g 4 P)).toSection x) :=
      endo_slot_succ_pointwise (I := I) (M := M) g 4 i P x
    _ ≤ (Module.finrank ℝ E : ℝ) *
        ((Module.finrank ℝ E : ℝ) *
          riemannianFiberNormSq (I := I) (M := M) g 4 (4 + i) x
            ((iteratedCovGrad (I := I) g 4 4 i
              (endoSlotZeroCcTensor (I := I) (M := M) g 3 P)).toSection x)) :=
      mul_le_mul_of_nonneg_left
        (endo_slot_succ_pointwise (I := I) (M := M) g 3 i P x) hfr
    _ = (Module.finrank ℝ E : ℝ) ^ 2 *
        riemannianFiberNormSq (I := I) (M := M) g 4 (4 + i) x
          ((iteratedCovGrad (I := I) g 4 4 i
            (endoSlotZeroCcTensor (I := I) (M := M) g 3 P)).toSection x) := by
      ring
    _ ≤ (Module.finrank ℝ E : ℝ) ^ 2 *
        ((Module.finrank ℝ E : ℝ) ^ 2 *
          riemannianFiberNormSq (I := I) (M := M) g 2 (2 + i) x
            ((iteratedCovGrad (I := I) g 2 2 i
              (endoSlotZeroCcTensor (I := I) (M := M) g 1 P)).toSection x)) := by
      exact mul_le_mul_of_nonneg_left
        (endo_slot_three_pointwise (I := I) (M := M) g P i x)
        (sq_nonneg _)
    _ = _ := by ring

private theorem endo_slot_five_jet
    (g : SmoothRiemannianMetric I M)
    (P : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x))
    (n : ℕ) :
    (∑ j ∈ Finset.range n,
      ‖iteratedCovGrad (I := I) g 6 6 j
        (endoSlotZeroCcTensor (I := I) (M := M) g 5 P)‖ ^ 2) ≤
      (Module.finrank ℝ E : ℝ) ^ 4 *
        ∑ j ∈ Finset.range n,
          ‖iteratedCovGrad (I := I) g 2 2 j
            (endoSlotZeroCcTensor (I := I) (M := M) g 1 P)‖ ^ 2 := by
  have hfr : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
  calc
    _ ≤ (Module.finrank ℝ E : ℝ) *
        ∑ j ∈ Finset.range n,
          ‖iteratedCovGrad (I := I) g 5 5 j
            (endoSlotZeroCcTensor (I := I) (M := M) g 4 P)‖ ^ 2 :=
      endo_slot_succ_jet (I := I) (M := M) g 4 n P
    _ ≤ (Module.finrank ℝ E : ℝ) *
        ((Module.finrank ℝ E : ℝ) *
          ∑ j ∈ Finset.range n,
            ‖iteratedCovGrad (I := I) g 4 4 j
              (endoSlotZeroCcTensor (I := I) (M := M) g 3 P)‖ ^ 2) :=
      mul_le_mul_of_nonneg_left
        (endo_slot_succ_jet (I := I) (M := M) g 3 n P) hfr
    _ = (Module.finrank ℝ E : ℝ) ^ 2 *
        ∑ j ∈ Finset.range n,
          ‖iteratedCovGrad (I := I) g 4 4 j
            (endoSlotZeroCcTensor (I := I) (M := M) g 3 P)‖ ^ 2 := by
      ring
    _ ≤ (Module.finrank ℝ E : ℝ) ^ 2 *
        ((Module.finrank ℝ E : ℝ) ^ 2 *
          ∑ j ∈ Finset.range n,
            ‖iteratedCovGrad (I := I) g 2 2 j
              (endoSlotZeroCcTensor (I := I) (M := M) g 1 P)‖ ^ 2) := by
      exact mul_le_mul_of_nonneg_left
        (endo_slot_three_jet (I := I) (M := M) g P n) (sq_nonneg _)
    _ = _ := by ring

private theorem double_trace_jet_four
    (g : SmoothRiemannianMetric I M) (p : ℕ) :
    (∑ j ∈ Finset.range 4,
      ‖iteratedCovGrad (I := I) g (p + 2) p j
        (DeTurck.cometricDoubleTraceField (I := I) g p)‖ ^ 2) ≤
      (Module.finrank ℝ E : ℝ) ^ (p + 6) *
        ((riemannianVolumeMeasure (I := I) (M := M) g) Set.univ).toReal := by
  have h0 : ‖iteratedCovGrad (I := I) g (p + 2) p 0
      (DeTurck.cometricDoubleTraceField (I := I) g p)‖ ^ 2 ≤
      (Module.finrank ℝ E : ℝ) ^ (p + 6) *
        ((riemannianVolumeMeasure (I := I) (M := M) g) Set.univ).toReal := by
    rw [iteratedCovGrad_zero]
    exact norm_le_of_pointwise_fiberNormSq_bound_rs (I := I) (M := M) g (p + 2) p
      (DeTurck.cometricDoubleTraceField (I := I) g p)
      ((Module.finrank ℝ E : ℝ) ^ (p + 6))
      (fun x => cometricTrace_riemannianFiberNormSq_p (I := I) (M := M) p g x)
  have hsucc : ∀ m : ℕ, ‖iteratedCovGrad (I := I) g (p + 2) p (m + 1)
      (DeTurck.cometricDoubleTraceField (I := I) g p)‖ = 0 := by
    intro m
    rw [iteratedCovGrad_eq_zero_of_covGrad_eq_zero (I := I) (M := M) g (p + 2) p
      (DeTurck.cometricDoubleTraceField (I := I) g p)
      (DeTurck.cometricDoubleTraceField_covGrad_eq_zero (I := I) g p) m]
    exact norm_zero
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [hsucc 0, hsucc 1, hsucc 2]
  norm_num
  simpa only [iteratedCovGrad_zero] using h0

omit [SigmaCompactSpace M] in
private theorem full_slot_pointwise
    (g gm : SmoothRiemannianMetric I M)
    (P : SmoothCcTensor g 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      gm.inner y v w = g.inner y v w +
        ccTensorBilinSymm (I := I) g P y v w)
    {delta : ℝ} (hdelta_le : delta ≤ 1 / 3) (hdelta0 : 0 ≤ delta)
    (hP : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g P) delta)
    (q : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g (q + 1) (q + 1) x
        ((endoSlotZeroCcTensor (I := I) (M := M) g q
          (metricComparisonEndomorphismField (I := I) (M := M) g gm)).toSection x) ≤
      (Module.finrank ℝ E : ℝ) ^ q *
        ((Module.finrank ℝ E : ℝ) ^ 2 *
          (1 / (1 - (1 / 3 : ℝ))) ^ 2) := by
  have hsharp := riemannianFiberNormSq_sharpFlatEndoCc_le_of_lt_one
    (I := I) (M := M) g (δ₀ := (1 : ℝ) / 3)
    (by norm_num) gm P htie hdelta_le hdelta0 hP x
  have hslot := riemannianFiberNormSq_iteratedCovGrad_slotInsertEndoCc_le_endo
    (I := I) (M := M) g q
      (metricComparisonEndomorphismField (I := I) (M := M) g gm) 0 x
  simp only [iteratedCovGrad_zero, Nat.add_zero] at hslot
  rw [show endoSlotZeroCcTensor (I := I) (M := M) g 0
      (metricComparisonEndomorphismField (I := I) (M := M) g gm) =
        sharpFlatEndoCc (I := I) g gm from
      (sharpFlatEndoCc_eq_slotInsert_fullRaised (I := I) (M := M) g gm).symm] at hslot
  exact hslot.trans (mul_le_mul_of_nonneg_left hsharp (by positivity))

theorem pureTrace_h3_uniform
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∃ rho Cp Cj : ℝ, 0 < rho ∧ 0 ≤ Cp ∧ 0 ≤ Cj ∧
      ∀ g : SmoothRiemannianMetric I M,
        MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
        (∀ a : ℕ, a ≤ 3 →
          MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ) →
        ∀ (P : SmoothCcTensor g 0 2) (gm : SmoothRiemannianMetric I M)
          {delta : ℝ}, delta ≤ 1 / 3 → 0 ≤ delta →
          gFibreOpBound (I := I) (M := M) g
            (ccTensorBilinSymm (I := I) g P) delta →
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) P‖ ≤ rho →
          (∀ (y : M) (v w : TangentSpace I y),
            gm.inner y v w = g.inner y v w +
              ccTensorBilinSymm (I := I) g P y v w) →
          let N := ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) P‖
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g 4 2 x
              ((pureTrace (I := I) (M := M) g gm 2).toSection x) ≤ Cp ^ 2) ∧
          (∑ j ∈ Finset.range 4,
            ‖iteratedCovGrad (I := I) g 4 2 j
              (pureTrace (I := I) (M := M) g gm 2)‖ ^ 2) ≤
                (Cj * (1 + N)) ^ 2 ∧
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g 6 4 x
              ((pureTrace (I := I) (M := M) g gm 4).toSection x) ≤ Cp ^ 2) ∧
          (∑ j ∈ Finset.range 4,
            ‖iteratedCovGrad (I := I) g 6 4 j
              (pureTrace (I := I) (M := M) g gm 4)‖ ^ 2) ≤
                (Cj * (1 + N)) ^ 2 := by
  classical
  obtain ⟨rho, Cf, hrho, hCf, hfull⟩ :=
    fullRaised_h3_uniform (I := I) (M := M) hDim gBase hΛ
  obtain ⟨Ca2, hCa2, happ2⟩ :=
    operatorFieldComposition_h3_sup_uniform_bound (I := I) (M := M) gBase Λ 4 4 2
  obtain ⟨Ca4, hCa4, happ4⟩ :=
    operatorFieldComposition_h3_sup_uniform_bound (I := I) (M := M) gBase Λ 6 6 4
  let n : ℝ := Module.finrank ℝ E
  let vol : ℝ := volCompareC (E := E) Λ *
    ((riemannianVolumeMeasure (I := I) (M := M) gBase) Set.univ).toReal
  let D2 : ℝ := n ^ 8
  let D4 : ℝ := n ^ 10
  let W3 : ℝ := n ^ 3 * (n ^ 2 * (1 / (1 - (1 / 3 : ℝ))) ^ 2)
  let W5 : ℝ := n ^ 5 * (n ^ 2 * (1 / (1 - (1 / 3 : ℝ))) ^ 2)
  let Kp : ℝ := max (D2 * W3) (D4 * W5)
  let K2 : ℝ := Ca2 * (W3 * (D2 * vol) + D2 * (n ^ 2 * Cf ^ 2))
  let K4 : ℝ := Ca4 * (W5 * (D4 * vol) + D4 * (n ^ 4 * Cf ^ 2))
  let Kj : ℝ := max K2 K4
  have hn : 0 ≤ n := by dsimp only [n]; positivity
  have hvol : 0 ≤ vol := by dsimp only [vol, volCompareC]; positivity
  have hD2 : 0 ≤ D2 := by dsimp only [D2]; positivity
  have hD4 : 0 ≤ D4 := by dsimp only [D4]; positivity
  have hW3 : 0 ≤ W3 := by dsimp only [W3]; positivity
  have hW5 : 0 ≤ W5 := by dsimp only [W5]; positivity
  have hKp : 0 ≤ Kp := le_trans (mul_nonneg hD2 hW3) (le_max_left _ _)
  have hK2 : 0 ≤ K2 := by dsimp only [K2]; positivity
  have hK4 : 0 ≤ K4 := by dsimp only [K4]; positivity
  have hKj : 0 ≤ Kj := le_trans hK2 (le_max_left _ _)
  refine ⟨rho, Real.sqrt Kp, Real.sqrt Kj, hrho,
    Real.sqrt_nonneg _, Real.sqrt_nonneg _, ?_⟩
  intro g hEq hjet P gm delta hdelta_le hdelta0 hP hP2 htie
  let N : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) P‖
  have hN : 0 ≤ N := norm_nonneg _
  obtain ⟨hfullPt, hfullJet⟩ := hfull g hEq hjet P gm hP2 htie
  let F := metricComparisonEndomorphismField (I := I) (M := M) g gm
  let S3 : SmoothCcTensor g 4 4 :=
    endoSlotZeroCcTensor (I := I) (M := M) g 3 F
  let S5 : SmoothCcTensor g 6 6 :=
    endoSlotZeroCcTensor (I := I) (M := M) g 5 F
  let Tr2 : SmoothCcTensor g 4 2 :=
    DeTurck.cometricDoubleTraceField (I := I) g 2
  let Tr4 : SmoothCcTensor g 6 4 :=
    DeTurck.cometricDoubleTraceField (I := I) g 4
  have hvolg :
      ((riemannianVolumeMeasure (I := I) (M := M) g) Set.univ).toReal ≤ vol := by
    simpa only [vol] using
      (volumeReal_cross (I := I) (M := M) gBase g hEq).1
  have hTr2pt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 4 2 x
          (Tr2.toSection x) ≤ D2 := by
    intro x
    simpa only [Tr2, D2, n] using
      cometricTrace_riemannianFiberNormSq_p (I := I) (M := M) 2 g x
  have hTr4pt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 6 4 x
          (Tr4.toSection x) ≤ D4 := by
    intro x
    simpa only [Tr4, D4, n] using
      cometricTrace_riemannianFiberNormSq_p (I := I) (M := M) 4 g x
  have hTr2jet : (∑ j ∈ Finset.range 4,
      ‖iteratedCovGrad (I := I) g 4 2 j Tr2‖ ^ 2) ≤ D2 * vol := by
    refine (double_trace_jet_four (I := I) (M := M) g 2).trans ?_
    exact mul_le_mul_of_nonneg_left hvolg hD2
  have hTr4jet : (∑ j ∈ Finset.range 4,
      ‖iteratedCovGrad (I := I) g 6 4 j Tr4‖ ^ 2) ≤ D4 * vol := by
    refine (double_trace_jet_four (I := I) (M := M) g 4).trans ?_
    exact mul_le_mul_of_nonneg_left hvolg hD4
  have hS3pt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 4 4 x
          (S3.toSection x) ≤ W3 := by
    intro x
    simpa only [S3, F, W3, n] using
      full_slot_pointwise (I := I) (M := M) g gm P htie
        hdelta_le hdelta0 hP 3 x
  have hS5pt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 6 6 x
          (S5.toSection x) ≤ W5 := by
    intro x
    simpa only [S5, F, W5, n] using
      full_slot_pointwise (I := I) (M := M) g gm P htie
        hdelta_le hdelta0 hP 5 x
  have hS3jet : (∑ j ∈ Finset.range 4,
      ‖iteratedCovGrad (I := I) g 4 4 j S3‖ ^ 2) ≤
        n ^ 2 * (Cf * (1 + N)) ^ 2 := by
    refine (endo_slot_three_jet (I := I) (M := M) g F 4).trans ?_
    exact mul_le_mul_of_nonneg_left (by simpa only [F, N] using hfullJet)
      (sq_nonneg n)
  have hS5jet : (∑ j ∈ Finset.range 4,
      ‖iteratedCovGrad (I := I) g 6 6 j S5‖ ^ 2) ≤
        n ^ 4 * (Cf * (1 + N)) ^ 2 := by
    refine (endo_slot_five_jet (I := I) (M := M) g F 4).trans ?_
    exact mul_le_mul_of_nonneg_left (by simpa only [F, N] using hfullJet)
      (by positivity)
  have hcomp2 (x : M) :
      riemannianFiberNormSq (I := I) (M := M) g 4 2 x
          ((ccOperatorFieldComp (I := I) (M := M) g 4 4 2 Tr2 S3).toSection x) ≤
        riemannianFiberNormSq (I := I) (M := M) g 4 2 x (Tr2.toSection x) *
          riemannianFiberNormSq (I := I) (M := M) g 4 4 x (S3.toSection x) := by
    simpa only [operatorFieldComposition_toSection] using
      riemannianFiberNormSq_compRS_le_mul
        (I := I) (M := M) g 4 4 2 x (Tr2.toSection x) (S3.toSection x)
  have hcomp4 (x : M) :
      riemannianFiberNormSq (I := I) (M := M) g 6 4 x
          ((ccOperatorFieldComp (I := I) (M := M) g 6 6 4 Tr4 S5).toSection x) ≤
        riemannianFiberNormSq (I := I) (M := M) g 6 4 x (Tr4.toSection x) *
          riemannianFiberNormSq (I := I) (M := M) g 6 6 x (S5.toSection x) := by
    simpa only [operatorFieldComposition_toSection] using
      riemannianFiberNormSq_compRS_le_mul
        (I := I) (M := M) g 6 6 4 x (Tr4.toSection x) (S5.toSection x)
  have hp2pt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 4 2 x
        ((pureTrace (I := I) (M := M) g gm 2).toSection x) ≤ Kp := by
    intro x
    rw [pureTrace, pureDoubleTraceField_eq_trace_fullRaised]
    calc
      _ ≤ riemannianFiberNormSq (I := I) (M := M) g 4 2 x (Tr2.toSection x) *
          riemannianFiberNormSq (I := I) (M := M) g 4 4 x (S3.toSection x) :=
        hcomp2 x
      _ ≤ D2 * W3 := mul_le_mul (hTr2pt x) (hS3pt x)
        (riemannianFiberNormSq_nonneg (I := I) (M := M) g 4 4 x _)
        hD2
      _ ≤ Kp := le_max_left _ _
  have hp4pt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 6 4 x
        ((pureTrace (I := I) (M := M) g gm 4).toSection x) ≤ Kp := by
    intro x
    rw [pureTrace, pureDoubleTraceField_eq_trace_fullRaised]
    calc
      _ ≤ riemannianFiberNormSq (I := I) (M := M) g 6 4 x (Tr4.toSection x) *
          riemannianFiberNormSq (I := I) (M := M) g 6 6 x (S5.toSection x) :=
        hcomp4 x
      _ ≤ D4 * W5 := mul_le_mul (hTr4pt x) (hS5pt x)
        (riemannianFiberNormSq_nonneg (I := I) (M := M) g 6 6 x _)
        hD4
      _ ≤ Kp := le_max_right _ _
  have happ2raw := happ2 g hEq Tr2 S3 (Real.sqrt D2) (Real.sqrt W3)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    (fun x => by simpa [Real.sq_sqrt hD2] using hTr2pt x)
    (fun x => by simpa [Real.sq_sqrt hW3] using hS3pt x)
  have happ4raw := happ4 g hEq Tr4 S5 (Real.sqrt D4) (Real.sqrt W5)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    (fun x => by simpa [Real.sq_sqrt hD4] using hTr4pt x)
    (fun x => by simpa [Real.sq_sqrt hW5] using hS5pt x)
  have hp2jet : (∑ j ∈ Finset.range 4,
      ‖iteratedCovGrad (I := I) g 4 2 j
        (pureTrace (I := I) (M := M) g gm 2)‖ ^ 2) ≤
        K2 * (1 + N) ^ 2 := by
    rw [pureTrace, pureDoubleTraceField_eq_trace_fullRaised]
    refine happ2raw.trans ?_
    rw [Real.sq_sqrt hD2, Real.sq_sqrt hW3]
    have hone : 1 ≤ (1 + N) ^ 2 := by nlinarith
    calc
      Ca2 * (W3 * (∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g 4 2 j Tr2‖ ^ 2) +
          D2 * (∑ j ∈ Finset.range 4,
            ‖iteratedCovGrad (I := I) g 4 4 j S3‖ ^ 2)) ≤
        Ca2 * (W3 * (D2 * vol) + D2 *
          (n ^ 2 * (Cf * (1 + N)) ^ 2)) := by
            exact mul_le_mul_of_nonneg_left
              (add_le_add
                (mul_le_mul_of_nonneg_left hTr2jet hW3)
                (mul_le_mul_of_nonneg_left hS3jet hD2)) hCa2
      _ ≤ K2 * (1 + N) ^ 2 := by
        dsimp only [K2]
        conv_rhs => rw [mul_assoc]
        apply mul_le_mul_of_nonneg_left _ hCa2
        calc
          W3 * (D2 * vol) + D2 * (n ^ 2 * (Cf * (1 + N)) ^ 2) ≤
              (W3 * (D2 * vol)) * (1 + N) ^ 2 +
                D2 * (n ^ 2 * (Cf * (1 + N)) ^ 2) := by
            exact add_le_add
              (by simpa only [mul_one] using
                (mul_le_mul_of_nonneg_left hone
                  (mul_nonneg hW3 (mul_nonneg hD2 hvol)))) le_rfl
          _ = (W3 * (D2 * vol) + D2 * (n ^ 2 * Cf ^ 2)) *
              (1 + N) ^ 2 := by ring
  have hp4jet : (∑ j ∈ Finset.range 4,
      ‖iteratedCovGrad (I := I) g 6 4 j
        (pureTrace (I := I) (M := M) g gm 4)‖ ^ 2) ≤
        K4 * (1 + N) ^ 2 := by
    rw [pureTrace, pureDoubleTraceField_eq_trace_fullRaised]
    refine happ4raw.trans ?_
    rw [Real.sq_sqrt hD4, Real.sq_sqrt hW5]
    have hone : 1 ≤ (1 + N) ^ 2 := by nlinarith
    calc
      Ca4 * (W5 * (∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g 6 4 j Tr4‖ ^ 2) +
          D4 * (∑ j ∈ Finset.range 4,
            ‖iteratedCovGrad (I := I) g 6 6 j S5‖ ^ 2)) ≤
        Ca4 * (W5 * (D4 * vol) + D4 *
          (n ^ 4 * (Cf * (1 + N)) ^ 2)) := by
            exact mul_le_mul_of_nonneg_left
              (add_le_add
                (mul_le_mul_of_nonneg_left hTr4jet hW5)
                (mul_le_mul_of_nonneg_left hS5jet hD4)) hCa4
      _ ≤ K4 * (1 + N) ^ 2 := by
        dsimp only [K4]
        conv_rhs => rw [mul_assoc]
        apply mul_le_mul_of_nonneg_left _ hCa4
        calc
          W5 * (D4 * vol) + D4 * (n ^ 4 * (Cf * (1 + N)) ^ 2) ≤
              (W5 * (D4 * vol)) * (1 + N) ^ 2 +
                D4 * (n ^ 4 * (Cf * (1 + N)) ^ 2) := by
            exact add_le_add
              (by simpa only [mul_one] using
                (mul_le_mul_of_nonneg_left hone
                  (mul_nonneg hW5 (mul_nonneg hD4 hvol)))) le_rfl
          _ = (W5 * (D4 * vol) + D4 * (n ^ 4 * Cf ^ 2)) *
              (1 + N) ^ 2 := by ring
  dsimp only
  refine ⟨?_, ?_⟩
  · intro x
    rw [Real.sq_sqrt hKp]
    exact hp2pt x
  · refine ⟨?_, ?_⟩
    · have hle : K2 ≤ Kj := le_max_left _ _
      calc
        _ ≤ K2 * (1 + N) ^ 2 := hp2jet
        _ ≤ Kj * (1 + N) ^ 2 := mul_le_mul_of_nonneg_right hle (sq_nonneg _)
        _ = (Real.sqrt Kj * (1 + N)) ^ 2 := by rw [mul_pow, Real.sq_sqrt hKj]
    · refine ⟨?_, ?_⟩
      · intro x
        rw [Real.sq_sqrt hKp]
        exact hp4pt x
      · have hle : K4 ≤ Kj := le_max_right _ _
        calc
          _ ≤ K4 * (1 + N) ^ 2 := hp4jet
          _ ≤ Kj * (1 + N) ^ 2 := mul_le_mul_of_nonneg_right hle (sq_nonneg _)
          _ = (Real.sqrt Kj * (1 + N)) ^ 2 := by rw [mul_pow, Real.sq_sqrt hKj]

theorem cometricDoublePairTraceCoefficient_h3_uniform
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∃ rho Cp Cj : ℝ, 0 < rho ∧ 0 ≤ Cp ∧ 0 ≤ Cj ∧
      ∀ g : SmoothRiemannianMetric I M,
        MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
        (∀ a : ℕ, a ≤ 3 →
          MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ) →
        ∀ (P : SmoothCcTensor g 0 2) (gm : SmoothRiemannianMetric I M)
          {delta : ℝ}, delta ≤ 1 / 3 → 0 ≤ delta →
          gFibreOpBound (I := I) (M := M) g
            (ccTensorBilinSymm (I := I) g P) delta →
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) P‖ ≤ rho →
          (∀ (y : M) (v w : TangentSpace I y),
            gm.inner y v w = g.inner y v w +
              ccTensorBilinSymm (I := I) g P y v w) →
          let N := ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) P‖
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g 6 2 x
              ((cometricDoublePairTraceCoefficient (I := I) (M := M) g gm).toSection x) ≤ Cp ^ 2) ∧
          (∑ j ∈ Finset.range 4,
            ‖iteratedCovGrad (I := I) g 6 2 j
              (cometricDoublePairTraceCoefficient (I := I) (M := M) g gm)‖ ^ 2) ≤
                (Cj * (1 + N)) ^ 2 := by
  obtain ⟨rho, Ct, Cj, hrho, hCt, hCj, htrace⟩ :=
    pureTrace_h3_uniform (I := I) (M := M) hDim gBase hΛ
  obtain ⟨Ca, hCa, happ⟩ :=
    operatorFieldComposition_h3_sup_uniform_bound (I := I) (M := M) gBase Λ 6 4 2
  let K : ℝ := 2 * Ca * Ct ^ 2 * Cj ^ 2
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  refine ⟨rho, Ct ^ 2, Real.sqrt K, hrho, sq_nonneg _,
    Real.sqrt_nonneg _, ?_⟩
  intro g hEq hjet P gm delta hdelta_le hdelta0 hP hP2 htie
  dsimp only
  obtain ⟨h2pt, h2jet, h4pt, h4jet⟩ :=
    htrace g hEq hjet P gm hdelta_le hdelta0 hP hP2 htie
  let T2 : SmoothCcTensor g 4 2 := pureTrace (I := I) (M := M) g gm 2
  let T4 : SmoothCcTensor g 6 4 := pureTrace (I := I) (M := M) g gm 4
  let N : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) P‖
  have hcomp (x : M) :
      riemannianFiberNormSq (I := I) (M := M) g 6 2 x
          ((ccOperatorFieldComp (I := I) (M := M) g 6 4 2 T2 T4).toSection x) ≤
        riemannianFiberNormSq (I := I) (M := M) g 4 2 x (T2.toSection x) *
          riemannianFiberNormSq (I := I) (M := M) g 6 4 x (T4.toSection x) := by
    simpa only [operatorFieldComposition_toSection] using
      riemannianFiberNormSq_compRS_le_mul
        (I := I) (M := M) g 6 4 2 x (T2.toSection x) (T4.toSection x)
  have hpoint : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 6 2 x
        ((cometricDoublePairTraceCoefficient (I := I) (M := M) g gm).toSection x) ≤ (Ct ^ 2) ^ 2 := by
    intro x
    rw [RicciDeTurckLowOrder.pairTrace_eq]
    calc
      _ ≤ riemannianFiberNormSq (I := I) (M := M) g 4 2 x (T2.toSection x) *
          riemannianFiberNormSq (I := I) (M := M) g 6 4 x (T4.toSection x) :=
        hcomp x
      _ ≤ Ct ^ 2 * Ct ^ 2 := mul_le_mul (h2pt x) (h4pt x)
        (riemannianFiberNormSq_nonneg (I := I) (M := M) g 6 4 x _)
        (sq_nonneg Ct)
      _ = (Ct ^ 2) ^ 2 := by ring
  have hraw := happ g hEq T2 T4 Ct Ct hCt hCt h2pt h4pt
  have hjetPair : (∑ j ∈ Finset.range 4,
      ‖iteratedCovGrad (I := I) g 6 2 j
        (cometricDoublePairTraceCoefficient (I := I) (M := M) g gm)‖ ^ 2) ≤
      K * (1 + N) ^ 2 := by
    rw [RicciDeTurckLowOrder.pairTrace_eq]
    refine hraw.trans ?_
    calc
      Ca * (Ct ^ 2 * (∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g 4 2 j T2‖ ^ 2) +
        Ct ^ 2 * (∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g 6 4 j T4‖ ^ 2)) ≤
        Ca * (Ct ^ 2 * (Cj * (1 + N)) ^ 2 +
          Ct ^ 2 * (Cj * (1 + N)) ^ 2) := by
            exact mul_le_mul_of_nonneg_left
              (add_le_add
                (mul_le_mul_of_nonneg_left h2jet (sq_nonneg Ct))
                (mul_le_mul_of_nonneg_left h4jet (sq_nonneg Ct))) hCa
      _ = K * (1 + N) ^ 2 := by dsimp only [K]; ring
  refine ⟨hpoint, ?_⟩
  calc
    _ ≤ K * (1 + N) ^ 2 := hjetPair
    _ = (Real.sqrt K * (1 + N)) ^ 2 := by rw [mul_pow, Real.sq_sqrt hK]

omit [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem slot_iter_pointwise
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (A : SmoothCcTensor g r s) (x : M) : ∀ w : ℕ,
    riemannianFiberNormSq (I := I) (M := M) g (r + w) (s + w) x
        ((slotExtendIter (I := I) (M := M) g r s w A).toSection x) ≤
      (Module.finrank ℝ E : ℝ) ^ w *
        riemannianFiberNormSq (I := I) (M := M) g r s x (A.toSection x) := by
  let n : ℝ := Module.finrank ℝ E
  intro w
  induction w with
  | zero => simpa only [slotExtendIter, Nat.add_zero, pow_zero, one_mul] using
      (le_refl (riemannianFiberNormSq (I := I) (M := M) g r s x (A.toSection x)))
  | succ w ih =>
      change riemannianFiberNormSq (I := I) (M := M) g
          ((r + w) + 1) ((s + w) + 1) x
          ((slotExtend (I := I) (M := M) g (r + w) (s + w)
            (slotExtendIter (I := I) (M := M) g r s w A)).toSection x) ≤ _
      calc
        _ = n * riemannianFiberNormSq (I := I) (M := M) g
            (r + w) (s + w) x
            ((slotExtendIter (I := I) (M := M) g r s w A).toSection x) := by
          simpa only [n] using riemannianFiberNormSq_slotExtend_eq
            (I := I) (M := M) g (r + w) (s + w)
              (slotExtendIter (I := I) (M := M) g r s w A) x
        _ ≤ n * (n ^ w *
            riemannianFiberNormSq (I := I) (M := M) g r s x
              (A.toSection x)) :=
          mul_le_mul_of_nonneg_left ih (by dsimp only [n]; positivity)
        _ = n ^ (w + 1) *
            riemannianFiberNormSq (I := I) (M := M) g r s x
              (A.toSection x) := by rw [pow_succ]; ring

omit [SigmaCompactSpace M] in
private theorem mono_ext_pointwise
    (g : SmoothRiemannianMetric I M) (r s w : ℕ)
    (tau : Equiv.Perm (Fin (s + w)))
    (A : SmoothCcTensor g r s) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g (r + w) (s + w) x
        ((monoExt (I := I) (M := M) g r s w tau A).toSection x) ≤
      (Module.finrank ℝ E : ℝ) ^ w *
        riemannianFiberNormSq (I := I) (M := M) g r s x
          (A.toSection x) := by
  have hperm := DifferentialGeometry.Analysis.Spectral.riemannianFiberNormSq_iteratedCovGrad_rs_eq_of_section_domDomCongr
    (I := I) (M := M) g (r + w) (s + w) tau
    (slotExtendIter (I := I) (M := M) g r s w A)
    (rsDomDomCongrSection (I := I) (M := M) g (r + w) (s + w) tau
      (slotExtendIter (I := I) (M := M) g r s w A))
    (fun y d => by
      rw [rsDomDomCongrSection_toSection, toModel_rsDomDomCongr_apply]) 0 x
  simp only [iteratedCovGrad_zero, Nat.add_zero] at hperm
  rw [monoExt, hperm]
  exact slot_iter_pointwise (I := I) (M := M) g r s A x w

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem jet_four_add
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (A B : SmoothCcTensor g r s) :
    (∑ j ∈ Finset.range 4,
      ‖iteratedCovGrad (I := I) g r s j (A + B)‖ ^ 2) ≤
      2 * ((∑ j ∈ Finset.range 4,
        ‖iteratedCovGrad (I := I) g r s j A‖ ^ 2) +
        ∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g r s j B‖ ^ 2) := by
  calc
    _ ≤ ∑ j ∈ Finset.range 4,
        2 * (‖iteratedCovGrad (I := I) g r s j A‖ ^ 2 +
          ‖iteratedCovGrad (I := I) g r s j B‖ ^ 2) := by
      refine Finset.sum_le_sum fun j _ => ?_
      rw [iteratedCovGrad_add]
      have htri := norm_add_le
        (iteratedCovGrad (I := I) g r s j A)
        (iteratedCovGrad (I := I) g r s j B)
      calc
        _ ≤ (‖iteratedCovGrad (I := I) g r s j A‖ +
            ‖iteratedCovGrad (I := I) g r s j B‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) htri 2
        _ ≤ 2 * (‖iteratedCovGrad (I := I) g r s j A‖ ^ 2 +
            ‖iteratedCovGrad (I := I) g r s j B‖ ^ 2) := by
          nlinarith [sq_nonneg
            (‖iteratedCovGrad (I := I) g r s j A‖ -
              ‖iteratedCovGrad (I := I) g r s j B‖)]
    _ = _ := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem jet_four_smul
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (a : ℝ) (A : SmoothCcTensor g r s) :
    (∑ j ∈ Finset.range 4,
      ‖iteratedCovGrad (I := I) g r s j (a • A)‖ ^ 2) =
      a ^ 2 * ∑ j ∈ Finset.range 4,
        ‖iteratedCovGrad (I := I) g r s j A‖ ^ 2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [iteratedCovGrad_smul, norm_smul, Real.norm_eq_abs]
  ring_nf
  rw [sq_abs]
  ring

omit [NeZero (Module.finrank ℝ E)] in
private theorem reindex_jet_four_eq
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (A : SmoothCcTensor g r s) (e : Equiv.Perm (Fin r)) :
    (∑ j ∈ Finset.range 4,
      ‖iteratedCovGrad (I := I) g r s j
        (reindexCoeffGen (I := I) (M := M) g r s A e)‖ ^ 2) =
      ∑ j ∈ Finset.range 4,
        ‖iteratedCovGrad (I := I) g r s j A‖ ^ 2 := by
  apply Finset.sum_congr rfl
  intro j _
  rw [iteratedCovGrad_reindexCoeffGen,
    norm_reindexCoeffGen_eq (I := I) (M := M)]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem perm_app_eq_reindex
    (g : SmoothRiemannianMetric I M) {d : ℕ}
    (A : SmoothCcTensor g d d) (e : Equiv.Perm (Fin d)) :
    ccOperatorFieldComp (I := I) (M := M) g d d d
        A (permCoeff (I := I) (M := M) g e) =
      reindexCoeffGen (I := I) (M := M) g d d A e := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  rw [operatorFieldComposition_toSection, ContinuousLinearMap.comp_apply,
    reindexCoeffGen_toSection, reindexCoeffFibGen_apply]
  change (show Tensor0SSpace d I x →L[ℝ] Tensor0SSpace d I x from
      A.toSection x) (slotPermCLM (I := I) e x D) = _
  rw [slotPermCLM_apply]

omit [SigmaCompactSpace M] in
private theorem perm_left_pointwise_jet
    (g : SmoothRiemannianMetric I M) {d : ℕ}
    (e : Equiv.Perm (Fin d)) (A : SmoothCcTensor g d d)
    (j : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g d (d + j) x
        ((iteratedCovGrad (I := I) g d d j
          (ccOperatorFieldComp (I := I) (M := M) g d d d
            (permCoeff (I := I) (M := M) g e) A)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g d (d + j) x
        ((iteratedCovGrad (I := I) g d d j A).toSection x) := by
  exact DifferentialGeometry.Analysis.Spectral.riemannianFiberNormSq_iteratedCovGrad_rs_eq_of_section_domDomCongr
    (I := I) (M := M) g d d e A
    (ccOperatorFieldComp (I := I) (M := M) g d d d
      (permCoeff (I := I) (M := M) g e) A)
    (fun y D => by
      rw [operatorFieldComposition_toSection, ContinuousLinearMap.comp_apply]
      change Tensor0SSpace.toModel
          (slotPermCLM (I := I) e y
            ((show Tensor0SSpace d I y →L[ℝ] Tensor0SSpace d I y from
              A.toSection y) D)) = _
      rw [slotPermCLM_apply, Tensor0SSpace.toModel_ofModel]) j x

private theorem perm_left_sq_le
    (g : SmoothRiemannianMetric I M) {d : ℕ}
    (e : Equiv.Perm (Fin d)) (A : SmoothCcTensor g d d) (j : ℕ) :
    ‖iteratedCovGrad (I := I) g d d j
        (ccOperatorFieldComp (I := I) (M := M) g d d d
          (permCoeff (I := I) (M := M) g e) A)‖ ^ 2 ≤
      ‖iteratedCovGrad (I := I) g d d j A‖ ^ 2 := by
  classical
  let F : M → ℝ := fun x =>
    riemannianFiberNormSq (I := I) (M := M) g d (d + j) x
      ((iteratedCovGrad (I := I) g d d j A).toSection x)
  have hFint : Integrable F (riemannianVolumeMeasure (I := I) (M := M) g) := by
    dsimp only [F]
    exact integrable_riemannianFiberNormSq_toSection
      (I := I) (M := M) g d (d + j)
        (iteratedCovGrad (I := I) g d d j A)
  have hsq := normSq_le_integral_of_pointwise_fiberNormSq_le_rs
    (I := I) (M := M) g d (d + j)
      (iteratedCovGrad (I := I) g d d j
        (ccOperatorFieldComp (I := I) (M := M) g d d d
          (permCoeff (I := I) (M := M) g e) A)) F hFint
      (fun x => (perm_left_pointwise_jet
        (I := I) (M := M) g e A j x).le)
  have hint :
      ∫ x, F x ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        ‖iteratedCovGrad (I := I) g d d j A‖ ^ 2 := by
    dsimp only [F]
    rw [SmoothCcTensor.norm_def,
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs
        (I := I) (M := M) g d (d + j)]
  exact hsq.trans_eq hint

private theorem perm_left_jet_four_le
    (g : SmoothRiemannianMetric I M) {d : ℕ}
    (e : Equiv.Perm (Fin d)) (A : SmoothCcTensor g d d) :
    (∑ j ∈ Finset.range 4,
      ‖iteratedCovGrad (I := I) g d d j
        (ccOperatorFieldComp (I := I) (M := M) g d d d
          (permCoeff (I := I) (M := M) g e) A)‖ ^ 2) ≤
      ∑ j ∈ Finset.range 4,
        ‖iteratedCovGrad (I := I) g d d j A‖ ^ 2 :=
  Finset.sum_le_sum fun j _ =>
    perm_left_sq_le (I := I) (M := M) g e A j

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M]
  [SigmaCompactSpace M] in
omit [I.Boundaryless] in
private theorem conn_low_nf
    (g gm : SmoothRiemannianMetric I M) :
    RicciDeTurckLowOrder.connectionDifferenceLowOrderOperator (I := I) (M := M) g gm =
      ccOperatorFieldComp (I := I) (M := M) g 3 3 3
        (permCoeff (I := I) (M := M) g RicciDeTurckLowOrder.connectionDifferenceLowOrderPermutation)
        (ccOperatorFieldComp (I := I) (M := M) g 3 3 3
          (slotInsertEndoCc (I := I) (M := M) g 2
            (metricComparisonEndomorphismField (I := I) (M := M) g gm))
          ((1 / 2 : ℝ) •
            (permCoeff (I := I) (M := M) g (Equiv.swap (0 : Fin 3) 2) +
              permCoeff (I := I) (M := M) g (finRotate 3) -
              permCoeff (I := I) (M := M) g
                (Equiv.swap (1 : Fin 3) 2)))) := rfl

private theorem slot_extend_sq
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (A : SmoothCcTensor g r s) (j : ℕ) :
    ‖iteratedCovGrad (I := I) g (r + 1) (s + 1) j
        (slotExtend (I := I) (M := M) g r s A)‖ ^ 2 ≤
      (Module.finrank ℝ E : ℝ) *
        ‖iteratedCovGrad (I := I) g r s j A‖ ^ 2 := by
  classical
  let F : M → ℝ := fun x => (Module.finrank ℝ E : ℝ) *
    riemannianFiberNormSq (I := I) (M := M) g r (s + j) x
      ((iteratedCovGrad (I := I) g r s j A).toSection x)
  have hFint : Integrable F (riemannianVolumeMeasure (I := I) (M := M) g) := by
    dsimp only [F]
    exact (integrable_riemannianFiberNormSq_toSection
      (I := I) (M := M) g r (s + j)
        (iteratedCovGrad (I := I) g r s j A)).const_mul _
  have hsq := normSq_le_integral_of_pointwise_fiberNormSq_le_rs
    (I := I) (M := M) g (r + 1) ((s + 1) + j)
      (iteratedCovGrad (I := I) g (r + 1) (s + 1) j
        (slotExtend (I := I) (M := M) g r s A)) F hFint
      (riemannianFiberNormSq_iteratedCovGrad_slotExtend_le
        (I := I) (M := M) g r s A j)
  have hint :
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g r (s + j) x
          ((iteratedCovGrad (I := I) g r s j A).toSection x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        ‖iteratedCovGrad (I := I) g r s j A‖ ^ 2 := by
    rw [SmoothCcTensor.norm_def,
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs
        (I := I) (M := M) g r (s + j)]
  dsimp only [F] at hsq
  rw [MeasureTheory.integral_const_mul, hint] at hsq
  exact hsq

theorem ricciConnectionPrincipalCoefficient_h3_uniform
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∃ rho Cp Cj : ℝ, 0 < rho ∧ 0 ≤ Cp ∧ 0 ≤ Cj ∧
      ∀ g : SmoothRiemannianMetric I M,
        MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
        (∀ a : ℕ, a ≤ 3 →
          MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ) →
        ∀ (P : SmoothCcTensor g 0 2) (gm : SmoothRiemannianMetric I M)
          {delta : ℝ}, delta ≤ 1 / 3 → 0 ≤ delta →
          gFibreOpBound (I := I) (M := M) g
            (ccTensorBilinSymm (I := I) g P) delta →
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) P‖ ≤ rho →
          (∀ (y : M) (v w : TangentSpace I y),
            gm.inner y v w = g.inner y v w +
              ccTensorBilinSymm (I := I) g P y v w) →
          let N := ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) P‖
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g 4 4 x
              ((RicciDeTurckLowOrder.ricciConnectionPrincipalCoefficient (I := I) (M := M) g gm).toSection x) ≤
                Cp ^ 2) ∧
          (∑ j ∈ Finset.range 4,
            ‖iteratedCovGrad (I := I) g 4 4 j
              (RicciDeTurckLowOrder.ricciConnectionPrincipalCoefficient (I := I) (M := M) g gm)‖ ^ 2) ≤
                (Cj * (1 + N)) ^ 2 := by
  classical
  obtain ⟨rho, Cf, hrho, hCf, hfull⟩ :=
    fullRaised_h3_uniform (I := I) (M := M) hDim gBase hΛ
  obtain ⟨Kp, hKp, hpoint⟩ :=
    RicciDeTurckLowOrder.exists_uniform_riemannianFiberNormSq_ricciConnectionPrincipalCoefficient_le (I := I) (M := M)
  let n : ℝ := Module.finrank ℝ E
  let Kj : ℝ := 10 * n ^ 2 * Cf ^ 2
  have hn : 0 ≤ n := by dsimp only [n]; positivity
  have hKj : 0 ≤ Kj := by dsimp only [Kj]; positivity
  refine ⟨rho, Real.sqrt Kp, Real.sqrt Kj, hrho,
    Real.sqrt_nonneg _, Real.sqrt_nonneg _, ?_⟩
  intro g hEq hjet P gm delta hdelta_le hdelta0 hdelta hP2 htie
  let N : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) P‖
  obtain ⟨hfullPt, hfullJet⟩ := hfull g hEq hjet P gm hP2 htie
  let F := metricComparisonEndomorphismField (I := I) (M := M) g gm
  let E1 : SmoothCcTensor g 3 3 :=
    slotInsertEndoCc (I := I) (M := M) g 2 F
  let A : SmoothCcTensor g 3 3 :=
    reindexCoeffGen (I := I) (M := M) g 3 3 E1
      (Equiv.swap (0 : Fin 3) 2)
  let B : SmoothCcTensor g 3 3 :=
    reindexCoeffGen (I := I) (M := M) g 3 3 E1 (finRotate 3)
  let C : SmoothCcTensor g 3 3 :=
    reindexCoeffGen (I := I) (M := M) g 3 3 E1
      (Equiv.swap (1 : Fin 3) 2)
  let Y : SmoothCcTensor g 3 3 := (1 / 2 : ℝ) • (A + B - C)
  have hE1 : (∑ j ∈ Finset.range 4,
      ‖iteratedCovGrad (I := I) g 3 3 j E1‖ ^ 2) ≤
        n * (Cf * (1 + N)) ^ 2 := by
    simpa only [E1, F, n, N] using
      endo_slot_succ_jet (I := I) (M := M) g 1 4
        (metricComparisonEndomorphismField (I := I) (M := M) g gm) |>.trans
          (mul_le_mul_of_nonneg_left hfullJet hn)
  have hA : (∑ j ∈ Finset.range 4,
      ‖iteratedCovGrad (I := I) g 3 3 j A‖ ^ 2) ≤
        n * (Cf * (1 + N)) ^ 2 := by
    rw [show (∑ j ∈ Finset.range 4,
      ‖iteratedCovGrad (I := I) g 3 3 j A‖ ^ 2) =
        ∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g 3 3 j E1‖ ^ 2 by
      exact reindex_jet_four_eq (I := I) (M := M) g E1
        (Equiv.swap (0 : Fin 3) 2)]
    exact hE1
  have hB : (∑ j ∈ Finset.range 4,
      ‖iteratedCovGrad (I := I) g 3 3 j B‖ ^ 2) ≤
        n * (Cf * (1 + N)) ^ 2 := by
    rw [show (∑ j ∈ Finset.range 4,
      ‖iteratedCovGrad (I := I) g 3 3 j B‖ ^ 2) =
        ∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g 3 3 j E1‖ ^ 2 by
      exact reindex_jet_four_eq (I := I) (M := M) g E1 (finRotate 3)]
    exact hE1
  have hC : (∑ j ∈ Finset.range 4,
      ‖iteratedCovGrad (I := I) g 3 3 j C‖ ^ 2) ≤
        n * (Cf * (1 + N)) ^ 2 := by
    rw [show (∑ j ∈ Finset.range 4,
      ‖iteratedCovGrad (I := I) g 3 3 j C‖ ^ 2) =
        ∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g 3 3 j E1‖ ^ 2 by
      exact reindex_jet_four_eq (I := I) (M := M) g E1
        (Equiv.swap (1 : Fin 3) 2)]
    exact hE1
  have hAB : (∑ j ∈ Finset.range 4,
      ‖iteratedCovGrad (I := I) g 3 3 j (A + B)‖ ^ 2) ≤
        4 * (n * (Cf * (1 + N)) ^ 2) := by
    refine (jet_four_add (I := I) (M := M) g A B).trans ?_
    calc
      2 * ((∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g 3 3 j A‖ ^ 2) +
        ∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g 3 3 j B‖ ^ 2) ≤
          2 * (n * (Cf * (1 + N)) ^ 2 +
            n * (Cf * (1 + N)) ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add hA hB) (by norm_num)
      _ = 4 * (n * (Cf * (1 + N)) ^ 2) := by ring
  have hABC : (∑ j ∈ Finset.range 4,
      ‖iteratedCovGrad (I := I) g 3 3 j (A + B - C)‖ ^ 2) ≤
        10 * (n * (Cf * (1 + N)) ^ 2) := by
    have hneg : (∑ j ∈ Finset.range 4,
        ‖iteratedCovGrad (I := I) g 3 3 j ((-1 : ℝ) • C)‖ ^ 2) ≤
          n * (Cf * (1 + N)) ^ 2 := by
      rw [jet_four_smul]
      norm_num
      exact hC
    rw [sub_eq_add_neg, ← neg_one_smul ℝ C]
    refine (jet_four_add (I := I) (M := M) g (A + B) ((-1 : ℝ) • C)).trans ?_
    calc
      2 * ((∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g 3 3 j (A + B)‖ ^ 2) +
        ∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g 3 3 j ((-1 : ℝ) • C)‖ ^ 2) ≤
          2 * (4 * (n * (Cf * (1 + N)) ^ 2) +
            n * (Cf * (1 + N)) ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add hAB hneg) (by norm_num)
      _ = 10 * (n * (Cf * (1 + N)) ^ 2) := by ring
  have hY : (∑ j ∈ Finset.range 4,
      ‖iteratedCovGrad (I := I) g 3 3 j Y‖ ^ 2) ≤
        10 * (n * (Cf * (1 + N)) ^ 2) := by
    rw [show Y = (1 / 2 : ℝ) • (A + B - C) from rfl, jet_four_smul]
    calc
      (1 / 2 : ℝ) ^ 2 * (∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g 3 3 j (A + B - C)‖ ^ 2) ≤
        ∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g 3 3 j (A + B - C)‖ ^ 2 :=
        mul_le_of_le_one_left (Finset.sum_nonneg fun j _ => sq_nonneg _)
          (by norm_num)
      _ ≤ _ := hABC
  have hYeq : ccOperatorFieldComp (I := I) (M := M) g 3 3 3 E1
      ((1 / 2 : ℝ) •
        (permCoeff (I := I) (M := M) g (Equiv.swap (0 : Fin 3) 2) +
          permCoeff (I := I) (M := M) g (finRotate 3) -
          permCoeff (I := I) (M := M) g (Equiv.swap (1 : Fin 3) 2))) = Y := by
    dsimp only [Y, A, B, C]
    have hinner :
        ccOperatorFieldComp (I := I) (M := M) g 3 3 3 E1
            (permCoeff (I := I) (M := M) g (Equiv.swap (0 : Fin 3) 2) +
              permCoeff (I := I) (M := M) g (finRotate 3) -
              permCoeff (I := I) (M := M) g (Equiv.swap (1 : Fin 3) 2)) =
          ccOperatorFieldComp (I := I) (M := M) g 3 3 3 E1
              (permCoeff (I := I) (M := M) g (Equiv.swap (0 : Fin 3) 2)) +
            ccOperatorFieldComp (I := I) (M := M) g 3 3 3 E1
              (permCoeff (I := I) (M := M) g (finRotate 3)) -
            ccOperatorFieldComp (I := I) (M := M) g 3 3 3 E1
              (permCoeff (I := I) (M := M) g
                (Equiv.swap (1 : Fin 3) 2)) := by
      calc
        _ = ccOperatorFieldComp (I := I) (M := M) g 3 3 3 E1
              (permCoeff (I := I) (M := M) g (Equiv.swap (0 : Fin 3) 2) +
                permCoeff (I := I) (M := M) g (finRotate 3)) -
            ccOperatorFieldComp (I := I) (M := M) g 3 3 3 E1
              (permCoeff (I := I) (M := M) g
                (Equiv.swap (1 : Fin 3) 2)) :=
          operatorFieldComposition_sub_right (I := I) (M := M) g 3 3 3 E1 _ _
        _ = _ := congrArg
          (fun Z => Z - ccOperatorFieldComp (I := I) (M := M) g 3 3 3 E1
            (permCoeff (I := I) (M := M) g (Equiv.swap (1 : Fin 3) 2)))
          (operatorFieldComposition_add_right (I := I) (M := M) g 3 3 3 E1 _ _)
    calc
      _ = (1 / 2 : ℝ) • ccOperatorFieldComp (I := I) (M := M) g 3 3 3 E1
          (permCoeff (I := I) (M := M) g (Equiv.swap (0 : Fin 3) 2) +
            permCoeff (I := I) (M := M) g (finRotate 3) -
            permCoeff (I := I) (M := M) g
              (Equiv.swap (1 : Fin 3) 2)) :=
        operatorFieldComposition_smul_right (I := I) (M := M) g 3 3 3 _ _ _
      _ = (1 / 2 : ℝ) •
          (ccOperatorFieldComp (I := I) (M := M) g 3 3 3 E1
              (permCoeff (I := I) (M := M) g (Equiv.swap (0 : Fin 3) 2)) +
            ccOperatorFieldComp (I := I) (M := M) g 3 3 3 E1
              (permCoeff (I := I) (M := M) g (finRotate 3)) -
            ccOperatorFieldComp (I := I) (M := M) g 3 3 3 E1
              (permCoeff (I := I) (M := M) g
                (Equiv.swap (1 : Fin 3) 2))) := by
        exact congrArg ((1 / 2 : ℝ) • ·) hinner
      _ = _ := by
        exact congrArg ((1 / 2 : ℝ) • ·) (by
          rw [perm_app_eq_reindex (I := I) (M := M) g E1,
            perm_app_eq_reindex (I := I) (M := M) g E1,
            perm_app_eq_reindex (I := I) (M := M) g E1])
  have hconn : (∑ j ∈ Finset.range 4,
      ‖iteratedCovGrad (I := I) g 3 3 j
        (RicciDeTurckLowOrder.connectionDifferenceLowOrderOperator (I := I) (M := M) g gm)‖ ^ 2) ≤
        10 * (n * (Cf * (1 + N)) ^ 2) := by
    rw [conn_low_nf (I := I) (M := M) g gm, hYeq]
    exact (perm_left_jet_four_le (I := I) (M := M) g
      RicciDeTurckLowOrder.connectionDifferenceLowOrderPermutation Y).trans hY
  have hdag : (∑ j ∈ Finset.range 4,
      ‖iteratedCovGrad (I := I) g 4 4 j
        (RicciDeTurckLowOrder.ricciConnectionPrincipalCoefficient (I := I) (M := M) g gm)‖ ^ 2) ≤
        10 * n ^ 2 * (Cf * (1 + N)) ^ 2 := by
    rw [RicciDeTurckLowOrder.ricciConnectionPrincipalCoefficient]
    calc
      _ ≤ ∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g 4 4 j
            (slotExtend (I := I) (M := M) g 3 3
              (RicciDeTurckLowOrder.connectionDifferenceLowOrderOperator (I := I) (M := M) g gm))‖ ^ 2 :=
        perm_left_jet_four_le (I := I) (M := M) g RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeCyclicPermutation _
      _ ≤ n * (∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g 3 3 j
            (RicciDeTurckLowOrder.connectionDifferenceLowOrderOperator (I := I) (M := M) g gm)‖ ^ 2) := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro j hj
        exact slot_extend_sq (I := I) (M := M) g
          (RicciDeTurckLowOrder.connectionDifferenceLowOrderOperator (I := I) (M := M) g gm) j
      _ ≤ n * (10 * (n * (Cf * (1 + N)) ^ 2)) :=
        mul_le_mul_of_nonneg_left hconn hn
      _ = 10 * n ^ 2 * (Cf * (1 + N)) ^ 2 := by ring
  constructor
  · intro x
    have hp := hpoint g gm P hdelta_le hdelta0 hdelta htie x
    simpa only [Real.sq_sqrt hKp] using hp
  · calc
      _ ≤ 10 * n ^ 2 * (Cf * (1 + N)) ^ 2 := hdag
      _ = Kj * (1 + N) ^ 2 := by dsimp only [Kj]; ring
      _ = Real.sqrt Kj ^ 2 * (1 + N) ^ 2 := by rw [Real.sq_sqrt hKj]
      _ = (Real.sqrt Kj * (1 + N)) ^ 2 := by ring

theorem lie_second_order_expansion_h3_uniform
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∃ rho C : ℝ, 0 < rho ∧ 0 ≤ C ∧
      ∀ g : SmoothRiemannianMetric I M,
        MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
        (∀ a : ℕ, a ≤ 3 →
          MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ) →
        ∀ (T : SmoothCcTensor g 0 2)
          (_hT : ∀ (x : M) (u v : TangentSpace I x),
            ccTensorBilin (I := I) g T x u v =
              ccTensorBilin (I := I) g T x v u)
          {delta : ℝ}, delta ≤ 1 / 3 → 0 ≤ delta →
          ∀ (hdelta : gFibreOpBound (I := I) (M := M) g
              (ccTensorBilinSymm (I := I) g T) delta)
            (hdeltaZ : gFibreOpBound (I := I) (M := M) g
              (ccTensorBilinSymm (I := I) g
                (0 : SmoothCcTensor g 0 2)) delta),
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ rho →
          ∀ {a : ℝ}, a ∈ Set.Icc (0 : ℝ) 1 →
          (∑ j ∈ Finset.range 4,
            ‖iteratedCovGrad (I := I) g 4 2 j
              (lieDecomposition2 (I := I) (M := M) g T hdelta hdeltaZ a)‖ ^ 2) ≤
            (C * ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖) ^ 2 := by
  classical
  obtain ⟨rhoP, Cp, Cj, hrhoP, hCp, hCj, hpair⟩ :=
    cometricDoublePairTraceCoefficient_h3_uniform (I := I) (M := M) hDim gBase hΛ
  obtain ⟨Ca, hCa, happ⟩ :=
    operatorFieldComposition_h3_sup_uniform_bound (I := I) (M := M) gBase Λ 4 6 2
  obtain ⟨Cmor, hCmor, hmor⟩ :=
    morreyRS_uniform (I := I) (M := M) hDim gBase hΛ 0 2
  obtain ⟨Kcurv, hKcurv⟩ :=
    exists_uniform_curvature_action_parameters (I := I) (M := M) gBase hΛ
  let C2 : ℝ := hs2FibreActionC Cmor Kcurv.rankTwo
  let C3 : ℝ := h3CovsumC Kcurv.rankTwo Kcurv.rankThree
  let n4 : ℝ := (Module.finrank ℝ E : ℝ) ^ 4
  let Km : ℝ := Ca * (4 * (n4 * C2 ^ 2) * Cj ^ 2 + Cp ^ 2 *
    (n4 * C3 ^ 2))
  let Ksum : ℝ := 10 * Km
  have hC2 : 0 ≤ C2 := by
    dsimp only [C2]
    exact hs2FibreAct_nonneg hCmor _
  have hC3 : 0 ≤ C3 := by
    dsimp only [C3]
    exact h3CovsumC_nonneg _ _
  have hn4 : 0 ≤ n4 := by dsimp only [n4]; positivity
  have hKm : 0 ≤ Km := by dsimp only [Km]; positivity
  have hKsum : 0 ≤ Ksum := mul_nonneg (by norm_num) hKm
  refine ⟨min rhoP 1, Real.sqrt Ksum, lt_min hrhoP (by norm_num),
    Real.sqrt_nonneg _, ?_⟩
  intro g hEq hjet T _hT delta hdelta_le hdelta0 hdelta hdeltaZ hT2 a ha
  let x : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖
  let N : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖
  let P : SmoothCcTensor g 0 2 := a • T
  let gm : SmoothRiemannianMetric I M :=
    DifferentialGeometry.PDE.DeTurck.RicciLinearization.metricPerturbationPath
      (I := I) g T 0 hdelta hdeltaZ a
  have hx : 0 ≤ x := norm_nonneg _
  have hN : 0 ≤ N := norm_nonneg _
  have hx1 : x ≤ 1 := hT2.trans (min_le_right _ _)
  have hxrho : x ≤ rhoP := hT2.trans (min_le_left _ _)
  have hxN : x ≤ N := by
    dsimp only [x, N]
    rw [norm_ccHs_eq_smoothHs, norm_ccHs_eq_smoothHs]
    exact ccSpectralEmbed_norm_mono
      (I := I) (M := M) g (by norm_num) T
  have ha2 : a ^ 2 ≤ 1 := by nlinarith [ha.1, ha.2]
  have ha0 : 0 ≤ a := ha.1
  have hP2 : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) P‖ ≤ rhoP := by
    rw [show P = a • T from rfl, ccTensorToHs_smul, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg ha0]
    exact (mul_le_of_le_one_left hx ha.2).trans hxrho
  have hP3 : ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) P‖ ≤ N := by
    rw [show P = a • T from rfl, ccTensorToHs_smul, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg ha0]
    exact mul_le_of_le_one_left hN ha.2
  have hdeltaP : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g P) delta := by
    have h := DifferentialGeometry.PDE.DeTurck.RicciLinearization.convexPerturbation_gFibreOpBound
      (I := I) (M := M) g T 0 hdelta hdeltaZ ha.1 ha.2
    have hscalar : (1 - a) * delta + a * delta = delta := by ring
    rw [hscalar] at h
    simpa only [P, convexPerturbation, smul_zero, zero_add] using h
  have hmem : a ∈ DifferentialGeometry.PDE.DeTurck.RicciLinearization.metricPerturbationPathDomain
      (δ := delta) (δ' := delta) :=
    DifferentialGeometry.PDE.DeTurck.RicciLinearization.Icc_subset_metricPerturbationPathDomain
      (lt_of_le_of_lt hdelta_le (by norm_num))
      (lt_of_le_of_lt hdelta_le (by norm_num)) ha
  have htie : ∀ (y : M) (v w : TangentSpace I y),
      gm.inner y v w = g.inner y v w +
        ccTensorBilinSymm (I := I) g P y v w := by
    intro y v w
    simpa only [gm, P, convexPerturbation, smul_zero, zero_add] using
      DifferentialGeometry.PDE.DeTurck.RicciLinearization.metricPerturbationPath_inner_of_mem
        (I := I) g T 0 hdelta hdeltaZ hmem y v w
  obtain ⟨hpairPt, hpairJet⟩ :=
    hpair g hEq hjet P gm hdelta_le hdelta0 hdeltaP hP2 htie
  have hpairJetN : (∑ j ∈ Finset.range 4,
      ‖iteratedCovGrad (I := I) g 6 2 j
        (cometricDoublePairTraceCoefficient (I := I) (M := M) g gm)‖ ^ 2) ≤
      (Cj * (1 + N)) ^ 2 := by
    exact hpairJet.trans
      (pow_le_pow_left₀ (mul_nonneg hCj (by positivity))
        (mul_le_mul_of_nonneg_left (add_le_add le_rfl hP3) hCj) 2)
  obtain ⟨hact2, hact3⟩ := hKcurv.bounds g hEq hjet
  have hmor' : ∀ (S : SmoothCcTensor g 0 2) (y : M),
      riemannianFiberNormSq (I := I) (M := M) g 0 2 y (S.toSection y) ≤
        Cmor ^ 2 * ∑ a ∈ Finset.range (Module.finrank ℝ E / 2 + 2),
          ‖iteratedCovGrad (I := I) g 0 2 a S‖ ^ 2 := by
    intro S y
    rw [hDim]
    norm_num
    exact hmor g hEq (hjet 1 (by norm_num)) (hjet 2 (by norm_num)) S y
  have hTpt : ∀ y : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 2 y (T.toSection y) ≤
        (C2 * x) ^ 2 := by
    intro y
    simpa only [C2, x, mul_pow] using
      hs2_fiber_sq_action (I := I) (M := M) hDim g hact2 hmor' T y
  have hTjet : (∑ j ∈ Finset.range 4,
      ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) ≤ (C3 * N) ^ 2 := by
    calc
      _ ≤ (∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g 0 2 j T‖) ^ 2 :=
        Finset.sum_sq_le_sq_sum_of_nonneg (fun j _ => norm_nonneg _)
      _ ≤ (C3 * N) ^ 2 := pow_le_pow_left₀
        (Finset.sum_nonneg fun j _ => norm_nonneg _)
        (by simpa only [C3, N] using
          covsum_hs_three (I := I) (M := M) g 2 hact2 hact3 T) 2
  let V : Fin 3 → SmoothCcTensor g 4 2 := fun i =>
    curvatureDecompositionMonomialCoeffField (I := I) (M := M) g gm
      (ccTensorUnitValueSection (I := I) (M := M) g T)
      (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g T)
      (lieDecompositionQ i)
  let U : Fin 3 → SmoothCcTensor g 4 2 := fun i => lieDecompositionEps i • V i
  have hmono (i : Fin 3) : (∑ j ∈ Finset.range 4,
      ‖iteratedCovGrad (I := I) g 4 2 j (V i)‖ ^ 2) ≤ Km * N ^ 2 := by
    let W : SmoothCcTensor g 4 6 :=
      monoExt (I := I) (M := M) g 0 2 4
        (RicciDeTurckLowOrder.monoPerm (lieDecompositionQ i)) T
    have hWpt : ∀ y : M,
        riemannianFiberNormSq (I := I) (M := M) g 4 6 y
          (W.toSection y) ≤ (Real.sqrt n4 * (C2 * x)) ^ 2 := by
      intro y
      refine (mono_ext_pointwise (I := I) (M := M) g 0 2 4
        (RicciDeTurckLowOrder.monoPerm (lieDecompositionQ i)) T y).trans ?_
      rw [mul_pow, Real.sq_sqrt hn4]
      exact mul_le_mul_of_nonneg_left (hTpt y) hn4
    have hWjet : (∑ j ∈ Finset.range 4,
        ‖iteratedCovGrad (I := I) g 4 6 j W‖ ^ 2) ≤
        n4 * (C3 * N) ^ 2 := by
      refine (monoExtJet (I := I) (M := M) g 0 2 4 3
        (RicciDeTurckLowOrder.monoPerm (lieDecompositionQ i)) T).trans ?_
      exact mul_le_mul_of_nonneg_left hTjet hn4
    have happRaw := happ g hEq
      (cometricDoublePairTraceCoefficient (I := I) (M := M) g gm) W Cp
      (Real.sqrt n4 * (C2 * x)) hCp
      (mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg hC2 hx))
      hpairPt hWpt
    dsimp only [V]
    rw [RicciDeTurckLowOrder.curvMono_eq]
    change (∑ j ∈ Finset.range 4,
      ‖iteratedCovGrad (I := I) g 4 2 j
        (ccOperatorFieldComp (I := I) (M := M) g 4 6 2
          (cometricDoublePairTraceCoefficient (I := I) (M := M) g gm) W)‖ ^ 2) ≤ _
    refine happRaw.trans ?_
    rw [mul_pow, Real.sq_sqrt hn4]
    have hxP : x * (1 + N) ≤ 2 * N := by
      have hxn : x * N ≤ N := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hx1 hN
      nlinarith
    have hxPsq : x ^ 2 * (1 + N) ^ 2 ≤ 4 * N ^ 2 := by
      have hs := pow_le_pow_left₀ (mul_nonneg hx (by positivity)) hxP 2
      nlinarith
    calc
      Ca * ((n4 * (C2 * x) ^ 2) *
          (∑ j ∈ Finset.range 4,
            ‖iteratedCovGrad (I := I) g 6 2 j
              (cometricDoublePairTraceCoefficient (I := I) (M := M) g gm)‖ ^ 2) +
        Cp ^ 2 * (∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g 4 6 j W‖ ^ 2)) ≤
        Ca * ((n4 * (C2 * x) ^ 2) * (Cj * (1 + N)) ^ 2 +
          Cp ^ 2 * (n4 * (C3 * N) ^ 2)) := by
            exact mul_le_mul_of_nonneg_left
              (add_le_add
                (mul_le_mul_of_nonneg_left hpairJetN
                  (mul_nonneg hn4 (sq_nonneg _)))
                (mul_le_mul_of_nonneg_left hWjet (sq_nonneg Cp))) hCa
      _ ≤ Km * N ^ 2 := by
        dsimp only [Km]
        conv_rhs => rw [mul_assoc]
        apply mul_le_mul_of_nonneg_left _ hCa
        have hfirst :
            (n4 * (C2 * x) ^ 2) * (Cj * (1 + N)) ^ 2 ≤
              (n4 * C2 ^ 2 * Cj ^ 2) * (4 * N ^ 2) := by
          calc
            _ = (n4 * C2 ^ 2 * Cj ^ 2) *
                (x ^ 2 * (1 + N) ^ 2) := by ring
            _ ≤ (n4 * C2 ^ 2 * Cj ^ 2) * (4 * N ^ 2) :=
              mul_le_mul_of_nonneg_left hxPsq
                (mul_nonneg (mul_nonneg hn4 (sq_nonneg C2)) (sq_nonneg Cj))
        calc
          (n4 * (C2 * x) ^ 2) * (Cj * (1 + N)) ^ 2 +
              Cp ^ 2 * (n4 * (C3 * N) ^ 2) ≤
            (n4 * C2 ^ 2 * Cj ^ 2) * (4 * N ^ 2) +
              (Cp ^ 2 * (n4 * C3 ^ 2)) * N ^ 2 := by
                exact add_le_add hfirst (by ring_nf; exact le_rfl)
          _ = (4 * (n4 * C2 ^ 2) * Cj ^ 2 + Cp ^ 2 *
              (n4 * C3 ^ 2)) * N ^ 2 := by ring
  have hU (i : Fin 3) : (∑ j ∈ Finset.range 4,
      ‖iteratedCovGrad (I := I) g 4 2 j (U i)‖ ^ 2) ≤ Km * N ^ 2 := by
    dsimp only [U]
    rw [jet_four_smul]
    have heps : lieDecompositionEps i ^ 2 = (1 : ℝ) := by
      fin_cases i <;> norm_num [lieDecompositionEps]
    rw [heps, one_mul]
    exact hmono i
  have hdecomposition :
      lieDecomposition2 (I := I) (M := M) g T hdelta hdeltaZ a =
        a • (U 0 + U 1 + U 2) := by
    rw [lieDecomposition2, deTurckLieCovariantDerivativeDecompositionC2Family_eq_symmS_weight]
    simp only [Fin.sum_univ_three, U, V, gm,
      symm_self (I := I) (M := M) g T _hT]
  have h01 : (∑ j ∈ Finset.range 4,
      ‖iteratedCovGrad (I := I) g 4 2 j (U 0 + U 1)‖ ^ 2) ≤
      4 * (Km * N ^ 2) := by
    refine (jet_four_add (I := I) (M := M) g (U 0) (U 1)).trans ?_
    calc
      2 * ((∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g 4 2 j (U 0)‖ ^ 2) +
        ∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g 4 2 j (U 1)‖ ^ 2) ≤
          2 * (Km * N ^ 2 + Km * N ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add (hU 0) (hU 1)) (by norm_num)
      _ = 4 * (Km * N ^ 2) := by ring
  have hsum : (∑ j ∈ Finset.range 4,
      ‖iteratedCovGrad (I := I) g 4 2 j (U 0 + U 1 + U 2)‖ ^ 2) ≤
      Ksum * N ^ 2 := by
    refine (jet_four_add (I := I) (M := M) g (U 0 + U 1) (U 2)).trans ?_
    calc
      2 * ((∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g 4 2 j (U 0 + U 1)‖ ^ 2) +
        ∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g 4 2 j (U 2)‖ ^ 2) ≤
          2 * (4 * (Km * N ^ 2) + Km * N ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add h01 (hU 2)) (by norm_num)
      _ = Ksum * N ^ 2 := by dsimp only [Ksum]; ring
  rw [hdecomposition, jet_four_smul]
  calc
    a ^ 2 * (∑ j ∈ Finset.range 4,
      ‖iteratedCovGrad (I := I) g 4 2 j (U 0 + U 1 + U 2)‖ ^ 2) ≤
        ∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g 4 2 j (U 0 + U 1 + U 2)‖ ^ 2 :=
      mul_le_of_le_one_left (Finset.sum_nonneg fun j _ => sq_nonneg _) ha2
    _ ≤ Ksum * N ^ 2 := hsum
    _ = (Real.sqrt Ksum * N) ^ 2 := by rw [mul_pow, Real.sq_sqrt hKsum]

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem ricciConnectionDifferenceDerivativeMetricWeight_h3_of_metricComparison
    (g : SmoothRiemannianMetric I M)
    (gm : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (x N Fq C2 C3 Cf Cw : ℝ)
    (hFq : 0 ≤ Fq) (hC2 : 0 ≤ C2) (hCw : 0 ≤ Cw) (hx : 0 ≤ x)
    (hFpt : ∀ y : M,
      riemannianFiberNormSq (I := I) (M := M) g 2 2 y
        ((slotInsertEndoCc (I := I) (M := M) g 1
          (metricComparisonEndomorphismField (I := I) (M := M) g gm)).toSection y) ≤ Fq)
    (hFjet : (∑ j ∈ Finset.range 4,
      ‖iteratedCovGrad (I := I) g 2 2 j
        (slotInsertEndoCc (I := I) (M := M) g 1
          (metricComparisonEndomorphismField (I := I) (M := M) g gm))‖ ^ 2) ≤
            (Cf * (1 + N)) ^ 2)
    (hTpt : ∀ y : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 2 y (T.toSection y) ≤
        (C2 * x) ^ 2)
    (hTjet : (∑ j ∈ Finset.range 4,
      ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) ≤ (C3 * N) ^ 2)
    (hxPsq : x ^ 2 * (1 + N) ^ 2 ≤ 4 * N ^ 2)
    (happW : ∀ (Φ : SmoothCcTensor g 2 2) (W : SmoothCcTensor g 0 2)
      (A B : ℝ), 0 ≤ A → 0 ≤ B →
      (∀ y : M, riemannianFiberNormSq (I := I) (M := M) g 2 2 y
        (Φ.toSection y) ≤ A ^ 2) →
      (∀ y : M, riemannianFiberNormSq (I := I) (M := M) g 0 2 y
        (W.toSection y) ≤ B ^ 2) →
      (∑ j ∈ Finset.range 4,
        ‖iteratedCovGrad (I := I) g 0 2 j
          (ccOperatorFieldComp (I := I) (M := M) g 0 2 2 Φ W)‖ ^ 2) ≤
        Cw * (B ^ 2 * (∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g 2 2 j Φ‖ ^ 2) +
          A ^ 2 * (∑ j ∈ Finset.range 4,
            ‖iteratedCovGrad (I := I) g 0 2 j W‖ ^ 2))) :
    let Kw := Cw * (4 * C2 ^ 2 * Cf ^ 2 + Fq * C3 ^ 2)
    (∀ y : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 2 y
        ((RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeMetricWeight (I := I) (M := M) g gm T).toSection y) ≤
          (Real.sqrt Fq * (C2 * x)) ^ 2) ∧
      (∑ j ∈ Finset.range 4,
        ‖iteratedCovGrad (I := I) g 0 2 j
          (RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeMetricWeight (I := I) (M := M) g gm T)‖ ^ 2) ≤
            Kw * N ^ 2 := by
  let F : SmoothCcTensor g 2 2 :=
    slotInsertEndoCc (I := I) (M := M) g 1
      (metricComparisonEndomorphismField (I := I) (M := M) g gm)
  let Kw : ℝ := Cw * (4 * C2 ^ 2 * Cf ^ 2 + Fq * C3 ^ 2)
  constructor
  · intro y
    have hc := riemannianFiberNormSq_compRS_le_mul
      (I := I) (M := M) g 0 2 2 y (F.toSection y) (T.toSection y)
    rw [← operatorFieldComposition_toSection] at hc
    have hm := mul_le_mul (hFpt y) (hTpt y)
      (riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 2 y _)
      hFq
    calc
      _ ≤ riemannianFiberNormSq (I := I) (M := M) g 2 2 y (F.toSection y) *
          riemannianFiberNormSq (I := I) (M := M) g 0 2 y (T.toSection y) := by
        simpa only [F, RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeMetricWeight,
          operatorFieldComposition_zero_eq_operatorFieldApply] using hc
      _ ≤ Fq * (C2 * x) ^ 2 := hm
      _ = (Real.sqrt Fq * (C2 * x)) ^ 2 := by
        calc
          Fq * (C2 * x) ^ 2 = Real.sqrt Fq ^ 2 * (C2 * x) ^ 2 := by
            rw [Real.sq_sqrt hFq]
          _ = _ := by ring
  · have hr := happW F T (Real.sqrt Fq) (C2 * x)
      (Real.sqrt_nonneg _) (mul_nonneg hC2 hx)
      (fun y => by simpa only [Real.sq_sqrt hFq] using hFpt y) hTpt
    change (∑ j ∈ Finset.range 4,
      ‖iteratedCovGrad (I := I) g 0 2 j
        (ccOperatorFieldComp (I := I) (M := M) g 0 2 2 F T)‖ ^ 2) ≤ Kw * N ^ 2
    refine hr.trans ?_
    calc
      Cw * ((C2 * x) ^ 2 * (∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g 2 2 j F‖ ^ 2) +
        Real.sqrt Fq ^ 2 * (∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2)) ≤
        Cw * ((C2 * x) ^ 2 * (Cf * (1 + N)) ^ 2 +
          Fq * (C3 * N) ^ 2) := by
            rw [Real.sq_sqrt hFq]
            exact mul_le_mul_of_nonneg_left
              (add_le_add
                (mul_le_mul_of_nonneg_left hFjet (sq_nonneg _))
                (mul_le_mul_of_nonneg_left hTjet hFq)) hCw
      _ ≤ Kw * N ^ 2 := by
        dsimp only [Kw]
        conv_rhs => rw [mul_assoc]
        apply mul_le_mul_of_nonneg_left _ hCw
        calc
          (C2 * x) ^ 2 * (Cf * (1 + N)) ^ 2 + Fq * (C3 * N) ^ 2 ≤
              (4 * C2 ^ 2 * Cf ^ 2) * N ^ 2 +
                (Fq * C3 ^ 2) * N ^ 2 := by
            exact add_le_add
              (by
                calc
                  _ = (C2 ^ 2 * Cf ^ 2) * (x ^ 2 * (1 + N) ^ 2) := by ring
                  _ ≤ (C2 ^ 2 * Cf ^ 2) * (4 * N ^ 2) :=
                    mul_le_mul_of_nonneg_left hxPsq
                      (mul_nonneg (sq_nonneg C2) (sq_nonneg Cf))
                  _ = (4 * C2 ^ 2 * Cf ^ 2) * N ^ 2 := by ring)
              (by ring_nf; exact le_rfl)
          _ = (4 * C2 ^ 2 * Cf ^ 2 + Fq * C3 ^ 2) * N ^ 2 := by ring

theorem ricciConnectionDifferenceDerivativeTransposedCoefficient_h3_of_metricWeight
    (g : SmoothRiemannianMetric I M)
    (gm : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (x N n4 Fq C2 Kw Qp Qj Cm : ℝ)
    (hn4 : 0 ≤ n4) (hn4eq : (Module.finrank ℝ E : ℝ) ^ 4 = n4)
    (hFq : 0 ≤ Fq) (hC2 : 0 ≤ C2) (hQp : 0 ≤ Qp) (hCm : 0 ≤ Cm)
    (hx : 0 ≤ x) (hxN : x ≤ N)
    (hpairPt : ∀ y : M,
      riemannianFiberNormSq (I := I) (M := M) g 6 2 y
        ((cometricDoublePairTraceCoefficient (I := I) (M := M) g g).toSection y) ≤ Qp ^ 2)
    (hpairJet : (∑ j ∈ Finset.range 4,
      ‖iteratedCovGrad (I := I) g 6 2 j
        (cometricDoublePairTraceCoefficient (I := I) (M := M) g g)‖ ^ 2) ≤ Qj ^ 2)
    (hWpt : ∀ y : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 2 y
        ((RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeMetricWeight (I := I) (M := M) g gm T).toSection y) ≤
          (Real.sqrt Fq * (C2 * x)) ^ 2)
    (hWjet : (∑ j ∈ Finset.range 4,
      ‖iteratedCovGrad (I := I) g 0 2 j
        (RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeMetricWeight (I := I) (M := M) g gm T)‖ ^ 2) ≤
          Kw * N ^ 2)
    (happM : ∀ (Φ : SmoothCcTensor g 6 2) (W : SmoothCcTensor g 4 6)
      (A B : ℝ), 0 ≤ A → 0 ≤ B →
      (∀ y : M, riemannianFiberNormSq (I := I) (M := M) g 6 2 y
        (Φ.toSection y) ≤ A ^ 2) →
      (∀ y : M, riemannianFiberNormSq (I := I) (M := M) g 4 6 y
        (W.toSection y) ≤ B ^ 2) →
      (∑ j ∈ Finset.range 4,
        ‖iteratedCovGrad (I := I) g 4 2 j
          (ccOperatorFieldComp (I := I) (M := M) g 4 6 2 Φ W)‖ ^ 2) ≤
        Cm * (B ^ 2 * (∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g 6 2 j Φ‖ ^ 2) +
          A ^ 2 * (∑ j ∈ Finset.range 4,
            ‖iteratedCovGrad (I := I) g 4 6 j W‖ ^ 2))) :
    let Wp := Fq * C2 ^ 2
    let Km := Cm * (n4 * Wp * Qj ^ 2 + Qp ^ 2 * (n4 * Kw))
    let Mp := Qp ^ 2 * (n4 * Wp)
    (∀ y : M,
      riemannianFiberNormSq (I := I) (M := M) g 4 2 y
        ((RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeTransposedCoefficient (I := I) (M := M) g gm T).toSection y) ≤
          (4 * Mp) * x ^ 2) ∧
      (∑ j ∈ Finset.range 4,
        ‖iteratedCovGrad (I := I) g 4 2 j
          (RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeTransposedCoefficient (I := I) (M := M) g gm T)‖ ^ 2) ≤
            (4 * Km) * N ^ 2 := by
  classical
  let W : SmoothCcTensor g 0 2 :=
    RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeMetricWeight (I := I) (M := M) g gm T
  let Wp : ℝ := Fq * C2 ^ 2
  let Km : ℝ := Cm * (n4 * Wp * Qj ^ 2 + Qp ^ 2 * (n4 * Kw))
  let Mp : ℝ := Qp ^ 2 * (n4 * Wp)
  have hWp : 0 ≤ Wp := by dsimp only [Wp]; positivity
  let V : Equiv.Perm (Fin 4) → SmoothCcTensor g 4 2 := fun e =>
    RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeTransposedMonomial (I := I) (M := M) g gm T e
  let Z : Equiv.Perm (Fin 4) → SmoothCcTensor g 4 6 := fun e =>
    monoExt (I := I) (M := M) g 0 2 4 (RicciDeTurckLowOrder.monoPerm e) W
  have hZpt (e : Equiv.Perm (Fin 4)) : ∀ y : M,
      riemannianFiberNormSq (I := I) (M := M) g 4 6 y ((Z e).toSection y) ≤
        (Real.sqrt n4 * (Real.sqrt Fq * (C2 * x))) ^ 2 := by
    intro y
    refine (mono_ext_pointwise (I := I) (M := M) g 0 2 4
      (RicciDeTurckLowOrder.monoPerm e) W y).trans ?_
    rw [hn4eq, mul_pow, Real.sq_sqrt hn4]
    exact mul_le_mul_of_nonneg_left (by simpa only [W] using hWpt y) hn4
  have hZjet (e : Equiv.Perm (Fin 4)) : (∑ j ∈ Finset.range 4,
      ‖iteratedCovGrad (I := I) g 4 6 j (Z e)‖ ^ 2) ≤ n4 * (Kw * N ^ 2) := by
    refine (monoExtJet (I := I) (M := M) g 0 2 4 3
      (RicciDeTurckLowOrder.monoPerm e) W).trans ?_
    rw [hn4eq]
    exact mul_le_mul_of_nonneg_left (by simpa only [W] using hWjet) hn4
  have hVeq (e : Equiv.Perm (Fin 4)) :
      V e = ccOperatorFieldComp (I := I) (M := M) g 4 6 2
        (cometricDoublePairTraceCoefficient (I := I) (M := M) g g) (Z e) := by
    dsimp only [V, Z, W, RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeTransposedMonomial,
      RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeMetricWeight]
    rw [RicciDeTurckLowOrder.curvMono_eq]
    rfl
  have hVpt (e : Equiv.Perm (Fin 4)) : ∀ y : M,
      riemannianFiberNormSq (I := I) (M := M) g 4 2 y ((V e).toSection y) ≤
        Mp * x ^ 2 := by
    intro y
    have hc := riemannianFiberNormSq_compRS_le_mul
      (I := I) (M := M) g 4 6 2 y
        ((cometricDoublePairTraceCoefficient (I := I) (M := M) g g).toSection y) ((Z e).toSection y)
    rw [hVeq e]
    have hc' := (by simpa only [operatorFieldComposition_toSection] using hc)
    refine hc'.trans ?_
    refine (mul_le_mul (hpairPt y) (hZpt e y)
      (riemannianFiberNormSq_nonneg (I := I) (M := M) g 4 6 y _)
      (sq_nonneg Qp)).trans ?_
    rw [mul_pow, Real.sq_sqrt hn4, mul_pow, Real.sq_sqrt hFq]
    dsimp only [Mp, Wp]
    ring_nf
    exact le_rfl
  have hVjet (e : Equiv.Perm (Fin 4)) : (∑ j ∈ Finset.range 4,
      ‖iteratedCovGrad (I := I) g 4 2 j (V e)‖ ^ 2) ≤ Km * N ^ 2 := by
    rw [hVeq e]
    refine (happM (cometricDoublePairTraceCoefficient (I := I) (M := M) g g) (Z e)
      Qp (Real.sqrt n4 * (Real.sqrt Fq * (C2 * x))) hQp
      (mul_nonneg (Real.sqrt_nonneg _)
        (mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg hC2 hx)))
      hpairPt (hZpt e)).trans ?_
    have hlead :
        (Real.sqrt n4 * (Real.sqrt Fq * (C2 * x))) ^ 2 *
            (∑ j ∈ Finset.range 4,
              ‖iteratedCovGrad (I := I) g 6 2 j
                (cometricDoublePairTraceCoefficient (I := I) (M := M) g g)‖ ^ 2) ≤
          (n4 * Wp * x ^ 2) * Qj ^ 2 := by
      calc
        _ = (n4 * Wp * x ^ 2) * (∑ j ∈ Finset.range 4,
            ‖iteratedCovGrad (I := I) g 6 2 j
              (cometricDoublePairTraceCoefficient (I := I) (M := M) g g)‖ ^ 2) := by
                rw [mul_pow, Real.sq_sqrt hn4, mul_pow, Real.sq_sqrt hFq]
                dsimp only [Wp]
                ring
        _ ≤ (n4 * Wp * x ^ 2) * Qj ^ 2 :=
          mul_le_mul_of_nonneg_left hpairJet
            (mul_nonneg (mul_nonneg hn4 hWp) (sq_nonneg x))
    calc
      Cm * (((Real.sqrt n4 * (Real.sqrt Fq * (C2 * x))) ^ 2) *
          (∑ j ∈ Finset.range 4,
            ‖iteratedCovGrad (I := I) g 6 2 j
              (cometricDoublePairTraceCoefficient (I := I) (M := M) g g)‖ ^ 2) +
        Qp ^ 2 * (∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g 4 6 j (Z e)‖ ^ 2)) ≤
        Cm * ((n4 * Wp * x ^ 2) * Qj ^ 2 +
          Qp ^ 2 * (n4 * (Kw * N ^ 2))) := by
            exact mul_le_mul_of_nonneg_left
              (add_le_add hlead
                (mul_le_mul_of_nonneg_left (hZjet e) (sq_nonneg Qp))) hCm
      _ ≤ Km * N ^ 2 := by
        dsimp only [Km]
        conv_rhs => rw [mul_assoc]
        apply mul_le_mul_of_nonneg_left _ hCm
        calc
          (n4 * Wp * x ^ 2) * Qj ^ 2 + Qp ^ 2 * (n4 * (Kw * N ^ 2)) ≤
            (n4 * Wp * Qj ^ 2) * N ^ 2 +
              (Qp ^ 2 * (n4 * Kw)) * N ^ 2 := by
                exact add_le_add
                  (by
                    calc
                      _ = (n4 * Wp * Qj ^ 2) * x ^ 2 := by ring
                      _ ≤ (n4 * Wp * Qj ^ 2) * N ^ 2 :=
                        mul_le_mul_of_nonneg_left
                          (pow_le_pow_left₀ hx hxN 2) (by positivity))
                  (by ring_nf; exact le_rfl)
          _ = (n4 * Wp * Qj ^ 2 + Qp ^ 2 * (n4 * Kw)) * N ^ 2 := by ring
  have htransEq : RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeTransposedCoefficient (I := I) (M := M) g gm T =
      V RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeCyclicPermutation - V RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeFirstPairSwap := by
    rfl
  constructor
  · intro y
    rw [htransEq, SmoothCcTensor.toSection_sub]
    refine (riemannianFiberNormSq_sub_le (I := I) (M := M) g 4 2 y _ _).trans ?_
    calc
      2 * riemannianFiberNormSq (I := I) (M := M) g 4 2 y
          ((V RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeCyclicPermutation).toSection y) +
        2 * riemannianFiberNormSq (I := I) (M := M) g 4 2 y
          ((V RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeFirstPairSwap).toSection y) ≤
        2 * (Mp * x ^ 2) + 2 * (Mp * x ^ 2) :=
          add_le_add
            (mul_le_mul_of_nonneg_left (hVpt RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeCyclicPermutation y) (by norm_num))
            (mul_le_mul_of_nonneg_left (hVpt RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeFirstPairSwap y) (by norm_num))
      _ = (4 * Mp) * x ^ 2 := by ring
  · rw [htransEq, sub_eq_add_neg, ← neg_one_smul ℝ (V RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeFirstPairSwap)]
    refine (jet_four_add (I := I) (M := M) g
      (V RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeCyclicPermutation) ((-1 : ℝ) • V RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeFirstPairSwap)).trans ?_
    rw [jet_four_smul]
    norm_num
    calc
      2 * ((∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g 4 2 j (V RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeCyclicPermutation)‖ ^ 2) +
        ∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g 4 2 j (V RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeFirstPairSwap)‖ ^ 2) ≤
          2 * (Km * N ^ 2 + Km * N ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add (hVjet _) (hVjet _)) (by norm_num)
      _ = (4 * Km) * N ^ 2 := by ring

omit [BoundarylessManifold I M] in
theorem ricciConnectionDifferenceTopOrderCoefficient_h3_of_transposed_and_principal
    (g : SmoothRiemannianMetric I M)
    (gm : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (x N Dp Dj Kt Tp Cr : ℝ)
    (hDp : 0 ≤ Dp) (hTp : 0 ≤ Tp) (hCr : 0 ≤ Cr)
    (hx : 0 ≤ x) (hxPsq : x ^ 2 * (1 + N) ^ 2 ≤ 4 * N ^ 2)
    (htransPt : ∀ y : M,
      riemannianFiberNormSq (I := I) (M := M) g 4 2 y
        ((RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeTransposedCoefficient (I := I) (M := M) g gm T).toSection y) ≤
          Tp * x ^ 2)
    (htransJet : (∑ j ∈ Finset.range 4,
      ‖iteratedCovGrad (I := I) g 4 2 j
        (RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeTransposedCoefficient (I := I) (M := M) g gm T)‖ ^ 2) ≤
          Kt * N ^ 2)
    (hdagPt : ∀ y : M,
      riemannianFiberNormSq (I := I) (M := M) g 4 4 y
        ((RicciDeTurckLowOrder.ricciConnectionPrincipalCoefficient (I := I) (M := M) g gm).toSection y) ≤
          Dp ^ 2)
    (hdagJet : (∑ j ∈ Finset.range 4,
      ‖iteratedCovGrad (I := I) g 4 4 j
        (RicciDeTurckLowOrder.ricciConnectionPrincipalCoefficient (I := I) (M := M) g gm)‖ ^ 2) ≤
          (Dj * (1 + N)) ^ 2)
    (happR : ∀ (Φ : SmoothCcTensor g 4 2) (W : SmoothCcTensor g 4 4)
      (A B : ℝ), 0 ≤ A → 0 ≤ B →
      (∀ y : M, riemannianFiberNormSq (I := I) (M := M) g 4 2 y
        (Φ.toSection y) ≤ A ^ 2) →
      (∀ y : M, riemannianFiberNormSq (I := I) (M := M) g 4 4 y
        (W.toSection y) ≤ B ^ 2) →
      (∑ j ∈ Finset.range 4,
        ‖iteratedCovGrad (I := I) g 4 2 j
          (ccOperatorFieldComp (I := I) (M := M) g 4 4 2 Φ W)‖ ^ 2) ≤
        Cr * (B ^ 2 * (∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g 4 2 j Φ‖ ^ 2) +
          A ^ 2 * (∑ j ∈ Finset.range 4,
            ‖iteratedCovGrad (I := I) g 4 4 j W‖ ^ 2))) :
    let Kr := Cr * (Dp ^ 2 * Kt + Tp * (4 * Dj ^ 2))
    (∑ j ∈ Finset.range 4,
      ‖iteratedCovGrad (I := I) g 4 2 j
        (RicciDeTurckLowOrder.ricciConnectionDifferenceTopOrderCoefficient (I := I) (M := M) g gm T)‖ ^ 2) ≤
          Kr * N ^ 2 := by
  let Kr : ℝ := Cr * (Dp ^ 2 * Kt + Tp * (4 * Dj ^ 2))
  unfold RicciDeTurckLowOrder.ricciConnectionDifferenceTopOrderCoefficient
  refine (happR
    (RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeTransposedCoefficient (I := I) (M := M) g gm T)
    (RicciDeTurckLowOrder.ricciConnectionPrincipalCoefficient (I := I) (M := M) g gm)
    (Real.sqrt Tp * x) Dp
    (mul_nonneg (Real.sqrt_nonneg _) hx) hDp
    (fun y => by simpa only [mul_pow, Real.sq_sqrt hTp] using htransPt y)
    hdagPt).trans ?_
  calc
    Cr * (Dp ^ 2 * (∑ j ∈ Finset.range 4,
        ‖iteratedCovGrad (I := I) g 4 2 j
          (RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeTransposedCoefficient (I := I) (M := M) g gm T)‖ ^ 2) +
      (Real.sqrt Tp * x) ^ 2 * (∑ j ∈ Finset.range 4,
        ‖iteratedCovGrad (I := I) g 4 4 j
          (RicciDeTurckLowOrder.ricciConnectionPrincipalCoefficient (I := I) (M := M) g gm)‖ ^ 2)) ≤
      Cr * (Dp ^ 2 * (Kt * N ^ 2) +
        (Tp * x ^ 2) * (Dj * (1 + N)) ^ 2) := by
          rw [mul_pow, Real.sq_sqrt hTp]
          exact mul_le_mul_of_nonneg_left
            (add_le_add
              (mul_le_mul_of_nonneg_left htransJet (sq_nonneg Dp))
              (mul_le_mul_of_nonneg_left hdagJet
                (mul_nonneg hTp (sq_nonneg x)))) hCr
    _ ≤ Kr * N ^ 2 := by
      dsimp only [Kr]
      conv_rhs => rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ hCr
      calc
        Dp ^ 2 * (Kt * N ^ 2) + (Tp * x ^ 2) * (Dj * (1 + N)) ^ 2 ≤
          (Dp ^ 2 * Kt) * N ^ 2 + (Tp * (4 * Dj ^ 2)) * N ^ 2 := by
            exact add_le_add (by ring_nf; exact le_rfl) (by
              calc
                _ = (Tp * Dj ^ 2) * (x ^ 2 * (1 + N) ^ 2) := by ring
                _ ≤ (Tp * Dj ^ 2) * (4 * N ^ 2) :=
                  mul_le_mul_of_nonneg_left hxPsq
                    (mul_nonneg hTp (sq_nonneg Dj))
                _ = (Tp * (4 * Dj ^ 2)) * N ^ 2 := by ring)
        _ = (Dp ^ 2 * Kt + Tp * (4 * Dj ^ 2)) * N ^ 2 := by ring

theorem ricciConnectionDifferenceTopOrderCoefficient_h3_of_metricWeight_and_principal
    (g : SmoothRiemannianMetric I M)
    (gm : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (x N n4 Fq C2 Kw Qp Qj Cm Dp Dj Cr : ℝ)
    (hn4 : 0 ≤ n4) (hn4eq : (Module.finrank ℝ E : ℝ) ^ 4 = n4)
    (hFq : 0 ≤ Fq) (hC2 : 0 ≤ C2) (hQp : 0 ≤ Qp)
    (hCm : 0 ≤ Cm) (hDp : 0 ≤ Dp) (hCr : 0 ≤ Cr)
    (hx : 0 ≤ x) (hxN : x ≤ N)
    (hxPsq : x ^ 2 * (1 + N) ^ 2 ≤ 4 * N ^ 2)
    (hpairPt : ∀ y : M,
      riemannianFiberNormSq (I := I) (M := M) g 6 2 y
        ((cometricDoublePairTraceCoefficient (I := I) (M := M) g g).toSection y) ≤ Qp ^ 2)
    (hpairJet : (∑ j ∈ Finset.range 4,
      ‖iteratedCovGrad (I := I) g 6 2 j
        (cometricDoublePairTraceCoefficient (I := I) (M := M) g g)‖ ^ 2) ≤ Qj ^ 2)
    (hWpt : ∀ y : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 2 y
        ((RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeMetricWeight (I := I) (M := M) g gm T).toSection y) ≤
          (Real.sqrt Fq * (C2 * x)) ^ 2)
    (hWjet : (∑ j ∈ Finset.range 4,
      ‖iteratedCovGrad (I := I) g 0 2 j
        (RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeMetricWeight (I := I) (M := M) g gm T)‖ ^ 2) ≤
          Kw * N ^ 2)
    (hdagPt : ∀ y : M,
      riemannianFiberNormSq (I := I) (M := M) g 4 4 y
        ((RicciDeTurckLowOrder.ricciConnectionPrincipalCoefficient (I := I) (M := M) g gm).toSection y) ≤
          Dp ^ 2)
    (hdagJet : (∑ j ∈ Finset.range 4,
      ‖iteratedCovGrad (I := I) g 4 4 j
        (RicciDeTurckLowOrder.ricciConnectionPrincipalCoefficient (I := I) (M := M) g gm)‖ ^ 2) ≤
          (Dj * (1 + N)) ^ 2)
    (happM : ∀ (Φ : SmoothCcTensor g 6 2) (W : SmoothCcTensor g 4 6)
      (A B : ℝ), 0 ≤ A → 0 ≤ B →
      (∀ y : M, riemannianFiberNormSq (I := I) (M := M) g 6 2 y
        (Φ.toSection y) ≤ A ^ 2) →
      (∀ y : M, riemannianFiberNormSq (I := I) (M := M) g 4 6 y
        (W.toSection y) ≤ B ^ 2) →
      (∑ j ∈ Finset.range 4,
        ‖iteratedCovGrad (I := I) g 4 2 j
          (ccOperatorFieldComp (I := I) (M := M) g 4 6 2 Φ W)‖ ^ 2) ≤
        Cm * (B ^ 2 * (∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g 6 2 j Φ‖ ^ 2) +
          A ^ 2 * (∑ j ∈ Finset.range 4,
            ‖iteratedCovGrad (I := I) g 4 6 j W‖ ^ 2)))
    (happR : ∀ (Φ : SmoothCcTensor g 4 2) (W : SmoothCcTensor g 4 4)
      (A B : ℝ), 0 ≤ A → 0 ≤ B →
      (∀ y : M, riemannianFiberNormSq (I := I) (M := M) g 4 2 y
        (Φ.toSection y) ≤ A ^ 2) →
      (∀ y : M, riemannianFiberNormSq (I := I) (M := M) g 4 4 y
        (W.toSection y) ≤ B ^ 2) →
      (∑ j ∈ Finset.range 4,
        ‖iteratedCovGrad (I := I) g 4 2 j
          (ccOperatorFieldComp (I := I) (M := M) g 4 4 2 Φ W)‖ ^ 2) ≤
        Cr * (B ^ 2 * (∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g 4 2 j Φ‖ ^ 2) +
          A ^ 2 * (∑ j ∈ Finset.range 4,
            ‖iteratedCovGrad (I := I) g 4 4 j W‖ ^ 2))) :
    let Wp := Fq * C2 ^ 2
    let Km := Cm * (n4 * Wp * Qj ^ 2 + Qp ^ 2 * (n4 * Kw))
    let Mp := Qp ^ 2 * (n4 * Wp)
    let Kt := 4 * Km
    let Tp := 4 * Mp
    let Kr := Cr * (Dp ^ 2 * Kt + Tp * (4 * Dj ^ 2))
    (∑ j ∈ Finset.range 4,
      ‖iteratedCovGrad (I := I) g 4 2 j
        (RicciDeTurckLowOrder.ricciConnectionDifferenceTopOrderCoefficient (I := I) (M := M) g gm T)‖ ^ 2) ≤
          Kr * N ^ 2 := by
  let Wp : ℝ := Fq * C2 ^ 2
  let Km : ℝ := Cm * (n4 * Wp * Qj ^ 2 + Qp ^ 2 * (n4 * Kw))
  let Mp : ℝ := Qp ^ 2 * (n4 * Wp)
  let Kt : ℝ := 4 * Km
  let Tp : ℝ := 4 * Mp
  let Kr : ℝ := Cr * (Dp ^ 2 * Kt + Tp * (4 * Dj ^ 2))
  have hTp : 0 ≤ Tp := by dsimp only [Tp, Mp, Wp]; positivity
  obtain ⟨htransPt, htransJet⟩ := ricciConnectionDifferenceDerivativeTransposedCoefficient_h3_of_metricWeight
    (I := I) (M := M) g gm T x N n4 Fq C2 Kw Qp Qj Cm
    hn4 hn4eq hFq hC2 hQp hCm hx hxN hpairPt hpairJet hWpt hWjet happM
  change (∀ y : M,
      riemannianFiberNormSq (I := I) (M := M) g 4 2 y
        ((RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeTransposedCoefficient (I := I) (M := M) g gm T).toSection y) ≤
          Tp * x ^ 2) at htransPt
  change (∑ j ∈ Finset.range 4,
      ‖iteratedCovGrad (I := I) g 4 2 j
        (RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeTransposedCoefficient (I := I) (M := M) g gm T)‖ ^ 2) ≤
          Kt * N ^ 2 at htransJet
  exact ricciConnectionDifferenceTopOrderCoefficient_h3_of_transposed_and_principal
    (I := I) (M := M) g gm T x N Dp Dj Kt Tp Cr
    hDp hTp hCr hx hxPsq htransPt htransJet hdagPt hdagJet happR

theorem ricciConnectionDifferenceTopOrderCoefficient_h3_uniform
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∃ rho C : ℝ, 0 < rho ∧ 0 ≤ C ∧
      ∀ g : SmoothRiemannianMetric I M,
        MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
        (∀ a : ℕ, a ≤ 3 →
          MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ) →
        ∀ (T : SmoothCcTensor g 0 2)
          {delta : ℝ}, delta ≤ 1 / 3 → 0 ≤ delta →
          ∀ (hdelta : gFibreOpBound (I := I) (M := M) g
              (ccTensorBilinSymm (I := I) g T) delta)
            (hdeltaZ : gFibreOpBound (I := I) (M := M) g
              (ccTensorBilinSymm (I := I) g
                (0 : SmoothCcTensor g 0 2)) delta),
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ rho →
          ∀ {a : ℝ}, a ∈ Set.Icc (0 : ℝ) 1 →
          let gm := DifferentialGeometry.PDE.DeTurck.RicciLinearization.metricPerturbationPath
            (I := I) g T 0 hdelta hdeltaZ a
          (∑ j ∈ Finset.range 4,
            ‖iteratedCovGrad (I := I) g 4 2 j
              (RicciDeTurckLowOrder.ricciConnectionDifferenceTopOrderCoefficient (I := I) (M := M) g gm T)‖ ^ 2) ≤
            (C * ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖) ^ 2 := by
  classical
  obtain ⟨rhoF, Cf, hrhoF, hCf, hfull⟩ :=
    fullRaised_h3_uniform (I := I) (M := M) hDim gBase hΛ
  obtain ⟨rhoD, Dp, Dj, hrhoD, hDp, hDj, hdag⟩ :=
    ricciConnectionPrincipalCoefficient_h3_uniform (I := I) (M := M) hDim gBase hΛ
  obtain ⟨rhoQ, Qp, Qj, hrhoQ, hQp, hQj, hpair⟩ :=
    cometricDoublePairTraceCoefficient_h3_uniform (I := I) (M := M) hDim gBase hΛ
  obtain ⟨Cw, hCw, happW⟩ :=
    operatorFieldComposition_h3_sup_uniform_bound (I := I) (M := M) gBase Λ 0 2 2
  obtain ⟨Cm, hCm, happM⟩ :=
    operatorFieldComposition_h3_sup_uniform_bound (I := I) (M := M) gBase Λ 4 6 2
  obtain ⟨Cr, hCr, happR⟩ :=
    operatorFieldComposition_h3_sup_uniform_bound (I := I) (M := M) gBase Λ 4 4 2
  obtain ⟨Cmor, hCmor, hmor⟩ :=
    morreyRS_uniform (I := I) (M := M) hDim gBase hΛ 0 2
  obtain ⟨Kcurv, hKcurv⟩ :=
    exists_uniform_curvature_action_parameters (I := I) (M := M) gBase hΛ
  let C2 : ℝ := hs2FibreActionC Cmor Kcurv.rankTwo
  let C3 : ℝ := h3CovsumC Kcurv.rankTwo Kcurv.rankThree
  let n : ℝ := Module.finrank ℝ E
  let n4 : ℝ := n ^ 4
  let Fq : ℝ := n * (n ^ 2 * (1 / (1 - (1 / 3 : ℝ))) ^ 2)
  let Kw : ℝ := Cw * (4 * C2 ^ 2 * Cf ^ 2 + Fq * C3 ^ 2)
  let Wp : ℝ := Fq * C2 ^ 2
  let Km : ℝ := Cm * (n4 * Wp * Qj ^ 2 + Qp ^ 2 * (n4 * Kw))
  let Mp : ℝ := Qp ^ 2 * (n4 * Wp)
  let Kt : ℝ := 4 * Km
  let Tp : ℝ := 4 * Mp
  let Kr : ℝ := Cr * (Dp ^ 2 * Kt + Tp * (4 * Dj ^ 2))
  have hC2 : 0 ≤ C2 := by dsimp only [C2]; exact hs2FibreAct_nonneg hCmor _
  have hC3 : 0 ≤ C3 := by dsimp only [C3]; exact h3CovsumC_nonneg _ _
  have hn : 0 ≤ n := by dsimp only [n]; positivity
  have hn4 : 0 ≤ n4 := by dsimp only [n4]; positivity
  have hFq : 0 ≤ Fq := by dsimp only [Fq]; positivity
  have hKr : 0 ≤ Kr := by dsimp only [Kr]; positivity
  refine ⟨min (min (min rhoF rhoD) rhoQ) 1, Real.sqrt Kr,
    lt_min (lt_min (lt_min hrhoF hrhoD) hrhoQ) (by norm_num),
    Real.sqrt_nonneg _, ?_⟩
  intro g hEq hjet T delta hdelta_le hdelta0 hdelta hdeltaZ hT2 a ha
  let x : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖
  let N : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖
  let P : SmoothCcTensor g 0 2 := a • T
  let gm : SmoothRiemannianMetric I M :=
    DifferentialGeometry.PDE.DeTurck.RicciLinearization.metricPerturbationPath
      (I := I) g T 0 hdelta hdeltaZ a
  have hx : 0 ≤ x := norm_nonneg _
  have hN : 0 ≤ N := norm_nonneg _
  have hx1 : x ≤ 1 := hT2.trans (min_le_right _ _)
  have hxN : x ≤ N := by
    dsimp only [x, N]
    rw [norm_ccHs_eq_smoothHs, norm_ccHs_eq_smoothHs]
    exact ccSpectralEmbed_norm_mono (I := I) (M := M) g (by norm_num) T
  have ha0 : 0 ≤ a := ha.1
  have hP2F : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) P‖ ≤ rhoF := by
    rw [show P = a • T from rfl, ccTensorToHs_smul, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg ha0]
    exact (mul_le_of_le_one_left hx ha.2).trans
      (hT2.trans ((min_le_left _ _).trans
        ((min_le_left _ _).trans (min_le_left _ _))))
  have hP2D : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) P‖ ≤ rhoD := by
    rw [show P = a • T from rfl, ccTensorToHs_smul, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg ha0]
    exact (mul_le_of_le_one_left hx ha.2).trans
      (hT2.trans ((min_le_left _ _).trans
        ((min_le_left _ _).trans (min_le_right _ _))))
  have hP3 : ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) P‖ ≤ N := by
    rw [show P = a • T from rfl, ccTensorToHs_smul, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg ha0]
    exact mul_le_of_le_one_left hN ha.2
  have hdeltaP : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g P) delta := by
    have h := DifferentialGeometry.PDE.DeTurck.RicciLinearization.convexPerturbation_gFibreOpBound
      (I := I) (M := M) g T 0 hdelta hdeltaZ ha.1 ha.2
    have hscalar : (1 - a) * delta + a * delta = delta := by ring
    rw [hscalar] at h
    simpa only [P, convexPerturbation, smul_zero, zero_add] using h
  have hmem : a ∈ DifferentialGeometry.PDE.DeTurck.RicciLinearization.metricPerturbationPathDomain
      (δ := delta) (δ' := delta) :=
    DifferentialGeometry.PDE.DeTurck.RicciLinearization.Icc_subset_metricPerturbationPathDomain
      (lt_of_le_of_lt hdelta_le (by norm_num))
      (lt_of_le_of_lt hdelta_le (by norm_num)) ha
  have htie : ∀ (y : M) (v w : TangentSpace I y),
      gm.inner y v w = g.inner y v w +
        ccTensorBilinSymm (I := I) g P y v w := by
    intro y v w
    simpa only [gm, P, convexPerturbation, smul_zero, zero_add] using
      DifferentialGeometry.PDE.DeTurck.RicciLinearization.metricPerturbationPath_inner_of_mem
        (I := I) g T 0 hdelta hdeltaZ hmem y v w
  obtain ⟨hfullPt, hfullJet⟩ := hfull g hEq hjet P gm hP2F htie
  obtain ⟨hdagPt, hdagJet⟩ :=
    hdag g hEq hjet P gm hdelta_le hdelta0 hdeltaP hP2D htie
  have hzero2 : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
      (0 : SmoothCcTensor g 0 2)‖ ≤ rhoQ := by
    rw [show (0 : SmoothCcTensor g 0 2) =
        (0 : ℝ) • (0 : SmoothCcTensor g 0 2) by simp,
      ccTensorToHs_smul, zero_smul, norm_zero]
    exact hrhoQ.le
  have htie0 : ∀ (y : M) (v w : TangentSpace I y),
      g.inner y v w = g.inner y v w +
        ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2) y v w := by
    intro y v w
    rw [ccTensorBilinSymm_apply, ccTensorBilin_zero,
      ccTensorBilin_zero]
    ring
  obtain ⟨hpairPt, hpairJetRaw⟩ := hpair g hEq hjet
    (0 : SmoothCcTensor g 0 2) g hdelta_le hdelta0 hdeltaZ hzero2 htie0
  have hpairJet : (∑ j ∈ Finset.range 4,
      ‖iteratedCovGrad (I := I) g 6 2 j
        (cometricDoublePairTraceCoefficient (I := I) (M := M) g g)‖ ^ 2) ≤ Qj ^ 2 := by
    have hz3 : ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ)
        (0 : SmoothCcTensor g 0 2)‖ = 0 := by
      rw [show (0 : SmoothCcTensor g 0 2) =
          (0 : ℝ) • (0 : SmoothCcTensor g 0 2) by simp,
        ccTensorToHs_smul, zero_smul, norm_zero]
    simpa only [hz3, add_zero, mul_one] using hpairJetRaw
  obtain ⟨hact2, hact3⟩ := hKcurv.bounds g hEq hjet
  have hmor' : ∀ (S : SmoothCcTensor g 0 2) (y : M),
      riemannianFiberNormSq (I := I) (M := M) g 0 2 y (S.toSection y) ≤
        Cmor ^ 2 * ∑ b ∈ Finset.range (Module.finrank ℝ E / 2 + 2),
          ‖iteratedCovGrad (I := I) g 0 2 b S‖ ^ 2 := by
    intro S y
    rw [hDim]
    norm_num
    exact hmor g hEq (hjet 1 (by norm_num)) (hjet 2 (by norm_num)) S y
  have hTpt : ∀ y : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 2 y (T.toSection y) ≤
        (C2 * x) ^ 2 := by
    intro y
    simpa only [C2, x, mul_pow] using
      hs2_fiber_sq_action (I := I) (M := M) hDim g hact2 hmor' T y
  have hTjet : (∑ j ∈ Finset.range 4,
      ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) ≤ (C3 * N) ^ 2 := by
    calc
      _ ≤ (∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g 0 2 j T‖) ^ 2 :=
        Finset.sum_sq_le_sq_sum_of_nonneg (fun j _ => norm_nonneg _)
      _ ≤ (C3 * N) ^ 2 := pow_le_pow_left₀
        (Finset.sum_nonneg fun j _ => norm_nonneg _)
        (by simpa only [C3, N] using
          covsum_hs_three (I := I) (M := M) g 2 hact2 hact3 T) 2
  have hxP : x * (1 + N) ≤ 2 * N := by
    have hxn : x * N ≤ N := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hx1 hN
    nlinarith
  have hxPsq : x ^ 2 * (1 + N) ^ 2 ≤ 4 * N ^ 2 := by
    have hs := pow_le_pow_left₀ (mul_nonneg hx (by positivity)) hxP 2
    calc
      x ^ 2 * (1 + N) ^ 2 = (x * (1 + N)) ^ 2 := by ring
      _ ≤ (2 * N) ^ 2 := hs
      _ = 4 * N ^ 2 := by ring
  let F : SmoothCcTensor g 2 2 :=
    slotInsertEndoCc (I := I) (M := M) g 1
      (metricComparisonEndomorphismField (I := I) (M := M) g gm)
  have hFpt : ∀ y : M,
      riemannianFiberNormSq (I := I) (M := M) g 2 2 y (F.toSection y) ≤ Fq := by
    intro y
    simpa only [F, Fq, n, pow_one] using
      full_slot_pointwise (I := I) (M := M) g gm P htie
        hdelta_le hdelta0 hdeltaP 1 y
  have hFjet : (∑ j ∈ Finset.range 4,
      ‖iteratedCovGrad (I := I) g 2 2 j F‖ ^ 2) ≤
        (Cf * (1 + N)) ^ 2 :=
    hfullJet.trans (pow_le_pow_left₀ (mul_nonneg hCf (by positivity))
      (mul_le_mul_of_nonneg_left (add_le_add le_rfl hP3) hCf) 2)
  obtain ⟨hWpt, hWjet⟩ := ricciConnectionDifferenceDerivativeMetricWeight_h3_of_metricComparison
    (I := I) (M := M) g gm T x N Fq C2 C3 Cf Cw
    hFq hC2 hCw hx hFpt hFjet hTpt hTjet hxPsq (happW g hEq)
  change (∀ y : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 2 y
        ((RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeMetricWeight (I := I) (M := M) g gm T).toSection y) ≤
          (Real.sqrt Fq * (C2 * x)) ^ 2) at hWpt
  change (∑ j ∈ Finset.range 4,
      ‖iteratedCovGrad (I := I) g 0 2 j
        (RicciDeTurckLowOrder.ricciConnectionDifferenceDerivativeMetricWeight (I := I) (M := M) g gm T)‖ ^ 2) ≤
          Kw * N ^ 2 at hWjet
  have hdagJetN : (∑ j ∈ Finset.range 4,
      ‖iteratedCovGrad (I := I) g 4 4 j
        (RicciDeTurckLowOrder.ricciConnectionPrincipalCoefficient (I := I) (M := M) g gm)‖ ^ 2) ≤
          (Dj * (1 + N)) ^ 2 :=
    hdagJet.trans (pow_le_pow_left₀ (mul_nonneg hDj (by positivity))
      (mul_le_mul_of_nonneg_left (add_le_add le_rfl hP3) hDj) 2)
  have hr := ricciConnectionDifferenceTopOrderCoefficient_h3_of_metricWeight_and_principal
    (I := I) (M := M) g gm T x N n4 Fq C2 Kw Qp Qj Cm Dp Dj Cr
    hn4 rfl hFq hC2 hQp hCm hDp hCr hx hxN hxPsq
    hpairPt hpairJet hWpt hWjet hdagPt hdagJetN
    (happM g hEq) (happR g hEq)
  change (∑ j ∈ Finset.range 4,
    ‖iteratedCovGrad (I := I) g 4 2 j
      (RicciDeTurckLowOrder.ricciConnectionDifferenceTopOrderCoefficient (I := I) (M := M) g gm T)‖ ^ 2) ≤
        (Real.sqrt Kr * N) ^ 2
  change (∑ j ∈ Finset.range 4,
    ‖iteratedCovGrad (I := I) g 4 2 j
      (RicciDeTurckLowOrder.ricciConnectionDifferenceTopOrderCoefficient (I := I) (M := M) g gm T)‖ ^ 2) ≤
        Kr * N ^ 2 at hr
  exact hr.trans_eq (by rw [mul_pow, Real.sq_sqrt hKr])

theorem ricciDeTurckTopOrderCoefficient_h3_uniform_bound
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∃ rho C : ℝ, 0 < rho ∧ 0 ≤ C ∧
      ∀ g : SmoothRiemannianMetric I M,
        MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
        (∀ b : ℕ, b ≤ 3 →
          MetricCovDerivOrderBoundOn (I := I) Set.univ b g gBase Λ) →
        ∀ (T : SmoothCcTensor g 0 2)
          (_hT : ∀ (x : M) (u v : TangentSpace I x),
            ccTensorBilin (I := I) g T x u v =
              ccTensorBilin (I := I) g T x v u)
          {delta : ℝ}, delta ≤ 1 / 3 → 0 ≤ delta →
          ∀ (hdelta : gFibreOpBound (I := I) (M := M) g
              (ccTensorBilinSymm (I := I) g T) delta)
            (hdeltaZ : gFibreOpBound (I := I) (M := M) g
              (ccTensorBilinSymm (I := I) g
                (0 : SmoothCcTensor g 0 2)) delta),
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ rho →
          ∀ {a : ℝ}, a ∈ Set.Icc (0 : ℝ) 1 →
          let gm := DifferentialGeometry.PDE.DeTurck.RicciLinearization.metricPerturbationPath
            (I := I) g T 0 hdelta hdeltaZ a
          (∑ j ∈ Finset.range 4,
            ‖iteratedCovGrad (I := I) g 4 2 j
              (lieDecomposition2 (I := I) (M := M) g T hdelta hdeltaZ a +
                (deTurckMetricPrincipalDefectTotal (I := I) (M := M) g gm -
                  deTurckMetricPrincipalDefectTotal (I := I) (M := M) g g) +
                (-2 * a : ℝ) •
                  RicciDeTurckLowOrder.ricciConnectionDifferenceTopOrderCoefficient (I := I) (M := M) g gm T)‖ ^ 2) ≤
            (C * ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖) ^ 2 := by
  classical
  obtain ⟨rhoL, CL, hrhoL, hCL, hlie⟩ :=
    lie_second_order_expansion_h3_uniform (I := I) (M := M) hDim gBase hΛ
  obtain ⟨rhoP, CP, hrhoP, hCP, hphi⟩ :=
    phi_dev_h3_uniform (I := I) (M := M) hDim gBase hΛ
  obtain ⟨rhoR, CR, hrhoR, hCR, hricci⟩ :=
    ricciConnectionDifferenceTopOrderCoefficient_h3_uniform (I := I) (M := M) hDim gBase hΛ
  let K : ℝ := 4 * (CL ^ 2 + CP ^ 2) + 8 * CR ^ 2
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  refine ⟨min (min rhoL rhoP) rhoR, Real.sqrt K,
    lt_min (lt_min hrhoL hrhoP) hrhoR, Real.sqrt_nonneg _, ?_⟩
  intro g hEq hjet T hT delta hdelta_le hdelta0 hdelta hdeltaZ hT2 a ha
  let N : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖
  let gm : SmoothRiemannianMetric I M :=
    DifferentialGeometry.PDE.DeTurck.RicciLinearization.metricPerturbationPath
      (I := I) g T 0 hdelta hdeltaZ a
  let L : SmoothCcTensor g 4 2 :=
    lieDecomposition2 (I := I) (M := M) g T hdelta hdeltaZ a
  let P : SmoothCcTensor g 4 2 :=
    deTurckMetricPrincipalDefectTotal (I := I) (M := M) g gm -
      deTurckMetricPrincipalDefectTotal (I := I) (M := M) g g
  let R : SmoothCcTensor g 4 2 :=
    RicciDeTurckLowOrder.ricciConnectionDifferenceTopOrderCoefficient (I := I) (M := M) g gm T
  have hT2L : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ rhoL :=
    hT2.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hT2P : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ rhoP :=
    hT2.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hT2R : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ rhoR :=
    hT2.trans (min_le_right _ _)
  have hdelta_lt : delta < 1 := lt_of_le_of_lt hdelta_le (by norm_num)
  have hx : 0 ≤ ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ :=
    norm_nonneg _
  have hzero : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
      (0 : SmoothCcTensor g 0 2)‖ ≤
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ := by
    rw [show (0 : SmoothCcTensor g 0 2) =
        (0 : ℝ) • (0 : SmoothCcTensor g 0 2) by simp,
      ccTensorToHs_smul, zero_smul, norm_zero]
    exact hx
  have hL : (∑ j ∈ Finset.range 4,
      ‖iteratedCovGrad (I := I) g 4 2 j L‖ ^ 2) ≤ (CL * N) ^ 2 := by
    simpa only [L, N] using
      hlie g hEq hjet T hT hdelta_le hdelta0 hdelta hdeltaZ hT2L ha
  have hP : (∑ j ∈ Finset.range 4,
      ‖iteratedCovGrad (I := I) g 4 2 j P‖ ^ 2) ≤ (CP * N) ^ 2 := by
    have hp := (hphi g hEq hjet T (0 : SmoothCcTensor g 0 2)
      hdelta_lt hdelta hdelta_lt hdeltaZ hx hT2P le_rfl hzero ha.1 ha.2).2
    have hzero3 : ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ)
        (0 : SmoothCcTensor g 0 2)‖ = 0 := by
      rw [show (0 : SmoothCcTensor g 0 2) =
          (0 : ℝ) • (0 : SmoothCcTensor g 0 2) by simp,
        ccTensorToHs_smul, zero_smul, norm_zero]
    rw [hzero3, add_zero] at hp
    simpa only [P, gm, N] using hp
  have hR : (∑ j ∈ Finset.range 4,
      ‖iteratedCovGrad (I := I) g 4 2 j R‖ ^ 2) ≤ (CR * N) ^ 2 := by
    simpa only [R, gm, N] using
      hricci g hEq hjet T hdelta_le hdelta0 hdelta hdeltaZ hT2R ha
  have hLP : (∑ j ∈ Finset.range 4,
      ‖iteratedCovGrad (I := I) g 4 2 j (L + P)‖ ^ 2) ≤
        2 * ((CL * N) ^ 2 + (CP * N) ^ 2) := by
    exact (jet_four_add (I := I) (M := M) g L P).trans
      (mul_le_mul_of_nonneg_left (add_le_add hL hP) (by norm_num))
  have ha2 : a ^ 2 ≤ 1 := by nlinarith [ha.1, ha.2]
  have hRs : (∑ j ∈ Finset.range 4,
      ‖iteratedCovGrad (I := I) g 4 2 j ((-2 * a : ℝ) • R)‖ ^ 2) ≤
        4 * (CR * N) ^ 2 := by
    rw [jet_four_smul]
    calc
      (-2 * a) ^ 2 * (∑ j ∈ Finset.range 4,
        ‖iteratedCovGrad (I := I) g 4 2 j R‖ ^ 2) ≤
          4 * (∑ j ∈ Finset.range 4,
            ‖iteratedCovGrad (I := I) g 4 2 j R‖ ^ 2) := by
        apply mul_le_mul_of_nonneg_right
        · nlinarith
        · exact Finset.sum_nonneg fun j _ => sq_nonneg _
      _ ≤ 4 * (CR * N) ^ 2 := mul_le_mul_of_nonneg_left hR (by norm_num)
  change (∑ j ∈ Finset.range 4,
    ‖iteratedCovGrad (I := I) g 4 2 j (L + P + (-2 * a : ℝ) • R)‖ ^ 2) ≤
      (Real.sqrt K * N) ^ 2
  refine (jet_four_add (I := I) (M := M) g (L + P) ((-2 * a : ℝ) • R)).trans ?_
  calc
    2 * ((∑ j ∈ Finset.range 4,
        ‖iteratedCovGrad (I := I) g 4 2 j (L + P)‖ ^ 2) +
      ∑ j ∈ Finset.range 4,
        ‖iteratedCovGrad (I := I) g 4 2 j ((-2 * a : ℝ) • R)‖ ^ 2) ≤
      2 * (2 * ((CL * N) ^ 2 + (CP * N) ^ 2) + 4 * (CR * N) ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add hLP hRs) (by norm_num)
    _ = K * N ^ 2 := by dsimp only [K]; ring
    _ = (Real.sqrt K * N) ^ 2 := by rw [mul_pow, Real.sq_sqrt hK]
end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
