import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.Coefficients.InverseLipschitzBounds
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.CovariantJetDecomposition.CometricTraceSelf
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifference.RaisedKoszul.ParallelRaise
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorField.FibreNormJet
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureCoefficientDifferenceJetTower.PairTrace
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureCoefficientDifferenceJetTower.TopOrderSeparatedCurvatureBounds
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.SlotPermJet

set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory Set DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.HCGCompactness
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Analysis.Elliptic
  (integrable_riemannianFiberNormSq_toSection riemannianFiberNormSq)
open DifferentialGeometry.Analysis.Sobolev
  (metricComparisonDifferenceEndomorphismField inverseMetricDifferenceSlotCoefficient_eq_slotInsertEndoCc iteratedCovGrad
   iteratedCovGrad_zero
   normSq_le_integral_of_pointwise_fiberNormSq_le_rs
   norm_le_of_pointwise_fiberNormSq_bound_rs riemannianFiberNormSq_iteratedCovGrad_rsDomDomCongr_both_eq
   rsDomDomCongrSection
   tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs)
open DifferentialGeometry.Analysis.Spectral
  (ccOperatorFieldComp operatorFieldComposition_sub_left operatorFieldComposition_sub_right ccOperatorFieldComp ccTensorToHs
   ccTensorToHs_smul inverseMetricDifferenceSlotCoefficient iteratedCovGrad_add pureTrace pureTrace_split
   riemannianFiberNormSq_iteratedCovGrad_slotExtend_le slotExtend slotExtendIter)
open DifferentialGeometry.Analysis.Spectral.CurvatureCoefficientDifferenceJetTower
  (slotInsertEndoCc_succ_eq_reindex_slotExtend)
open DifferentialGeometry.Geometry.Connection
  (curvatureDecompositionMonomialCoeffField endoSlotZeroCcTensor slotInsertEndoCc)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem endoSlotZero_sub_traceLip
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (A B : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)) :
    endoSlotZeroCcTensor (I := I) (M := M) g s (A - B) =
      endoSlotZeroCcTensor (I := I) (M := M) g s A -
        endoSlotZeroCcTensor (I := I) (M := M) g s B := by
  change slotInsertEndoCc (I := I) (M := M) g s (A - B) =
    slotInsertEndoCc (I := I) (M := M) g s A -
      slotInsertEndoCc (I := I) (M := M) g s B
  exact slotInsertEndoCc_sub (I := I) (M := M) g s A B

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
private theorem inverseMetricDifferenceSlotCoefficient_eq_endoSlotZero
    (g₀ g₁ : SmoothRiemannianMetric I M) :
    inverseMetricDifferenceSlotCoefficient (I := I) g₀ g₁ =
      endoSlotZeroCcTensor (I := I) (M := M) g₀ 1
        (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁) := by
  change inverseMetricDifferenceSlotCoefficient (I := I) g₀ g₁ =
    slotInsertEndoCc (I := I) (M := M) g₀ 1
      (metricComparisonDifferenceEndomorphismField (I := I) g₀ g₁)
  exact inverseMetricDifferenceSlotCoefficient_eq_slotInsertEndoCc (I := I) g₀ g₁

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem endoSlotZero_succ_eq_reindex_slotExtend
    (g : SmoothRiemannianMetric I M) (q : ℕ)
    (P : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)) :
    endoSlotZeroCcTensor (I := I) (M := M) g (q + 1) P =
      reindexCoeffGen (I := I) (M := M) g (q + 1 + 1) (q + 1 + 1)
        (rsDomDomCongrSection (I := I) (M := M) g (q + 1 + 1) (q + 1 + 1)
          (Equiv.swap (0 : Fin (q + 1 + 1)) 1)
          (slotExtend (I := I) (M := M) g (q + 1) (q + 1)
            (endoSlotZeroCcTensor (I := I) (M := M) g q P)))
        (Equiv.swap (0 : Fin (q + 1 + 1)) 1) := by
  change slotInsertEndoCc (I := I) (M := M) g (q + 1) P =
    reindexCoeffGen (I := I) (M := M) g (q + 1 + 1) (q + 1 + 1)
      (rsDomDomCongrSection (I := I) (M := M) g (q + 1 + 1) (q + 1 + 1)
        (Equiv.swap (0 : Fin (q + 1 + 1)) 1)
        (slotExtend (I := I) (M := M) g (q + 1) (q + 1)
          (slotInsertEndoCc (I := I) (M := M) g q P)))
      (Equiv.swap (0 : Fin (q + 1 + 1)) 1)
  exact slotInsertEndoCc_succ_eq_reindex_slotExtend (I := I) (M := M) g q P

omit [SigmaCompactSpace M] in
private theorem insSuccPt (g : SmoothRiemannianMetric I M) (q : ℕ)
    (P : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x))
    (i : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g (q + 1 + 1) ((q + 1 + 1) + i) x
        ((iteratedCovGrad (I := I) g (q + 1 + 1) (q + 1 + 1) i
          (endoSlotZeroCcTensor (I := I) (M := M) g (q + 1) P)).toSection x) ≤
      (Module.finrank ℝ E : ℝ) *
        riemannianFiberNormSq (I := I) (M := M) g (q + 1) ((q + 1) + i) x
          ((iteratedCovGrad (I := I) g (q + 1) (q + 1) i
            (endoSlotZeroCcTensor (I := I) (M := M) g q P)).toSection x) := by
  have hA :
      riemannianFiberNormSq (I := I) (M := M) g (q + 1 + 1) ((q + 1 + 1) + i) x
          ((iteratedCovGrad (I := I) g (q + 1 + 1) (q + 1 + 1) i
            (endoSlotZeroCcTensor (I := I) (M := M) g (q + 1) P)).toSection x) =
        riemannianFiberNormSq (I := I) (M := M) g (q + 1 + 1) ((q + 1 + 1) + i) x
          ((iteratedCovGrad (I := I) g (q + 1 + 1) (q + 1 + 1) i
            (slotExtend (I := I) (M := M) g (q + 1) (q + 1)
              (endoSlotZeroCcTensor (I := I) (M := M) g q P))).toSection x) := by
    rw [endoSlotZero_succ_eq_reindex_slotExtend (I := I) (M := M) g q P]
    exact riemannianFiberNormSq_iteratedCovGrad_rsDomDomCongr_both_eq (I := I) (M := M) g
      (q + 1 + 1) (q + 1 + 1)
      (Equiv.swap (0 : Fin (q + 1 + 1)) 1) (Equiv.swap (0 : Fin (q + 1 + 1)) 1)
      (slotExtend (I := I) (M := M) g (q + 1) (q + 1)
        (endoSlotZeroCcTensor (I := I) (M := M) g q P)) i x
  rw [hA]
  exact riemannianFiberNormSq_iteratedCovGrad_slotExtend_le (I := I) (M := M) g (q + 1) (q + 1)
    (endoSlotZeroCcTensor (I := I) (M := M) g q P) i x

private theorem insSuccSq (g : SmoothRiemannianMetric I M) (q : ℕ)
    (P : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x))
    (i : ℕ) :
    ‖iteratedCovGrad (I := I) g (q + 1 + 1) (q + 1 + 1) i
        (endoSlotZeroCcTensor (I := I) (M := M) g (q + 1) P)‖ ^ 2 ≤
      (Module.finrank ℝ E : ℝ) *
        ‖iteratedCovGrad (I := I) g (q + 1) (q + 1) i
          (endoSlotZeroCcTensor (I := I) (M := M) g q P)‖ ^ 2 := by
  classical
  set F : M → ℝ := fun x => (Module.finrank ℝ E : ℝ) *
    riemannianFiberNormSq (I := I) (M := M) g (q + 1) ((q + 1) + i) x
      ((iteratedCovGrad (I := I) g (q + 1) (q + 1) i
        (endoSlotZeroCcTensor (I := I) (M := M) g q P)).toSection x) with hF
  have hFint : MeasureTheory.Integrable F
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    rw [hF]
    exact (integrable_riemannianFiberNormSq_toSection
      (I := I) (M := M) g (q + 1) ((q + 1) + i)
        (iteratedCovGrad (I := I) g (q + 1) (q + 1) i
          (endoSlotZeroCcTensor (I := I) (M := M) g q P))).const_mul _
  have hsq := normSq_le_integral_of_pointwise_fiberNormSq_le_rs
    (I := I) (M := M) g (q + 1 + 1) ((q + 1 + 1) + i)
      (iteratedCovGrad (I := I) g (q + 1 + 1) (q + 1 + 1) i
        (endoSlotZeroCcTensor (I := I) (M := M) g (q + 1) P)) F hFint
      (fun x => insSuccPt (I := I) (M := M) g q P i x)
  have hint :
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g (q + 1) ((q + 1) + i) x
          ((iteratedCovGrad (I := I) g (q + 1) (q + 1) i
            (endoSlotZeroCcTensor (I := I) (M := M) g q P)).toSection x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        ‖iteratedCovGrad (I := I) g (q + 1) (q + 1) i
          (endoSlotZeroCcTensor (I := I) (M := M) g q P)‖ ^ 2 := by
    rw [SmoothCcTensor.norm_def,
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs
        (I := I) (M := M) g (q + 1) ((q + 1) + i)]
  rw [hF] at hsq
  rw [MeasureTheory.integral_const_mul, hint] at hsq
  exact hsq

private theorem insSuccJet (g : SmoothRiemannianMetric I M) (q : ℕ)
    (P : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)) :
    (∑ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g (q + 1 + 1) (q + 1 + 1) j
        (endoSlotZeroCcTensor (I := I) (M := M) g (q + 1) P)‖ ^ 2) ≤
      (Module.finrank ℝ E : ℝ) *
        ∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g (q + 1) (q + 1) j
            (endoSlotZeroCcTensor (I := I) (M := M) g q P)‖ ^ 2 := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun j _ => insSuccSq (I := I) (M := M) g q P j

private theorem ins3Jet (g : SmoothRiemannianMetric I M)
    (P : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)) :
    (∑ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g 4 4 j
        (endoSlotZeroCcTensor (I := I) (M := M) g 3 P)‖ ^ 2) ≤
      (Module.finrank ℝ E : ℝ) ^ 2 *
        ∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 2 2 j
            (endoSlotZeroCcTensor (I := I) (M := M) g 1 P)‖ ^ 2 := by
  have hfr : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
  calc
    (∑ j ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 4 4 j
          (endoSlotZeroCcTensor (I := I) (M := M) g 3 P)‖ ^ 2) ≤
        (Module.finrank ℝ E : ℝ) *
          ∑ j ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g 3 3 j
              (endoSlotZeroCcTensor (I := I) (M := M) g 2 P)‖ ^ 2 :=
      insSuccJet (I := I) (M := M) g 2 P
    _ ≤ (Module.finrank ℝ E : ℝ) *
        ((Module.finrank ℝ E : ℝ) *
          ∑ j ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g 2 2 j
              (endoSlotZeroCcTensor (I := I) (M := M) g 1 P)‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (insSuccJet (I := I) (M := M) g 1 P) hfr
    _ = _ := by ring

private theorem ins5Jet (g : SmoothRiemannianMetric I M)
    (P : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)) :
    (∑ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g 6 6 j
        (endoSlotZeroCcTensor (I := I) (M := M) g 5 P)‖ ^ 2) ≤
      (Module.finrank ℝ E : ℝ) ^ 4 *
        ∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 2 2 j
            (endoSlotZeroCcTensor (I := I) (M := M) g 1 P)‖ ^ 2 := by
  have hfr : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
  calc
    (∑ j ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 6 6 j
          (endoSlotZeroCcTensor (I := I) (M := M) g 5 P)‖ ^ 2) ≤
        (Module.finrank ℝ E : ℝ) *
          ∑ j ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g 5 5 j
              (endoSlotZeroCcTensor (I := I) (M := M) g 4 P)‖ ^ 2 :=
      insSuccJet (I := I) (M := M) g 4 P
    _ ≤ (Module.finrank ℝ E : ℝ) *
        ((Module.finrank ℝ E : ℝ) *
          ∑ j ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g 4 4 j
              (endoSlotZeroCcTensor (I := I) (M := M) g 3 P)‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (insSuccJet (I := I) (M := M) g 3 P) hfr
    _ ≤ (Module.finrank ℝ E : ℝ) *
        ((Module.finrank ℝ E : ℝ) *
          ((Module.finrank ℝ E : ℝ) ^ 2 *
            ∑ j ∈ Finset.range 3,
              ‖iteratedCovGrad (I := I) g 2 2 j
                (endoSlotZeroCcTensor (I := I) (M := M) g 1 P)‖ ^ 2)) := by
      refine mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (ins3Jet (I := I) (M := M) g P) hfr) hfr
    _ = _ := by ring

private theorem dtJet (g : SmoothRiemannianMetric I M) (p : ℕ) :
    (∑ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g (p + 2) p j
        (DifferentialGeometry.Analysis.Spectral.DeTurck.cometricDoubleTraceField
          (I := I) g p)‖ ^ 2) ≤
      (Module.finrank ℝ E : ℝ) ^ (p + 6) *
        ((riemannianVolumeMeasure (I := I) (M := M) g) Set.univ).toReal := by
  have h0 : ‖iteratedCovGrad (I := I) g (p + 2) p 0
      (DifferentialGeometry.Analysis.Spectral.DeTurck.cometricDoubleTraceField
        (I := I) g p)‖ ^ 2 ≤
      (Module.finrank ℝ E : ℝ) ^ (p + 6) *
        ((riemannianVolumeMeasure (I := I) (M := M) g) Set.univ).toReal := by
    rw [iteratedCovGrad_zero]
    exact norm_le_of_pointwise_fiberNormSq_bound_rs (I := I) (M := M) g (p + 2) p
      (DifferentialGeometry.Analysis.Spectral.DeTurck.cometricDoubleTraceField
        (I := I) g p)
      ((Module.finrank ℝ E : ℝ) ^ (p + 6))
      (fun x => cometricTrace_riemannianFiberNormSq_p (I := I) (M := M) p g x)
  have hsucc : ∀ m : ℕ, ‖iteratedCovGrad (I := I) g (p + 2) p (m + 1)
      (DifferentialGeometry.Analysis.Spectral.DeTurck.cometricDoubleTraceField
        (I := I) g p)‖ = 0 := by
    intro m
    rw [iteratedCovGrad_eq_zero_of_covGrad_eq_zero (I := I) (M := M) g (p + 2) p
      (DifferentialGeometry.Analysis.Spectral.DeTurck.cometricDoubleTraceField
        (I := I) g p)
      (DifferentialGeometry.Analysis.Spectral.DeTurck.cometricDoubleTraceField_covGrad_eq_zero
        (I := I) g p) m]
    exact norm_zero
  have hexp : (∑ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g (p + 2) p j
        (DifferentialGeometry.Analysis.Spectral.DeTurck.cometricDoubleTraceField
          (I := I) g p)‖ ^ 2) =
      ‖iteratedCovGrad (I := I) g (p + 2) p 0
        (DifferentialGeometry.Analysis.Spectral.DeTurck.cometricDoubleTraceField
          (I := I) g p)‖ ^ 2 +
      ‖iteratedCovGrad (I := I) g (p + 2) p 1
        (DifferentialGeometry.Analysis.Spectral.DeTurck.cometricDoubleTraceField
          (I := I) g p)‖ ^ 2 +
      ‖iteratedCovGrad (I := I) g (p + 2) p 2
        (DifferentialGeometry.Analysis.Spectral.DeTurck.cometricDoubleTraceField
          (I := I) g p)‖ ^ 2 := by
    norm_num [Finset.sum_range_succ]
  rw [hexp, hsucc 0, hsucc 1]
  simpa using h0


theorem trace24_h2_lip_uniform
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ g : SmoothRiemannianMetric I M,
        MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
        (∀ a : ℕ, a ≤ 3 →
          MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ) →
        ∀ (T U : SmoothCcTensor g 0 2)
          (gT gU : SmoothRiemannianMetric I M),
          (∀ (y : M) (v w : TangentSpace I y),
            gT.inner y v w =
              g.inner y v w + ccTensorBilinSymm (I := I) g T y v w) →
          (∀ (y : M) (v w : TangentSpace I y),
            gU.inner y v w =
              g.inner y v w + ccTensorBilinSymm (I := I) g U y v w) →
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
          (∑ j ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g 4 2 j
              (pureTrace (I := I) (M := M) g gT 2 -
                pureTrace (I := I) (M := M) g gU 2)‖ ^ 2) ≤
            (C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
              (T - U)‖) ^ 2 ∧
          (∑ j ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g 6 4 j
              (pureTrace (I := I) (M := M) g gT 4 -
                pureTrace (I := I) (M := M) g gU 4)‖ ^ 2) ≤
            (C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
              (T - U)‖) ^ 2 := by
  classical
  obtain ⟨ρ, Cinv, hρ, hCinv, hinv⟩ :=
    invCoeff_h2_lip_uniform (I := I) (M := M) hDim gBase hΛ
  obtain ⟨C₂, hC₂, happ₂⟩ :=
    operatorFieldComposition_h2_h2_to_h2_uniform_bound (I := I) (M := M) hDim gBase hΛ 4 4 2
  obtain ⟨C₄, hC₄, happ₄⟩ :=
    operatorFieldComposition_h2_h2_to_h2_uniform_bound (I := I) (M := M) hDim gBase hΛ 6 6 4
  let vol : ℝ := volCompareC (E := E) Λ *
    ((riemannianVolumeMeasure (I := I) (M := M) gBase) Set.univ).toReal
  let A₂ : ℝ := Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 8 * vol)
  let A₄ : ℝ := Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 10 * vol)
  let K₂ : ℝ := C₂ * A₂ * (3 * Cinv)
  let K₄ : ℝ := C₄ * A₄ * (9 * Cinv)
  let C : ℝ := K₂ + K₄
  have hvol : 0 ≤ vol := by
    dsimp only [vol]
    exact mul_nonneg (Real.sqrt_nonneg _) ENNReal.toReal_nonneg
  have hA₂ : 0 ≤ A₂ := Real.sqrt_nonneg _
  have hA₄ : 0 ≤ A₄ := Real.sqrt_nonneg _
  have hA₂sq : A₂ ^ 2 = (Module.finrank ℝ E : ℝ) ^ 8 * vol := by
    dsimp only [A₂]
    exact Real.sq_sqrt (by positivity)
  have hA₄sq : A₄ ^ 2 = (Module.finrank ℝ E : ℝ) ^ 10 * vol := by
    dsimp only [A₄]
    exact Real.sq_sqrt (by positivity)
  have hK₂ : 0 ≤ K₂ :=
    mul_nonneg (mul_nonneg hC₂ hA₂) (mul_nonneg (by norm_num) hCinv)
  have hK₄ : 0 ≤ K₄ :=
    mul_nonneg (mul_nonneg hC₄ hA₄) (mul_nonneg (by norm_num) hCinv)
  have hC : 0 ≤ C := add_nonneg hK₂ hK₄
  refine ⟨ρ, C, hρ, hC, ?_⟩
  intro g hEq hjet T U gT gU hTtie hUtie hT hU
  have hjet1 := hjet 1 (by norm_num)
  have hjet2 := hjet 2 (by norm_num)
  have hvolg : ((riemannianVolumeMeasure (I := I) (M := M) g) Set.univ).toReal ≤
      vol := by
    simpa only [vol] using
      (volumeReal_cross (I := I) (M := M) gBase g hEq).1
  let N : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖
  have hN : 0 ≤ N := norm_nonneg _
  let F₂ : SmoothCcTensor g 4 2 :=
    DifferentialGeometry.Analysis.Spectral.DeTurck.cometricDoubleTraceField (I := I) g 2
  let F₄ : SmoothCcTensor g 6 4 :=
    DifferentialGeometry.Analysis.Spectral.DeTurck.cometricDoubleTraceField (I := I) g 4
  let dEndo := metricComparisonDifferenceEndomorphismField (I := I) g gT -
    metricComparisonDifferenceEndomorphismField (I := I) g gU
  let D₂ : SmoothCcTensor g 4 4 :=
    endoSlotZeroCcTensor (I := I) (M := M) g 3 dEndo
  let D₄ : SmoothCcTensor g 6 6 :=
    endoSlotZeroCcTensor (I := I) (M := M) g 5 dEndo
  have hF₂ : (∑ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g 4 2 j F₂‖ ^ 2) ≤ A₂ ^ 2 := by
    rw [hA₂sq]
    refine (dtJet (I := I) (M := M) g 2).trans ?_
    have hfr : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) ^ (2 + 6) := by positivity
    exact mul_le_mul_of_nonneg_left hvolg hfr
  have hF₄ : (∑ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g 6 4 j F₄‖ ^ 2) ≤ A₄ ^ 2 := by
    rw [hA₄sq]
    refine (dtJet (I := I) (M := M) g 4).trans ?_
    have hfr : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) ^ (4 + 6) := by positivity
    exact mul_le_mul_of_nonneg_left hvolg hfr
  have hslot1 :
      endoSlotZeroCcTensor (I := I) (M := M) g 1 dEndo =
        inverseMetricDifferenceSlotCoefficient (I := I) g gT -
          inverseMetricDifferenceSlotCoefficient (I := I) g gU := by
    dsimp only [dEndo]
    rw [endoSlotZero_sub_traceLip,
      ← inverseMetricDifferenceSlotCoefficient_eq_endoSlotZero (I := I) (M := M) g gT,
      ← inverseMetricDifferenceSlotCoefficient_eq_endoSlotZero (I := I) (M := M) g gU]
  have hinvJet : (∑ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g 2 2 j
        (inverseMetricDifferenceSlotCoefficient (I := I) g gT -
          inverseMetricDifferenceSlotCoefficient (I := I) g gU)‖ ^ 2) ≤ (Cinv * N) ^ 2 := by
    simpa only [N] using
      (hinv g hEq hjet T U gT gU hTtie hUtie hT hU).2
  have hD₂ : (∑ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g 4 4 j D₂‖ ^ 2) ≤ (3 * Cinv * N) ^ 2 := by
    calc
      (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 4 4 j D₂‖ ^ 2) ≤
          (Module.finrank ℝ E : ℝ) ^ 2 *
            ∑ j ∈ Finset.range 3,
              ‖iteratedCovGrad (I := I) g 2 2 j
                (endoSlotZeroCcTensor (I := I) (M := M) g 1 dEndo)‖ ^ 2 :=
        ins3Jet (I := I) (M := M) g dEndo
      _ = 9 * ∑ j ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g 2 2 j
              (inverseMetricDifferenceSlotCoefficient (I := I) g gT -
                inverseMetricDifferenceSlotCoefficient (I := I) g gU)‖ ^ 2 := by
        rw [hDim, hslot1]
        norm_num
      _ ≤ 9 * (Cinv * N) ^ 2 :=
        mul_le_mul_of_nonneg_left hinvJet (by norm_num)
      _ = (3 * Cinv * N) ^ 2 := by ring
  have hD₄ : (∑ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g 6 6 j D₄‖ ^ 2) ≤ (9 * Cinv * N) ^ 2 := by
    calc
      (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 6 6 j D₄‖ ^ 2) ≤
          (Module.finrank ℝ E : ℝ) ^ 4 *
            ∑ j ∈ Finset.range 3,
              ‖iteratedCovGrad (I := I) g 2 2 j
                (endoSlotZeroCcTensor (I := I) (M := M) g 1 dEndo)‖ ^ 2 :=
        ins5Jet (I := I) (M := M) g dEndo
      _ = 81 * ∑ j ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g 2 2 j
              (inverseMetricDifferenceSlotCoefficient (I := I) g gT -
                inverseMetricDifferenceSlotCoefficient (I := I) g gU)‖ ^ 2 := by
        rw [hDim, hslot1]
        norm_num
      _ ≤ 81 * (Cinv * N) ^ 2 :=
        mul_le_mul_of_nonneg_left hinvJet (by norm_num)
      _ = (9 * Cinv * N) ^ 2 := by ring
  have htrace₂ :
      pureTrace (I := I) (M := M) g gT 2 -
          pureTrace (I := I) (M := M) g gU 2 =
        ccOperatorFieldComp (I := I) (M := M) g 4 4 2 F₂ D₂ := by
    rw [pureTrace_split (I := I) (M := M) g gT 2,
      pureTrace_split (I := I) (M := M) g gU 2]
    calc
      (ccOperatorFieldComp (I := I) (M := M) g 4 4 2 F₂
            (endoSlotZeroCcTensor (I := I) (M := M) g 3
              (metricComparisonDifferenceEndomorphismField (I := I) g gT)) + F₂) -
          (ccOperatorFieldComp (I := I) (M := M) g 4 4 2 F₂
            (endoSlotZeroCcTensor (I := I) (M := M) g 3
              (metricComparisonDifferenceEndomorphismField (I := I) g gU)) + F₂) =
        ccOperatorFieldComp (I := I) (M := M) g 4 4 2 F₂
            (endoSlotZeroCcTensor (I := I) (M := M) g 3
              (metricComparisonDifferenceEndomorphismField (I := I) g gT)) -
          ccOperatorFieldComp (I := I) (M := M) g 4 4 2 F₂
            (endoSlotZeroCcTensor (I := I) (M := M) g 3
              (metricComparisonDifferenceEndomorphismField (I := I) g gU)) := by abel
      _ = ccOperatorFieldComp (I := I) (M := M) g 4 4 2 F₂ D₂ := by
        rw [← operatorFieldComposition_sub_right]
        congr 1
        dsimp only [D₂, dEndo]
        exact (endoSlotZero_sub_traceLip (I := I) (M := M) g 3 _ _).symm
  have htrace₄ :
      pureTrace (I := I) (M := M) g gT 4 -
          pureTrace (I := I) (M := M) g gU 4 =
        ccOperatorFieldComp (I := I) (M := M) g 6 6 4 F₄ D₄ := by
    rw [pureTrace_split (I := I) (M := M) g gT 4,
      pureTrace_split (I := I) (M := M) g gU 4]
    calc
      (ccOperatorFieldComp (I := I) (M := M) g 6 6 4 F₄
            (endoSlotZeroCcTensor (I := I) (M := M) g 5
              (metricComparisonDifferenceEndomorphismField (I := I) g gT)) + F₄) -
          (ccOperatorFieldComp (I := I) (M := M) g 6 6 4 F₄
            (endoSlotZeroCcTensor (I := I) (M := M) g 5
              (metricComparisonDifferenceEndomorphismField (I := I) g gU)) + F₄) =
        ccOperatorFieldComp (I := I) (M := M) g 6 6 4 F₄
            (endoSlotZeroCcTensor (I := I) (M := M) g 5
              (metricComparisonDifferenceEndomorphismField (I := I) g gT)) -
          ccOperatorFieldComp (I := I) (M := M) g 6 6 4 F₄
            (endoSlotZeroCcTensor (I := I) (M := M) g 5
              (metricComparisonDifferenceEndomorphismField (I := I) g gU)) := by abel
      _ = ccOperatorFieldComp (I := I) (M := M) g 6 6 4 F₄ D₄ := by
        rw [← operatorFieldComposition_sub_right]
        congr 1
        dsimp only [D₄, dEndo]
        exact (endoSlotZero_sub_traceLip (I := I) (M := M) g 5 _ _).symm
  have hout₂ : (∑ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g 4 2 j
        (pureTrace (I := I) (M := M) g gT 2 -
          pureTrace (I := I) (M := M) g gU 2)‖ ^ 2) ≤ (K₂ * N) ^ 2 := by
    rw [htrace₂]
    refine (happ₂ g hEq hjet1 hjet2 F₂ D₂ A₂ (3 * Cinv * N) hA₂
      (mul_nonneg (mul_nonneg (by norm_num) hCinv) hN) hF₂ hD₂).trans
      (le_of_eq ?_)
    dsimp only [K₂]
    ring
  have hout₄ : (∑ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g 6 4 j
        (pureTrace (I := I) (M := M) g gT 4 -
          pureTrace (I := I) (M := M) g gU 4)‖ ^ 2) ≤ (K₄ * N) ^ 2 := by
    rw [htrace₄]
    refine (happ₄ g hEq hjet1 hjet2 F₄ D₄ A₄ (9 * Cinv * N) hA₄
      (mul_nonneg (mul_nonneg (by norm_num) hCinv) hN) hF₄ hD₄).trans
      (le_of_eq ?_)
    dsimp only [K₄]
    ring
  refine ⟨hout₂.trans ?_, hout₄.trans ?_⟩
  · exact pow_le_pow_left₀ (mul_nonneg hK₂ hN)
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hK₄) hN) 2
  · exact pow_le_pow_left₀ (mul_nonneg hK₄ hN)
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hK₂) hN) 2

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
private theorem ptSelf (g : SmoothRiemannianMetric I M) (p : ℕ) :
    pureTrace (I := I) (M := M) g g p =
      DifferentialGeometry.Analysis.Spectral.DeTurck.cometricDoubleTraceField
        (I := I) g p := rfl

private theorem ptDiag (gBase g : SmoothRiemannianMetric I M) {Λ : ℝ}
    (hEq : MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ) (p : ℕ) :
    (∑ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g (p + 2) p j
        (pureTrace (I := I) (M := M) g g p)‖ ^ 2) ≤
      (Module.finrank ℝ E : ℝ) ^ (p + 6) *
        (volCompareC (E := E) Λ *
          ((riemannianVolumeMeasure (I := I) (M := M) gBase) Set.univ).toReal) := by
  rw [ptSelf (I := I) (M := M) g p]
  refine (dtJet (I := I) (M := M) g p).trans ?_
  exact mul_le_mul_of_nonneg_left
    (volumeReal_cross (I := I) (M := M) gBase g hEq).1
    (pow_nonneg (Nat.cast_nonneg _) (p + 6))

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem iteratedCovGradNormSq_add_le (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (A B : SmoothCcTensor g r s) :
    (∑ j ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g r s j (A + B)‖ ^ 2) ≤
      2 * ((∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g r s j A‖ ^ 2) +
        ∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g r s j B‖ ^ 2) := by
  calc
    (∑ j ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g r s j (A + B)‖ ^ 2) ≤
        ∑ j ∈ Finset.range 3,
          2 * (‖iteratedCovGrad (I := I) g r s j A‖ ^ 2 +
            ‖iteratedCovGrad (I := I) g r s j B‖ ^ 2) := by
      refine Finset.sum_le_sum fun j _ => ?_
      rw [iteratedCovGrad_add]
      have htri := norm_add_le
        (iteratedCovGrad (I := I) g r s j A)
        (iteratedCovGrad (I := I) g r s j B)
      have hstep :
          ‖iteratedCovGrad (I := I) g r s j A +
              iteratedCovGrad (I := I) g r s j B‖ ^ 2 ≤
            (‖iteratedCovGrad (I := I) g r s j A‖ +
              ‖iteratedCovGrad (I := I) g r s j B‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) htri 2
      nlinarith [hstep, sq_nonneg
        (‖iteratedCovGrad (I := I) g r s j A‖ -
          ‖iteratedCovGrad (I := I) g r s j B‖)]
    _ = 2 * ((∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g r s j A‖ ^ 2) +
        ∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g r s j B‖ ^ 2) := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem jetAbs (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (A B : SmoothCcTensor g r s) {d b : ℝ}
    (hd : (∑ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g r s j (A - B)‖ ^ 2) ≤ d)
    (hb : (∑ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g r s j B‖ ^ 2) ≤ b) :
    (∑ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g r s j A‖ ^ 2) ≤ 2 * (d + b) := by
  have hsplit : A - B + B = A := by abel
  calc
    (∑ j ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g r s j A‖ ^ 2) =
        ∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g r s j (A - B + B)‖ ^ 2 := by
      rw [hsplit]
    _ ≤ 2 * ((∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g r s j (A - B)‖ ^ 2) +
        ∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g r s j B‖ ^ 2) :=
      iteratedCovGradNormSq_add_le (I := I) (M := M) g _ _
    _ ≤ 2 * (d + b) :=
      mul_le_mul_of_nonneg_left (add_le_add hd hb) (by norm_num)

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
omit [I.Boundaryless] in
private theorem pairSplit (g gT gU : SmoothRiemannianMetric I M) :
    cometricDoublePairTraceCoefficient (I := I) (M := M) g gT -
        cometricDoublePairTraceCoefficient (I := I) (M := M) g gU =
      ccOperatorFieldComp (I := I) (M := M) g 6 4 2
          (pureTrace (I := I) (M := M) g gT 2 -
            pureTrace (I := I) (M := M) g gU 2)
          (pureTrace (I := I) (M := M) g gT 4) +
        ccOperatorFieldComp (I := I) (M := M) g 6 4 2
          (pureTrace (I := I) (M := M) g gU 2)
          (pureTrace (I := I) (M := M) g gT 4 -
            pureTrace (I := I) (M := M) g gU 4) := by
  rw [RicciDeTurckLowOrder.pairTrace_eq (I := I) (M := M) g gT,
    RicciDeTurckLowOrder.pairTrace_eq (I := I) (M := M) g gU,
    operatorFieldComposition_sub_left, operatorFieldComposition_sub_right]
  abel

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem zeroTie (g : SmoothRiemannianMetric I M)
    (y : M) (v w : TangentSpace I y) :
    g.inner y v w =
      g.inner y v w +
        ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2) y v w := by
  rw [show (0 : SmoothCcTensor g 0 2) =
      (0 : ℝ) • (0 : SmoothCcTensor g 0 2) from (zero_smul ℝ _).symm,
    ccTensorBilinSymm_smul]
  ring

private theorem zeroHs (g : SmoothRiemannianMetric I M) :
    ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
      (0 : SmoothCcTensor g 0 2) = 0 := by
  rw [show (0 : SmoothCcTensor g 0 2) =
      (0 : ℝ) • (0 : SmoothCcTensor g 0 2) from (zero_smul ℝ _).symm,
    ccTensorToHs_smul, zero_smul]

private theorem movWin (gBase g gm : SmoothRiemannianMetric I M) {Λ ρ Ct : ℝ}
    (hEq : MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ)
    (hρ : 0 < ρ) (hCt : 0 ≤ Ct)
    (htr : ∀ (T U : SmoothCcTensor g 0 2)
      (gT gU : SmoothRiemannianMetric I M),
      (∀ (y : M) (v w : TangentSpace I y),
        gT.inner y v w =
          g.inner y v w + ccTensorBilinSymm (I := I) g T y v w) →
      (∀ (y : M) (v w : TangentSpace I y),
        gU.inner y v w =
          g.inner y v w + ccTensorBilinSymm (I := I) g U y v w) →
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
      (∑ j ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 4 2 j
          (pureTrace (I := I) (M := M) g gT 2 -
            pureTrace (I := I) (M := M) g gU 2)‖ ^ 2) ≤
        (Ct * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖) ^ 2 ∧
      (∑ j ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 6 4 j
          (pureTrace (I := I) (M := M) g gT 4 -
            pureTrace (I := I) (M := M) g gU 4)‖ ^ 2) ≤
        (Ct * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖) ^ 2)
    (P : SmoothCcTensor g 0 2)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      gm.inner y v w =
        g.inner y v w + ccTensorBilinSymm (I := I) g P y v w)
    (hP : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) P‖ ≤ ρ) :
    (∑ j ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 4 2 j
          (pureTrace (I := I) (M := M) g gm 2)‖ ^ 2) ≤
      2 * ((Ct * ρ) ^ 2 + (Module.finrank ℝ E : ℝ) ^ 8 *
        (volCompareC (E := E) Λ *
          ((riemannianVolumeMeasure (I := I) (M := M) gBase)
            Set.univ).toReal)) ∧
    (∑ j ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 6 4 j
          (pureTrace (I := I) (M := M) g gm 4)‖ ^ 2) ≤
      2 * ((Ct * ρ) ^ 2 + (Module.finrank ℝ E : ℝ) ^ 10 *
        (volCompareC (E := E) Λ *
          ((riemannianVolumeMeasure (I := I) (M := M) gBase)
            Set.univ).toReal)) := by
  have hzρ : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
      (0 : SmoothCcTensor g 0 2)‖ ≤ ρ := by
    rw [zeroHs (I := I) (M := M) g, norm_zero]
    exact le_of_lt hρ
  obtain ⟨h₂, h₄⟩ :=
    htr P (0 : SmoothCcTensor g 0 2) gm g htie
      (zeroTie (I := I) (M := M) g) hP hzρ
  have hmul : Ct * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
      (P - 0)‖ ≤ Ct * ρ := by
    rw [sub_zero]
    exact mul_le_mul_of_nonneg_left hP hCt
  have hcut : ∀ x : ℝ,
      x ≤ (Ct * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
          (P - 0)‖) ^ 2 → x ≤ (Ct * ρ) ^ 2 :=
    fun _ hx => hx.trans
      (pow_le_pow_left₀ (mul_nonneg hCt (norm_nonneg _)) hmul 2)
  exact ⟨jetAbs (I := I) (M := M) g _ _ (hcut _ h₂)
      (ptDiag (I := I) (M := M) gBase g hEq 2),
    jetAbs (I := I) (M := M) g _ _ (hcut _ h₄)
      (ptDiag (I := I) (M := M) gBase g hEq 4)⟩

theorem pairTrace_h2_lip_uniform
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ g : SmoothRiemannianMetric I M,
        MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
        (∀ a : ℕ, a ≤ 3 →
          MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ) →
        ∀ (T U : SmoothCcTensor g 0 2)
          (gT gU : SmoothRiemannianMetric I M),
          (∀ (y : M) (v w : TangentSpace I y),
            gT.inner y v w =
              g.inner y v w + ccTensorBilinSymm (I := I) g T y v w) →
          (∀ (y : M) (v w : TangentSpace I y),
            gU.inner y v w =
              g.inner y v w + ccTensorBilinSymm (I := I) g U y v w) →
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
          (∑ j ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g 6 2 j
              (cometricDoublePairTraceCoefficient (I := I) (M := M) g gT -
                cometricDoublePairTraceCoefficient (I := I) (M := M) g gU)‖ ^ 2) ≤
            (C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
              (T - U)‖) ^ 2 := by
  classical
  obtain ⟨ρ, Ct, hρ, hCt, htrace⟩ :=
    trace24_h2_lip_uniform (I := I) (M := M) hDim gBase hΛ
  obtain ⟨Ca, hCa, happ⟩ :=
    operatorFieldComposition_h2_h2_to_h2_uniform_bound (I := I) (M := M) hDim gBase hΛ 6 4 2
  let vol : ℝ := volCompareC (E := E) Λ *
    ((riemannianVolumeMeasure (I := I) (M := M) gBase) Set.univ).toReal
  let A₂ : ℝ := (Module.finrank ℝ E : ℝ) ^ 8 * vol
  let A₄ : ℝ := (Module.finrank ℝ E : ℝ) ^ 10 * vol
  let B₂ : ℝ := Real.sqrt (2 * ((Ct * ρ) ^ 2 + A₂))
  let B₄ : ℝ := Real.sqrt (2 * ((Ct * ρ) ^ 2 + A₄))
  let K₁ : ℝ := Ca * Ct * B₄
  let K₂ : ℝ := Ca * B₂ * Ct
  let C : ℝ := 2 * (K₁ + K₂)
  have hvol : 0 ≤ vol := by
    dsimp only [vol]
    exact mul_nonneg (Real.sqrt_nonneg _) ENNReal.toReal_nonneg
  have hA₂ : 0 ≤ A₂ := by
    dsimp only [A₂]
    exact mul_nonneg (pow_nonneg (Nat.cast_nonneg _) 8) hvol
  have hA₄ : 0 ≤ A₄ := by
    dsimp only [A₄]
    exact mul_nonneg (pow_nonneg (Nat.cast_nonneg _) 10) hvol
  have hZ₂ : (0 : ℝ) ≤ 2 * ((Ct * ρ) ^ 2 + A₂) :=
    mul_nonneg (by norm_num) (add_nonneg (sq_nonneg _) hA₂)
  have hZ₄ : (0 : ℝ) ≤ 2 * ((Ct * ρ) ^ 2 + A₄) :=
    mul_nonneg (by norm_num) (add_nonneg (sq_nonneg _) hA₄)
  have hB₂ : 0 ≤ B₂ := Real.sqrt_nonneg _
  have hB₄ : 0 ≤ B₄ := Real.sqrt_nonneg _
  have hB₂sq : B₂ ^ 2 = 2 * ((Ct * ρ) ^ 2 + A₂) := by
    dsimp only [B₂]
    exact Real.sq_sqrt hZ₂
  have hB₄sq : B₄ ^ 2 = 2 * ((Ct * ρ) ^ 2 + A₄) := by
    dsimp only [B₄]
    exact Real.sq_sqrt hZ₄
  have hK₁ : 0 ≤ K₁ := mul_nonneg (mul_nonneg hCa hCt) hB₄
  have hK₂ : 0 ≤ K₂ := mul_nonneg (mul_nonneg hCa hB₂) hCt
  have hC : 0 ≤ C := mul_nonneg (by norm_num) (add_nonneg hK₁ hK₂)
  refine ⟨ρ, C, hρ, hC, ?_⟩
  intro g hEq hjet T U gT gU hTtie hUtie hT hU
  have hjet1 := hjet 1 (by norm_num)
  have hjet2 := hjet 2 (by norm_num)
  let N : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖
  have hN : 0 ≤ N := norm_nonneg _
  have hmov : ∀ (P : SmoothCcTensor g 0 2)
      (gm : SmoothRiemannianMetric I M),
      (∀ (y : M) (v w : TangentSpace I y),
        gm.inner y v w =
          g.inner y v w + ccTensorBilinSymm (I := I) g P y v w) →
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) P‖ ≤ ρ →
      (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 4 2 j
            (pureTrace (I := I) (M := M) g gm 2)‖ ^ 2) ≤ B₂ ^ 2 ∧
        (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 6 4 j
            (pureTrace (I := I) (M := M) g gm 4)‖ ^ 2) ≤ B₄ ^ 2 := by
    intro P gm htie hP
    rw [hB₂sq, hB₄sq]
    dsimp only [A₂, A₄, vol]
    exact movWin (I := I) (M := M) gBase g gm hEq hρ hCt
      (htrace g hEq hjet) P htie hP
  obtain ⟨hd₂, hd₄⟩ := htrace g hEq hjet T U gT gU hTtie hUtie hT hU
  obtain ⟨_, hT₄⟩ := hmov T gT hTtie hT
  obtain ⟨hU₂, _⟩ := hmov U gU hUtie hU
  have hQ₁ : (∑ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g 6 2 j
        (ccOperatorFieldComp (I := I) (M := M) g 6 4 2
          (pureTrace (I := I) (M := M) g gT 2 -
            pureTrace (I := I) (M := M) g gU 2)
          (pureTrace (I := I) (M := M) g gT 4))‖ ^ 2) ≤
      (K₁ * N) ^ 2 := by
    refine (happ g hEq hjet1 hjet2 _ _ (Ct * N) B₄
      (mul_nonneg hCt hN) hB₄ (by simpa only [N] using hd₂) hT₄).trans
      (le_of_eq ?_)
    dsimp only [K₁]
    ring
  have hQ₂ : (∑ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g 6 2 j
        (ccOperatorFieldComp (I := I) (M := M) g 6 4 2
          (pureTrace (I := I) (M := M) g gU 2)
          (pureTrace (I := I) (M := M) g gT 4 -
            pureTrace (I := I) (M := M) g gU 4))‖ ^ 2) ≤
      (K₂ * N) ^ 2 := by
    refine (happ g hEq hjet1 hjet2 _ _ B₂ (Ct * N)
      hB₂ (mul_nonneg hCt hN) hU₂ (by simpa only [N] using hd₄)).trans
      (le_of_eq ?_)
    dsimp only [K₂]
    ring
  have hfin : (∑ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g 6 2 j
        (cometricDoublePairTraceCoefficient (I := I) (M := M) g gT -
          cometricDoublePairTraceCoefficient (I := I) (M := M) g gU)‖ ^ 2) ≤
      2 * ((K₁ * N) ^ 2 + (K₂ * N) ^ 2) := by
    rw [pairSplit (I := I) (M := M) g gT gU]
    exact (iteratedCovGradNormSq_add_le (I := I) (M := M) g _ _).trans
      (mul_le_mul_of_nonneg_left (add_le_add hQ₁ hQ₂) (by norm_num))
  have hend : 2 * ((K₁ * N) ^ 2 + (K₂ * N) ^ 2) ≤ (C * N) ^ 2 := by
    dsimp only [C]
    nlinarith [sq_nonneg (K₁ * N - K₂ * N),
      mul_nonneg (mul_nonneg hK₁ hN) (mul_nonneg hK₂ hN)]
  exact hfin.trans hend

theorem pair_trace_sobolev_two_uniform_bound
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∃ ρ B : ℝ, 0 < ρ ∧ 0 ≤ B ∧
      ∀ g : SmoothRiemannianMetric I M,
        MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
        (∀ a : ℕ, a ≤ 3 →
          MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ) →
        ∀ (T : SmoothCcTensor g 0 2)
          (gT : SmoothRiemannianMetric I M),
          (∀ (y : M) (v w : TangentSpace I y),
            gT.inner y v w =
              g.inner y v w + ccTensorBilinSymm (I := I) g T y v w) →
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
          (∑ j ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g 6 2 j
              (cometricDoublePairTraceCoefficient (I := I) (M := M) g gT)‖ ^ 2) ≤ B ^ 2 := by
  classical
  obtain ⟨ρ, Ct, hρ, hCt, htrace⟩ :=
    trace24_h2_lip_uniform (I := I) (M := M) hDim gBase hΛ
  obtain ⟨Ca, hCa, happ⟩ :=
    operatorFieldComposition_h2_h2_to_h2_uniform_bound (I := I) (M := M) hDim gBase hΛ 6 4 2
  let vol : ℝ := volCompareC (E := E) Λ *
    ((riemannianVolumeMeasure (I := I) (M := M) gBase) Set.univ).toReal
  let A₂ : ℝ := (Module.finrank ℝ E : ℝ) ^ 8 * vol
  let A₄ : ℝ := (Module.finrank ℝ E : ℝ) ^ 10 * vol
  let B₂ : ℝ := Real.sqrt (2 * ((Ct * ρ) ^ 2 + A₂))
  let B₄ : ℝ := Real.sqrt (2 * ((Ct * ρ) ^ 2 + A₄))
  let B : ℝ := Ca * B₂ * B₄
  have hvol : 0 ≤ vol := by
    dsimp only [vol]
    exact mul_nonneg (Real.sqrt_nonneg _) ENNReal.toReal_nonneg
  have hA₂ : 0 ≤ A₂ := by
    dsimp only [A₂]
    exact mul_nonneg (pow_nonneg (Nat.cast_nonneg _) 8) hvol
  have hA₄ : 0 ≤ A₄ := by
    dsimp only [A₄]
    exact mul_nonneg (pow_nonneg (Nat.cast_nonneg _) 10) hvol
  have hZ₂ : (0 : ℝ) ≤ 2 * ((Ct * ρ) ^ 2 + A₂) :=
    mul_nonneg (by norm_num) (add_nonneg (sq_nonneg _) hA₂)
  have hZ₄ : (0 : ℝ) ≤ 2 * ((Ct * ρ) ^ 2 + A₄) :=
    mul_nonneg (by norm_num) (add_nonneg (sq_nonneg _) hA₄)
  have hB₂ : 0 ≤ B₂ := Real.sqrt_nonneg _
  have hB₄ : 0 ≤ B₄ := Real.sqrt_nonneg _
  have hB₂sq : B₂ ^ 2 = 2 * ((Ct * ρ) ^ 2 + A₂) := by
    dsimp only [B₂]
    exact Real.sq_sqrt hZ₂
  have hB₄sq : B₄ ^ 2 = 2 * ((Ct * ρ) ^ 2 + A₄) := by
    dsimp only [B₄]
    exact Real.sq_sqrt hZ₄
  have hB : 0 ≤ B := mul_nonneg (mul_nonneg hCa hB₂) hB₄
  refine ⟨ρ, B, hρ, hB, ?_⟩
  intro g hEq hjet T gT hTtie hT
  have hjet1 := hjet 1 (by norm_num)
  have hjet2 := hjet 2 (by norm_num)
  obtain ⟨hraw₂, hraw₄⟩ :=
    movWin (I := I) (M := M) gBase g gT hEq hρ hCt
      (htrace g hEq hjet) T hTtie hT
  have hT₂ : (∑ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g 4 2 j
        (pureTrace (I := I) (M := M) g gT 2)‖ ^ 2) ≤ B₂ ^ 2 := by
    rw [hB₂sq]
    dsimp only [A₂, vol]
    exact hraw₂
  have hT₄ : (∑ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g 6 4 j
        (pureTrace (I := I) (M := M) g gT 4)‖ ^ 2) ≤ B₄ ^ 2 := by
    rw [hB₄sq]
    dsimp only [A₄, vol]
    exact hraw₄
  rw [RicciDeTurckLowOrder.pairTrace_eq (I := I) (M := M) g gT]
  dsimp only [B]
  exact happ g hEq hjet1 hjet2 _ _ B₂ B₄ hB₂ hB₄ hT₂ hT₄

omit [SigmaCompactSpace M] in
omit [BoundarylessManifold I M] in
omit [I.Boundaryless] in
private theorem monoSplit (g gT gU : SmoothRiemannianMetric I M)
    (S R : SmoothCcTensor g 0 2) (σ : Equiv.Perm (Fin 4)) :
    curvatureDecompositionMonomialCoeffField (I := I) (M := M) g gT
          (ccTensorUnitValueSection (I := I) (M := M) g S)
          (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g S) σ -
        curvatureDecompositionMonomialCoeffField (I := I) (M := M) g gU
          (ccTensorUnitValueSection (I := I) (M := M) g R)
          (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g R) σ =
      ccOperatorFieldComp (I := I) (M := M) g 4 6 2
          (cometricDoublePairTraceCoefficient (I := I) (M := M) g gT -
            cometricDoublePairTraceCoefficient (I := I) (M := M) g gU)
          (monoExt (I := I) (M := M) g 0 2 4
            (RicciDeTurckLowOrder.monoPerm σ) S) +
        ccOperatorFieldComp (I := I) (M := M) g 4 6 2
          (cometricDoublePairTraceCoefficient (I := I) (M := M) g gU)
          (monoExt (I := I) (M := M) g 0 2 4
              (RicciDeTurckLowOrder.monoPerm σ) S -
            monoExt (I := I) (M := M) g 0 2 4
              (RicciDeTurckLowOrder.monoPerm σ) R) := by
  rw [RicciDeTurckLowOrder.curvMono_eq (I := I) (M := M) g gT S σ,
    RicciDeTurckLowOrder.curvMono_eq (I := I) (M := M) g gU R σ,
    show monoExt (I := I) (M := M) g 0 2 4 (RicciDeTurckLowOrder.monoPerm σ) S =
        rsDomDomCongrSection (I := I) (M := M) g 4 6
          (RicciDeTurckLowOrder.monoPerm σ)
          (slotExtendIter (I := I) (M := M) g 0 2 4 S) from rfl,
    show monoExt (I := I) (M := M) g 0 2 4 (RicciDeTurckLowOrder.monoPerm σ) R =
        rsDomDomCongrSection (I := I) (M := M) g 4 6
          (RicciDeTurckLowOrder.monoPerm σ)
          (slotExtendIter (I := I) (M := M) g 0 2 4 R) from rfl,
    operatorFieldComposition_sub_left, operatorFieldComposition_sub_right]
  abel

private theorem twoTerm {K₁ K₂ x y : ℝ}
    (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    2 * ((K₁ * x) ^ 2 + (K₂ * y) ^ 2) ≤ (2 * (K₁ + K₂) * (x + y)) ^ 2 := by
  have hK : 0 ≤ K₁ + K₂ := add_nonneg hK₁ hK₂
  have h₁ : K₁ * x ≤ (K₁ + K₂) * (x + y) := by
    calc
      K₁ * x ≤ (K₁ + K₂) * x :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hK₂) hx
      _ ≤ (K₁ + K₂) * (x + y) :=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hy) hK
  have h₂ : K₂ * y ≤ (K₁ + K₂) * (x + y) := by
    calc
      K₂ * y ≤ (K₁ + K₂) * y :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hK₁) hy
      _ ≤ (K₁ + K₂) * (x + y) :=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hx) hK
  have hs₁ := pow_le_pow_left₀ (mul_nonneg hK₁ hx) h₁ 2
  have hs₂ := pow_le_pow_left₀ (mul_nonneg hK₂ hy) h₂ 2
  calc
    2 * ((K₁ * x) ^ 2 + (K₂ * y) ^ 2) ≤
        2 * (((K₁ + K₂) * (x + y)) ^ 2 + ((K₁ + K₂) * (x + y)) ^ 2) :=
      mul_le_mul_of_nonneg_left (add_le_add hs₁ hs₂) (by norm_num)
    _ = (2 * (K₁ + K₂) * (x + y)) ^ 2 := by ring

theorem curvMono_h2_lip_uniform
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧
      ∀ g : SmoothRiemannianMetric I M,
        MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
        (∀ a : ℕ, a ≤ 3 →
          MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ) →
        ∀ (T U : SmoothCcTensor g 0 2)
          (gT gU : SmoothRiemannianMetric I M),
          (∀ (y : M) (v w : TangentSpace I y),
            gT.inner y v w =
              g.inner y v w + ccTensorBilinSymm (I := I) g T y v w) →
          (∀ (y : M) (v w : TangentSpace I y),
            gU.inner y v w =
              g.inner y v w + ccTensorBilinSymm (I := I) g U y v w) →
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
          ∀ (S R : SmoothCcTensor g 0 2)
            (σ : Equiv.Perm (Fin 4)) (A D : ℝ),
            0 ≤ A → 0 ≤ D →
            (∑ j ∈ Finset.range 3,
              ‖iteratedCovGrad (I := I) g 0 2 j S‖ ^ 2) ≤ A ^ 2 →
            (∑ j ∈ Finset.range 3,
              ‖iteratedCovGrad (I := I) g 0 2 j (S - R)‖ ^ 2) ≤ D ^ 2 →
            (∑ j ∈ Finset.range 3,
              ‖iteratedCovGrad (I := I) g 4 2 j
                (curvatureDecompositionMonomialCoeffField (I := I) (M := M) g gT
                    (ccTensorUnitValueSection (I := I) (M := M) g S)
                    (ccTensorUnitValueSection_contMDiff
                      (I := I) (M := M) g S) σ -
                  curvatureDecompositionMonomialCoeffField (I := I) (M := M) g gU
                    (ccTensorUnitValueSection (I := I) (M := M) g R)
                    (ccTensorUnitValueSection_contMDiff
                      (I := I) (M := M) g R) σ)‖ ^ 2) ≤
              (C * (A * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
                (T - U)‖ + D)) ^ 2 := by
  classical
  obtain ⟨ρ₁, Cp, hρ₁, hCp, hpair⟩ :=
    pairTrace_h2_lip_uniform (I := I) (M := M) hDim gBase hΛ
  obtain ⟨ρ₂, Bp, hρ₂, hBp, hbpair⟩ :=
    pair_trace_sobolev_two_uniform_bound (I := I) (M := M) hDim gBase hΛ
  obtain ⟨Ca, hCa, happ⟩ :=
    operatorFieldComposition_h2_h2_to_h2_uniform_bound (I := I) (M := M) hDim gBase hΛ 4 6 2
  have hfr3 : ((Module.finrank ℝ E : ℕ) : ℝ) = 3 := by rw [hDim]; norm_num
  let ρ : ℝ := min ρ₁ ρ₂
  let K₁ : ℝ := 9 * Ca * Cp
  let K₂ : ℝ := 9 * Ca * Bp
  let C : ℝ := 2 * (K₁ + K₂)
  have hρ : 0 < ρ := lt_min hρ₁ hρ₂
  have hK₁ : 0 ≤ K₁ :=
    mul_nonneg (mul_nonneg (by norm_num) hCa) hCp
  have hK₂ : 0 ≤ K₂ :=
    mul_nonneg (mul_nonneg (by norm_num) hCa) hBp
  have hC : 0 ≤ C :=
    mul_nonneg (by norm_num) (add_nonneg hK₁ hK₂)
  refine ⟨ρ, C, hρ, hC, ?_⟩
  intro g hEq hjet T U gT gU hTtie hUtie hT hU S R σ A D hA hD hS hSR
  have hjet1 := hjet 1 (by norm_num)
  have hjet2 := hjet 2 (by norm_num)
  let N : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖
  let X : SmoothCcTensor g 0 2 → SmoothCcTensor g 4 6 :=
    fun W => monoExt (I := I) (M := M) g 0 2 4 (RicciDeTurckLowOrder.monoPerm σ) W
  let Q₁ : SmoothCcTensor g 4 2 :=
    ccOperatorFieldComp (I := I) (M := M) g 4 6 2
      (cometricDoublePairTraceCoefficient (I := I) (M := M) g gT -
        cometricDoublePairTraceCoefficient (I := I) (M := M) g gU) (X S)
  let Q₂ : SmoothCcTensor g 4 2 :=
    ccOperatorFieldComp (I := I) (M := M) g 4 6 2
      (cometricDoublePairTraceCoefficient (I := I) (M := M) g gU) (X S - X R)
  have hN : 0 ≤ N := norm_nonneg _
  have hT₁ : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ₁ :=
    hT.trans (min_le_left _ _)
  have hU₁ : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ₁ :=
    hU.trans (min_le_left _ _)
  have hU₂ : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ₂ :=
    hU.trans (min_le_right _ _)
  have hPdiff :
      (∑ j ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 6 2 j
          (cometricDoublePairTraceCoefficient (I := I) (M := M) g gT -
            cometricDoublePairTraceCoefficient (I := I) (M := M) g gU)‖ ^ 2) ≤ (Cp * N) ^ 2 :=
    hpair g hEq hjet T U gT gU hTtie hUtie hT₁ hU₁
  have hPend :
      (∑ j ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 6 2 j
          (cometricDoublePairTraceCoefficient (I := I) (M := M) g gU)‖ ^ 2) ≤ Bp ^ 2 :=
    hbpair g hEq hjet U gU hUtie hU₂
  have hXS :
      (∑ j ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 4 6 j (X S)‖ ^ 2) ≤ (9 * A) ^ 2 := by
    calc
      (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 4 6 j (X S)‖ ^ 2) ≤
          (Module.finrank ℝ E : ℝ) ^ 4 *
            ∑ j ∈ Finset.range 3,
              ‖iteratedCovGrad (I := I) g 0 2 j S‖ ^ 2 :=
        monoExtJet (I := I) (M := M) g 0 2 4 2
          (RicciDeTurckLowOrder.monoPerm σ) S
      _ ≤ (Module.finrank ℝ E : ℝ) ^ 4 * A ^ 2 :=
        mul_le_mul_of_nonneg_left hS (pow_nonneg (Nat.cast_nonneg _) 4)
      _ = (9 * A) ^ 2 := by rw [hfr3]; ring
  have hXdiff :
      (∑ j ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 4 6 j (X S - X R)‖ ^ 2) ≤
        (9 * D) ^ 2 := by
    rw [show X S - X R =
        monoExt (I := I) (M := M) g 0 2 4
          (RicciDeTurckLowOrder.monoPerm σ) (S - R) from
      (monoExtSub (I := I) (M := M) g 0 2 4
        (RicciDeTurckLowOrder.monoPerm σ) S R).symm]
    calc
      (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 4 6 j
            (monoExt (I := I) (M := M) g 0 2 4
              (RicciDeTurckLowOrder.monoPerm σ) (S - R))‖ ^ 2) ≤
          (Module.finrank ℝ E : ℝ) ^ 4 *
            ∑ j ∈ Finset.range 3,
              ‖iteratedCovGrad (I := I) g 0 2 j (S - R)‖ ^ 2 :=
        monoExtJet (I := I) (M := M) g 0 2 4 2
          (RicciDeTurckLowOrder.monoPerm σ) (S - R)
      _ ≤ (Module.finrank ℝ E : ℝ) ^ 4 * D ^ 2 :=
        mul_le_mul_of_nonneg_left hSR (pow_nonneg (Nat.cast_nonneg _) 4)
      _ = (9 * D) ^ 2 := by rw [hfr3]; ring
  have hr₁ : (Ca * (Cp * N) * (9 * A)) ^ 2 = (K₁ * (A * N)) ^ 2 := by
    dsimp only [K₁]; ring
  have hr₂ : (Ca * Bp * (9 * D)) ^ 2 = (K₂ * D) ^ 2 := by
    dsimp only [K₂]; ring
  have hQ₁ :
      (∑ j ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 4 2 j Q₁‖ ^ 2) ≤
        (K₁ * (A * N)) ^ 2 :=
    (happ g hEq hjet1 hjet2 _ (X S) (Cp * N) (9 * A)
      (mul_nonneg hCp hN) (mul_nonneg (by norm_num) hA)
      hPdiff hXS).trans (le_of_eq hr₁)
  have hQ₂ :
      (∑ j ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 4 2 j Q₂‖ ^ 2) ≤ (K₂ * D) ^ 2 :=
    (happ g hEq hjet1 hjet2 _ (X S - X R) Bp (9 * D)
      hBp (mul_nonneg (by norm_num) hD)
      hPend hXdiff).trans (le_of_eq hr₂)
  have hmono :
      curvatureDecompositionMonomialCoeffField (I := I) (M := M) g gT
            (ccTensorUnitValueSection (I := I) (M := M) g S)
            (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g S) σ -
          curvatureDecompositionMonomialCoeffField (I := I) (M := M) g gU
            (ccTensorUnitValueSection (I := I) (M := M) g R)
            (ccTensorUnitValueSection_contMDiff (I := I) (M := M) g R) σ =
        Q₁ + Q₂ := by
    dsimp only [Q₁, Q₂, X]
    exact monoSplit (I := I) (M := M) g gT gU S R σ
  rw [hmono]
  calc
    (∑ j ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 4 2 j (Q₁ + Q₂)‖ ^ 2) ≤
        2 * ((∑ j ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g 4 2 j Q₁‖ ^ 2) +
          ∑ j ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g 4 2 j Q₂‖ ^ 2) :=
      iteratedCovGradNormSq_add_le (I := I) (M := M) g Q₁ Q₂
    _ ≤ 2 * ((K₁ * (A * N)) ^ 2 + (K₂ * D) ^ 2) :=
      mul_le_mul_of_nonneg_left (add_le_add hQ₁ hQ₂) (by norm_num)
    _ ≤ (C * (A * N + D)) ^ 2 := by
      dsimp only [C]
      exact twoTerm hK₁ hK₂ (mul_nonneg hA hN) hD

theorem curv_pair_h2_uniform
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ g : SmoothRiemannianMetric I M,
        MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
        (∀ a : ℕ, a ≤ 3 →
          MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ) →
        ∀ (S R : SmoothCcTensor g 0 2)
          (σ : Equiv.Perm (Fin 4)) (D : ℝ),
          0 ≤ D →
          (∑ j ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g 0 2 j (S - R)‖ ^ 2) ≤ D ^ 2 →
          (∑ j ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g 4 2 j
              (curvatureDecompositionMonomialCoeffField (I := I) (M := M) g g
                  (ccTensorUnitValueSection (I := I) (M := M) g S)
                  (ccTensorUnitValueSection_contMDiff
                    (I := I) (M := M) g S) σ -
                curvatureDecompositionMonomialCoeffField (I := I) (M := M) g g
                  (ccTensorUnitValueSection (I := I) (M := M) g R)
                  (ccTensorUnitValueSection_contMDiff
                    (I := I) (M := M) g R) σ)‖ ^ 2) ≤ (C * D) ^ 2 := by
  obtain ⟨ρ, C, hρ, hC, hlip⟩ :=
    curvMono_h2_lip_uniform (I := I) (M := M) hDim gBase hΛ
  refine ⟨C, hC, ?_⟩
  intro g hEq hjet S R σ D hD hSR
  let A : ℝ := Real.sqrt (∑ j ∈ Finset.range 3,
    ‖iteratedCovGrad (I := I) g 0 2 j S‖ ^ 2)
  have hA : 0 ≤ A := Real.sqrt_nonneg _
  have hS : (∑ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g 0 2 j S‖ ^ 2) ≤ A ^ 2 :=
    (Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)).symm.le
  have hzero : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
      (0 : SmoothCcTensor g 0 2)‖ ≤ ρ := by
    rw [zeroHs (I := I) (M := M) g, norm_zero]
    exact le_of_lt hρ
  have hraw := hlip g hEq hjet
    (0 : SmoothCcTensor g 0 2) (0 : SmoothCcTensor g 0 2) g g
    (zeroTie (I := I) (M := M) g) (zeroTie (I := I) (M := M) g)
    hzero hzero S R σ A D hA hD hS hSR
  simpa only [sub_self, zeroHs (I := I) (M := M) g, norm_zero,
    mul_zero, zero_add] using hraw

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
