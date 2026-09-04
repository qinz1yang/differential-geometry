import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureCoefficientDifferenceJetTower.PairTrace


noncomputable section

open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open Bundle Manifold MeasureTheory Set Filter DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

theorem slotIteratedCovGradSq (g : SmoothRiemannianMetric I M) (r s i : ℕ)
    (A : SmoothCcTensor g r s) :
    ‖iteratedCovGrad (I := I) g (r + 1) (s + 1) i
        (slotExtend (I := I) (M := M) g r s A)‖ ^ 2 ≤
      (Module.finrank ℝ E : ℝ) *
        ‖iteratedCovGrad (I := I) g r s i A‖ ^ 2 := by
  let F : M → ℝ := fun x =>
    (Module.finrank ℝ E : ℝ) *
      riemannianFiberNormSq (I := I) (M := M) g r (s + i) x
        ((iteratedCovGrad (I := I) g r s i A).toSection x)
  have hF : MeasureTheory.Integrable F
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    dsimp only [F]
    exact (integrable_riemannianFiberNormSq_toSection
      (I := I) (M := M) g r (s + i)
      (iteratedCovGrad (I := I) g r s i A)).const_mul _
  have hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g
          (r + 1) ((s + 1) + i) x
          ((iteratedCovGrad (I := I) g (r + 1) (s + 1) i
            (slotExtend (I := I) (M := M) g r s A)).toSection x) ≤
        F x := by
    intro x
    simpa only [F, Nat.add_assoc] using
      riemannianFiberNormSq_iteratedCovGrad_slotExtend_le
        (I := I) (M := M) g r s A i x
  have hsq := normSq_le_integral_of_pointwise_fiberNormSq_le_rs
    (I := I) (M := M) g (r + 1) ((s + 1) + i)
    (iteratedCovGrad (I := I) g (r + 1) (s + 1) i
      (slotExtend (I := I) (M := M) g r s A))
    F hF hpt
  have hint :
      ∫ x, riemannianFiberNormSq (I := I) (M := M) g
          r (s + i) x
          ((iteratedCovGrad (I := I) g r s i A).toSection x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ‖iteratedCovGrad (I := I) g r s i A‖ ^ 2 := by
    rw [SmoothCcTensor.norm_def,
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs
        (I := I) (M := M) g r (s + i)]
  dsimp only [F] at hsq
  rw [MeasureTheory.integral_const_mul, hint] at hsq
  exact hsq

theorem slotJet (g : SmoothRiemannianMetric I M) (r s m : ℕ)
    (A : SmoothCcTensor g r s) :
    (∑ j ∈ Finset.range (m + 1),
        ‖iteratedCovGrad (I := I) g (r + 1) (s + 1) j
          (slotExtend (I := I) (M := M) g r s A)‖ ^ 2) ≤
      (Module.finrank ℝ E : ℝ) *
        ∑ j ∈ Finset.range (m + 1),
          ‖iteratedCovGrad (I := I) g r s j A‖ ^ 2 := by
  calc
    (∑ j ∈ Finset.range (m + 1),
        ‖iteratedCovGrad (I := I) g (r + 1) (s + 1) j
          (slotExtend (I := I) (M := M) g r s A)‖ ^ 2) ≤
        ∑ j ∈ Finset.range (m + 1), (Module.finrank ℝ E : ℝ) *
          ‖iteratedCovGrad (I := I) g r s j A‖ ^ 2 :=
      Finset.sum_le_sum fun j _ =>
        slotIteratedCovGradSq (I := I) (M := M) g r s j A
    _ = (Module.finrank ℝ E : ℝ) *
        ∑ j ∈ Finset.range (m + 1),
          ‖iteratedCovGrad (I := I) g r s j A‖ ^ 2 := by
      rw [Finset.mul_sum]

theorem slotIterJet (g : SmoothRiemannianMetric I M) (r s m w : ℕ)
    (A : SmoothCcTensor g r s) :
    (∑ j ∈ Finset.range (m + 1),
        ‖iteratedCovGrad (I := I) g (r + w) (s + w) j
          (slotExtendIter (I := I) (M := M) g r s w A)‖ ^ 2) ≤
      (Module.finrank ℝ E : ℝ) ^ w *
        ∑ j ∈ Finset.range (m + 1),
          ‖iteratedCovGrad (I := I) g r s j A‖ ^ 2 := by
  have hfr : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
  induction w with
  | zero =>
    simpa only [slotExtendIter, Nat.add_zero, pow_zero, one_mul] using
      le_refl (∑ j ∈ Finset.range (m + 1),
        ‖iteratedCovGrad (I := I) g r s j A‖ ^ 2)
  | succ w ih =>
    calc
      (∑ j ∈ Finset.range (m + 1),
          ‖iteratedCovGrad (I := I) g (r + (w + 1)) (s + (w + 1)) j
            (slotExtendIter (I := I) (M := M) g r s (w + 1) A)‖ ^ 2) =
          ∑ j ∈ Finset.range (m + 1),
            ‖iteratedCovGrad (I := I) g ((r + w) + 1) ((s + w) + 1) j
              (slotExtend (I := I) (M := M) g (r + w) (s + w)
                (slotExtendIter (I := I) (M := M) g r s w A))‖ ^ 2 := rfl
      _ ≤ (Module.finrank ℝ E : ℝ) *
            ∑ j ∈ Finset.range (m + 1),
              ‖iteratedCovGrad (I := I) g (r + w) (s + w) j
                (slotExtendIter (I := I) (M := M) g r s w A)‖ ^ 2 :=
        slotJet (I := I) (M := M) g (r + w) (s + w) m _
      _ ≤ (Module.finrank ℝ E : ℝ) *
            ((Module.finrank ℝ E : ℝ) ^ w *
              ∑ j ∈ Finset.range (m + 1),
                ‖iteratedCovGrad (I := I) g r s j A‖ ^ 2) :=
        mul_le_mul_of_nonneg_left ih hfr
      _ = (Module.finrank ℝ E : ℝ) ^ (w + 1) *
            ∑ j ∈ Finset.range (m + 1),
              ‖iteratedCovGrad (I := I) g r s j A‖ ^ 2 := by ring

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem slotExtendIter_sub (g : SmoothRiemannianMetric I M) (r s w : ℕ)
    (A B : SmoothCcTensor g r s) :
    slotExtendIter (I := I) (M := M) g r s w (A - B) =
      slotExtendIter (I := I) (M := M) g r s w A -
        slotExtendIter (I := I) (M := M) g r s w B := by
  induction w with
  | zero => rfl
  | succ w ih =>
    change slotExtend (I := I) (M := M) g (r + w) (s + w)
        (slotExtendIter (I := I) (M := M) g r s w (A - B)) =
      slotExtend (I := I) (M := M) g (r + w) (s + w)
          (slotExtendIter (I := I) (M := M) g r s w A) -
        slotExtend (I := I) (M := M) g (r + w) (s + w)
          (slotExtendIter (I := I) (M := M) g r s w B)
    rw [ih, slotExtend_sub]

theorem rspermSq (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (σ : Equiv.Perm (Fin s)) (A : SmoothCcTensor g r s) (i : ℕ) :
    ‖iteratedCovGrad (I := I) g r s i
        (rsDomDomCongrSection (I := I) (M := M) g r s σ A)‖ ^ 2 =
      ‖iteratedCovGrad (I := I) g r s i A‖ ^ 2 := by
  rw [SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs,
    SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs]
  refine MeasureTheory.integral_congr_ae
    (Filter.Eventually.of_forall fun x => ?_)
  exact riemannianFiberNormSq_iteratedCovGrad_rs_eq_of_section_domDomCongr
    (I := I) (M := M) g r s σ A
      (rsDomDomCongrSection (I := I) (M := M) g r s σ A)
      (fun y d => by
        rw [rsDomDomCongrSection_toSection,
          toModel_rsDomDomCongr_apply]) i x

theorem rspermJet (g : SmoothRiemannianMetric I M) {r s : ℕ} (m : ℕ)
    (σ : Equiv.Perm (Fin s)) (A : SmoothCcTensor g r s) :
    (∑ j ∈ Finset.range (m + 1),
        ‖iteratedCovGrad (I := I) g r s j
          (rsDomDomCongrSection (I := I) (M := M) g r s σ A)‖ ^ 2) =
      ∑ j ∈ Finset.range (m + 1),
        ‖iteratedCovGrad (I := I) g r s j A‖ ^ 2 :=
  Finset.sum_congr rfl fun i _ =>
    rspermSq (I := I) (M := M) g σ A i

def monoExt (g : SmoothRiemannianMetric I M) (r s w : ℕ)
    (τ : Equiv.Perm (Fin (s + w))) (A : SmoothCcTensor g r s) :
    SmoothCcTensor g (r + w) (s + w) :=
  rsDomDomCongrSection (I := I) (M := M) g (r + w) (s + w) τ
    (slotExtendIter (I := I) (M := M) g r s w A)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem monoExtSub (g : SmoothRiemannianMetric I M) (r s w : ℕ)
    (τ : Equiv.Perm (Fin (s + w))) (A B : SmoothCcTensor g r s) :
    monoExt (I := I) (M := M) g r s w τ (A - B) =
      monoExt (I := I) (M := M) g r s w τ A -
        monoExt (I := I) (M := M) g r s w τ B := by
  rw [monoExt, slotExtendIter_sub,
    CurvatureCoefficientDifferenceJetTower.rsDomDomCongrSection_sub_cc]
  rfl

theorem monoExtJet (g : SmoothRiemannianMetric I M) (r s w m : ℕ)
    (τ : Equiv.Perm (Fin (s + w))) (A : SmoothCcTensor g r s) :
    (∑ j ∈ Finset.range (m + 1),
        ‖iteratedCovGrad (I := I) g (r + w) (s + w) j
          (monoExt (I := I) (M := M) g r s w τ A)‖ ^ 2) ≤
      (Module.finrank ℝ E : ℝ) ^ w *
        ∑ j ∈ Finset.range (m + 1),
          ‖iteratedCovGrad (I := I) g r s j A‖ ^ 2 := by
  rw [monoExt, rspermJet]
  exact slotIterJet (I := I) (M := M) g r s m w A

end Connection
end Integral
end DifferentialGeometry

end
