import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricArmCoeffPassZero
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection

noncomputable section

open Bundle Manifold MeasureTheory Set Filter DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.TensorRSNabla
open DifferentialGeometry.TensorMultilinear
open DifferentialGeometry.Analysis.Spectral.MetricRealization
  (metricCauchySchwarzBound ccTensorBilinSymm)
section NormedReindexingNorm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

theorem rfns_iteratedCovGrad_rsDomDomCongr_both_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (σ' : Equiv.Perm (Fin r)) (σ : Equiv.Perm (Fin s))
    (R : SmoothCcTensor g r s) (i : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g r (s + i) x
        ((iteratedCovGrad (I := I) g r s i
          (reindexCoeffGen (I := I) (M := M) g r s
            (rsDomDomCongrSection (I := I) (M := M) g r s σ R) σ')).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g r (s + i) x
        ((iteratedCovGrad (I := I) g r s i R).toSection x) := by
  rw [riemannianFiberNormSq_iteratedCovGrad_reindexCoeffGen_eq (I := I) (M := M) g r s
    (rsDomDomCongrSection (I := I) (M := M) g r s σ R) σ' i x]
  exact riemannianFiberNormSq_iteratedCovGrad_rs_eq_of_section_domDomCongr (I := I) (M := M) g r s σ
    R
    (rsDomDomCongrSection (I := I) (M := M) g r s σ R)
    (fun y d => by
      rw [rsDomDomCongrSection_toSection, toModel_rsDomDomCongr_apply]) i x

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M]
    in
private lemma slotInsertEndoCc_succ_eq_reindex_slotExtend
    (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (Λ : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)) :
    endoSlotZeroCcTensor (I := I) (M := M) g₀ (s + 1) Λ =
      reindexCoeffGen (I := I) (M := M) g₀ (s + 1 + 1) (s + 1 + 1)
        (rsDomDomCongrSection (I := I) (M := M) g₀ (s + 1 + 1) (s + 1 + 1)
          (Equiv.swap (0 : Fin (s + 1 + 1)) 1)
          (slotExtend (I := I) (M := M) g₀ (s + 1) (s + 1)
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ s Λ)))
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
        (endoSlotZeroCcTensor (I := I) (M := M) g₀ (s + 1) Λ).toSection x) D) m =
    Tensor0SSpace.toModel
      ((show Tensor0SSpace (s + 1 + 1) I x →L[ℝ] Tensor0SSpace (s + 1 + 1) I x from
        (reindexCoeffGen (I := I) (M := M) g₀ (s + 1 + 1) (s + 1 + 1)
          (rsDomDomCongrSection (I := I) (M := M) g₀ (s + 1 + 1) (s + 1 + 1)
            (Equiv.swap (0 : Fin (s + 1 + 1)) 1)
            (slotExtend (I := I) (M := M) g₀ (s + 1) (s + 1)
              (endoSlotZeroCcTensor (I := I) (M := M) g₀ s Λ)))
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
  rw [slotInsertEndoCc_toSection, slotInsertEndoFib_apply_eval, tensor0S_curry_apply_eval,
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

theorem rfns_iteratedCovGrad_slotInsertEndoCc_le_endo
    (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (Λ : ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x))
    (i : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ (s + 1) ((s + 1) + i) x
        ((iteratedCovGrad (I := I) g₀ (s + 1) (s + 1) i
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ s Λ)).toSection x) ≤
      (Module.finrank ℝ E : ℝ) ^ s *
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
          ((iteratedCovGrad (I := I) g₀ 1 1 i
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0 Λ)).toSection x) := by
  induction s with
  | zero =>
    rw [pow_zero, one_mul]
  | succ s ih =>
    have hfr : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
    have hA : riemannianFiberNormSq (I := I) (M := M) g₀ (s + 1 + 1) ((s + 1 + 1) + i) x
          ((iteratedCovGrad (I := I) g₀ (s + 1 + 1) (s + 1 + 1) i
            (endoSlotZeroCcTensor (I := I) (M := M) g₀ (s + 1) Λ)).toSection x) =
        riemannianFiberNormSq (I := I) (M := M) g₀ (s + 1 + 1) ((s + 1 + 1) + i) x
          ((iteratedCovGrad (I := I) g₀ (s + 1 + 1) (s + 1 + 1) i
            (slotExtend (I := I) (M := M) g₀ (s + 1) (s + 1)
              (endoSlotZeroCcTensor (I := I) (M := M) g₀ s Λ))).toSection x) := by
      rw [slotInsertEndoCc_succ_eq_reindex_slotExtend (I := I) (M := M) g₀ s Λ]
      exact rfns_iteratedCovGrad_rsDomDomCongr_both_eq (I := I) (M := M) g₀ (s + 1 + 1) (s + 1 + 1)
        (Equiv.swap (0 : Fin (s + 1 + 1)) 1) (Equiv.swap (0 : Fin (s + 1 + 1)) 1)
        (slotExtend (I := I) (M := M) g₀ (s + 1) (s + 1)
          (endoSlotZeroCcTensor (I := I) (M := M) g₀ s Λ)) i x
    rw [hA]
    refine le_trans (rfns_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ (s + 1) (s + 1)
      (endoSlotZeroCcTensor (I := I) (M := M) g₀ s Λ) i x) ?_
    calc (Module.finrank ℝ E : ℝ) *
            riemannianFiberNormSq (I := I) (M := M) g₀ (s + 1) ((s + 1) + i) x
              ((iteratedCovGrad (I := I) g₀ (s + 1) (s + 1) i
                (endoSlotZeroCcTensor (I := I) (M := M) g₀ s Λ)).toSection x)
        ≤ (Module.finrank ℝ E : ℝ) *
            ((Module.finrank ℝ E : ℝ) ^ s *
              riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
                ((iteratedCovGrad (I := I) g₀ 1 1 i
                  (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0 Λ)).toSection x)) :=
          mul_le_mul_of_nonneg_left ih hfr
      _ = (Module.finrank ℝ E : ℝ) ^ (s + 1) *
            riemannianFiberNormSq (I := I) (M := M) g₀ 1 (1 + i) x
              ((iteratedCovGrad (I := I) g₀ 1 1 i
                (endoSlotZeroCcTensor (I := I) (M := M) g₀ 0 Λ)).toSection x) := by
          rw [pow_succ]; ring

end NormedReindexingNorm

end Sobolev
end Analysis
end DifferentialGeometry

end
