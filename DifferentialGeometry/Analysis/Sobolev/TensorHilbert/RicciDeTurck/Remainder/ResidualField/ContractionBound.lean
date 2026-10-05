import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.OperatorField.HomFieldActionL2JetBound
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.CovariantJet.Naturality
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RicciDeTurck.Remainder.ResidualField.GridWindow.Basic

noncomputable section

open Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Analysis.Sobolev

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Spectral (ccOperatorFieldComp slotExtend slotExtendIter)
open DifferentialGeometry.Integral.L2 (SmoothCcTensor)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M]

theorem exists_decompositionKernelContractionMonomialField_covariantJetNormSq_le
    (g₀ g₁ : SmoothRiemannianMetric I M) (m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (G : SmoothCcTensor g₀ 0 4) (σ : Equiv.Perm (Fin 4)),
      covariantJetNormSq (I := I) (M := M) g₀ m
          (decompositionKernelContractionMonomialField (I := I) (M := M) g₀ g₁ G σ) ≤
        K * covariantJetNormSq (I := I) (M := M) g₀ m G := by
  obtain ⟨C, hC, hcomp⟩ :=
    exists_operatorFieldComposition_covariantJetNormSq_le (I := I) (M := M) g₀ 6 2
      (secondMetricPairTraceOperator (I := I) (M := M) g₀ g₁) m
  let fr : ℝ := Module.finrank ℝ E
  let K : ℝ := C * (fr * fr)
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  have hK : 0 ≤ K := mul_nonneg hC (mul_nonneg hfr hfr)
  refine ⟨K, hK, fun G σ => ?_⟩
  let τ : Equiv.Perm (Fin 4) :=
    Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3 * σ
  let D : SmoothCcTensor g₀ 0 4 := domDomCongrSection (I := I) g₀ τ G
  let S : SmoothCcTensor g₀ 2 6 := slotExtendIter (I := I) (M := M) g₀ 0 4 2 D
  let R : SmoothCcTensor g₀ 2 6 :=
    rsDomDomCongrSection (I := I) (M := M) g₀ 2 6 ricciContractionRemainderSlotPerm S
  have hD : covariantJetNormSq (I := I) (M := M) g₀ m D =
      covariantJetNormSq (I := I) (M := M) g₀ m G :=
    covariantJetNormSq_domDomCongrSection (I := I) (M := M) g₀ τ G
  have hS : covariantJetNormSq (I := I) (M := M) g₀ m S ≤
      fr * (fr * covariantJetNormSq (I := I) (M := M) g₀ m D) := by
    calc
      covariantJetNormSq (I := I) (M := M) g₀ m S =
        covariantJetNormSq (I := I) (M := M) g₀ m
          (slotExtend (I := I) (M := M) g₀ 1 5
            (slotExtend (I := I) (M := M) g₀ 0 4 D)) := rfl
      _ ≤ fr * covariantJetNormSq (I := I) (M := M) g₀ m
          (slotExtend (I := I) (M := M) g₀ 0 4 D) :=
        covariantJetNormSq_slotExtend_le (I := I) (M := M) g₀ 1 5 _
      _ ≤ fr * (fr * covariantJetNormSq (I := I) (M := M) g₀ m D) :=
        mul_le_mul_of_nonneg_left
          (covariantJetNormSq_slotExtend_le (I := I) (M := M) g₀ 0 4 D) hfr
  have hR : covariantJetNormSq (I := I) (M := M) g₀ m R =
      covariantJetNormSq (I := I) (M := M) g₀ m S :=
    covariantJetNormSq_rsDomDomCongrSection (I := I) (M := M) g₀ ricciContractionRemainderSlotPerm S
  have href : decompositionKernelContractionMonomialField (I := I) (M := M) g₀ g₁ G σ =
      ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
        (secondMetricPairTraceOperator (I := I) (M := M) g₀ g₁) R := by
    exact decompositionKernelContractionMonomialField_eq_movingMetricPairTraceOperator_comp
      (I := I) (M := M) g₀ g₁ G σ
  rw [href]
  calc
    covariantJetNormSq (I := I) (M := M) g₀ m
        (ccOperatorFieldComp (I := I) (M := M) g₀ 2 6 2
          (secondMetricPairTraceOperator (I := I) (M := M) g₀ g₁) R) ≤
      C * covariantJetNormSq (I := I) (M := M) g₀ m R := hcomp 2 R
    _ = C * covariantJetNormSq (I := I) (M := M) g₀ m S := by rw [hR]
    _ ≤ C * (fr * (fr * covariantJetNormSq (I := I) (M := M) g₀ m D)) :=
      mul_le_mul_of_nonneg_left hS hC
    _ = K * covariantJetNormSq (I := I) (M := M) g₀ m G := by
      rw [hD]
      dsimp only [K]
      ring

end DifferentialGeometry.Analysis.Sobolev
