import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderPrincipalArmOpNormConnLapIterateAppCcCovGradSobolevBound
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Elliptic


noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Spectral

open DifferentialGeometry
open DifferentialGeometry.Integral.L2

open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

section BalLadder

variable (g₀ : SmoothRiemannianMetric I M)


lemma exists_deTurckRemainder_connLapIterate_sobolevHs_bound (g₀ : SmoothRiemannianMetric I M)
    (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    (Kc : ℕ → ℝ) (hKc_nn : ∀ i, 0 ≤ Kc i) (εa : ℝ) (hεa_nn : 0 ≤ εa) :
    ∃ KZ : ℕ → ℕ → ℝ, (∀ q m, 0 ≤ KZ q m) ∧
      ∀ (C₀ : SmoothCcTensor g₀ 2 2) (T₀ : SmoothCcTensor g₀ 0 2),
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
        (∀ i : ℕ,
          ‖iteratedCovGrad (I := I) g₀ 2 2 i C₀‖ ^ 2 ≤
            Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2) +
              εa ^ 2 * ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T₀‖ ^ 2) →
        ∀ (q m : ℕ),
          ‖oneMinusConnLapSmoothIter (I := I) g₀ 0 2 m
              (-(operatorFieldApply (I := I) (M := M) g₀ 2 2
                    (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)
                    (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀))
                - operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2
                    (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
                    (operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 2)
                      (slotExtend (I := I) (M := M) g₀ 2 (2 + 1)
                        (covGrad (I := I) (M := M) g₀ 2 2
                          (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)))
                      (covGrad (I := I) (M := M) g₀ 0 2 T₀))
                - operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2
                    (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
                    (operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 2)
                      (covGrad (I := I) (M := M) g₀ (2 + 1) (2 + 1)
                        (slotExtend (I := I) (M := M) g₀ 2 2
                          (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)))
                      (covGrad (I := I) (M := M) g₀ 0 2 T₀)))‖ ≤
            KZ q m * ‖smoothCcToTensorHs (I := I) (M := M) g₀
              ((2 * m + 2 * q + 3 : ℕ) : ℝ) T₀‖ ∧
          ‖covGrad (I := I) (M := M) g₀ 0 2 (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 m
              (-(operatorFieldApply (I := I) (M := M) g₀ 2 2
                    (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)
                    (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀))
                - operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2
                    (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
                    (operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 2)
                      (slotExtend (I := I) (M := M) g₀ 2 (2 + 1)
                        (covGrad (I := I) (M := M) g₀ 2 2
                          (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)))
                      (covGrad (I := I) (M := M) g₀ 0 2 T₀))
                - operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2
                    (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
                    (operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 2)
                      (covGrad (I := I) (M := M) g₀ (2 + 1) (2 + 1)
                        (slotExtend (I := I) (M := M) g₀ 2 2
                          (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)))
                      (covGrad (I := I) (M := M) g₀ 0 2 T₀))))‖ ≤
            KZ q m * ‖smoothCcToTensorHs (I := I) (M := M) g₀
              ((2 * m + 2 * q + 4 : ℕ) : ℝ) T₀‖ := by
  classical
  obtain ⟨CB1, hCB1_nn, hCB1⟩ := bal_block1 (I := I) (M := M) g₀ a ha_super hR₀
    Kc hKc_nn εa hεa_nn
  obtain ⟨CB23, hCB23_nn, hCB23⟩ := bal_block23 (I := I) (M := M) g₀ a ha_super hR₀
    Kc hKc_nn εa hεa_nn
  obtain ⟨c02, hc02_nn, hc02⟩ := bal_Ccore (I := I) (M := M) g₀ 0 2
  set CBtot : ℕ → ℕ → ℝ := fun q j => CB1 q j + 2 * CB23 q j with hCBtot_def
  have hCBtot_nn : ∀ q j, 0 ≤ CBtot q j := fun q j => by
    have := hCB1_nn q j
    have := hCB23_nn q j
    rw [hCBtot_def]
    dsimp only
    linarith
  refine ⟨fun q m => (CBtot q (2 * m) + c02 m * ∑ b ∈ Finset.range (2 * m), CBtot q b) +
      (CBtot q (2 * m + 1) + c02 m * ∑ b ∈ Finset.range (2 * m + 1), CBtot q b),
    fun q m => ?_, ?_⟩
  · have h1 := hCBtot_nn q (2 * m)
    have h2 := hCBtot_nn q (2 * m + 1)
    have h3 : (0:ℝ) ≤ ∑ b ∈ Finset.range (2 * m), CBtot q b :=
      Finset.sum_nonneg (fun b _ => hCBtot_nn q b)
    have h4 : (0:ℝ) ≤ ∑ b ∈ Finset.range (2 * m + 1), CBtot q b :=
      Finset.sum_nonneg (fun b _ => hCBtot_nn q b)
    have := hc02_nn m
    have := mul_nonneg (hc02_nn m) h3
    have := mul_nonneg (hc02_nn m) h4
    linarith
  intro C₀ T₀ hball henv q m
  set fT : ℕ → ℝ := fun k => ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((k : ℕ) : ℝ) T₀‖
    with hfT_def
  have hfT_nn : ∀ k, 0 ≤ fT k := fun k => norm_nonneg _
  have hfT_mono : ∀ {k k' : ℕ}, k ≤ k' → fT k ≤ fT k' := fun {k k'} h =>
    smoothCcToTensorHs_norm_mono_of_le (I := I) (M := M) g₀ T₀ h
  set Eq : SmoothCcTensor g₀ 0 2 :=
    -(operatorFieldApply (I := I) (M := M) g₀ 2 2
          (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)
          (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀))
      - operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2
          (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
          (operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 2)
            (slotExtend (I := I) (M := M) g₀ 2 (2 + 1)
              (covGrad (I := I) (M := M) g₀ 2 2
                (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)))
            (covGrad (I := I) (M := M) g₀ 0 2 T₀))
      - operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2
          (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
          (operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 2)
            (covGrad (I := I) (M := M) g₀ (2 + 1) (2 + 1)
              (slotExtend (I := I) (M := M) g₀ 2 2
                (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)))
            (covGrad (I := I) (M := M) g₀ 0 2 T₀)) with hEq_def
  have hjets : ∀ j : ℕ, ‖iteratedCovGrad (I := I) g₀ 0 2 j Eq‖ ≤
      CBtot q j * fT (j + 2 * q + 3) := by
    intro j
    have hsplit : iteratedCovGrad (I := I) g₀ 0 2 j Eq =
        -(iteratedCovGrad (I := I) g₀ 0 2 j (operatorFieldApply (I := I) (M := M) g₀ 2 2
            (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)
            (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)))
          - iteratedCovGrad (I := I) g₀ 0 2 j (operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2
              (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
              (operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 2)
                (slotExtend (I := I) (M := M) g₀ 2 (2 + 1)
                  (covGrad (I := I) (M := M) g₀ 2 2
                    (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)))
                (covGrad (I := I) (M := M) g₀ 0 2 T₀)))
          - iteratedCovGrad (I := I) g₀ 0 2 j (operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2
              (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
              (operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 2)
                (covGrad (I := I) (M := M) g₀ (2 + 1) (2 + 1)
                  (slotExtend (I := I) (M := M) g₀ 2 2
                    (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)))
                (covGrad (I := I) (M := M) g₀ 0 2 T₀))) := by
      rw [hEq_def, iteratedCovGrad_sub, iteratedCovGrad_sub, iteratedCovGrad_neg]
    rw [hsplit]
    have h1 := hCB1 C₀ T₀ hball henv q j
    have h23 := hCB23 C₀ T₀ hball henv q j
    have hn1 := norm_sub_le
      (-(iteratedCovGrad (I := I) g₀ 0 2 j (operatorFieldApply (I := I) (M := M) g₀ 2 2
          (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)
          (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)))
        - iteratedCovGrad (I := I) g₀ 0 2 j (operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2
            (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
            (operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 2)
              (slotExtend (I := I) (M := M) g₀ 2 (2 + 1)
                (covGrad (I := I) (M := M) g₀ 2 2
                  (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)))
              (covGrad (I := I) (M := M) g₀ 0 2 T₀))))
      (iteratedCovGrad (I := I) g₀ 0 2 j (operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2
          (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
          (operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 2)
            (covGrad (I := I) (M := M) g₀ (2 + 1) (2 + 1)
              (slotExtend (I := I) (M := M) g₀ 2 2
                (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)))
            (covGrad (I := I) (M := M) g₀ 0 2 T₀))))
    have hn2 := norm_sub_le
      (-(iteratedCovGrad (I := I) g₀ 0 2 j (operatorFieldApply (I := I) (M := M) g₀ 2 2
          (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)
          (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀))))
      (iteratedCovGrad (I := I) g₀ 0 2 j (operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2
          (DeTurck.cometricDoubleTraceField (I := I) g₀ 2)
          (operatorFieldApply (I := I) (M := M) g₀ (2 + 1) (2 + 2)
            (slotExtend (I := I) (M := M) g₀ 2 (2 + 1)
              (covGrad (I := I) (M := M) g₀ 2 2
                (oneMinusConnLapSmoothIter (I := I) g₀ 2 2 q C₀)))
            (covGrad (I := I) (M := M) g₀ 0 2 T₀))))
    rw [norm_neg] at hn2
    have hfold : CBtot q j * fT (j + 2 * q + 3) =
        CB1 q j * fT (j + 2 * q + 3) + CB23 q j * fT (j + 2 * q + 3) +
          CB23 q j * fT (j + 2 * q + 3) := by
      rw [hCBtot_def]
      dsimp only
      ring
    rw [hfold]
    have hfeq : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((j + 2 * q + 3 : ℕ) : ℝ) T₀‖ =
        fT (j + 2 * q + 3) := rfl
    rw [hfeq] at h1 h23
    linarith [h1, h23.1, h23.2, hn1, hn2]
  have hcore := hc02 m Eq
  constructor
  · refine le_trans hcore.1 ?_
    have htop : ‖iteratedCovGrad (I := I) g₀ 0 2 (2 * m) Eq‖ ≤
        CBtot q (2 * m) * fT (2 * m + 2 * q + 3) := hjets (2 * m)
    have hlow : ∑ b ∈ Finset.range (2 * m), ‖iteratedCovGrad (I := I) g₀ 0 2 b Eq‖ ≤
        (∑ b ∈ Finset.range (2 * m), CBtot q b) * fT (2 * m + 2 * q + 3) := by
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum (fun b hb => ?_)
      have hbm := Finset.mem_range.mp hb
      refine le_trans (hjets b) ?_
      exact mul_le_mul_of_nonneg_left (hfT_mono (by omega)) (hCBtot_nn q b)
    have h2 := mul_le_mul_of_nonneg_left hlow (hc02_nn m)
    have hnn : 0 ≤ (CBtot q (2 * m + 1) + c02 m * ∑ b ∈ Finset.range (2 * m + 1),
        CBtot q b) * fT (2 * m + 2 * q + 3) := by
      have h3 : (0:ℝ) ≤ ∑ b ∈ Finset.range (2 * m + 1), CBtot q b :=
        Finset.sum_nonneg (fun b _ => hCBtot_nn q b)
      exact mul_nonneg (by
        have := hCBtot_nn q (2 * m + 1)
        have := mul_nonneg (hc02_nn m) h3
        linarith) (hfT_nn _)
    have hgoalf : ‖smoothCcToTensorHs (I := I) (M := M) g₀
        ((2 * m + 2 * q + 3 : ℕ) : ℝ) T₀‖ = fT (2 * m + 2 * q + 3) := rfl
    rw [hgoalf]
    nlinarith [htop, h2]
  · refine le_trans hcore.2 ?_
    have htop : ‖iteratedCovGrad (I := I) g₀ 0 2 (2 * m + 1) Eq‖ ≤
        CBtot q (2 * m + 1) * fT (2 * m + 2 * q + 4) := by
      refine le_trans (hjets (2 * m + 1)) ?_
      exact mul_le_mul_of_nonneg_left (hfT_mono (by omega)) (hCBtot_nn q (2 * m + 1))
    have hlow : ∑ b ∈ Finset.range (2 * m + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 b Eq‖ ≤
        (∑ b ∈ Finset.range (2 * m + 1), CBtot q b) * fT (2 * m + 2 * q + 4) := by
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum (fun b hb => ?_)
      have hbm := Finset.mem_range.mp hb
      refine le_trans (hjets b) ?_
      exact mul_le_mul_of_nonneg_left (hfT_mono (by omega)) (hCBtot_nn q b)
    have h2 := mul_le_mul_of_nonneg_left hlow (hc02_nn m)
    have hnn : 0 ≤ (CBtot q (2 * m) + c02 m * ∑ b ∈ Finset.range (2 * m),
        CBtot q b) * fT (2 * m + 2 * q + 4) := by
      have h3 : (0:ℝ) ≤ ∑ b ∈ Finset.range (2 * m), CBtot q b :=
        Finset.sum_nonneg (fun b _ => hCBtot_nn q b)
      exact mul_nonneg (by
        have := hCBtot_nn q (2 * m)
        have := mul_nonneg (hc02_nn m) h3
        linarith) (hfT_nn _)
    have hgoalf : ‖smoothCcToTensorHs (I := I) (M := M) g₀
        ((2 * m + 2 * q + 4 : ℕ) : ℝ) T₀‖ = fT (2 * m + 2 * q + 4) := rfl
    rw [hgoalf]
    nlinarith [htop, h2]
end BalLadder

end Spectral
end Analysis
end DifferentialGeometry

end
