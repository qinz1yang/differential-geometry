import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.IteratedCovGradHsJetBound

set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory Set Filter DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

def hsTwoJetC (d : ℕ) : ℝ := Real.sqrt (2 * (1 + (d : ℝ) ^ 2))

theorem hsTwoJetC_nonneg (d : ℕ) : 0 ≤ hsTwoJetC d := Real.sqrt_nonneg _

theorem rawLap_le_grad2
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    ‖rawTensorConnLapSmooth (I := I) g 0 s S‖ ≤
      (Module.finrank ℝ E : ℝ) *
        ‖covGrad (I := I) (M := M) g 0 (s + 1)
          (covGrad (I := I) (M := M) g 0 s S)‖ := by
  classical
  set HH : SmoothCcTensor g 0 (s + 1 + 1) :=
    covGrad (I := I) (M := M) g 0 (s + 1)
      (covGrad (I := I) (M := M) g 0 s S) with hHH
  have hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 s x
          ((rawTensorConnLapSmooth (I := I) g 0 s S).toSection x) ≤
        (Module.finrank ℝ E : ℝ) ^ 2 * ∑ _i ∈ Finset.range 1,
          riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1 + 1) x
            (HH.toSection x) := by
    intro x
    rw [Finset.sum_const, Finset.card_range, one_nsmul, hHH]
    exact rawConnLap_fiberNormSq_le_secondCovGrad
      (I := I) (M := M) g s S x
  have hpack := tensorL2Norm_le_of_pointwise_fiberNormSq_bound_sum
    (I := I) (M := M) g 1 (fun _ => s + 1 + 1) (fun _ => HH)
    (rawTensorConnLapSmooth (I := I) g 0 s S)
    (Module.finrank ℝ E : ℝ) (Nat.cast_nonneg _) hpt
  rw [Finset.sum_const, Finset.card_range, one_nsmul, hHH] at hpack
  exact hpack

private theorem mode_summable_two
    (g : SmoothRiemannianMetric I M) (s j : ℕ)
    (S : SmoothCcTensor g 0 s) (hj : j = 0 ∨ j = 2) :
    Summable (fun m :
        DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
          (I := I) (M := M) g 0 s =>
      (DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
        (I := I) (M := M) m) ^ j *
        (tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 s)
          (SmoothCcTensor.toL2 S) m) ^ 2) := by
  have hfull := (ccTensorToHs (I := I) (M := M) g s (2 : ℝ) S).weighted_summable
  refine Summable.of_nonneg_of_le ?_ ?_ hfull
  · intro m
    have hL : 0 ≤
        DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
          (I := I) (M := M) m :=
      tensor_lambda_nonneg (I := I) (M := M) m
    positivity
  · intro m
    let L : ℝ :=
      DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
        (I := I) (M := M) m
    let c : ℝ := tensorL2Coeff (I := I) (M := M)
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 s)
      (SmoothCcTensor.toL2 S) m
    have hL : 0 ≤ L := tensor_lambda_nonneg (I := I) (M := M) m
    have hpow : L ^ j ≤ (1 + L) ^ 2 := by
      rcases hj with rfl | rfl
      · simpa only [pow_zero] using
          (one_le_pow₀ (show (1 : ℝ) ≤ 1 + L by linarith) :
            (1 : ℝ) ≤ (1 + L) ^ 2)
      · exact pow_le_pow_left₀ hL (by linarith) 2
    have hweight : tensorSobolevWeight (I := I) (M := M) m (2 : ℝ) =
        (1 + L) ^ 2 := by
      unfold tensorSobolevWeight
      dsimp only [L]
      exact Real.rpow_natCast _ 2
    rw [ccTensorToHs_coeff, hweight]
    exact mul_le_mul_of_nonneg_right hpow (sq_nonneg c)

theorem hs_two_le_jet
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    ‖ccTensorToHs (I := I) (M := M) g s (2 : ℝ) S‖ ≤
      hsTwoJetC (Module.finrank ℝ E) *
        ∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 0 s j S‖ := by
  classical
  let d : ℝ := Module.finrank ℝ E
  let Sall : ℝ := ∑ j ∈ Finset.range 3,
    ‖iteratedCovGrad (I := I) g 0 s j S‖
  let term : ℕ →
      DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
        (I := I) (M := M) g 0 s → ℝ := fun j m =>
    (DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
      (I := I) (M := M) m) ^ j *
      (tensorL2Coeff (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 s)
        (SmoothCcTensor.toL2 S) m) ^ 2
  let mass : ℕ → ℝ := fun j => ∑' m, term j m
  have hd : 0 ≤ d := Nat.cast_nonneg _
  have hSall : 0 ≤ Sall := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hterm0 : Summable (term 0) := by
    simpa only [term] using
      mode_summable_two (I := I) (M := M) g s 0 S (Or.inl rfl)
  have hterm2 : Summable (term 2) := by
    simpa only [term] using
      mode_summable_two (I := I) (M := M) g s 2 S (Or.inr rfl)
  have hmass0 : mass 0 = ‖S‖ ^ 2 := by
    have h := rawIter_tsum (I := I) (M := M) g s 0 S
    rw [rawTensorConnLapIter_zero, SmoothCcTensor.norm_toL2] at h
    simpa only [mass, term, Nat.zero_eq, zero_mul] using h.symm
  have hmass2 : mass 2 = ‖rawTensorConnLapSmooth (I := I) g 0 s S‖ ^ 2 := by
    have h := rawIter_tsum (I := I) (M := M) g s 1 S
    rw [rawTensorConnLapIter_one, SmoothCcTensor.norm_toL2] at h
    simpa only [mass, term, Nat.reduceMul] using h.symm
  have hzero : ‖S‖ ≤ Sall := by
    rw [show ‖S‖ = ‖iteratedCovGrad (I := I) g 0 s 0 S‖ by
      rw [iteratedCovGrad_zero]]
    exact Finset.single_le_sum
      (fun j _ => norm_nonneg (iteratedCovGrad (I := I) g 0 s j S))
      (by rw [Finset.mem_range]; omega)
  have htwo :
      ‖covGrad (I := I) (M := M) g 0 (s + 1)
          (covGrad (I := I) (M := M) g 0 s S)‖ ≤ Sall := by
    change ‖iteratedCovGrad (I := I) g 0 s 2 S‖ ≤ Sall
    exact Finset.single_le_sum
      (fun j _ => norm_nonneg (iteratedCovGrad (I := I) g 0 s j S))
      (by rw [Finset.mem_range]; omega)
  have hlap : ‖rawTensorConnLapSmooth (I := I) g 0 s S‖ ≤ d * Sall := by
    exact (rawLap_le_grad2 (I := I) (M := M) g s S).trans
      (mul_le_mul_of_nonneg_left htwo hd)
  have hmass : mass 0 + mass 2 ≤ (1 + d ^ 2) * Sall ^ 2 := by
    rw [hmass0, hmass2]
    have hzsq := pow_le_pow_left₀ (norm_nonneg S) hzero 2
    have hlsq := pow_le_pow_left₀
      (norm_nonneg (rawTensorConnLapSmooth (I := I) g 0 s S)) hlap 2
    calc
      ‖S‖ ^ 2 + ‖rawTensorConnLapSmooth (I := I) g 0 s S‖ ^ 2 ≤
          Sall ^ 2 + (d * Sall) ^ 2 := add_le_add hzsq hlsq
      _ = (1 + d ^ 2) * Sall ^ 2 := by ring
  have hrhs : Summable (fun m => 2 * (term 0 m + term 2 m)) :=
    (hterm0.add hterm2).mul_left 2
  have hsq :
      ‖ccTensorToHs (I := I) (M := M) g s (2 : ℝ) S‖ ^ 2 ≤
        2 * (1 + d ^ 2) * Sall ^ 2 := by
    rw [ccToHs_norm_sq]
    calc
      ∑' m : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
          (I := I) (M := M) g 0 s,
          tensorSobolevWeight (I := I) (M := M) m (2 : ℝ) *
            (tensorL2Coeff (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 s)
              (SmoothCcTensor.toL2 S) m) ^ 2 ≤
          ∑' m, 2 * (term 0 m + term 2 m) := by
        refine Summable.tsum_le_tsum (fun m => ?_)
          (ccTensorToHs (I := I) (M := M) g s (2 : ℝ) S).weighted_summable hrhs
        let L : ℝ :=
          DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx.lambda
            (I := I) (M := M) m
        let c : ℝ := tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 s)
          (SmoothCcTensor.toL2 S) m
        have hL : 0 ≤ L := tensor_lambda_nonneg (I := I) (M := M) m
        have hp : (1 + L) ^ 2 ≤ 2 * (1 + L ^ 2) := by
          nlinarith [sq_nonneg (1 - L)]
        have hw : tensorSobolevWeight (I := I) (M := M) m (2 : ℝ) =
            (1 + L) ^ 2 := by
          unfold tensorSobolevWeight
          dsimp only [L]
          exact Real.rpow_natCast _ 2
        rw [hw]
        calc
          (1 + L) ^ 2 * c ^ 2 ≤ 2 * (1 + L ^ 2) * c ^ 2 :=
            mul_le_mul_of_nonneg_right hp (sq_nonneg c)
          _ = 2 * (term 0 m + term 2 m) := by
            dsimp only [term, L, c]
            ring
      _ = 2 * (mass 0 + mass 2) := by
        rw [tsum_mul_left, Summable.tsum_add hterm0 hterm2]
      _ ≤ 2 * ((1 + d ^ 2) * Sall ^ 2) :=
        mul_le_mul_of_nonneg_left hmass (by norm_num)
      _ = 2 * (1 + d ^ 2) * Sall ^ 2 := by ring
  have hcoef : 0 ≤ 2 * (1 + d ^ 2) := by positivity
  have hsqrt : hsTwoJetC (Module.finrank ℝ E) ^ 2 = 2 * (1 + d ^ 2) := by
    unfold hsTwoJetC d
    rw [Real.sq_sqrt hcoef]
  have hrhs_nonneg : 0 ≤ hsTwoJetC (Module.finrank ℝ E) * Sall :=
    mul_nonneg (hsTwoJetC_nonneg _) hSall
  apply le_of_sq_le_sq _ hrhs_nonneg
  calc
    ‖ccTensorToHs (I := I) (M := M) g s (2 : ℝ) S‖ ^ 2 ≤
        2 * (1 + d ^ 2) * Sall ^ 2 := hsq
    _ = (hsTwoJetC (Module.finrank ℝ E) * Sall) ^ 2 := by
      rw [mul_pow, hsqrt]
    _ = (hsTwoJetC (Module.finrank ℝ E) *
        ∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 0 s j S‖) ^ 2 := by rfl

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
