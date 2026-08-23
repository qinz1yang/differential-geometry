import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.HsTwoJet
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.UnifBochnerGap
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.SpectralNormLIterateLadder

set_option autoImplicit false

noncomputable section

open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open Bundle Manifold MeasureTheory Set Filter DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem norm_iterCovGrad_comp_three
    (g : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g 0 2) :
    ‖covGrad (I := I) (M := M) g 0 4
        (covGrad (I := I) (M := M) g 0 3
          (covGrad (I := I) (M := M) g 0 2 S))‖ =
      ‖iteratedCovGrad (I := I) g 0 2 3 S‖ := by
  rfl

private theorem norm_ccHs_eq_smoothHs_three
    (g : SmoothRiemannianMetric I M) (σ : ℝ)
    (S : SmoothCcTensor g 0 2) :
    ‖ccTensorToHs (I := I) (M := M) g 2 σ S‖ =
      ‖smoothCcToTensorHs (I := I) (M := M) g σ S‖ := by
  have h : ccTensorToHs (I := I) (M := M) g 2 σ S =
      smoothCcToTensorHs (I := I) (M := M) g σ S :=
    tensorHs.ext (funext fun _ => rfl)
  rw [h]

theorem hs_three_le_jet
    (g : SmoothRiemannianMetric I M) {K : ℝ}
    (hact : IsCurvAction0 (I := I) (M := M) g 2 K)
    (S : SmoothCcTensor g 0 2) :
    ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) S‖ ≤
      (2 + 2 * (Module.finrank ℝ E : ℝ) + K) *
        ∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g 0 2 j S‖ := by
  classical
  let L : SmoothCcTensor g 0 2 :=
    oneMinusConnLapSmooth (I := I) g 0 2 S
  let P : SmoothCcTensor g 0 3 :=
    covGrad (I := I) (M := M) g 0 2 S
  let J : ℝ := ∑ j ∈ Finset.range 4,
    ‖iteratedCovGrad (I := I) g 0 2 j S‖
  let d : ℝ := Module.finrank ℝ E
  let N : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) S‖
  have hJ : 0 ≤ J := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hd : 0 ≤ d := Nat.cast_nonneg _
  have hN : 0 ≤ N := norm_nonneg _
  have hpick : ∀ j : ℕ, j < 4 →
      ‖iteratedCovGrad (I := I) g 0 2 j S‖ ≤ J := by
    intro j hj
    dsimp only [J]
    exact Finset.single_le_sum
      (fun i _ => norm_nonneg (iteratedCovGrad (I := I) g 0 2 i S))
      (Finset.mem_range.mpr hj)
  have hlap : ‖rawTensorConnLapSmooth (I := I) g 0 2 S‖ ≤ d * J := by
    refine (rawLap_le_grad2 (I := I) (M := M) g 2 S).trans ?_
    exact mul_le_mul_of_nonneg_left (by simpa using hpick 2 (by norm_num)) hd
  have hL : ‖L‖ ≤ (1 + d) * J := by
    refine (norm_sub_le S (rawTensorConnLapSmooth (I := I) g 0 2 S)).trans ?_
    have hS : ‖S‖ ≤ J := by
      simpa only [iteratedCovGrad_zero] using hpick 0 (by norm_num)
    linarith
  have hcomm : rawTensorConnLapSmooth (I := I) g 0 3 P =
      covGrad (I := I) (M := M) g 0 2
          (rawTensorConnLapSmooth (I := I) g 0 2 S) +
        pointwiseTensorCurv (I := I) (M := M) g 2 S := by
    dsimp only [P]
    rw [pointwiseTensorCurv_commutator_eq (I := I) (M := M) g 2 S]
  have hlapP : ‖rawTensorConnLapSmooth (I := I) g 0 3 P‖ ≤ d * J := by
    refine (rawLap_le_grad2 (I := I) (M := M) g 3 P).trans ?_
    have htop :
        ‖covGrad (I := I) (M := M) g 0 4
            (covGrad (I := I) (M := M) g 0 3 P)‖ ≤ J := by
      dsimp only [P]
      rw [norm_iterCovGrad_comp_three (I := I) (M := M) g S]
      exact hpick 3 (by norm_num)
    exact mul_le_mul_of_nonneg_left htop hd
  have hcurv : ‖pointwiseTensorCurv (I := I) (M := M) g 2 S‖ ≤ K * J := by
    refine hact.bound S |>.trans ?_
    apply mul_le_mul_of_nonneg_left _ hact.nonneg
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_mono (by norm_num)) (fun j _ _ => norm_nonneg _)
  have hgradLap :
      ‖covGrad (I := I) (M := M) g 0 2
          (rawTensorConnLapSmooth (I := I) g 0 2 S)‖ ≤
        (d + K) * J := by
    have hsub := norm_sub_le
      (rawTensorConnLapSmooth (I := I) g 0 3 P)
      (pointwiseTensorCurv (I := I) (M := M) g 2 S)
    rw [show rawTensorConnLapSmooth (I := I) g 0 3 P -
        pointwiseTensorCurv (I := I) (M := M) g 2 S =
      covGrad (I := I) (M := M) g 0 2
        (rawTensorConnLapSmooth (I := I) g 0 2 S) by rw [hcomm]; abel] at hsub
    exact hsub.trans (by linarith)
  have hgradL :
      ‖covGrad (I := I) (M := M) g 0 2 L‖ ≤
        (1 + d + K) * J := by
    rw [show covGrad (I := I) (M := M) g 0 2 L =
        covGrad (I := I) (M := M) g 0 2 S -
          covGrad (I := I) (M := M) g 0 2
            (rawTensorConnLapSmooth (I := I) g 0 2 S) by
      change covGrad (I := I) (M := M) g 0 2
          (S - rawTensorConnLapSmooth (I := I) g 0 2 S) = _
      exact covGrad_sub (I := I) (M := M) g 0 2 S
        (rawTensorConnLapSmooth (I := I) g 0 2 S)]
    refine (norm_sub_le _ _).trans ?_
    have hgrad : ‖covGrad (I := I) (M := M) g 0 2 S‖ ≤ J := by
      simpa only [iteratedCovGrad_succ, iteratedCovGrad_zero] using hpick 1 (by norm_num)
    linarith
  have hodd := smoothCcToTensorHs_odd_norm_sq_eq_toL2_iter_add_covGrad
    (I := I) (M := M) g 1 S
  have hsq : N ^ 2 = ‖L‖ ^ 2 +
      ‖covGrad (I := I) (M := M) g 0 2 L‖ ^ 2 := by
    simpa only [N, L, Nat.reduceMul, Nat.reduceAdd, Nat.cast_ofNat,
      norm_ccHs_eq_smoothHs_three, oneMinusConnLapSmoothIter_succ,
      oneMinusConnLapSmoothIter_zero, SmoothCcTensor.norm_toL2] using hodd
  have hroot : N ≤ ‖L‖ +
      ‖covGrad (I := I) (M := M) g 0 2 L‖ := by
    refine le_of_sq_le_sq ?_ (add_nonneg (norm_nonneg _) (norm_nonneg _))
    rw [hsq]
    calc
      ‖L‖ ^ 2 + ‖covGrad (I := I) (M := M) g 0 2 L‖ ^ 2 ≤
          ‖L‖ ^ 2 + ‖covGrad (I := I) (M := M) g 0 2 L‖ ^ 2 +
            2 * (‖L‖ * ‖covGrad (I := I) (M := M) g 0 2 L‖) :=
        le_add_of_nonneg_right (mul_nonneg (by norm_num)
          (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
      _ = (‖L‖ + ‖covGrad (I := I) (M := M) g 0 2 L‖) ^ 2 := by ring
  change N ≤ (2 + 2 * d + K) * J
  calc
    N ≤ ‖L‖ + ‖covGrad (I := I) (M := M) g 0 2 L‖ := hroot
    _ ≤ (1 + d) * J + (1 + d + K) * J := add_le_add hL hgradL
    _ = (2 + 2 * d + K) * J := by ring

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
