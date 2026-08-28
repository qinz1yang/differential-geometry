import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.H2H4Principal
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.ParametricAppHs


noncomputable section

open Bundle Manifold
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

theorem appHs_h2_norm
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (b c : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Φ : SmoothCcTensor g b c) (A : ℝ), 0 ≤ A →
        (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g b c j Φ‖ ^ 2) ≤ A ^ 2 →
        ‖appHs (I := I) (M := M) g b c 2 Φ‖ ≤ C * A := by
  classical
  obtain ⟨Csp, hCsp, hsp⟩ := hs_le_jet (I := I) (M := M) g c 2
  obtain ⟨Cin, hCin, hin⟩ := hsJet_le (I := I) (M := M) g b 2
  obtain ⟨Capp, hCapp, happ⟩ :=
    operatorFieldApplication_h2_h2_h2 (I := I) (M := M) hDim g b c
  let C : ℝ := Csp * 3 * Capp * Cin
  refine ⟨C, by
    dsimp only [C]
    positivity, ?_⟩
  intro Φ A hA hΦ
  have hdense : DenseRange
      (ccToHsLin (I := I) (M := M) g b (2 : ℝ)) :=
    ccToHsLin_dense (I := I) (M := M) g b (by positivity)
  unfold appHs
  apply LinearMap.opNorm_extendOfNorm_le hdense (mul_nonneg (by positivity) hA)
  intro W
  let N : ℝ := ‖ccTensorToHs (I := I) (M := M) g b (2 : ℝ) W‖
  let B : ℝ := Cin * N
  let Y : SmoothCcTensor g 0 c :=
    operatorFieldApply (I := I) (M := M) g b c Φ W
  let Q : ℝ := Capp * A * B
  have hN : 0 ≤ N := norm_nonneg _
  have hB : 0 ≤ B := mul_nonneg hCin hN
  have hQ : 0 ≤ Q := mul_nonneg (mul_nonneg hCapp hA) hB
  have hJ :
      ∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 0 b j W‖ ≤ B := by
    have h := hin W
    rw [show (((2 : ℕ) : ℝ)) = 2 by norm_num] at h
    simpa only [B, N, Nat.reduceAdd] using h
  have hWsq :
      (∑ j ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 0 b j W‖ ^ 2) ≤ B ^ 2 := by
    calc
      _ ≤ (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 0 b j W‖) ^ 2 :=
        Finset.sum_sq_le_sq_sum_of_nonneg
          (fun j _ => norm_nonneg
            (iteratedCovGrad (I := I) g 0 b j W))
      _ ≤ B ^ 2 := pow_le_pow_left₀
        (Finset.sum_nonneg (fun j _ => norm_nonneg
          (iteratedCovGrad (I := I) g 0 b j W)))
        hJ 2
  have hYsq :
      (∑ j ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 0 c j Y‖ ^ 2) ≤ Q ^ 2 := by
    simpa only [Y, Q] using happ Φ W A B hA hB hΦ hWsq
  have hterm : ∀ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g 0 c j Y‖ ≤ Q := by
    intro j hj
    have hsingle :
        ‖iteratedCovGrad (I := I) g 0 c j Y‖ ^ 2 ≤
          ∑ i ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g 0 c i Y‖ ^ 2 :=
      Finset.single_le_sum
        (f := fun i => ‖iteratedCovGrad (I := I) g 0 c i Y‖ ^ 2)
        (fun i _ => sq_nonneg _) hj
    nlinarith [hsingle.trans hYsq,
      norm_nonneg (iteratedCovGrad (I := I) g 0 c j Y)]
  have hYsum :
      ∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 0 c j Y‖ ≤ 3 * Q := by
    calc
      _ ≤ ∑ _j ∈ Finset.range 3, Q :=
        Finset.sum_le_sum fun j hj => hterm j hj
      _ = 3 * Q := by norm_num
  have hspY :
      ‖ccTensorToHs (I := I) (M := M) g c (2 : ℝ) Y‖ ≤
        Csp * ∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 0 c j Y‖ := by
    have h := hsp Y
    rw [show (((2 : ℕ) : ℝ)) = 2 by norm_num] at h
    simpa only [Nat.reduceAdd] using h
  change ‖ccTensorToHs (I := I) (M := M) g c (2 : ℝ) Y‖ ≤
    (C * A) * N
  calc
    _ ≤ Csp * ∑ j ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 0 c j Y‖ := hspY
    _ ≤ Csp * (3 * Q) := mul_le_mul_of_nonneg_left hYsum hCsp
    _ = (C * A) * N := by
      dsimp only [C, Q, B]
      ring

end Connection
end Integral
end DifferentialGeometry

end
