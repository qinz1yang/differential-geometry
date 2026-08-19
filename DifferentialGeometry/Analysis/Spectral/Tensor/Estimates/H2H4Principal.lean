import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.H1H2OperatorFieldComposition
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.IteratedCovGradHsJetBound

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open scoped ContDiff Manifold Topology BigOperators
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [T2Space M] [SigmaCompactSpace M]

theorem operatorFieldApplication_h2_h2_h2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (r c : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Φ : SmoothCcTensor g r c) (W : SmoothCcTensor g 0 r) (A B : ℝ),
        0 ≤ A → 0 ≤ B →
        (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g r c j Φ‖ ^ 2) ≤ A ^ 2 →
        (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 0 r j W‖ ^ 2) ≤ B ^ 2 →
        (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 0 c j
            (operatorFieldApply (I := I) (M := M) g r c Φ W)‖ ^ 2) ≤
          (C * A * B) ^ 2 := by
  obtain ⟨C, hC, happ⟩ :=
    operator_field_composition_h2_h2_to_h2_bound (I := I) (M := M) hDim g 0 r c
  refine ⟨C, hC, ?_⟩
  intro Φ W A B hA hB hΦ hW
  simpa only [operatorFieldComposition_zero_eq_operatorFieldApply] using
    happ Φ W A B hA hB hΦ hW

theorem operatorFieldApplication_h2_h4_h2
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (s c : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Φ : SmoothCcTensor g (s + 2) c) (U : SmoothCcTensor g 0 s)
        (A : ℝ), 0 ≤ A →
        (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g (s + 2) c j Φ‖ ^ 2) ≤ A ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g c (2 : ℝ)
            (operatorFieldApply (I := I) (M := M) g (s + 2) c Φ
              (iteratedCovGrad (I := I) g 0 s 2 U))‖ ≤
          C * A * ‖ccTensorToHs (I := I) (M := M) g s (4 : ℝ) U‖ := by
  classical
  obtain ⟨Csp, hCsp, hsp⟩ := hs_le_jet (I := I) (M := M) g c 2
  obtain ⟨Cin, hCin, hin⟩ := hsJet_le (I := I) (M := M) g s 4
  obtain ⟨Capp, hCapp, happ⟩ :=
    operatorFieldApplication_h2_h2_h2 (I := I) (M := M) hDim g (s + 2) c
  let C : ℝ := Csp * 3 * Capp * Cin
  refine ⟨C, by
    dsimp only [C]
    positivity, ?_⟩
  intro Φ U A hA hΦ
  let N : ℝ := ‖ccTensorToHs (I := I) (M := M) g s (4 : ℝ) U‖
  let B : ℝ := Cin * N
  let W : SmoothCcTensor g 0 (s + 2) :=
    iteratedCovGrad (I := I) g 0 s 2 U
  let Y : SmoothCcTensor g 0 c :=
    operatorFieldApply (I := I) (M := M) g (s + 2) c Φ W
  let Q : ℝ := Capp * A * B
  have hN : 0 ≤ N := norm_nonneg _
  have hB : 0 ≤ B := mul_nonneg hCin hN
  have hQ : 0 ≤ Q := mul_nonneg (mul_nonneg hCapp hA) hB
  have hJ :
      ∑ j ∈ Finset.range 5,
          ‖iteratedCovGrad (I := I) g 0 s j U‖ ≤ B := by
    simpa only [B, N, Nat.reduceAdd] using hin U
  have hWsum :
      ∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 0 (s + 2) j W‖ ≤ B := by
    calc
      ∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 0 (s + 2) j W‖ =
          ∑ j ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g 0 s (2 + j) U‖ := by
              refine Finset.sum_congr rfl (fun j _ => ?_)
              simpa only [W] using
                iteratedCovGrad_comp_norm (I := I) (M := M) g s 2 j U
      _ ≤ ∑ j ∈ Finset.range 5,
          ‖iteratedCovGrad (I := I) g 0 s j U‖ := by
            simp only [Finset.sum_range_succ, Finset.sum_range_zero,
              zero_add, Nat.reduceAdd]
            nlinarith [
              norm_nonneg (iteratedCovGrad (I := I) g 0 s 0 U),
              norm_nonneg (iteratedCovGrad (I := I) g 0 s 1 U)]
      _ ≤ B := hJ
  have hWsq :
      (∑ j ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 0 (s + 2) j W‖ ^ 2) ≤ B ^ 2 := by
    calc
      _ ≤ (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 0 (s + 2) j W‖) ^ 2 :=
        Finset.sum_sq_le_sq_sum_of_nonneg
          (fun j _ => norm_nonneg
            (iteratedCovGrad (I := I) g 0 (s + 2) j W))
      _ ≤ B ^ 2 := pow_le_pow_left₀
        (Finset.sum_nonneg (fun j _ => norm_nonneg
          (iteratedCovGrad (I := I) g 0 (s + 2) j W)))
        hWsum 2
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
    simpa only [Nat.reduceAdd] using hsp Y
  change ‖ccTensorToHs (I := I) (M := M) g c (2 : ℝ) Y‖ ≤
    C * A * N
  calc
    _ ≤ Csp * ∑ j ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 0 c j Y‖ := hspY
    _ ≤ Csp * (3 * Q) := mul_le_mul_of_nonneg_left hYsum hCsp
    _ = C * A * N := by
      dsimp only [C, Q, B]
      ring

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
