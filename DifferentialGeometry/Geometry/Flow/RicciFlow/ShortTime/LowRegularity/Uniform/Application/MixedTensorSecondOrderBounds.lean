import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.OperatorField.H1H2Composition
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Jet.SecondOrder
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Uniform.Grid.Regularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.Grid.ConvexJets

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
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral

private lemma triGrid_le
    (a b : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 ≤ b n)
    {i : ℕ} (hi : i < 3) :
    (∑ n ∈ Finset.range (i + 1), a n *
        ∑ l ∈ Finset.range (i + 1 - n), b l) ≤
      ∑ n ∈ Finset.range 3, a n *
        ∑ l ∈ Finset.range (3 - n), b l := by
  have hi3 : i + 1 ≤ 3 := by omega
  calc
    (∑ n ∈ Finset.range (i + 1), a n *
        ∑ l ∈ Finset.range (i + 1 - n), b l) ≤
        ∑ n ∈ Finset.range (i + 1), a n *
          ∑ l ∈ Finset.range (3 - n), b l := by
      apply Finset.sum_le_sum
      intro n hn
      apply mul_le_mul_of_nonneg_left _ (ha n)
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_mono (by omega)) (fun l _ _ => hb l)
    _ ≤ ∑ n ∈ Finset.range 3, a n *
        ∑ l ∈ Finset.range (3 - n), b l := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_mono hi3) (fun n _ _ =>
          mul_nonneg (ha n) (Finset.sum_nonneg (fun l _ => hb l)))

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem operatorFieldComposition_h2_h2_to_h2_uniform_bound
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) (p r c : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ g : SmoothRiemannianMetric I M,
        MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
        MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g gBase Λ →
        MetricCovDerivOrderBoundOn (I := I) Set.univ 2 g gBase Λ →
        ∀ (Φ : SmoothCcTensor g r c) (W : SmoothCcTensor g p r) (A B : ℝ),
          0 ≤ A → 0 ≤ B →
          (∑ j ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g r c j Φ‖ ^ 2) ≤ A ^ 2 →
          (∑ j ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g p r j W‖ ^ 2) ≤ B ^ 2 →
          (∑ j ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g p c j
              (ccOperatorFieldComp (I := I) (M := M) g p r c Φ W)‖ ^ 2) ≤
            (C * A * B) ^ 2 := by
  classical
  obtain ⟨Cg, hCg, hgrid⟩ :=
    DifferentialGeometry.PDE.RicciFlow.grid_rs_uniform
      (I := I) (M := M) hDim gBase hΛ r p c r
  let D : ℝ := ∑ i ∈ Finset.range 3, operatorFieldApplicationGdiag (E := E) i
  have hD : 0 ≤ D := by
    dsimp only [D]
    exact Finset.sum_nonneg (fun i _ => operatorFieldApplicationGdiag_nonneg (E := E) i)
  let K : ℝ := D * Cg
  have hK : 0 ≤ K := by
    dsimp only [K]
    exact mul_nonneg hD hCg
  let C : ℝ := Real.sqrt K
  refine ⟨C, Real.sqrt_nonneg _, ?_⟩
  intro g hEq hjet1 hjet2 Φ W A B hA hB hΦ hW
  let grid : M → ℝ := fun x =>
    ∑ n ∈ Finset.range 3,
      riemannianFiberNormSq (I := I) (M := M) g r (c + n) x
          ((iteratedCovGrad (I := I) g r c n Φ).toSection x) *
        ∑ l ∈ Finset.range (3 - n),
          riemannianFiberNormSq (I := I) (M := M) g p (r + l) x
            ((iteratedCovGrad (I := I) g p r l W).toSection x)
  obtain ⟨hgridInt, hgridBd⟩ :=
    hgrid g hEq hjet1 hjet2 Φ W A B hA hB hΦ hW
  have hgridInt' : Integrable grid
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    simpa only [grid] using hgridInt
  have hterm : ∀ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g p c i
          (ccOperatorFieldComp (I := I) (M := M) g p r c Φ W)‖ ^ 2 ≤
        operatorFieldApplicationGdiag (E := E) i *
          ∫ x, grid x ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    intro i hi
    have hpoint : ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g p (c + i) x
            ((iteratedCovGrad (I := I) g p c i
              (ccOperatorFieldComp (I := I) (M := M) g p r c Φ W)).toSection x) ≤
          operatorFieldApplicationGdiag (E := E) i * grid x := by
      intro x
      refine (riemannianFiberNormSq_iteratedCovGrad_operatorFieldComposition_diagonalProductGrid_rankLeft_le
        (I := I) (M := M) g i p r c Φ W x).trans ?_
      apply mul_le_mul_of_nonneg_left _ (operatorFieldApplicationGdiag_nonneg (E := E) i)
      simpa only [grid] using
        (triGrid_le
          (fun n => riemannianFiberNormSq (I := I) (M := M) g r (c + n) x
            ((iteratedCovGrad (I := I) g r c n Φ).toSection x))
          (fun l => riemannianFiberNormSq (I := I) (M := M) g p (r + l) x
            ((iteratedCovGrad (I := I) g p r l W).toSection x))
          (fun n => riemannianFiberNormSq_nonneg
            (I := I) (M := M) g r (c + n) x _)
          (fun l => riemannianFiberNormSq_nonneg
            (I := I) (M := M) g p (r + l) x _)
          (Finset.mem_range.mp hi))
    have hkey := normSq_le_integral_of_pointwise_fiberNormSq_le_rs
      (I := I) (M := M) g p (c + i)
      (iteratedCovGrad (I := I) g p c i
        (ccOperatorFieldComp (I := I) (M := M) g p r c Φ W))
      (fun x => operatorFieldApplicationGdiag (E := E) i * grid x)
      (hgridInt'.const_mul (operatorFieldApplicationGdiag (E := E) i)) hpoint
    calc
      _ ≤ ∫ x, operatorFieldApplicationGdiag (E := E) i * grid x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := hkey
      _ = operatorFieldApplicationGdiag (E := E) i *
          ∫ x, grid x ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
        rw [MeasureTheory.integral_const_mul]
  calc
    (∑ i ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g p c i
          (ccOperatorFieldComp (I := I) (M := M) g p r c Φ W)‖ ^ 2) ≤
        ∑ i ∈ Finset.range 3, operatorFieldApplicationGdiag (E := E) i *
          ∫ x, grid x ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
      Finset.sum_le_sum hterm
    _ = D * ∫ x, grid x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
      dsimp only [D]
      rw [Finset.sum_mul]
    _ ≤ D * (Cg * A ^ 2 * B ^ 2) :=
      mul_le_mul_of_nonneg_left (by simpa only [grid] using hgridBd) hD
    _ = K * A ^ 2 * B ^ 2 := by
      dsimp only [K]
      ring
    _ = (C * A * B) ^ 2 := by
      rw [mul_pow, mul_pow, show C ^ 2 = K by
        simp only [C, Real.sq_sqrt hK]]

theorem operatorFieldApplication_h23_h2_uniform
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ g : SmoothRiemannianMetric I M,
        MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
        (∀ a : ℕ, a ≤ 3 →
          MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ) →
        ∀ (Φ : SmoothCcTensor g 3 2) (U : SmoothCcTensor g 0 2) (A : ℝ),
          0 ≤ A →
          (∑ j ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g 3 2 j Φ‖ ^ 2) ≤ A ^ 2 →
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
              (operatorFieldApply (I := I) (M := M) g 3 2 Φ
                (iteratedCovGrad (I := I) g 0 2 1 U))‖ ≤
            C * A *
              ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U‖ := by
  classical
  obtain ⟨K, hK⟩ :=
    DifferentialGeometry.PDE.RicciFlow.exists_uniform_curvature_action_parameters
      (I := I) (M := M) gBase hΛ
  obtain ⟨Capp, hCapp, happ⟩ :=
    operatorFieldComposition_h2_h2_to_h2_uniform_bound (I := I) (M := M) hDim gBase hΛ 0 3 2
  let Csp : ℝ := hsTwoJetC (Module.finrank ℝ E)
  let Ch : ℝ := h3CovsumC K.rankTwo K.rankThree
  let C : ℝ := Csp * 3 * Capp * Ch
  have hCsp : 0 ≤ Csp := by
    simpa only [Csp] using hsTwoJetC_nonneg (Module.finrank ℝ E)
  have hCh : 0 ≤ Ch := by
    simpa only [Ch] using h3CovsumC_nonneg K.rankTwo K.rankThree
  refine ⟨C, by
    dsimp only [C]
    positivity, ?_⟩
  intro g hEq hjet Φ U A hA hΦ
  obtain ⟨hact2, hact3⟩ := hK.bounds g hEq hjet
  let N : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U‖
  let B : ℝ := Ch * N
  let W : SmoothCcTensor g 0 3 :=
    iteratedCovGrad (I := I) g 0 2 1 U
  let Y : SmoothCcTensor g 0 2 :=
    operatorFieldApply (I := I) (M := M) g 3 2 Φ W
  let Q : ℝ := Capp * A * B
  have hN : 0 ≤ N := norm_nonneg _
  have hB : 0 ≤ B := mul_nonneg hCh hN
  have hQ : 0 ≤ Q := mul_nonneg (mul_nonneg hCapp hA) hB
  have hJ :
      ∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g 0 2 j U‖ ≤ B := by
    simpa only [B, Ch, N] using
      covsum_hs_three (I := I) (M := M) g 2 hact2 hact3 U
  have hWsum :
      ∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 0 3 j W‖ ≤ B := by
    calc
      ∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 0 3 j W‖ =
          ∑ j ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g 0 2 (1 + j) U‖ := by
              refine Finset.sum_congr rfl (fun j _ => ?_)
              simpa only [W] using
                iteratedCovGrad_comp_norm (I := I) (M := M) g 2 1 j U
      _ ≤ ∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g 0 2 j U‖ := by
            simp only [Finset.sum_range_succ, Finset.sum_range_zero,
              zero_add, Nat.reduceAdd]
            nlinarith [
              norm_nonneg (iteratedCovGrad (I := I) g 0 2 0 U)]
      _ ≤ B := hJ
  have hWsq :
      (∑ j ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 0 3 j W‖ ^ 2) ≤ B ^ 2 := by
    calc
      _ ≤ (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 0 3 j W‖) ^ 2 :=
        Finset.sum_sq_le_sq_sum_of_nonneg
          (fun j _ => norm_nonneg
            (iteratedCovGrad (I := I) g 0 3 j W))
      _ ≤ B ^ 2 := pow_le_pow_left₀
        (Finset.sum_nonneg (fun j _ => norm_nonneg
          (iteratedCovGrad (I := I) g 0 3 j W))) hWsum 2
  have hYsq :
      (∑ j ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 0 2 j Y‖ ^ 2) ≤ Q ^ 2 := by
    have hmix := happ g hEq (hjet 1 (by norm_num)) (hjet 2 (by norm_num))
      Φ W A B hA hB hΦ hWsq
    simpa only [Y, Q, operatorFieldComposition_zero_eq_operatorFieldApply] using hmix
  have hterm : ∀ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g 0 2 j Y‖ ≤ Q := by
    intro j hj
    have hsingle :
        ‖iteratedCovGrad (I := I) g 0 2 j Y‖ ^ 2 ≤
          ∑ i ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g 0 2 i Y‖ ^ 2 :=
      Finset.single_le_sum
        (f := fun i => ‖iteratedCovGrad (I := I) g 0 2 i Y‖ ^ 2)
        (fun i _ => sq_nonneg _) hj
    nlinarith [hsingle.trans hYsq,
      norm_nonneg (iteratedCovGrad (I := I) g 0 2 j Y)]
  have hYsum :
      ∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 0 2 j Y‖ ≤ 3 * Q := by
    calc
      _ ≤ ∑ _j ∈ Finset.range 3, Q :=
        Finset.sum_le_sum fun j hj => hterm j hj
      _ = 3 * Q := by norm_num
  have hspY :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) Y‖ ≤
        Csp * ∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 0 2 j Y‖ := by
    simpa only [Csp] using hs_two_le_jet (I := I) (M := M) g 2 Y
  change ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) Y‖ ≤
    C * A * N
  calc
    _ ≤ Csp * ∑ j ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 0 2 j Y‖ := hspY
    _ ≤ Csp * (3 * Q) := mul_le_mul_of_nonneg_left hYsum hCsp
    _ = C * A * N := by
      dsimp only [C, Q, B, Ch]
      ring

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
