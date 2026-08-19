import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.RemainderCoeffPerOrderJetEnvelopes

import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Uniform.GagliardoNirenberg
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Uniform.Morrey

set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory Set DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow

open DifferentialGeometry.HCGCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Sobolev.Tensor

private lemma grid_two_mul_le
    {Cg C CS CT A B JS JT : ℝ}
    (hC : 0 ≤ C) (hcap : Cg ≤ C)
    (hJS0 : 0 ≤ JS) (hJT0 : 0 ≤ JT)
    (hJS : JS ≤ A ^ 2) (hJT : JT ≤ B ^ 2) :
    Cg * ((CT * B) ^ 2 * JS + (CS * A) ^ 2 * JT) ≤
      C * (CT ^ 2 + CS ^ 2) * A ^ 2 * B ^ 2 := by
  have hinner0 : 0 ≤ (CT * B) ^ 2 * JS + (CS * A) ^ 2 * JT :=
    add_nonneg (mul_nonneg (sq_nonneg _) hJS0) (mul_nonneg (sq_nonneg _) hJT0)
  calc
    Cg * ((CT * B) ^ 2 * JS + (CS * A) ^ 2 * JT)
        ≤ C * ((CT * B) ^ 2 * JS + (CS * A) ^ 2 * JT) :=
      mul_le_mul_of_nonneg_right hcap hinner0
    _ ≤ C * ((CT * B) ^ 2 * A ^ 2 + (CS * A) ^ 2 * B ^ 2) :=
      mul_le_mul_of_nonneg_left
        (add_le_add
          (mul_le_mul_of_nonneg_left hJS (sq_nonneg _))
          (mul_le_mul_of_nonneg_left hJT (sq_nonneg _))) hC
    _ = C * (CT ^ 2 + CS ^ 2) * A ^ 2 * B ^ 2 := by ring

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

noncomputable def gridRSClassC
    (gBase : SmoothRiemannianMetric I M) (Λ : ℝ) (k : ℕ) : ℝ :=
  (k + 1) ^ 2 *
    (1 + ∑ m ∈ Finset.range (k + 1),
      gnClassC (E := E) (I := I) (M := M) gBase Λ m *
        gnClassC (E := E) (I := I) (M := M) gBase Λ m)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] in
theorem gridRSClassC_nonneg
    (gBase : SmoothRiemannianMetric I M) (Λ : ℝ) (k : ℕ) :
    0 ≤ gridRSClassC (E := E) (I := I) (M := M) gBase Λ k := by
  unfold gridRSClassC
  apply mul_nonneg
  · positivity
  · exact add_nonneg zero_le_one (Finset.sum_nonneg (fun m _ =>
      mul_nonneg
        (gnClassC_nonneg (E := E) (I := I) (M := M) gBase Λ m)
        (gnClassC_nonneg (E := E) (I := I) (M := M) gBase Λ m)))

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [BoundarylessManifold I M] in
private lemma gnGridCoeff_le
    (gBase : SmoothRiemannianMetric I M) {Λ : ℝ}
    (g : SmoothRiemannianMetric I M)
    (hEq : MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ) (m : ℕ) :
    gnGridCoeff (I := I) (M := M) g m ≤
      gnClassC (E := E) (I := I) (M := M) gBase Λ m := by
  by_cases hm : 1 ≤ m
  · simpa only [gnGridCoeff, if_pos hm, metricVolRadius] using
      (gnClassC_spec (I := I) (M := M) gBase g hEq m)
  · simpa only [gnGridCoeff, if_neg hm] using
      (gnClassC_nonneg (E := E) (I := I) (M := M) gBase Λ m)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [BoundarylessManifold I M] in
theorem grid_rs_const_le
    (gBase : SmoothRiemannianMetric I M) {Λ : ℝ}
    (g : SmoothRiemannianMetric I M)
    (hEq : MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ) (k : ℕ) :
    gridRsConst (I := I) (M := M) g k ≤
      gridRSClassC (E := E) (I := I) (M := M) gBase Λ k := by
  unfold gridRsConst gridRSClassC
  apply mul_le_mul_of_nonneg_left
  · apply add_le_add (le_refl 1)
    apply Finset.sum_le_sum
    intro m hm
    have hcoeff := gnGridCoeff_le (I := I) (M := M) gBase g hEq m
    exact mul_le_mul hcoeff hcoeff
      (gnGridCoeff_nonneg (I := I) (M := M) g m)
      (gnClassC_nonneg (E := E) (I := I) (M := M) gBase Λ m)
  · positivity

theorem grid_rs_uniform
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) (r₁ r₂ s₁ s₂ : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ g : SmoothRiemannianMetric I M,
        MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
        MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g gBase Λ →
        MetricCovDerivOrderBoundOn (I := I) Set.univ 2 g gBase Λ →
        ∀ (S : SmoothCcTensor g r₁ s₁) (T : SmoothCcTensor g r₂ s₂)
          (A B : ℝ), 0 ≤ A → 0 ≤ B →
          (∑ j ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g r₁ s₁ j S‖ ^ 2) ≤ A ^ 2 →
          (∑ j ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g r₂ s₂ j T‖ ^ 2) ≤ B ^ 2 →
          MeasureTheory.Integrable
              (fun x => ∑ i ∈ Finset.range 3,
                riemannianFiberNormSq (I := I) (M := M) g r₁ (s₁ + i) x
                    ((iteratedCovGrad (I := I) g r₁ s₁ i S).toSection x) *
                  ∑ l ∈ Finset.range (3 - i),
                    riemannianFiberNormSq (I := I) (M := M) g r₂ (s₂ + l) x
                      ((iteratedCovGrad (I := I) g r₂ s₂ l T).toSection x))
              (riemannianVolumeMeasure (I := I) (M := M) g) ∧
            (∫ x, (∑ i ∈ Finset.range 3,
                riemannianFiberNormSq (I := I) (M := M) g r₁ (s₁ + i) x
                    ((iteratedCovGrad (I := I) g r₁ s₁ i S).toSection x) *
                  ∑ l ∈ Finset.range (3 - i),
                    riemannianFiberNormSq (I := I) (M := M) g r₂ (s₂ + l) x
                      ((iteratedCovGrad (I := I) g r₂ s₂ l T).toSection x))
                ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ≤
              C * A ^ 2 * B ^ 2 := by
  obtain ⟨CS, hCS, hMorS⟩ :=
    morreyRS_uniform (I := I) (M := M) hDim gBase hΛ r₁ s₁
  obtain ⟨CT, hCT, hMorT⟩ :=
    morreyRS_uniform (I := I) (M := M) hDim gBase hΛ r₂ s₂
  refine ⟨gridRSClassC (E := E) (I := I) (M := M) gBase Λ 2 *
      (CT ^ 2 + CS ^ 2),
    mul_nonneg (gridRSClassC_nonneg (E := E) (I := I) (M := M) gBase Λ 2)
      (add_nonneg (sq_nonneg _) (sq_nonneg _)), ?_⟩
  intro g hEq hjet1 hjet2 S T A B hA hB hSjet hTjet
  have hSpoint : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g r₁ s₁ x (S.toSection x) ≤
        (CS * A) ^ 2 := by
    intro x
    calc
      riemannianFiberNormSq (I := I) (M := M) g r₁ s₁ x (S.toSection x)
          ≤ CS ^ 2 * ∑ j ∈ Finset.range 3,
              ‖iteratedCovGrad (I := I) g r₁ s₁ j S‖ ^ 2 :=
        hMorS g hEq hjet1 hjet2 S x
      _ ≤ CS ^ 2 * A ^ 2 := mul_le_mul_of_nonneg_left hSjet (sq_nonneg _)
      _ = (CS * A) ^ 2 := by ring
  have hTpoint : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g r₂ s₂ x (T.toSection x) ≤
        (CT * B) ^ 2 := by
    intro x
    calc
      riemannianFiberNormSq (I := I) (M := M) g r₂ s₂ x (T.toSection x)
          ≤ CT ^ 2 * ∑ j ∈ Finset.range 3,
              ‖iteratedCovGrad (I := I) g r₂ s₂ j T‖ ^ 2 :=
        hMorT g hEq hjet1 hjet2 T x
      _ ≤ CT ^ 2 * B ^ 2 := mul_le_mul_of_nonneg_left hTjet (sq_nonneg _)
      _ = (CT * B) ^ 2 := by ring
  obtain ⟨hgridInt, hgridBd⟩ :=
    (grid_rs_bound (I := I) (M := M) g r₁ r₂ s₁ s₂ 2).2
      S T (CS * A) (CT * B) (mul_nonneg hCS hA) (mul_nonneg hCT hB)
        hSpoint hTpoint
  refine ⟨hgridInt, le_trans hgridBd ?_⟩
  apply grid_two_mul_le
  · exact gridRSClassC_nonneg (E := E) (I := I) (M := M) gBase Λ 2
  · exact grid_rs_const_le (I := I) (M := M) gBase g hEq 2
  · exact Finset.sum_nonneg (fun j _ => sq_nonneg
      ‖iteratedCovGrad (I := I) g r₁ s₁ j S‖)
  · exact Finset.sum_nonneg (fun j _ => sq_nonneg
      ‖iteratedCovGrad (I := I) g r₂ s₂ j T‖)
  · exact hSjet
  · exact hTjet

end RicciFlow
end PDE
end DifferentialGeometry

end
