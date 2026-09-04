import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Uniform.DeTurck.RHSFirstDerivative
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Uniform.Sobolev.GagliardoNirenberg
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricPerturbation.CovariantOrderCoefficient.ReindexingNorm

set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory Set DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

noncomputable def connFixH2C
    (gBase : SmoothRiemannianMetric I M) (Λ : ℝ) : ℝ :=
  let R₁ := revJetOneC (E := E) Λ
  let R₂ := revJetTwoC (E := E) Λ
  let R₃ := revJetThreeC (E := E) Λ
  let A₀ := 3 / 2 * Λ ^ 3 * R₁
  let A₁ := 3 / 2 * Λ ^ 4 * (R₂ + Λ * R₁ ^ 2)
  let A₂ :=
    3 / 2 * Λ ^ 5 * R₃ +
      9 / 2 * Λ ^ 6 * R₁ * R₂ +
      3 * Λ ^ 7 * R₁ ^ 3
  Real.sqrt
    (((3 : ℝ) ^ 3 * A₀ ^ 2 + (3 : ℝ) ^ 4 * A₁ ^ 2 +
        (3 : ℝ) ^ 5 * A₂ ^ 2) *
      (volCompareC (E := E) Λ *
        ((riemannianVolumeMeasure (I := I) (M := M) gBase) Set.univ).toReal))

noncomputable def connFixGridC (Λ : ℝ) (j : ℕ) : ℝ :=
  if j = 0 then connectionDifferenceZeroSqC (E := E) Λ
  else if j = 1 then connectionDifferenceOneSqC (E := E) Λ
  else connectionDifferenceTwoC (E := E) Λ

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
lemma connFixGridC_nonneg (Λ : ℝ) (j : ℕ) :
    0 ≤ connFixGridC (E := E) Λ j := by
  unfold connFixGridC
  split
  · unfold connectionDifferenceZeroSqC
    positivity
  · split
    · unfold connectionDifferenceOneSqC
      positivity
    · unfold connectionDifferenceTwoC
      positivity

omit [SigmaCompactSpace M] in
theorem connFix_grid_uniform
    (gBase : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∃ F : ℕ → ℝ, (∀ j, 0 ≤ F j) ∧
      ∀ g₀ : SmoothRiemannianMetric I M,
        MetricUniformEquivalentOn (I := I) Set.univ gBase g₀ Λ →
        MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g₀ gBase Λ →
        MetricCovDerivOrderBoundOn (I := I) Set.univ 2 g₀ gBase Λ →
        MetricCovDerivOrderBoundOn (I := I) Set.univ 3 g₀ gBase Λ →
        ∀ j, j < 3 → ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + j) x
              ((iteratedCovGrad (I := I) g₀ 1 2 j
                (connectionDifferenceSection (I := I) gBase g₀)).toSection x) ≤
            F j := by
  refine ⟨connFixGridC (E := E) Λ, connFixGridC_nonneg (E := E) Λ, ?_⟩
  intro g₀ hEq hjet1 hjet2 hjet3 j hj x
  have hcomp : ∀ (y : M) (v : TangentSpace I y),
      Λ⁻¹ * gBase.inner y v v ≤ g₀.inner y v v ∧
        g₀.inner y v v ≤ Λ * gBase.inner y v v :=
    fun y v => hEq.2 y (Set.mem_univ y) v
  by_cases hj0 : j = 0
  · subst j
    simpa [connFixGridC] using
      (uniformConnectionDifferenceZero (I := I) (M := M) gBase g₀ hΛ hcomp hjet1 x)
  by_cases hj1 : j = 1
  · subst j
    simpa [connFixGridC] using
      (uniformConnectionDifferenceOne (I := I) (M := M) gBase g₀ hΛ hcomp hjet1 hjet2 x)
  have hj2 : j = 2 := by omega
  subst j
  simpa [connFixGridC] using
    (uniformConnectionDifferenceTwo (I := I) (M := M) gBase g₀ hΛ hcomp hjet1 hjet2 hjet3 x)

theorem connFix_h2_uniform
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∃ F : ℝ, 0 ≤ F ∧
      ∀ g₀ : SmoothRiemannianMetric I M,
        MetricUniformEquivalentOn (I := I) Set.univ gBase g₀ Λ →
        MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g₀ gBase Λ →
        MetricCovDerivOrderBoundOn (I := I) Set.univ 2 g₀ gBase Λ →
        MetricCovDerivOrderBoundOn (I := I) Set.univ 3 g₀ gBase Λ →
        (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g₀ 1 2 j
            (connectionDifferenceSection (I := I) gBase g₀)‖ ^ 2) ≤ F ^ 2 := by
  classical
  let R₁ : ℝ := revJetOneC (E := E) Λ
  let R₂ : ℝ := revJetTwoC (E := E) Λ
  let R₃ : ℝ := revJetThreeC (E := E) Λ
  let A₀ : ℝ := 3 / 2 * Λ ^ 3 * R₁
  let A₁ : ℝ := 3 / 2 * Λ ^ 4 * (R₂ + Λ * R₁ ^ 2)
  let A₂ : ℝ :=
    3 / 2 * Λ ^ 5 * R₃ +
      9 / 2 * Λ ^ 6 * R₁ * R₂ +
      3 * Λ ^ 7 * R₁ ^ 3
  let C₀ : ℝ := (3 : ℝ) ^ 3 * A₀ ^ 2
  let C₁ : ℝ := (3 : ℝ) ^ 4 * A₁ ^ 2
  let C₂ : ℝ := (3 : ℝ) ^ 5 * A₂ ^ 2
  let V : ℝ := volCompareC (E := E) Λ *
    ((riemannianVolumeMeasure (I := I) (M := M) gBase) Set.univ).toReal
  have hC₀ : 0 ≤ C₀ := by
    dsimp [C₀]
    positivity
  have hC₁ : 0 ≤ C₁ := by
    dsimp [C₁]
    positivity
  have hC₂ : 0 ≤ C₂ := by
    dsimp [C₂]
    positivity
  have hV : 0 ≤ V := by
    dsimp [V, volCompareC]
    positivity
  refine ⟨connFixH2C (E := E) (I := I) (M := M) gBase Λ,
    Real.sqrt_nonneg _, ?_⟩
  intro g₀ hEq hjet1 hjet2 hjet3
  have hcomp : ∀ (x : M) (v : TangentSpace I x),
      Λ⁻¹ * gBase.inner x v v ≤ g₀.inner x v v ∧
        g₀.inner x v v ≤ Λ * gBase.inner x v v :=
    fun x v => hEq.2 x (Set.mem_univ x) v
  have hpt₀ := uniformConnectionDifferenceZero (I := I) (M := M) gBase g₀
    hΛ hcomp hjet1
  have hpt₁ := uniformConnectionDifferenceOne (I := I) (M := M) gBase g₀
    hΛ hcomp hjet1 hjet2
  have hpt₂ := uniformConnectionDifferenceTwo (I := I) (M := M) gBase g₀
    hΛ hcomp hjet1 hjet2 hjet3
  have hpt₀' : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + 0) x
          ((iteratedCovGrad (I := I) g₀ 1 2 0
            (connectionDifferenceSection (I := I) gBase g₀)).toSection x) ≤ C₀ := by
    simpa only [C₀, A₀, R₁, connectionDifferenceZeroSqC, hDim, Nat.cast_ofNat] using hpt₀
  have hpt₁' : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + 1) x
          ((iteratedCovGrad (I := I) g₀ 1 2 1
            (connectionDifferenceSection (I := I) gBase g₀)).toSection x) ≤ C₁ := by
    simpa only [C₁, A₁, R₁, R₂, connectionDifferenceOneSqC, hDim, Nat.cast_ofNat] using hpt₁
  have hpt₂' : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + 2) x
          ((iteratedCovGrad (I := I) g₀ 1 2 2
            (connectionDifferenceSection (I := I) gBase g₀)).toSection x) ≤ C₂ := by
    simpa only [C₂, A₂, R₁, R₂, R₃, connectionDifferenceTwoC, hDim, Nat.cast_ofNat] using hpt₂
  have hvol := (volumeReal_cross (I := I) (M := M) gBase g₀ hEq).1
  have hvolV :
      ((riemannianVolumeMeasure (I := I) (M := M) g₀) Set.univ).toReal ≤ V := by
    simpa only [V] using hvol
  have hnorm₀ :
      ‖iteratedCovGrad (I := I) g₀ 1 2 0
          (connectionDifferenceSection (I := I) gBase g₀)‖ ^ 2 ≤ C₀ * V := by
    refine (norm_le_of_pointwise_fiberNormSq_bound_rs
      (I := I) (M := M) g₀ 1 (2 + 0)
      (iteratedCovGrad (I := I) g₀ 1 2 0
        (connectionDifferenceSection (I := I) gBase g₀)) C₀ ?_).trans ?_
    · exact hpt₀'
    · exact mul_le_mul_of_nonneg_left hvolV hC₀
  have hnorm₁ :
      ‖iteratedCovGrad (I := I) g₀ 1 2 1
          (connectionDifferenceSection (I := I) gBase g₀)‖ ^ 2 ≤ C₁ * V := by
    refine (norm_le_of_pointwise_fiberNormSq_bound_rs
      (I := I) (M := M) g₀ 1 (2 + 1)
      (iteratedCovGrad (I := I) g₀ 1 2 1
        (connectionDifferenceSection (I := I) gBase g₀)) C₁ ?_).trans ?_
    · exact hpt₁'
    · exact mul_le_mul_of_nonneg_left hvolV hC₁
  have hnorm₂ :
      ‖iteratedCovGrad (I := I) g₀ 1 2 2
          (connectionDifferenceSection (I := I) gBase g₀)‖ ^ 2 ≤ C₂ * V := by
    refine (norm_le_of_pointwise_fiberNormSq_bound_rs
      (I := I) (M := M) g₀ 1 (2 + 2)
      (iteratedCovGrad (I := I) g₀ 1 2 2
        (connectionDifferenceSection (I := I) gBase g₀)) C₂ ?_).trans ?_
    · exact hpt₂'
    · exact mul_le_mul_of_nonneg_left hvolV hC₂
  let f : ℕ → ℝ := fun j =>
    ‖iteratedCovGrad (I := I) g₀ 1 2 j
      (connectionDifferenceSection (I := I) gBase g₀)‖ ^ 2
  change (∑ j ∈ Finset.range 3, f j) ≤
    connFixH2C (E := E) (I := I) (M := M) gBase Λ ^ 2
  have hf₀ : f 0 ≤ C₀ * V := by simpa only [f] using hnorm₀
  have hf₁ : f 1 ≤ C₁ * V := by simpa only [f] using hnorm₁
  have hf₂ : f 2 ≤ C₂ * V := by simpa only [f] using hnorm₂
  calc
    ∑ j ∈ Finset.range 3, f j = f 0 + f 1 + f 2 := by
      norm_num [Finset.sum_range_succ]
    _ ≤ C₀ * V + C₁ * V + C₂ * V :=
      add_le_add (add_le_add hf₀ hf₁) hf₂
    _ = (C₀ + C₁ + C₂) * V := by ring
    _ = connFixH2C (E := E) (I := I) (M := M) gBase Λ ^ 2 := by
      change (C₀ + C₁ + C₂) * V = Real.sqrt ((C₀ + C₁ + C₂) * V) ^ 2
      rw [Real.sq_sqrt (mul_nonneg (add_nonneg (add_nonneg hC₀ hC₁) hC₂) hV)]

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
