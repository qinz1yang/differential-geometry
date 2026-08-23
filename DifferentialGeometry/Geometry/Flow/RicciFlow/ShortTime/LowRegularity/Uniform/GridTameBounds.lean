import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.CoefficientJetBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Uniform.GagliardoNirenberg

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

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

theorem h1_grid_uniform
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    {r s : ℕ} (C : ℕ → ℝ) (hC : ∀ i, 0 ≤ C i) :
    ∃ B0 B1 : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
      ∀ g : SmoothRiemannianMetric I M,
        MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
        MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g gBase Λ →
        MetricCovDerivOrderBoundOn (I := I) Set.univ 2 g gBase Λ →
        ∀ (P : SmoothCcTensor g 0 2) (Φ : SmoothCcTensor g r s)
          (R A : ℝ), 0 ≤ R → 0 ≤ A →
          (∑ j ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g 0 2 j P‖ ^ 2) ≤ R ^ 2 →
          ‖iteratedCovGrad (I := I) g 0 2 3 P‖ ≤ A →
          (∀ (i : ℕ), i < 2 → ∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g r (s + i) x
                ((iteratedCovGrad (I := I) g r s i Φ).toSection x) ≤
              C i * ∑ k ∈ Finset.range (i + 3),
                lowJetGrid (I := I) (M := M) g P k x) →
          (∑ i ∈ Finset.range 2,
            ‖iteratedCovGrad (I := I) g r s i Φ‖ ^ 2) ≤
            (B0 R + B1 R * A) ^ 2 := by
  classical
  let K0 : ℝ → ℕ → ℝ := fun R k ↦
    DifferentialGeometry.PDE.RicciFlow.h2GridC
      (E := E) (I := I) (M := M) gBase Λ R k
  let K3 : ℝ → ℝ := fun R ↦
    DifferentialGeometry.PDE.RicciFlow.h3TopGridC
      (E := E) (I := I) (M := M) gBase Λ R
  let L : ℝ → ℕ → ℝ := fun R i ↦
    ∑ k ∈ Finset.range (i + 3), if k = 3 then 0 else K0 R k
  let T : ℝ → ℕ → ℝ := fun R i ↦
    ∑ k ∈ Finset.range (i + 3), if k = 3 then K3 R else 0
  let Q0 : ℝ → ℝ := fun R ↦
    ∑ i ∈ Finset.range 2, C i * L R i
  let Q1 : ℝ → ℝ := fun R ↦
    ∑ i ∈ Finset.range 2, C i * T R i
  let B0 : ℝ → ℝ := fun R ↦ Real.sqrt (Q0 R)
  let B1 : ℝ → ℝ := fun R ↦ Real.sqrt (Q1 R)
  have hK0 : ∀ R : ℝ, 0 ≤ R → ∀ k, 0 ≤ K0 R k := by
    intro R _ k
    simpa only [K0] using
      (DifferentialGeometry.PDE.RicciFlow.h2_grid_nonneg
        (E := E) (I := I) (M := M) gBase Λ R k)
  have hK3 : ∀ R : ℝ, 0 ≤ R → 0 ≤ K3 R := by
    intro R _
    simpa only [K3, DifferentialGeometry.PDE.RicciFlow.h3TopGridC] using
      (DifferentialGeometry.PDE.RicciFlow.rank_two_grid_nonneg
        (E := E) (I := I) (M := M) gBase Λ 3 R)
  have hL : ∀ R : ℝ, 0 ≤ R → ∀ i, 0 ≤ L R i := by
    intro R hR i
    exact Finset.sum_nonneg fun k _ ↦ by
      by_cases hk : k = 3
      · simp only [hk, if_pos]
        exact le_rfl
      · simp only [if_neg hk]
        exact hK0 R hR k
  have hT : ∀ R : ℝ, 0 ≤ R → ∀ i, 0 ≤ T R i := by
    intro R hR i
    exact Finset.sum_nonneg fun k _ ↦ by
      by_cases hk : k = 3
      · simp only [hk, if_pos]
        exact hK3 R hR
      · simp only [if_neg hk]
        exact le_rfl
  have hQ0 : ∀ R : ℝ, 0 ≤ R → 0 ≤ Q0 R := by
    intro R hR
    exact Finset.sum_nonneg fun i _ ↦ mul_nonneg (hC i) (hL R hR i)
  have hQ1 : ∀ R : ℝ, 0 ≤ R → 0 ≤ Q1 R := by
    intro R hR
    exact Finset.sum_nonneg fun i _ ↦ mul_nonneg (hC i) (hT R hR i)
  refine ⟨B0, B1, fun R _ ↦ Real.sqrt_nonneg _,
    fun R _ ↦ Real.sqrt_nonneg _, ?_⟩
  intro g hEq hjet1 hjet2 P Φ R A hR hA hP2 htop hΦ
  have hgrid0 := DifferentialGeometry.PDE.RicciFlow.h2_grid_uniform
    (E := E) (I := I) (M := M) hDim gBase hΛ
    g hEq hjet1 hjet2 P R hR hP2
  have hgrid3 := DifferentialGeometry.PDE.RicciFlow.h3_top_grid_uniform
    (E := E) (I := I) (M := M) hDim gBase hΛ
    g hEq hjet1 hjet2 P R A hR hA hP2 htop
  let Km : ℕ → ℝ := fun k ↦ if k = 3 then K3 R * A ^ 2 else K0 R k
  have hKm : ∀ k, 0 ≤ Km k := by
    intro k
    by_cases hk : k = 3
    · simp only [Km, hk, if_pos]
      exact mul_nonneg (hK3 R hR) (sq_nonneg A)
    · simp only [Km, if_neg hk]
      exact hK0 R hR k
  have hgr : ∀ k : ℕ, k ≤ 3 →
      MeasureTheory.Integrable (lowJetGrid (I := I) (M := M) g P k)
        (riemannianVolumeMeasure (I := I) (M := M) g) ∧
      (∫ x, lowJetGrid (I := I) (M := M) g P k x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ≤ Km k := by
    intro k hk
    by_cases hk3 : k = 3
    · subst k
      simpa only [lowJetGrid, Km, if_pos, K3, Nat.reduceAdd] using hgrid3
    · have hk2 : k ≤ 2 := by omega
      simpa only [lowJetGrid, Km, if_neg hk3, K0] using hgrid0 k hk2
  have hle := grid_h1_le (I := I) (M := M) g P Km C
    hgr hC Φ hΦ
  have hsplit : ∀ i : ℕ,
      (∑ k ∈ Finset.range (i + 3), Km k) = L R i + T R i * A ^ 2 := by
    intro i
    simp only [L, T]
    calc
      _ = ∑ k ∈ Finset.range (i + 3),
          ((if k = 3 then 0 else K0 R k) +
            (if k = 3 then K3 R else 0) * A ^ 2) := by
        apply Finset.sum_congr rfl
        intro k _
        by_cases hk : k = 3
        · simp only [Km, hk, if_pos, zero_add]
        · simp only [Km, if_neg hk, zero_mul, add_zero]
      _ = (∑ k ∈ Finset.range (i + 3), if k = 3 then 0 else K0 R k) +
          ∑ k ∈ Finset.range (i + 3),
            (if k = 3 then K3 R else 0) * A ^ 2 := by
        rw [Finset.sum_add_distrib]
      _ = (∑ k ∈ Finset.range (i + 3), if k = 3 then 0 else K0 R k) +
          (∑ k ∈ Finset.range (i + 3), if k = 3 then K3 R else 0) *
            A ^ 2 := by
        rw [Finset.sum_mul]
  have hQeq :
      (∑ i ∈ Finset.range 2,
        C i * ∑ k ∈ Finset.range (i + 3), Km k) =
        Q0 R + Q1 R * A ^ 2 := by
    calc
      _ = ∑ i ∈ Finset.range 2,
          (C i * L R i + (C i * T R i) * A ^ 2) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hsplit i, mul_add, mul_assoc]
      _ = (∑ i ∈ Finset.range 2, C i * L R i) +
          ∑ i ∈ Finset.range 2, (C i * T R i) * A ^ 2 := by
        rw [Finset.sum_add_distrib]
      _ = Q0 R + Q1 R * A ^ 2 := by
        simp only [Q0, Q1, Finset.sum_mul]
  rw [hQeq] at hle
  calc
    _ ≤ Q0 R + Q1 R * A ^ 2 := hle
    _ = (B0 R) ^ 2 + (B1 R * A) ^ 2 := by
      simp only [B0, B1, mul_pow, Real.sq_sqrt (hQ0 R hR),
        Real.sq_sqrt (hQ1 R hR)]
    _ ≤ (B0 R + B1 R * A) ^ 2 := by
      nlinarith [mul_nonneg (Real.sqrt_nonneg (Q0 R))
        (mul_nonneg (Real.sqrt_nonneg (Q1 R)) hA)]

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
