import DifferentialGeometry.Geometry.Comparison.Volume.EnlargedBallPackingRow

/-!
# Consumers of the FC08 row

* `fc08_two_stratum_row`: FC08 with the two-stratum parameters `R = 10`, `a = 1/3`, `C = 10`,
  `κ = 1` (blueprint line 494).
* `fc08_edge_count_of_sectional`: the edge family (`C₀ = 100`) with the explicit buffer radius
  `Q = 4(10 + 200Δ + Δ/3)`; the count is bounded by a constant independent of `Δ`.
* `fc08_ratio_example`: the ratio clause on `ℝ` with a constant scale (nonvacuity).
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

open _root_.Metric

/-- The ratio clause on `ℝ` with the constant scale `1`. -/
theorem fc08_ratio_example :
    (fun _ : ℝ => (1 : ℝ)) 0 / (fun _ : ℝ => (1 : ℝ)) 5 ∈ Icc (1 / 2 : ℝ) 2 := by
  refine fc08_ratio_mem_Icc (X := ℝ) (ρ := fun _ : ℝ => (1 : ℝ)) (Λ := 0) (R := 10) (C := 10)
    (S := {0}) (c := 0) (p := 5)
    (LipschitzWith.const _) (fun _ => one_pos) (by simp) ?_ ?_
  · intro x hx
    rw [mem_singleton_iff.mp hx]
    simp
  · refine ⟨0, mem_singleton 0, ?_⟩
    have h05 : dist (0 : ℝ) 5 < 10 * 1 := by
      rw [Real.dist_eq]
      norm_num
    exact mem_ball.mpr (by simpa only [mul_one] using h05)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space (TangentBundle I M)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsRiemannianManifold I M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
  [SigmaCompactSpace M] [CompleteSpace M]

/-- FC08 with the two-stratum parameters `R = 10`, `a = 1/3`, `C = 10`, `κ = 1`. -/
theorem fc08_two_stratum_row (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    {ι : Type*} (J : Finset ι) (c : ι → M) (S : ι → Set M) {ρ : M → ℝ} {Λ : NNReal}
    (hρ : LipschitzWith Λ ρ) (hρpos : ∀ x, 0 < ρ x) (hΛ : (Λ : ℝ) * 10 ≤ 1 / 4)
    (hS : ∀ j ∈ J, S j ⊆ closedBall (c j) (10 * ρ (c j)))
    (hdisj : (J : Set ι).PairwiseDisjoint fun j => ball (c j) (1 / 3 * ρ (c j))) (p : M)
    (hRic : ∀ j ∈ J, (S j ∩ ball p (10 * ρ p)).Nonempty → ricciBoundedBelowOn (I := I) g
      (ball (c j) (4 * (10 + 2 * 10 + 1 / 3) * ρ (c j)))
      (((Module.finrank ℝ E - 1 : ℕ) : ℝ) * (-((1 / ρ (c j)) ^ 2)))) :
    ({j | j ∈ J ∧ (S j ∩ ball p (10 * ρ p)).Nonempty}.ncard : ℝ) ≤
        modelVolume (-(1 ^ 2)) (Module.finrank ℝ E) (4 * (10 + 2 * 10 + 1 / 3)) /
          modelVolume (-(1 ^ 2)) (Module.finrank ℝ E) (1 / 3) ∧
      ∀ j ∈ J, (S j ∩ ball p (10 * ρ p)).Nonempty → ρ (c j) / ρ p ∈ Icc (1 / 2 : ℝ) 2 :=
  fc08_row g hEnorm J c S hρ hρpos (by norm_num) (by norm_num) (by norm_num) zero_le_one
    (by simpa using hΛ) hS hdisj p hRic

/-- The edge family (`C₀ = 100`, cores `Δ r_j / 3`) under a sectional buffer of radius
`Q = 4(10 + 200Δ + Δ/3)`: the count is bounded independently of `Δ`. -/
theorem fc08_edge_count_of_sectional (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) g)
    {ι : Type*} (J : Finset ι) (c : ι → M) (S : ι → Set M) {ρ : M → ℝ} {Λ : NNReal}
    (hρ : LipschitzWith Λ ρ) (hρpos : ∀ x, 0 < ρ x) {Δ : ℝ} (hΔ : 1 ≤ Δ)
    (hbudget : (Λ : ℝ) * (100 * Δ) ≤ 1 / 4)
    (hS : ∀ j ∈ J, S j ⊆ closedBall (c j) (100 * Δ * ρ (c j)))
    (hdisj : (J : Set ι).PairwiseDisjoint fun j => ball (c j) (Δ * ρ (c j) / 3)) (p : M)
    (hsec : ∀ j ∈ J, (S j ∩ ball p (10 * ρ p)).Nonempty →
      ∀ y ∈ ball (c j) (4 * (10 + 2 * (100 * Δ) + Δ / 3) * ρ (c j)),
        SectionalBoundedBelowAt (I := I) g y
          (-(4 * (10 + 2 * (100 * Δ) + Δ / 3) * ρ (c j))⁻¹ ^ 2)) :
    ({j | j ∈ J ∧ (S j ∩ ball p (10 * ρ p)).Nonempty}.ncard : ℝ) ≤
      modelVolume (-(1 ^ 2)) (Module.finrank ℝ E) (4 * (10 + 2 * 100 + 1 / 3)) /
        modelVolume (-(1 ^ 2)) (Module.finrank ℝ E) (1 / 3) := by
  have hmax : max 10 (100 * Δ) = 100 * Δ := max_eq_right (by linarith)
  exact fc08_count_of_sectional g hEnorm J c S hρ hρpos hΔ (by norm_num)
    (by rw [hmax]; exact hbudget) le_rfl (by linarith) hS hdisj p hsec

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
