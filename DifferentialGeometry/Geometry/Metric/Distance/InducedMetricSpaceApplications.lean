import DifferentialGeometry.Geometry.Metric.Distance.InducedMetricSpace
import DifferentialGeometry.Geometry.Comparison.Volume.RicciScaleMultiplicity

/-!
# Consumer of the induced metric: the Ricci-scale cover on an actual manifold

`exists_finite_scale_cover_of_ricci_bound` (`Geometry/Comparison/Volume/RicciScaleMultiplicity.lean`)
is stated for a manifold that already carries a `MetricSpace` structure together with
`RiemannianBundle`, `IsRiemannianManifold` and `IsContinuousRiemannianBundle` instances and the
compatibility `IsMetricNorm g`. Here its whole instance block is discharged on a compact connected
boundaryless manifold with its given topology and an arbitrary smooth Riemannian metric `g`, using
only `inducedMetricSpace g` and the bundle `⟨g.toRiemannianMetric⟩`.

* `exists_finite_scale_cover_of_ricci_bound_induced`: the cover, with the Lipschitz and Ricci
  hypotheses phrased through `riemannianEDistOf g` / `riemannianBallOf g`, conclusion in the
  metric balls of `inducedMetricSpace g`.
* `exists_finite_scale_cover_of_ricci_bound_riemannianBallOf`: the same with every ball a `g`-ball,
  so that no metric structure appears in the statement.
* `exists_finite_uniform_cover_of_ricci_bound`: the constant-scale special case.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped ContDiff ENNReal NNReal Manifold Topology

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space (TangentBundle I M)]
  [T3Space M] [ConnectedSpace M] [CompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

/-- `exists_finite_scale_cover_of_ricci_bound` on a compact connected boundaryless manifold with an
arbitrary smooth metric `g`, for the metric induced by `g`. -/
theorem exists_finite_scale_cover_of_ricci_bound_induced
    (g : SmoothRiemannianMetric I M) (S : Set M) {ρ : M → ℝ} {Λ : ℝ≥0} {Δ C q : ℝ}
    (hρ : ∀ p p' : M, |ρ p - ρ p'| ≤ Λ * (riemannianEDistOf (I := I) g p p').toReal)
    (hρpos : ∀ p, 0 < ρ p)
    (hΔ : 0 < Δ) (hC : 0 ≤ C) (hq : 0 ≤ q)
    (hselection : (Λ : ℝ) * Δ ≤ 1 / 100) (hoverlap : (Λ : ℝ) * C ≤ 1 / 4)
    (hRic : ∀ p ∈ S, ricciBoundedBelowOn (I := I) g
      (riemannianBallOf g p ((3 * C + 2 * (Δ / 3)) * ρ p))
      (((Module.finrank ℝ E - 1 : ℕ) : ℝ) * (-((q / ρ p) ^ 2)))) :
    letI := inducedMetricSpace g
    ∃ J : Set M, J ⊆ S ∧ J.Finite ∧ J.PairwiseDisjoint (fun p => Metric.ball p (Δ * ρ p / 3)) ∧
      (∀ p ∈ S, ∃ i ∈ J, Metric.ball p (Δ * ρ p) ⊆ Metric.ball i (2 * Δ * ρ i)) ∧
      ∀ x : M, ((J ∩ {i | x ∈ Metric.ball i (C * ρ i)}).ncard : ℝ) ≤
        modelVolume (-(q ^ 2)) (Module.finrank ℝ E) (3 * C + 2 * (Δ / 3)) /
          modelVolume (-(q ^ 2)) (Module.finrank ℝ E) (Δ / 3) := by
  let := inducedMetricSpace g
  let : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  obtain ⟨hRM, hEnorm, hcont⟩ := inducedMetricSpace_riemannian g
  have := hRM
  have := hcont
  have hLip : LipschitzWith Λ ρ := inducedMetricSpace_lipschitzWith_iff.2 hρ
  have hRic' : ∀ p ∈ S, ricciBoundedBelowOn (I := I) g
      (Metric.ball p ((3 * C + 2 * (Δ / 3)) * ρ p))
      (((Module.finrank ℝ E - 1 : ℕ) : ℝ) * (-((q / ρ p) ^ 2))) := by
    intro p hp
    rw [inducedMetricSpace_ball g]
    exact hRic p hp
  exact exists_finite_scale_cover_of_ricci_bound g hEnorm S hLip hρpos hΔ hC hq hselection
    hoverlap hRic'

/-- The cover of `exists_finite_scale_cover_of_ricci_bound_induced` with every ball a `g`-ball:
no metric structure occurs in the statement. -/
theorem exists_finite_scale_cover_of_ricci_bound_riemannianBallOf
    (g : SmoothRiemannianMetric I M) (S : Set M) {ρ : M → ℝ} {Λ : ℝ≥0} {Δ C q : ℝ}
    (hρ : ∀ p p' : M, |ρ p - ρ p'| ≤ Λ * (riemannianEDistOf (I := I) g p p').toReal)
    (hρpos : ∀ p, 0 < ρ p)
    (hΔ : 0 < Δ) (hC : 0 ≤ C) (hq : 0 ≤ q)
    (hselection : (Λ : ℝ) * Δ ≤ 1 / 100) (hoverlap : (Λ : ℝ) * C ≤ 1 / 4)
    (hRic : ∀ p ∈ S, ricciBoundedBelowOn (I := I) g
      (riemannianBallOf g p ((3 * C + 2 * (Δ / 3)) * ρ p))
      (((Module.finrank ℝ E - 1 : ℕ) : ℝ) * (-((q / ρ p) ^ 2)))) :
    ∃ J : Set M, J ⊆ S ∧ J.Finite ∧
      J.PairwiseDisjoint (fun p => riemannianBallOf g p (Δ * ρ p / 3)) ∧
      (∀ p ∈ S, ∃ i ∈ J, riemannianBallOf g p (Δ * ρ p) ⊆ riemannianBallOf g i (2 * Δ * ρ i)) ∧
      ∀ x : M, ((J ∩ {i | x ∈ riemannianBallOf g i (C * ρ i)}).ncard : ℝ) ≤
        modelVolume (-(q ^ 2)) (Module.finrank ℝ E) (3 * C + 2 * (Δ / 3)) /
          modelVolume (-(q ^ 2)) (Module.finrank ℝ E) (Δ / 3) := by
  have h := exists_finite_scale_cover_of_ricci_bound_induced g S hρ hρpos hΔ hC hq hselection
    hoverlap hRic
  simp only [inducedMetricSpace_ball g] at h
  exact h

/-- Constant scale: on a compact connected boundaryless manifold with `Ric ≥ -(n-1) q² / R²`,
finitely many `g`-balls of radius `Δ R` centred in `S` cover `S` up to doubling, their thirds are
disjoint, and every point lies in at most the model-volume ratio of the balls of radius `C R`. -/
theorem exists_finite_uniform_cover_of_ricci_bound
    (g : SmoothRiemannianMetric I M) (S : Set M) {R Δ C q : ℝ} (hR : 0 < R)
    (hΔ : 0 < Δ) (hC : 0 ≤ C) (hq : 0 ≤ q)
    (hRic : ricciBoundedBelowOn (I := I) g univ
      (((Module.finrank ℝ E - 1 : ℕ) : ℝ) * (-((q / R) ^ 2)))) :
    ∃ J : Set M, J ⊆ S ∧ J.Finite ∧
      J.PairwiseDisjoint (fun p => riemannianBallOf g p (Δ * R / 3)) ∧
      (∀ p ∈ S, ∃ i ∈ J, riemannianBallOf g p (Δ * R) ⊆ riemannianBallOf g i (2 * Δ * R)) ∧
      ∀ x : M, ((J ∩ {i | x ∈ riemannianBallOf g i (C * R)}).ncard : ℝ) ≤
        modelVolume (-(q ^ 2)) (Module.finrank ℝ E) (3 * C + 2 * (Δ / 3)) /
          modelVolume (-(q ^ 2)) (Module.finrank ℝ E) (Δ / 3) :=
  exists_finite_scale_cover_of_ricci_bound_riemannianBallOf (ρ := fun _ => R) (Λ := 0) g S
    (fun _ _ => by simp) (fun _ => hR) hΔ hC hq (by simp) (by simp)
    (fun _ _ => ricciBoundedBelowOn_mono (subset_univ _) hRic)

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison

end
