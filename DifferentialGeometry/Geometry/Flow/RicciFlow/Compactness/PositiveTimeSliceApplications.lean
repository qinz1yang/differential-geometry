import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.PositiveTimeSlice

/-!
# Consumers of LFR50 part D on closed 3-manifolds

Concrete consumers of `Estimates/Shi/PositiveTimeUniform.lean` and `Compactness/PositiveTimeSlice.lean`
for a sequence of Ricci flows on one closed connected 3-manifold `M` modelled on
`EuclideanSpace ℝ (Fin 3)`, with the part-B bounds (`T < τ n`, `|Rm| ≤ B` on `[0, T]`) and initial
metrics uniformly bilipschitz to one fixed metric (the part-A interface):

* `threeManifold_curvDerivNorm_le_at_half_time`: every `|∇^m Rm|` at `T/2` is bounded by
  `shiCompleteGlobalBound 3 m · B · (1/√(T/4) + √B)^m`, for every flow of the sequence;
* `exists_canonical_metric_compactness_of_threeManifold_slices`: the canonical bounded-geometry
  compactness supplier applies to the time-`T/2` slices.
-/

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞ M] [T2Space M] [CompactSpace M]
  [ConnectedSpace M]

private local instance threeSpaceFinrankNeZero :
    NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) :=
  ⟨by simp⟩

omit [ConnectedSpace M] in
/-- On a closed 3-manifold, the time-`T/2` slice of every flow of the sequence has
`|∇^m Rm| ≤ shiCompleteGlobalBound 3 m · B · (1/√(T/4) + √B)^m`. -/
theorem threeManifold_curvDerivNorm_le_at_half_time
    (gSeq : ℕ → SmoothRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) M)
    (T B : ℝ) (hT : 0 < T) (hB : 0 < B)
    (τ : ℕ → ℝ) (hτ : ∀ n, T < τ n)
    (F : (n : ℕ) → FlowTo (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) (M := M) (gSeq n) (τ n))
    (hcurv : ∀ n t, t ∈ Icc 0 T → ∀ x : M,
      Real.sqrt (DifferentialGeometry.Tensor0SBundle.normSq0S
        ((F n).S.base.metric t) x 4
        (metricRm04 ((F n).S.base.metric t) x)) ≤ B)
    (m n : ℕ) (x : M) :
    curvDerivNorm m ((F n).S.base.metric (T / 2)) x ≤
      shiCompleteGlobalBound 3 m * B * (1 / Real.sqrt (T / 4) + Real.sqrt B) ^ m := by
  have h := curvDerivNorm_le_of_flowTo_curvature_bound (F n) hT hB (hτ n)
    (fun t ht y => hcurv n t ht y) m (T / 2) ⟨le_rfl, by linarith⟩ x
  simpa only [finrank_euclideanSpace, Fintype.card_fin] using h

/-- On a closed connected 3-manifold, the time-`T/2` slices of a sequence of Ricci flows with the
part-B bounds, starting from metrics uniformly bilipschitz to one fixed metric, have a canonical
metric compact limit (reference metric = limit metric, connected limit). -/
theorem exists_canonical_metric_compactness_of_threeManifold_slices
    (gSeq : ℕ → SmoothRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) M)
    (T B : ℝ) (hT : 0 < T) (hB : 0 < B)
    (τ : ℕ → ℝ) (hτ : ∀ n, T < τ n)
    (F : (n : ℕ) → FlowTo (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) (M := M) (gSeq n) (τ n))
    (hcurv : ∀ n t, t ∈ Icc 0 T → ∀ x : M,
      Real.sqrt (DifferentialGeometry.Tensor0SBundle.normSq0S
        ((F n).S.base.metric t) x 4
        (metricRm04 ((F n).S.base.metric t) x)) ≤ B)
    (gRef : SmoothRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) M) {Λ : ℝ} (hΛ : 0 < Λ)
    (hbil : ∀ n (x : M) (w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) x),
      (gSeq n).inner x w w ≤ Λ * gRef.inner x w w ∧ gRef.inner x w w ≤ Λ * (gSeq n).inner x w w)
    (p : M) :
    ∃ P : MetricCompactLimit (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))
        (pointedMetricSeq p fun n => (F n).S.base.metric (T / 2)),
      (∀ k : ℕ, P.convergence.metrics.domain k =
        CanonicalMetricCompactness.canonicalSourceData P.maps k) ∧
      (let _ : TopologicalSpace P.limit.M := P.limit.topology
       ConnectedSpace P.limit.M) := by
  obtain ⟨hcomplete, hconnected, ⟨hgeom⟩, ⟨hinj⟩⟩ :=
    positiveTimeSlice_canonical_compactness_hypotheses_of_bilipschitz gSeq T B hT hB τ hτ F
      hcurv gRef hΛ hbil p
  obtain ⟨P, hdomain, -, hlimit⟩ := exists_canonical_metric_compactness_of_boundedGeometry
    (pointedMetricSeq p fun n => (F n).S.base.metric (T / 2)) hcomplete hconnected hgeom hinj
  exact ⟨P, hdomain, hlimit⟩

end DifferentialGeometry.PDE.RicciFlow
