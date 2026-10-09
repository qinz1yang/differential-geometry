import DifferentialGeometry.Geometry.Comparison.FiniteSoul.ClosedGeodesicCircle

/-!
# Consumers of SA1 / SA2

* `nonempty_homeomorph_addCircle_of_closedGeodesic`: a set that is the trace of a closed unit
  geodesic injective on `[0, ℓ)` (the circle case of S-SHAPE2 / S-SOUL2) is homeomorphic to
  `AddCircle ℓ`.
* `geodesicFlow_ne_self_of_lt_period`: no return in phase space before time `ℓ`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Metric
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.FiniteSoul

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {r : ℕ∞}

/-- The trace of a closed unit geodesic, injective on one period, is a topological circle. -/
theorem nonempty_homeomorph_addCircle_of_closedGeodesic
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {C : Set M} {p : TangentBundle I M} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hunit : g.inner p.proj p.snd p.snd = 1) (hper : g.geodesicFlow p ℓ = p)
    (hinj : InjOn (fun t => (g.geodesicFlow p t).proj) (Ico 0 ℓ))
    (hC : C = range (fun t => (g.geodesicFlow p t).proj)) :
    Nonempty (C ≃ₜ AddCircle ℓ) := by
  have : Fact (0 < ℓ) := ⟨hℓ⟩
  obtain ⟨e, -⟩ := exists_homeomorph_addCircle_range_geodesicFlow g hr hnorm hunit hper hinj
  subst hC
  exact ⟨e.symm⟩

/-- No return of the orbit before time `ℓ`. -/
theorem geodesicFlow_ne_self_of_lt_period
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {p : TangentBundle I M} {ℓ : ℝ} (hℓ : 0 < ℓ) (hper : g.geodesicFlow p ℓ = p)
    (hinj : InjOn (fun t => (g.geodesicFlow p t).proj) (Ico 0 ℓ)) {T : ℝ} (hT0 : 0 < T)
    (hTℓ : T < ℓ) : g.geodesicFlow p T ≠ p := by
  intro h
  obtain ⟨k, hk⟩ := (geodesicFlow_eq_self_iff_of_closed g hr hnorm hℓ hper hinj).1 h
  have h1 : (0 : ℝ) < k := by
    by_contra hle
    push Not at hle
    nlinarith
  have h2 : (k : ℝ) < 1 := by
    by_contra hle
    push Not at hle
    nlinarith
  have h3 : (0 : ℤ) < k := by exact_mod_cast h1
  have h4 : k < (1 : ℤ) := by exact_mod_cast h2
  omega

end DifferentialGeometry.Geometry.FiniteSoul
