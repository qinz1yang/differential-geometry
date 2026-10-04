import DifferentialGeometry.Geometry.Comparison.FiniteSoul.ShapeTwo

/-!
# Consumers of S-SHAPE2

* `range_eq_image_Icc_of_geodesicFlow_eq`: the trace of a periodic geodesic is the image of one
  period.
* `exists_eq_image_geodesicFlow_Icc_dim_two`: every compact, nonempty, totally convex set with
  empty interior in a complete surface is the trace of the geodesic flow on a compact interval
  (a point is the trace of the zero vector). This is the form in which S-SOUL2 sees a shaved
  soul: a compact geodesic trace.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Metric
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.FiniteSoul

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {r : ℕ∞}

omit [NeZero (Module.finrank ℝ E)] in
/-- The trace of a periodic geodesic of a complete finite metric is the image of one period. -/
theorem range_eq_image_Icc_of_geodesicFlow_eq
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {p : TangentBundle I M} {ℓ : ℝ} (hℓ : 0 < ℓ) (hper : g.geodesicFlow p ℓ = p) :
    range (fun t => (g.geodesicFlow p t).proj) =
      (fun t => (g.geodesicFlow p t).proj) '' Icc 0 ℓ := by
  have hr1 : 1 ≤ r := one_le_two.trans hr
  have hD : g.geodesicFlowDomain = univ :=
    Bundle.ContMDiffRiemannianMetric.geodesicFlowDomain_eq_univ g hr hnorm
  have hmem : ∀ (Q : TangentBundle I M) (τ : ℝ), (Q, τ) ∈ g.geodesicFlowDomain := fun Q τ => by
    rw [hD]; exact mem_univ _
  have hadd : ∀ (Q : TangentBundle I M) (s t : ℝ),
      g.geodesicFlow (g.geodesicFlow Q s) t = g.geodesicFlow Q (s + t) := fun Q s t =>
    (g.geodesicFlow_add hr1 (hmem Q s) (hmem Q (s + t))).symm
  have hstep : ∀ t, g.geodesicFlow p (t + ℓ) = g.geodesicFlow p t := fun t => by
    rw [add_comm t ℓ, ← hadd, hper]
  have hperZ : ∀ k : ℤ, ∀ t, g.geodesicFlow p (t + k * ℓ) = g.geodesicFlow p t := by
    intro k
    refine Int.induction_on k ?_ ?_ ?_
    · intro t; simp
    · intro i ih t
      have h3 : t + (((i : ℤ) + 1 : ℤ) : ℝ) * ℓ = (t + ((i : ℤ) : ℝ) * ℓ) + ℓ := by
        push_cast; ring
      rw [h3, hstep, ih]
    · intro i ih t
      have h3 : t + ((-(i : ℤ) - 1 : ℤ) : ℝ) * ℓ + ℓ = t + ((-(i : ℤ) : ℤ) : ℝ) * ℓ := by
        push_cast; ring
      rw [← hstep (t + ((-(i : ℤ) - 1 : ℤ) : ℝ) * ℓ), h3, ih]
  refine Subset.antisymm ?_ (image_subset_range _ _)
  rintro _ ⟨s, rfl⟩
  set k : ℤ := ⌊s / ℓ⌋ with hkdef
  have h1 : (k : ℝ) ≤ s / ℓ := Int.floor_le _
  have h2 : s / ℓ < k + 1 := Int.lt_floor_add_one _
  rw [le_div_iff₀ hℓ] at h1
  rw [div_lt_iff₀ hℓ] at h2
  refine ⟨s - k * ℓ, ⟨by linarith, by linarith⟩, ?_⟩
  change (g.geodesicFlow p (s - k * ℓ)).proj = (g.geodesicFlow p s).proj
  rw [← hperZ k (s - k * ℓ), sub_add_cancel]

/-- **Consumer of S-SHAPE2.** A compact, nonempty, totally convex set with empty interior in a
complete surface is the trace of the geodesic flow on a compact interval. -/
theorem exists_eq_image_geodesicFlow_Icc_dim_two
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hdim : Module.finrank ℝ E = 2) {C : Set M} (hCc : IsCompact C) (hCne : C.Nonempty)
    (hconv : IsTotallyConvexFinite g C) (hint : interior C = ∅) :
    ∃ (p : TangentBundle I M) (ℓ : ℝ), 0 ≤ ℓ ∧
      C = (fun t => (g.geodesicFlow p t).proj) '' Icc 0 ℓ := by
  have hr1 : 1 ≤ r := one_le_two.trans hr
  rcases totallyConvex_point_or_arc_or_closedGeodesic_dim_two g hr hnorm hdim hCc hCne hconv
      hint with ⟨x, rfl⟩ | ⟨p, ℓ, hℓ, -, -, hC⟩ | ⟨p, ℓ, hℓ, -, hper, -, hC⟩
  · refine ⟨⟨x, 0⟩, 0, le_rfl, ?_⟩
    rw [Icc_self, image_singleton]
    rw [g.geodesicFlow_zeroSection hr1]
  · exact ⟨p, ℓ, hℓ.le, hC⟩
  · exact ⟨p, ℓ, hℓ.le, hC.trans (range_eq_image_Icc_of_geodesicFlow_eq g hr hnorm hℓ hper)⟩

end DifferentialGeometry.Geometry.FiniteSoul
