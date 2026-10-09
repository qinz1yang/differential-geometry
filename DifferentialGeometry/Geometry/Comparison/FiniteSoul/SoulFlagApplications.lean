import DifferentialGeometry.Geometry.Comparison.FiniteSoul.SoulFlag

/-!
# Consumers of SOUL3 (CMS3-REL, G4)

* `exists_finite_soul_strict_outward_dim_three`: the three-dimensional instance (LFR45's "dimension at
  most two"): the soul of a complete noncompact connected `3`-manifold with `sec ≥ 0` is a compact
  connected totally convex totally geodesic `C^r` slice without relative boundary of relative dimension
  `≤ 2`, with strict outward directions off it.
* `exists_finite_soul_strict_outward_dim_two`-shaped consequence (`finrank = 2`): relative dimension
  `≤ 1` (a point or a closed geodesic, as in CMS-C's S-SOUL2).
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.FiniteSoul

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {r : ℕ∞}

/-- **SOUL3 in dimension three**: the soul has relative dimension at most two. -/
theorem exists_finite_soul_strict_outward_dim_three [NoncompactSpace M] [ConnectedSpace M]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 3 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂)
    (hdim : Module.finrank ℝ E = 3) :
    ∃ S : Set M, S.Nonempty ∧ IsCompact S ∧ IsConnected S ∧ IsTotallyConvexFinite g S ∧
      IsEmbeddedSliceOfOrder I (r : ℕ∞ω) (maxSliceDimOfOrder I (r : ℕ∞ω) S) S ∧
      relBoundaryOfOrder I (r : ℕ∞ω) S = ∅ ∧ maxSliceDimOfOrder I (r : ℕ∞ω) S ≤ 2 ∧
      IsTotallyGeodesicFinite g S ∧
      ∀ q ∉ S, ∃ v : E, g.inner q v v = 1 ∧
        ∀ u ∈ g.finiteMinimizingDirectionsTo S q, g.inner q v u < 0 := by
  have : NeZero (Module.finrank ℝ E) := ⟨by rw [hdim]; norm_num⟩
  obtain ⟨S, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := exists_finite_soul_strict_outward g hr hnorm hsec
  exact ⟨S, h1, h2, h3, h4, h5, h6, by omega, h8, h9⟩

/-- **SOUL3 in dimension two**: the soul has relative dimension at most one. -/
theorem exists_finite_soul_strict_outward_dim_le_one [NoncompactSpace M] [ConnectedSpace M]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 3 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂)
    (hdim : Module.finrank ℝ E = 2) :
    ∃ S : Set M, S.Nonempty ∧ IsCompact S ∧ IsTotallyConvexFinite g S ∧
      relBoundaryOfOrder I (r : ℕ∞ω) S = ∅ ∧ maxSliceDimOfOrder I (r : ℕ∞ω) S ≤ 1 ∧
      ∀ q ∉ S, ∃ v : E, g.inner q v v = 1 ∧
        ∀ u ∈ g.finiteMinimizingDirectionsTo S q, g.inner q v u < 0 := by
  have : NeZero (Module.finrank ℝ E) := ⟨by rw [hdim]; norm_num⟩
  obtain ⟨S, h1, h2, -, h4, -, h6, h7, -, h9⟩ := exists_finite_soul_strict_outward g hr hnorm hsec
  exact ⟨S, h1, h2, h4, h6, by omega, h9⟩

end DifferentialGeometry.Geometry.FiniteSoul

end
