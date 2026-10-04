import DifferentialGeometry.Geometry.Comparison.FiniteSoul.SoulStrictOutward
import DifferentialGeometry.Geometry.Comparison.FiniteSoul.ClosedGeodesicTube

/-!
# Consumers of the arc layer, the strict-outward kernel and SA3–SA5

* `exists_finite_soul_strict_outward_of_interior_eq_empty`: when the minimum set
  `C₀ = {rayExhaustion o ≤ 0}` of the convex exhaustion has empty interior, the S-SOUL2 conclusion
  holds with no shaving (`hr : 2 ≤ r`, no use of boundary concavity);
* `closedGeodesic_soul_isConnected_isCompact_charts`: the circle soul is a compact, connected trace
  with local arc charts of the right length at every parameter (SA3–SA5 + CMS-T compactness).
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Metric Filter Topology
open scoped Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry.Geometry.FiniteSoul

open DifferentialGeometry.Geometry.Topology (rayExhaustion rayExhaustion_self)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {r : ℕ∞}

/-- **Consumer (S-SOUL2 without shaving).** If the minimum set of the convex exhaustion has empty
interior, it contains a soul with strict outward unit vectors at every other point of `M`. -/
theorem exists_finite_soul_strict_outward_of_interior_eq_empty
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂)
    (hdim : Module.finrank ℝ E = 2) (o : M)
    (hint : interior {x : M | rayExhaustion o x ≤ 0} = ∅) :
    ∃ S : Set M, S.Nonempty ∧ IsCompact S ∧ IsTotallyConvexFinite g S ∧
      ((∃ x, S = {x}) ∨
        ∃ (p : TangentBundle I M) (ℓ : ℝ), 0 < ℓ ∧ g.inner p.proj p.snd p.snd = 1 ∧
          g.geodesicFlow p ℓ = p ∧ InjOn (fun t => (g.geodesicFlow p t).proj) (Ico 0 ℓ) ∧
          S = range (fun t => (g.geodesicFlow p t).proj)) ∧
      ∀ q ∉ S, ∃ v : E, g.inner q v v = 1 ∧
        ∀ u ∈ g.finiteMinimizingDirectionsTo S q, g.inner q v u < 0 := by
  have : ProperSpace M := Manifold.properSpace_of_isRiemannianManifold I
  obtain ⟨hC₀c, hC₀conv⟩ := isCompact_isTotallyConvexFinite_rayExhaustion_sublevel g hr hnorm hsec o 0
  have hne : ({x : M | rayExhaustion o x ≤ 0} : Set M).Nonempty :=
    ⟨o, by change rayExhaustion o o ≤ 0; rw [rayExhaustion_self]⟩
  exact exists_soul_of_layer_dim_two g hr hnorm hsec hdim o hC₀c hne hC₀conv hint subset_rfl
    fun _ _ _ _ q hq hq' => absurd hq hq'

omit [NeZero (Module.finrank ℝ E)] in
/-- **Consumer (SA3–SA5).** A closed unit geodesic of least period `ℓ` has a compact connected
trace, unit speed, and a local arc chart of length `ℓ` around every parameter. -/
theorem closedGeodesic_soul_isConnected_isCompact_charts
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {p : TangentBundle I M} {ℓ : ℝ} (hℓ : 0 < ℓ) (hunit : g.inner p.proj p.snd p.snd = 1)
    (hper : g.geodesicFlow p ℓ = p)
    (hinj : InjOn (fun t => (g.geodesicFlow p t).proj) (Ico 0 ℓ)) :
    IsConnected (range (fun t => (g.geodesicFlow p t).proj)) ∧
      IsCompact (range (fun t => (g.geodesicFlow p t).proj)) ∧
      (∀ t, g.inner (g.geodesicFlow p t).proj (g.geodesicFlow p t).snd
        (g.geodesicFlow p t).snd = 1) ∧
      ∀ t₀ : ℝ, IsOpenEmbedding (fun t : Ioo (t₀ - ℓ / 2) (t₀ - ℓ / 2 + ℓ) =>
        (⟨(g.geodesicFlow p t).proj, mem_range_self (t : ℝ)⟩ :
          range (fun t => (g.geodesicFlow p t).proj))) :=
  ⟨isConnected_range_proj_geodesicFlow g hr hnorm p,
    isCompact_range_geodesicFlow g (one_le_two.trans hr)
      (Bundle.ContMDiffRiemannianMetric.geodesicFlowDomain_eq_univ g hr hnorm) hℓ hper,
    inner_snd_geodesicFlow_eq_one g hr hnorm hunit,
    fun t₀ => isOpenEmbedding_restrict_proj_geodesicFlow g hr hnorm hℓ hunit hper hinj (t₀ - ℓ / 2)⟩

end DifferentialGeometry.Geometry.FiniteSoul
