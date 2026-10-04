import DifferentialGeometry.Geometry.Collapse.FiniteSurface.EndpointDirections
import DifferentialGeometry.Geometry.Comparison.FiniteSoul.QuantitativePatch

/-!
# LFR23 (i), (ii) and the level lemmas on an actual finite surface

Row LFR23 (`thm:collapse-finite-endpoint-disk-band`, master207A:26745). Setting: a complete
finite-order metric `g : C^{r+1}` (`2 ≤ r`), `sec ≥ 0`, a base point `z₀`, and an endpoint model
`q` on `B̄(z₀, 10)` (`q z₀ = 0`, `q ≥ 0`, distortion `≤ δ`, `δ`-dense image in `[0, 10]`); `r = d(z₀, ·)`.

* `exists_endpoint_far_segment`: the point `x⁺` (`r(x⁺) = 19/2`) on a unit segment from `z₀` (density
  at the endpoint `10`, a trimmed minimizing segment);
* `sqrt_inner_sub_lt_of_endpoint_band` (LFR23 (i)) and `inner_neg_lt_of_endpoint_band`: on the band
  `1/2 ≤ r ≤ 37/4`, any two inward unit directions are within `2√(600δ)`, and `-v` has pairing
  `< -7/8` with every inward direction;
* `exists_endpoint_field` (LFR23 (ii)): ONE smooth field `V`, `|V| < 2`, pairing `< -3/4` with EVERY
  inward direction on an open `O ⊇` band, its complete flow, the rate `3/4`, the unique continuous
  hitting time and the band product `{r = 5} × [1/2, 37/4] ≃ₜ {1/2 ≤ r ≤ 37/4}` (CMS-T's
  `exists_endpoint_band_field` with `S = {z₀}`);
* `frontier_closedBall_eq_sphere_of_flow`: `∂B̄(z₀, a) = {r = a}` inside the band (`r` increases
  along the flow);
* `isPathConnected_sphere_of_flow`: every level `{r = a}`, `a ∈ [1, 9]`, is path connected (two level
  points are `3δ`-close; project a short segment to the level by the hitting time).
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Metric Filter Topology
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Geometry.FiniteSoul

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M]
  {r : ℕ∞}

omit [SigmaCompactSpace M] in
/-- **LFR23, the far point `x⁺`.** The `δ`-dense endpoint model gives a unit segment from `z₀` of
length `19/2`, ending at `x⁺`. -/
theorem exists_endpoint_far_segment
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {z₀ : M} {q : M → ℝ} {δ : ℝ} (hδ : δ < 1 / 4) (hq0 : q z₀ = 0)
    (hqnn : ∀ y ∈ closedBall z₀ 10, 0 ≤ q y)
    (hdist : ∀ y ∈ closedBall z₀ 10, ∀ y' ∈ closedBall z₀ 10,
      |dist (q y) (q y') - dist y y'| ≤ δ)
    (hdense : ∀ t ∈ Icc (0 : ℝ) 10, ∃ y ∈ closedBall z₀ 10, |q y - t| ≤ δ) :
    ∃ u : E, g.inner z₀ u u = 1 ∧
      (∀ s ∈ Icc (0 : ℝ) (19 / 2), ∀ t ∈ Icc (0 : ℝ) (19 / 2),
        dist (g.expMap (⟨z₀, s • u⟩ : TangentBundle I M))
          (g.expMap (⟨z₀, t • u⟩ : TangentBundle I M)) = |s - t|) ∧
      g.expMap (⟨z₀, (0 : ℝ) • u⟩ : TangentBundle I M) = z₀ := by
  have hr1 : 1 ≤ r := one_le_two.trans hr
  have hD : g.geodesicFlowDomain = univ :=
    Bundle.ContMDiffRiemannianMetric.geodesicFlowDomain_eq_univ g hr hnorm
  obtain ⟨y, hyB, hqy⟩ := hdense 10 ⟨by norm_num, le_rfl⟩
  have hz₀ : z₀ ∈ closedBall z₀ 10 := mem_closedBall_self (by norm_num)
  have h1 := abs_le.mp (hdist z₀ hz₀ y hyB)
  rw [hq0, Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg (hqnn y hyB)] at h1
  have h2 := abs_le.mp hqy
  have hfar : 19 / 2 ≤ dist z₀ y := by linarith [h1.2, h2.1]
  obtain ⟨u, hu, hiso, -⟩ := Bundle.ContMDiffRiemannianMetric.exists_unit_segment_expMap g hr hnorm z₀ y
  refine ⟨u, hu, fun s hs t ht => hiso s ⟨hs.1, hs.2.trans hfar⟩ t ⟨ht.1, ht.2.trans hfar⟩, ?_⟩
  have h3 := g.expMap_smul_eq_proj_geodesicFlow hr1 z₀ u 0 (by rw [hD]; exact mem_univ _)
  rw [g.geodesicFlow_zero hr1] at h3
  exact h3

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M] [CompleteSpace M] in
/-- Membership in the inward directions: `u ∈ finiteMinimizingDirectionsTo {z₀} x` iff `u` is a unit
vector with `exp_x (d(z₀, x) u) = z₀`. -/
theorem expMap_eq_of_mem_finiteMinimizingDirectionsTo_singleton
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    {z₀ x : M} {u : TangentSpace I x} (hu : u ∈ g.finiteMinimizingDirectionsTo {z₀} x) :
    g.inner x u u = 1 ∧ g.expMap (⟨x, dist z₀ x • (u : E)⟩ : TangentBundle I M) = z₀ := by
  obtain ⟨hu1, hend⟩ := hu
  rw [infDist_singleton, dist_comm] at hend
  exact ⟨hu1, hend⟩

/-- **LFR23, the negated direction on the band** (`δ ≤ 1/9600`): at a point of `1/2 ≤ r ≤ 37/4`,
for inward unit directions `v, v'`, `g_x(-v, v') < -7/8`. -/
theorem inner_neg_lt_of_endpoint_band
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂)
    {z₀ : M} {q : M → ℝ} {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1 / 9600) (hq0 : q z₀ = 0)
    (hqnn : ∀ y ∈ closedBall z₀ 10, 0 ≤ q y)
    (hdist : ∀ y ∈ closedBall z₀ 10, ∀ y' ∈ closedBall z₀ 10,
      |dist (q y) (q y') - dist y y'| ≤ δ)
    (hdense : ∀ t ∈ Icc (0 : ℝ) 10, ∃ y ∈ closedBall z₀ 10, |q y - t| ≤ δ) {x : M}
    (hx₁ : 1 / 2 ≤ dist z₀ x) (hx₂ : dist z₀ x ≤ 37 / 4) {v v' : TangentSpace I x}
    (hv : v ∈ g.finiteMinimizingDirectionsTo {z₀} x)
    (hv' : v' ∈ g.finiteMinimizingDirectionsTo {z₀} x) :
    g.inner x (-(v : E)) v' < -(7 / 8) := by
  obtain ⟨u, -, hiso, h0⟩ := exists_endpoint_far_segment g hr hnorm (by linarith) hq0 hqnn hdist hdense
  set x' := g.expMap (⟨z₀, (19 / 2 : ℝ) • u⟩ : TangentBundle I M) with hx'def
  have hx' : dist z₀ x' = 19 / 2 := by
    have := hiso 0 ⟨le_rfl, by norm_num⟩ (19 / 2) ⟨by norm_num, le_rfl⟩
    rw [h0] at this
    rw [this]; norm_num
  obtain ⟨w, hw, -, hwx⟩ := Bundle.ContMDiffRiemannianMetric.exists_unit_segment_expMap g hr hnorm x x'
  rw [dist_comm] at hwx
  obtain ⟨hv1, hvz⟩ := expMap_eq_of_mem_finiteMinimizingDirectionsTo_singleton g hv
  obtain ⟨hv'1, hv'z⟩ := expMap_eq_of_mem_finiteMinimizingDirectionsTo_singleton g hv'
  exact inner_neg_lt_of_endpoint_finite g (one_le_two.trans hr) hnorm hsec hδ hδ' hq0 hqnn hdist hx'
    hx₁ hx₂ hv1 hv'1 hw hvz hv'z hwx

/-- **LFR23 (i): the direction diameter.** On the band `1/2 ≤ r ≤ 37/4`, two inward unit directions
are within `2√(600δ)` (`δ < 1/1000`). -/
theorem sqrt_inner_sub_lt_of_endpoint_band
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂)
    {z₀ : M} {q : M → ℝ} {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 1000) (hq0 : q z₀ = 0)
    (hqnn : ∀ y ∈ closedBall z₀ 10, 0 ≤ q y)
    (hdist : ∀ y ∈ closedBall z₀ 10, ∀ y' ∈ closedBall z₀ 10,
      |dist (q y) (q y') - dist y y'| ≤ δ)
    (hdense : ∀ t ∈ Icc (0 : ℝ) 10, ∃ y ∈ closedBall z₀ 10, |q y - t| ≤ δ) {x : M}
    (hx₁ : 1 / 2 ≤ dist z₀ x) (hx₂ : dist z₀ x ≤ 37 / 4) {v v' : TangentSpace I x}
    (hv : v ∈ g.finiteMinimizingDirectionsTo {z₀} x)
    (hv' : v' ∈ g.finiteMinimizingDirectionsTo {z₀} x) :
    Real.sqrt (g.inner x ((v : E) - v') ((v : E) - v')) < 2 * Real.sqrt (600 * δ) := by
  obtain ⟨u, -, hiso, h0⟩ := exists_endpoint_far_segment g hr hnorm (by linarith) hq0 hqnn hdist hdense
  set x' := g.expMap (⟨z₀, (19 / 2 : ℝ) • u⟩ : TangentBundle I M) with hx'def
  have hx' : dist z₀ x' = 19 / 2 := by
    have := hiso 0 ⟨le_rfl, by norm_num⟩ (19 / 2) ⟨by norm_num, le_rfl⟩
    rw [h0] at this
    rw [this]; norm_num
  obtain ⟨w, hw, -, hwx⟩ := Bundle.ContMDiffRiemannianMetric.exists_unit_segment_expMap g hr hnorm x x'
  rw [dist_comm] at hwx
  obtain ⟨hv1, hvz⟩ := expMap_eq_of_mem_finiteMinimizingDirectionsTo_singleton g hv
  obtain ⟨hv'1, hv'z⟩ := expMap_eq_of_mem_finiteMinimizingDirectionsTo_singleton g hv'
  exact sqrt_inner_sub_lt_of_endpoint_finite g (one_le_two.trans hr) hnorm hsec hδ hδ' hq0 hqnn
    hdist hx' hx₁ hx₂ hv1 hv'1 hw hvz hv'z hwx

end DifferentialGeometry.Geometry.Collapse
