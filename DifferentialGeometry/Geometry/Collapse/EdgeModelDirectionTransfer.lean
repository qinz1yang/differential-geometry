import DifferentialGeometry.Geometry.Geodesic.Convergence.FiniteDirectionNeighbourhood
import DifferentialGeometry.Geometry.Collapse.EdgeNearestDirections
import DifferentialGeometry.Geometry.Exponential.FiniteMetric.SmoothDirections
import DifferentialGeometry.Geometry.Comparison.FiniteMetric.RiemannianHinge

/-!
# LFR26: comparison of inward directions without an exact set limit (modulo LFR14 data)

Blueprint LFR26 (`lem:collapse-edge-model-direction-transfer`, master207A:27079–27149); statement
frozen by lane F8-NEW2 (sheet-F8-NEW2.md §3), the coarse-border charts unbundled as in LFR25's kernel.
The product `N = ℝ × Z` enters through a metric isometry `Φ : N ≃ᵢ ℓ²(ℝ × W)` with `Φ q = (0, z₀)`;
`r(x) = d_W((Φ x).2, z₀)` and the axis is `Φ⁻¹(ℝ × {z₀})`.

* `exists_mem_finiteMinimizingDirectionsTo_singleton_of_riemannianEDistOf`,
  `one_add_inner_le_of_finite_nearest_direction`: the source side (LFR25's hinge) for a complete smooth
  metric carrying its distance, in the finite-direction vocabulary of LC50′;
* `infDist_axis_eq`, `dist_snd_le_of_withLp`: the axis distance in the metric product;
* `eventually_inverse_nearest_directions_close_radial` (**LFR26**): on the collar
  `|t| ≤ 10Δ`, `5Δ/2 ≤ r ≤ 13Δ/2`, for every `c > 40 √(h + τ)`, eventually EVERY pulled-back source
  nearest-set direction and EVERY radial inward direction of the model satisfy
  `‖d(j i)⁻¹ v_i − v‖_G ≤ c`.

Route (A:27100–27149), by contradiction on a bad sequence: LFR25's outward points `y_i` and arbitrary
minimizing arms; their lifts converge by the compact-endpoint LC50′; the radial directions converge by
`G`-unit compactness and the closed graph CM3.b; the source hinge bounds `‖v_i + w_i‖²`, the model hinge
with `sec ≥ 0` (CM5.b) bounds `‖v + w‖²` through `d(o, y) ≥ r(y)` for every axis point `o`; for
`h + τ ≥ 1/400` the bound is the trivial `‖u − v‖ ≤ 2 < c`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Riemannian.Geodesic

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.MetricSmoothing
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.Geometry.Comparison.Toponogov
open GC.MetricGeometry

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

section Metric

variable {W : Type*} [MetricSpace W]

/-- In the `ℓ²` product the second factor is `1`-Lipschitz. -/
theorem dist_snd_le_of_withLp (f g : WithLp 2 (ℝ × W)) : dist f.snd g.snd ≤ dist f g := by
  rw [dist_withLp_two_prod]
  exact Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg (dist f.fst g.fst)])

/-- In the `ℓ²` product the first factor is `1`-Lipschitz. -/
theorem dist_fst_le_of_withLp (f g : WithLp 2 (ℝ × W)) : dist f.fst g.fst ≤ dist f g := by
  rw [dist_withLp_two_prod]
  exact Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg (dist f.snd g.snd)])

variable {N : Type*} [MetricSpace N]

/-- The distance to the axis `Φ⁻¹(ℝ × {z₀})` is `d_W((Φ x).2, z₀)`. -/
theorem infDist_axis_eq (Φ : N ≃ᵢ WithLp 2 (ℝ × W)) (z₀ : W) (x : N) :
    infDist x (Φ ⁻¹' {z | z.snd = z₀}) = dist (Φ x).snd z₀ := by
  set o : N := Φ.symm (WithLp.toLp 2 ((Φ x).fst, z₀)) with ho
  have hoS : o ∈ Φ ⁻¹' {z | z.snd = z₀} := by
    simp only [mem_preimage, mem_ofPred_eq, ho, Φ.apply_symm_apply, WithLp.toLp_snd]
  have hxo : dist x o = dist (Φ x).snd z₀ := by
    have hΦx : Φ x = WithLp.toLp 2 ((Φ x).fst, (Φ x).snd) := rfl
    rw [ho, ← Φ.dist_eq, Φ.apply_symm_apply, hΦx, dist_withLp_two_prod]
    simp only [WithLp.toLp_fst, WithLp.toLp_snd, dist_self]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add]
    exact Real.sqrt_sq dist_nonneg
  refine le_antisymm (hxo ▸ infDist_le_dist_of_mem hoS) ?_
  refine (le_infDist ⟨o, hoS⟩).mpr fun P hP => ?_
  have h := dist_snd_le_of_withLp (Φ x) (Φ P)
  rw [Φ.dist_eq] at h
  have hP' : (Φ P).snd = z₀ := hP
  rwa [hP'] at h

/-- The axis distance `r(x) = d_W((Φ x).2, z₀)` is `1`-Lipschitz. -/
theorem lipschitzWith_axisDist (Φ : N ≃ᵢ WithLp 2 (ℝ × W)) (z₀ : W) :
    LipschitzWith 1 (fun x : N => dist (Φ x).snd z₀) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [NNReal.coe_one, one_mul, Real.dist_eq]
  have h := dist_snd_le_of_withLp (Φ x) (Φ y)
  rw [Φ.dist_eq] at h
  exact (abs_dist_sub_le _ _ _).trans h

/-- The height coordinate `t(x) = (Φ x).1` is `1`-Lipschitz. -/
theorem lipschitzWith_heightCoord (Φ : N ≃ᵢ WithLp 2 (ℝ × W)) :
    LipschitzWith 1 (fun x : N => (Φ x).fst) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [NNReal.coe_one, one_mul]
  have h := dist_fst_le_of_withLp (Φ x) (Φ y)
  rwa [Φ.dist_eq] at h

/-- Distance to the base point `q` with `Φ q = (0, z₀)`: `d(x, q) ≤ |t(x)| + r(x)`. -/
theorem dist_le_abs_fst_add_axisDist (Φ : N ≃ᵢ WithLp 2 (ℝ × W)) {q : N} {z₀ : W}
    (hΦq : Φ q = WithLp.toLp 2 ((0 : ℝ), z₀)) (x : N) :
    dist x q ≤ |(Φ x).fst| + dist (Φ x).snd z₀ := by
  rw [← Φ.dist_eq, hΦq, dist_withLp_two_prod]
  simp only [WithLp.toLp_fst, WithLp.toLp_snd, Real.dist_eq, sub_zero]
  refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
  nlinarith [sq_abs (Φ x).fst, mul_nonneg (abs_nonneg (Φ x).fst) (dist_nonneg (x := (Φ x).snd) (y := z₀))]

/-- The axis `Φ⁻¹(ℝ × {z₀})` is closed. -/
theorem isClosed_axis (Φ : N ≃ᵢ WithLp 2 (ℝ × W)) (z₀ : W) :
    IsClosed (Φ ⁻¹' {z | z.snd = z₀}) := by
  have hS' : Φ ⁻¹' {z | z.snd = z₀} = {x : N | dist (Φ x).snd z₀ = 0} := by
    ext x
    simp only [mem_preimage, mem_ofPred_eq, dist_eq_zero]
  rw [hS']
  exact isClosed_eq (lipschitzWith_axisDist Φ z₀).continuous continuous_const

end Metric

section Algebra

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {N : Type*} [MetricSpace N] [ChartedSpace H N] [IsManifold I ∞ N]

theorem inner_add_self_eq_finite {n : ℕ∞ω}
    (G : ContMDiffRiemannianMetric I n E (TangentSpace I : N → Type _)) (x : N)
    (a b : TangentSpace I x) :
    G.inner x (a + b) (a + b) = G.inner x a a + 2 * G.inner x a b + G.inner x b b := by
  simp only [map_add, add_apply]
  rw [G.symm x b a]
  ring

theorem inner_sub_self_eq_finite {n : ℕ∞ω}
    (G : ContMDiffRiemannianMetric I n E (TangentSpace I : N → Type _)) (x : N)
    (a b : TangentSpace I x) :
    G.inner x (a - b) (a - b) = G.inner x a a - 2 * G.inner x a b + G.inner x b b := by
  simp only [map_sub, sub_apply]
  rw [G.symm x b a]
  ring

theorem abs_inner_le_one_of_unit_finite {n : ℕ∞ω}
    (G : ContMDiffRiemannianMetric I n E (TangentSpace I : N → Type _)) (x : N)
    {a b : TangentSpace I x} (ha : G.inner x a a = 1) (hb : G.inner x b b = 1) :
    |G.inner x a b| ≤ 1 := by
  have h1 := finite_inner_self_nonneg G x (a + b)
  have h2 := finite_inner_self_nonneg G x (a - b)
  rw [inner_add_self_eq_finite] at h1
  rw [inner_sub_self_eq_finite] at h2
  rw [abs_le]
  constructor <;> linarith

end Algebra

section Source

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M' : Type*} [MetricSpace M'] [ChartedSpace H M'] [IsManifold I ∞ M'] [CompleteSpace M']

section Bundle

variable [RiemannianBundle (fun z : M' => TangentSpace I z)] [IsRiemannianManifold I M']
  [IsContinuousRiemannianBundle E (fun z : M' => TangentSpace I z)]

private theorem one_add_inner_le_of_finite_nearest_direction_aux (g : SmoothRiemannianMetric I M')
    (hEnorm : DifferentialGeometry.Geometry.Riemannian.IsMetricNorm g)
    {p x y : M'} {A : Set M'} {k R : ℝ} (hk : 0 < k)
    (hsec : ∀ z ∈ ball p R, SectionalBoundedBelowAt g z (-k ^ 2))
    (ha : 0 < infDist x A) (hℓ : 0 < dist x y)
    (hR : dist x p + 2 * infDist x A + dist x y < R)
    {v w : TangentSpace I x}
    (hv : v ∈ ContMDiffRiemannianMetric.finiteMinimizingDirectionsTo g A x)
    (hw : w ∈ ContMDiffRiemannianMetric.finiteMinimizingDirectionsTo g {y} x) :
    1 + g.inner x v w ≤ Real.cosh (k * (infDist x A + dist x y)) *
      (infDist x A + dist x y - infDist y A) * (infDist x A + dist x y) /
        (infDist x A * dist x y) := by
  have : ProperSpace M' := Manifold.properSpace_of_isRiemannianManifold I
  have hv' : v ∈ DifferentialGeometry.Geometry.Topology.minimizingDirectionsTo g hEnorm A x := by
    rw [ContMDiffRiemannianMetric.minimizingDirectionsTo_eq_setOf_expMap g hEnorm A x]
    exact hv
  have hw' : w ∈ inwardMinimizingDirections (I := I) g hEnorm y x := by
    refine (ContMDiffRiemannianMetric.mem_inwardMinimizingDirections_iff_expMap hEnorm).mpr
      ⟨hw.1, ?_⟩
    have h := hw.2
    rwa [infDist_singleton, mem_singleton_iff, dist_comm] at h
  exact one_add_inner_le_of_nearest_direction g hEnorm hk hsec ha hℓ hR hv' hw'

end Bundle

/-- A complete smooth metric carrying the distance of `M'` (T0's convention, no bundle instances)
has a minimizing unit direction from `x` to any `y`. -/
theorem exists_mem_finiteMinimizingDirectionsTo_singleton_of_riemannianEDistOf
    (g : SmoothRiemannianMetric I M')
    (hmetric : ∀ a b : M', riemannianEDistOf g a b = ENNReal.ofReal (dist a b)) (x y : M') :
    ∃ w : TangentSpace I x, w ∈ ContMDiffRiemannianMetric.finiteMinimizingDirectionsTo g {y} x := by
  let hRB : RiemannianBundle (fun z : M' => TangentSpace I z) := ⟨g.toRiemannianMetric⟩
  have hRM : IsRiemannianManifold I M' := ⟨fun a b => by
    change edist a b = riemannianEDistOf g a b
    rw [edist_dist, hmetric]⟩
  exact (@ContMDiffRiemannianMetric.finiteMinimizingDirectionsTo_nonempty_isCompact _ _ _ _ _ _ _ _
    _ _ _ _ _ hRB hRM ⊤ _ g le_top (isMetricNorm_of_riemannianBundle g) _ isClosed_singleton
    (singleton_nonempty y) x).1

/-- **Source hinge (LFR25) in the finite-direction vocabulary.** For a complete smooth metric
carrying the distance of `M'` (no bundle instances), `sec ≥ -k²` on `B(p, R)` and
`d(x,p) + 2 d_A(x) + d(x,y) < R`: every nearest direction `v` to `A` and every minimizing unit
direction `w` from `x` to `y` satisfy
`1 + g(v, w) ≤ cosh (k (a + ℓ)) (a + ℓ - d_A(y)) (a + ℓ) / (a ℓ)`. -/
theorem one_add_inner_le_of_finite_nearest_direction (g : SmoothRiemannianMetric I M')
    (hmetric : ∀ a b : M', riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
    {p x y : M'} {A : Set M'} {k R : ℝ} (hk : 0 < k)
    (hsec : ∀ z ∈ ball p R, SectionalBoundedBelowAt g z (-k ^ 2))
    (ha : 0 < infDist x A) (hℓ : 0 < dist x y)
    (hR : dist x p + 2 * infDist x A + dist x y < R)
    {v w : TangentSpace I x}
    (hv : v ∈ ContMDiffRiemannianMetric.finiteMinimizingDirectionsTo g A x)
    (hw : w ∈ ContMDiffRiemannianMetric.finiteMinimizingDirectionsTo g {y} x) :
    1 + g.inner x v w ≤ Real.cosh (k * (infDist x A + dist x y)) *
      (infDist x A + dist x y - infDist y A) * (infDist x A + dist x y) /
        (infDist x A * dist x y) := by
  let hRB : RiemannianBundle (fun z : M' => TangentSpace I z) := ⟨g.toRiemannianMetric⟩
  have hRM : IsRiemannianManifold I M' := ⟨fun a b => by
    change edist a b = riemannianEDistOf g a b
    rw [edist_dist, hmetric]⟩
  have hcont : IsContinuousRiemannianBundle E (fun z : M' => TangentSpace I z) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  exact @one_add_inner_le_of_finite_nearest_direction_aux _ _ _ _ _ _ _ _ _ _ _ _ _ _ hRB hRM hcont
    g (isMetricNorm_of_riemannianBundle g) _ _ _ _ _ _ hk hsec ha hℓ hR _ _ hv hw

/-- **Source pair bound (LFR25 numerics).** At a point `x` with `62Δ/25 ≤ d_A(x) ≤ 7Δ`,
`d(x, p) < 18Δ`, an outward point `y` with LFR25.3's bounds, `0 ≤ τ < 1/400`,
`sec ≥ -k²` on `B(p, 1000Δ)` and `kΔ ≤ 1/100`: every nearest direction `v` to `A` and every
minimizing unit direction `w` from `x` to `y` satisfy `|v + w|²_g ≤ 49 τ`. -/
theorem inner_add_le_of_coarseBorder_outward (g : SmoothRiemannianMetric I M')
    (hmetric : ∀ a b : M', riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
    {p x y : M'} {A : Set M'} {Δ τ k : ℝ} (hΔ : 0 < Δ) (hτ : 0 ≤ τ) (hτs : τ < 1 / 400)
    (hk : 0 < k) (hkΔ : k * Δ ≤ 1 / 100)
    (hsec : ∀ z ∈ ball p (1000 * Δ), SectionalBoundedBelowAt g z (-k ^ 2))
    (hxp : dist x p < 18 * Δ) (halo : 62 / 25 * Δ ≤ infDist x A) (haup : infDist x A ≤ 7 * Δ)
    (hy1 : |dist x y - infDist x A| ≤ 4 * (τ * Δ))
    (hy2 : |infDist y A - 2 * infDist x A| ≤ 7 * (τ * Δ))
    {v w : TangentSpace I x}
    (hv : v ∈ ContMDiffRiemannianMetric.finiteMinimizingDirectionsTo g A x)
    (hw : w ∈ ContMDiffRiemannianMetric.finiteMinimizingDirectionsTo g {y} x) :
    g.inner x (v + w) (v + w) ≤ 49 * τ := by
  set a := infDist x A with ha_def
  set ℓ := dist x y with hℓ_def
  have h1 := abs_le.mp hy1
  have h5 := abs_le.mp hy2
  have hτΔ0 : 0 ≤ τ * Δ := by positivity
  have hτΔs : τ * Δ ≤ Δ / 400 := by nlinarith
  have ha24 : 12 / 5 * Δ ≤ a := by linarith
  have hℓ24 : 12 / 5 * Δ ≤ ℓ := by linarith
  have hℓup : ℓ ≤ 8 * Δ := by linarith
  have ha0 : 0 < a := by linarith
  have hℓ0 : 0 < ℓ := by linarith
  have hexc : a + ℓ - infDist y A ≤ 11 * (τ * Δ) := by linarith
  have hexc0 : 0 ≤ a + ℓ - infDist y A := by
    have h6 := infDist_le_infDist_add_dist (x := y) (y := x) (s := A)
    rw [dist_comm] at h6
    linarith
  have hR : dist x p + 2 * a + ℓ < 1000 * Δ := by linarith
  have hhinge := one_add_inner_le_of_finite_nearest_direction g hmetric hk hsec ha0 hℓ0 hR hv hw
  have hkt0 : 0 ≤ k * (a + ℓ) := by positivity
  have hkt : k * (a + ℓ) ≤ 1 := by
    have : k * (a + ℓ) ≤ k * (15 * Δ) := mul_le_mul_of_nonneg_left (by linarith) hk.le
    linarith
  have hcosh : Real.cosh (k * (a + ℓ)) ≤ 2 := by
    have h7 := Real.cosh_sub_one_le_sq hkt0 hkt
    nlinarith
  have hcosh0 : 0 ≤ Real.cosh (k * (a + ℓ)) := (Real.cosh_pos _).le
  have hQ : (a + ℓ) / (a * ℓ) ≤ 5 / (6 * Δ) := by
    rw [div_le_div_iff₀ (mul_pos ha0 hℓ0) (by positivity)]
    nlinarith [mul_nonneg (sub_nonneg.mpr ha24) (sub_nonneg.mpr hℓ24)]
  have hQ0 : 0 ≤ (a + ℓ) / (a * ℓ) := by positivity
  have hprod : Real.cosh (k * (a + ℓ)) * (a + ℓ - infDist y A) * (a + ℓ) / (a * ℓ) ≤
      2 * (11 * (τ * Δ)) * (5 / (6 * Δ)) := by
    rw [mul_div_assoc]
    exact mul_le_mul (mul_le_mul hcosh hexc hexc0 (by norm_num)) hQ hQ0 (by positivity)
  have hval : 2 * (11 * (τ * Δ)) * (5 / (6 * Δ)) = 55 / 3 * τ := by
    field_simp
    ring
  rw [inner_add_self_eq_finite g x v w, hv.1, hw.1]
  linarith

end Source


section Row

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {N : Type*} [MetricSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  {M : ℕ → Type*} [∀ i, MetricSpace (M i)] [∀ i, ChartedSpace H (M i)]
  [∀ i, IsManifold I ∞ (M i)]
  [ProperSpace N] [RiemannianBundle (fun x : N => TangentSpace I x)] [IsRiemannianManifold I N]


/-- **Model pair bound (nonnegative hinge, CM5.b).** In a complete `C^{r+1}` metric (`2 ≤ r`) with
`sec ≥ 0` carrying the distance of `N`, with a metric product structure `Φ`: if `v` is a minimizing
unit direction from `x` to the axis `Φ⁻¹(ℝ × {z₀})`, `w` one from `x` to `y`, `r(x), d(x,y) ≥ 12Δ/5`
and `r(x) + d(x, y) - r(y) ≤ 23 s Δ`, then `|v + w|²_G ≤ 49 s`. The comparison uses only
`d(o, y) ≥ r(y)` for the axis endpoint `o` of the radial arm. -/
theorem inner_add_le_of_axis_hinge [CompleteSpace N] {r : ℕ∞} (hr : 2 ≤ r)
    (G : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : N → Type _))
    (hGnorm : ∀ (x : N) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (G.inner x w w)))
    (hGsec : ∀ (y : N) (w₁ w₂ : TangentSpace I y), 0 ≤ G.sectionalCurvature y w₁ w₂)
    {W : Type*} [MetricSpace W] (Φ : N ≃ᵢ WithLp 2 (ℝ × W)) (z₀ : W) {x y : N}
    {v w : TangentSpace I x}
    (hv : v ∈ G.finiteMinimizingDirectionsTo (Φ ⁻¹' {z | z.snd = z₀}) x)
    (hw : w ∈ G.finiteMinimizingDirectionsTo {y} x) {Δ s : ℝ} (hΔ : 0 < Δ) (hs : 0 ≤ s)
    (hrx : 12 / 5 * Δ ≤ dist (Φ x).snd z₀) (hℓ : 12 / 5 * Δ ≤ dist x y)
    (hδ : dist (Φ x).snd z₀ + dist x y - dist (Φ y).snd z₀ ≤ 23 * s * Δ) :
    G.inner x (v + w) (v + w) ≤ 49 * s := by
  have hr1 : 1 ≤ r := one_le_two.trans hr
  set r0 := dist (Φ x).snd z₀ with hr0def
  set ℓ0 := dist x y with hℓ0def
  have hinf : infDist x (Φ ⁻¹' {z | z.snd = z₀}) = r0 := infDist_axis_eq Φ z₀ x
  have hP := hv.2
  rw [hinf] at hP
  set P := G.expMap (⟨x, r0 • v⟩ : TangentBundle I N) with hPdef
  have hr0p : 0 < r0 := by linarith
  have hℓ0p : 0 < ℓ0 := by linarith
  have hxP : dist x P = r0 := by
    refine le_antisymm ?_ (hinf ▸ infDist_le_dist_of_mem hP)
    have h := G.dist_expMap_smul_le_of_completeSpace hr1 hGnorm v 0 r0
    rw [zero_smul, G.expMap_zero hr1 x, hv.1, Real.sqrt_one, one_mul, sub_zero,
      abs_of_pos hr0p] at h
    exact h
  have hend : G.expMap (⟨x, ℓ0 • w⟩ : TangentBundle I N) = y := by
    have h := hw.2
    rwa [infDist_singleton, mem_singleton_iff] at h
  have hminB : dist x (G.expMap (⟨x, ℓ0 • w⟩ : TangentBundle I N)) = ℓ0 := by rw [hend]
  have hhinge : comparisonAngle r0 ℓ0 (dist P y) ≤ Real.arccos (G.inner x v w) := by
    have h := DifferentialGeometry.Geometry.FiniteComparison.comparisonAngle_le_arccos_inner_finite
      G hr1 hGnorm x v w hr0p hℓ0p hv.1 hw.1 hxP hminB hGsec
    convert h using 3
    · rfl
    · exact hend.symm
  set D := dist P y with hD
  have hD1 : D ≤ r0 + ℓ0 := by
    have := dist_triangle P x y
    rw [dist_comm P x] at this
    linarith
  have hD2 : |r0 - ℓ0| ≤ D := by
    rw [abs_le]
    constructor
    · have := dist_triangle x P y
      linarith
    · have := dist_triangle x y P
      rw [dist_comm y P] at this
      linarith
  have hDr : dist (Φ y).snd z₀ ≤ D := by
    have h := dist_snd_le_of_withLp (Φ P) (Φ y)
    rw [Φ.dist_eq] at h
    have hPz : (Φ P).snd = z₀ := hP
    rw [hPz, dist_comm] at h
    exact h
  have hcc := comparison_cosine_mem_Icc hr0p hℓ0p hD2 hD1
  have hGvw := abs_le.mp (abs_inner_le_one_of_unit_finite G x hv.1 hw.1)
  have hcos : G.inner x v w ≤ (r0 ^ 2 + ℓ0 ^ 2 - D ^ 2) / (2 * r0 * ℓ0) := by
    have h1 := Real.cos_le_cos_of_nonneg_of_le_pi (comparisonAngle_mem_Icc _ _ _).1
      (Real.arccos_le_pi _) hhinge
    rw [Real.cos_arccos hGvw.1 hGvw.2, comparisonAngle, Real.cos_arccos hcc.1 hcc.2] at h1
    exact h1
  rw [le_div_iff₀ (by positivity)] at hcos
  have hδ' : r0 + ℓ0 - D ≤ 23 * s * Δ := by linarith
  have hD0 : 0 ≤ D := dist_nonneg
  have hprod : (r0 + ℓ0 - D) * (r0 + ℓ0 + D) ≤ (23 * s * Δ) * (2 * (r0 + ℓ0)) :=
    mul_le_mul hδ' (by linarith) (by linarith) (by positivity)
  have h1 : r0 * ℓ0 * (1 + G.inner x v w) ≤ 23 * s * Δ * (r0 + ℓ0) := by nlinarith
  have h2 : 6 * Δ * (r0 + ℓ0) ≤ 5 * (r0 * ℓ0) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hrx) (sub_nonneg.mpr hℓ)]
  have h3 : (r0 * ℓ0) * (6 * (1 + G.inner x v w)) ≤ (r0 * ℓ0) * (115 * s) := by
    nlinarith [mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 23 * s)]
  have h4 : 6 * (1 + G.inner x v w) ≤ 115 * s := le_of_mul_le_mul_left h3 (by positivity)
  rw [inner_add_self_eq_finite G x v w, hv.1, hw.1]
  linarith

/-- **LFR26: comparison of inward directions without an exact set limit** (modulo LFR14 data and a
metric product structure `Φ`, `Φ q = (0, z₀)`). Coarse-border charts `Q i` centred at `j i q` with
the SAME `Δ, τ` (LFR25.1), LFR25's curvature bound `sec ≥ -k²` on `B(j i q, 1000Δ)`, `kΔ ≤ 1/100`,
`sec_G ≥ 0`, and the height bound (LFR26.1) `limsup sup_{B(q,100Δ)} |b_i j_i - r| ≤ hΔ` give
(LFR26.2): for every `c > 40 √(h + τ)`, eventually, on the collar `|t| ≤ 10Δ`,
`5Δ/2 ≤ r ≤ 13Δ/2`, EVERY pulled-back source nearest-set direction `d(j i)⁻¹ v_i` and EVERY radial
inward direction `v` of the model satisfy `‖d(j i)⁻¹ v_i − v‖_G ≤ c`. -/
theorem eventually_inverse_nearest_directions_close_radial [∀ i, CompleteSpace (M i)]
    [CompleteSpace N] {r : ℕ∞} (hr : 2 ≤ r)
    (G : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : N → Type _))
    (hGnorm : ∀ (x : N) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (G.inner x w w)))
    (hGsec : ∀ (y : N) (w₁ w₂ : TangentSpace I y), 0 ≤ G.sectionalCurvature y w₁ w₂)
    (g : ∀ i, SmoothRiemannianMetric I (M i))
    (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
    {K : ℕ} (hK : 2 ≤ K) (q : N) (j : ∀ i, PartialDiffeomorph I I N (M i) K)
    (hexh : ∀ C : Set N, IsCompact C → ∀ᶠ i in atTop, C ⊆ (j i).source)
    (hconv : ∀ (x : N) (L : Set E), IsCompact L → L ⊆ (extChartAt I x).target →
      MapCPConvergenceOn L 1
        (fun i => pullbackMetricCoefficients (g i) ((j i : N → M i) ∘ (extChartAt I x).symm))
        (chartCoeff G x))
    (hdist : ∀ R ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ x ∈ ball q R, ∀ y ∈ ball q R,
      |dist (j i x) (j i y) - dist x y| < ε)
    (hcover : ∀ a b : ℝ, 0 < a → a < b → ∀ᶠ i in atTop,
      ball (j i q) a ⊆ (j i : N → M i) '' ball q b)
    {W : Type*} [MetricSpace W] (Φ : N ≃ᵢ WithLp 2 (ℝ × W)) {z₀ : W}
    (hΦq : Φ q = WithLp.toLp 2 ((0 : ℝ), z₀))
    {Δ τ k h : ℝ} (hΔ : 0 < Δ) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) (hk : 0 < k) (hkΔ : k * Δ ≤ 1 / 100)
    (hh : 0 < h) (hh1 : h < 1 / 100)
    (Q : ∀ i, M i → WithLp 2 (ℝ × ℝ)) (A : ∀ i, Set (M i))
    (hQp : ∀ i, Q i (j i q) = 0)
    (hQdist : ∀ i, ∀ x ∈ ball (j i q) (200 * Δ), ∀ y ∈ ball (j i q) (200 * Δ),
      |dist (Q i x) (Q i y) - dist x y| ≤ τ * Δ)
    (hheight : ∀ i, ∀ x ∈ ball (j i q) (200 * Δ), 0 ≤ (Q i x).snd)
    (hQcover : ∀ i, ∀ z : WithLp 2 (ℝ × ℝ), |z.fst| ≤ 100 * Δ → z.snd ∈ Icc 0 (100 * Δ) →
      ∃ x ∈ ball (j i q) (200 * Δ), dist (Q i x) z ≤ τ * Δ)
    (hpA : ∀ i, j i q ∈ A i)
    (hborder : ∀ i, ∀ a ∈ A i ∩ ball (j i q) (190 * Δ), (Q i a).snd ≤ τ * Δ)
    (hbordercover : ∀ i, ∀ t : ℝ, |t| ≤ 100 * Δ →
      ∃ a ∈ A i ∩ ball (j i q) (190 * Δ), dist (Q i a) (WithLp.toLp 2 (t, (0 : ℝ))) ≤ τ * Δ)
    (hsec : ∀ i, letI : RiemannianBundle (fun x : M i => TangentSpace I x) :=
        ⟨(g i).toRiemannianMetric⟩
      ∀ z ∈ ball (j i q) (1000 * Δ), DifferentialGeometry.Geometry.Riemannian.SectionalBoundedBelowAt
        (g i) z (-k ^ 2))
    (hhgt : ∀ h' : ℝ, h < h' → ∀ᶠ i in atTop, ∀ x ∈ ball q (100 * Δ),
      |(Q i (j i x)).snd - dist (Φ x).snd z₀| ≤ h' * Δ) :
    ∀ c : ℝ, 40 * Real.sqrt (h + τ) < c → ∀ᶠ i in atTop, ∀ x : N,
      |(Φ x).fst| ≤ 10 * Δ → 5 / 2 * Δ ≤ dist (Φ x).snd z₀ → dist (Φ x).snd z₀ ≤ 13 / 2 * Δ →
      ∀ vi ∈ ContMDiffRiemannianMetric.finiteMinimizingDirectionsTo (g i) (A i) (j i x),
      ∀ v ∈ G.finiteMinimizingDirectionsTo (Φ ⁻¹' {z | z.snd = z₀}) x,
        let u : TangentSpace I x := mfderiv I I ((j i).symm : M i → N) (j i x) vi
        G.inner x (u - v) (u - v) ≤ c ^ 2 := by
  intro c hc
  have hr1 : 1 ≤ r := one_le_two.trans hr
  have hK1 : 1 ≤ K := by omega
  have hhτ : 0 < h + τ := by linarith
  set S : Set N := Φ ⁻¹' {z | z.snd = z₀} with hSdef
  have hrrc : Continuous (fun x : N => dist (Φ x).snd z₀) := (lipschitzWith_axisDist Φ z₀).continuous
  have hSc : IsClosed S := isClosed_axis Φ z₀
  set h' : ℝ := 2 * h + τ with hh'
  have hhh' : h < h' := by linarith
  have hF : ∀ᶠ i in atTop, closedBall q (17 * Δ) ⊆ (j i).source ∧
      (∀ x ∈ ball q (18 * Δ), ∀ y ∈ ball q (18 * Δ), |dist (j i x) (j i y) - dist x y| < Δ) ∧
      (∀ x ∈ ball q (100 * Δ), |(Q i (j i x)).snd - dist (Φ x).snd z₀| ≤ h' * Δ) ∧
      ball (j i q) (70 * Δ) ⊆ (j i : N → M i) '' ball q (71 * Δ) :=
    (hexh _ (isCompact_closedBall q _)).and ((hdist (18 * Δ) Δ hΔ).and ((hhgt h' hhh').and
      (hcover (70 * Δ) (71 * Δ) (by positivity) (by linarith))))
  by_contra hbad
  rw [Filter.not_eventually] at hbad
  obtain ⟨ψ, hψ, hψbad⟩ := Filter.extraction_of_frequently_atTop (hbad.and_eventually hF)
  have hψt := hψ.tendsto_atTop
  choose hneg hfact using hψbad
  simp only [not_forall, not_le, exists_prop] at hneg
  choose x hxt hxr1 hxr2 vi hvi v hv hbadk using hneg
  -- per-index facts
  have hq18 : q ∈ ball q (18 * Δ) := mem_ball_self (by positivity)
  have hxq : ∀ k, x k ∈ closedBall q (17 * Δ) := fun k => by
    rw [mem_closedBall]
    have := dist_le_abs_fst_add_axisDist Φ hΦq (x k)
    linarith [hxt k, hxr2 k]
  have hx18 : ∀ k, x k ∈ ball q (18 * Δ) := fun k => by
    have := hxq k
    rw [mem_closedBall] at this
    rw [mem_ball]
    linarith
  have hx100 : ∀ k, x k ∈ ball q (100 * Δ) := fun k => by
    have := hx18 k
    rw [mem_ball] at this ⊢
    linarith
  have hxsrc : ∀ k, x k ∈ (j (ψ k)).source := fun k => (hfact k).1 (hxq k)
  have hjx : ∀ k, dist (j (ψ k) (x k)) (j (ψ k) q) < 18 * Δ := fun k => by
    have h1 := (abs_lt.mp ((hfact k).2.1 (x k) (hx18 k) q hq18)).2
    have h2 := hxq k
    rw [mem_closedBall] at h2
    linarith
  have hjx70 : ∀ k, j (ψ k) (x k) ∈ ball (j (ψ k) q) (70 * Δ) := fun k => by
    rw [mem_ball]; linarith [hjx k]
  have hjx30 : ∀ k, j (ψ k) (x k) ∈ ball (j (ψ k) q) (30 * Δ) := fun k => by
    rw [mem_ball]; linarith [hjx k]
  have hb : ∀ k, |(Q (ψ k) (j (ψ k) (x k))).snd - dist (Φ (x k)).snd z₀| ≤ h' * Δ :=
    fun k => (hfact k).2.2.1 (x k) (hx100 k)
  have ha : ∀ k, |infDist (j (ψ k) (x k)) (A (ψ k)) - (Q (ψ k) (j (ψ k) (x k))).snd| ≤
      2 * (τ * Δ) := fun k =>
    coarseBorder_abs_infDist_sub_height_le hΔ hτ1 (hQp _) (hQdist _) (hheight _) (hpA _)
      (hborder _) (hbordercover _) (hjx70 k)
  have hτΔ : τ * Δ ≤ Δ := by nlinarith
  have hA12 : ∀ k, infDist (j (ψ k) (x k)) (A (ψ k)) ≤ 12 * Δ := fun k => by
    have h1 := (abs_le.mp (ha k)).2
    have h2 := (abs_le.mp (hb k)).2
    have h3 := hxr2 k
    have h4 : h' * Δ ≤ 3 * Δ := by nlinarith
    linarith
  have hout : ∀ k, ∃ y ∈ ball (j (ψ k) q) (70 * Δ),
      |dist (j (ψ k) (x k)) y - infDist (j (ψ k) (x k)) (A (ψ k))| ≤ 4 * (τ * Δ) ∧
      |infDist y (A (ψ k)) - 2 * infDist (j (ψ k) (x k)) (A (ψ k))| ≤ 7 * (τ * Δ) := fun k =>
    exists_coarseBorder_outward_point hΔ hτ1 (hQp _) (hQdist _) (hheight _) (hQcover _) (hpA _)
      (hborder _) (hbordercover _) (hjx30 k) (hA12 k)
  choose y hyb hy1 hy2 using hout
  have hlift : ∀ k, ∃ yt ∈ ball q (71 * Δ), j (ψ k) yt = y k := fun k => (hfact k).2.2.2 (hyb k)
  choose yt hyt hjyt using hlift
  have harm : ∀ k, ∃ w : TangentSpace I (j (ψ k) (x k)),
      w ∈ ContMDiffRiemannianMetric.finiteMinimizingDirectionsTo (g (ψ k)) {j (ψ k) (yt k)}
        (j (ψ k) (x k)) := fun k =>
    exists_mem_finiteMinimizingDirectionsTo_singleton_of_riemannianEDistOf (g (ψ k)) (hmetric _) _ _
  choose w hw using harm
  have hbY : ∀ k, |(Q (ψ k) (y k)).snd - dist (Φ (yt k)).snd z₀| ≤ h' * Δ := fun k => by
    have h1 := (hfact k).2.2.1 (yt k) (by have := hyt k; rw [mem_ball] at this ⊢; linarith)
    rwa [hjyt k] at h1
  have haY : ∀ k, |infDist (y k) (A (ψ k)) - (Q (ψ k) (y k)).snd| ≤ 2 * (τ * Δ) := fun k =>
    coarseBorder_abs_infDist_sub_height_le hΔ hτ1 (hQp _) (hQdist _) (hheight _) (hpA _)
      (hborder _) (hbordercover _) (hyb k)
  -- the three scalar inequalities used in the limit
  have hP1 : ∀ k, dist (j (ψ k) (x k)) (y k) ≤ dist (Φ (x k)).snd z₀ + (h' + 6 * τ) * Δ ∧
      dist (Φ (x k)).snd z₀ - (h' + 6 * τ) * Δ ≤ dist (j (ψ k) (x k)) (y k) := fun k => by
    have h1 := abs_le.mp (hy1 k)
    have h2 := abs_le.mp (ha k)
    have h3 := abs_le.mp (hb k)
    constructor <;> nlinarith
  have hP2 : ∀ k, 2 * dist (Φ (x k)).snd z₀ - (3 * h' + 13 * τ) * Δ ≤ dist (Φ (yt k)).snd z₀ :=
    fun k => by
    have h1 := abs_le.mp (hy2 k)
    have h2 := abs_le.mp (ha k)
    have h3 := abs_le.mp (hb k)
    have h4 := abs_le.mp (hbY k)
    have h5 := abs_le.mp (haY k)
    nlinarith
  -- extraction: source nearest directions, radial directions, outward arms
  have hC17 : IsCompact (closedBall q (17 * Δ)) := isCompact_closedBall q _
  obtain ⟨U, -, hUunit, φ₁, hφ₁, hU⟩ := exists_subseq_tendsto_inverse_unit_finite
    (M := fun k => M (ψ k)) hr1 G (fun k => g (ψ k)) hK1 (fun k => j (ψ k))
    (fun C hC => hψt.eventually (hexh C hC)) (fun z L hL hLt => (hconv z L hL hLt).comp_subseq hψ)
    hC17 x hxq vi (fun k => (hvi k).1)
  obtain ⟨xI, uI⟩ := U
  have hx₁ : Tendsto (fun k => x (φ₁ k)) atTop (𝓝 xI) :=
    ((FiberBundle.continuous_proj E (TangentSpace I)).tendsto _).comp hU
  obtain ⟨vI, φ₂, hφ₂, hV⟩ := exists_subseq_tendsto_tangentBundle_of_inner_le hr1 G hx₁
    (fun k => v (φ₁ k)) (B := 1) (fun k => (hv _).1.le)
  have hψ₂ : StrictMono (fun k => ψ (φ₁ (φ₂ k))) := hψ.comp (hφ₁.comp hφ₂)
  obtain ⟨yI, -, vw, -, hvwdir, -, φ₃, hφ₃, hyconv, hW⟩ :=
    exists_subseq_minimizing_direction_limit_finite_of_isCompact
      (M := fun k => M (ψ (φ₁ (φ₂ k)))) hr1 G hGnorm (fun k => g (ψ (φ₁ (φ₂ k))))
      (fun k => hmetric _) hK q (fun k => j (ψ (φ₁ (φ₂ k))))
      (fun C hC => hψ₂.tendsto_atTop.eventually (hexh C hC))
      (fun z L hL hLt => (hconv z L hL hLt).comp_subseq hψ₂)
      (fun R ε hε => hψ₂.tendsto_atTop.eventually (hdist R ε hε))
      (fun a b ha hab => hψ₂.tendsto_atTop.eventually (hcover a b ha hab))
      hC17 (fun k => x (φ₁ (φ₂ k))) (fun k => hxq _) (isCompact_closedBall q (71 * Δ))
      (fun k => yt (φ₁ (φ₂ k))) (fun k => ball_subset_closedBall (hyt _))
      (fun k => w (φ₁ (φ₂ k))) (fun k => hw _)
  obtain ⟨xw, wI⟩ := vw
  set ι : ℕ → ℕ := fun k => φ₁ (φ₂ (φ₃ k)) with hι
  have hι' : StrictMono ι := hφ₁.comp (hφ₂.comp hφ₃)
  have hψι : StrictMono (fun k => ψ (ι k)) := hψ.comp hι'
  have hxι : Tendsto (fun k => x (ι k)) atTop (𝓝 xI) := hx₁.comp (hφ₂.comp hφ₃).tendsto_atTop
  have hxw : xw = xI := by
    have h1 := ((FiberBundle.continuous_proj E (TangentSpace I)).tendsto _).comp hW
    exact tendsto_nhds_unique h1 hxι
  subst hxw
  have hUι : Tendsto (fun k => (⟨x (ι k), mfderiv I I ((j (ψ (ι k))).symm : M (ψ (ι k)) → N)
      (j (ψ (ι k)) (x (ι k))) (vi (ι k))⟩ : TangentBundle I N)) atTop (𝓝 ⟨xw, uI⟩) :=
    hU.comp (hφ₂.comp hφ₃).tendsto_atTop
  have hVι : Tendsto (fun k => (⟨x (ι k), v (ι k)⟩ : TangentBundle I N)) atTop (𝓝 ⟨xw, vI⟩) :=
    hV.comp hφ₃.tendsto_atTop
  have hWι : Tendsto (fun k => (⟨x (ι k), mfderiv I I ((j (ψ (ι k))).symm : M (ψ (ι k)) → N)
      (j (ψ (ι k)) (x (ι k))) (w (ι k))⟩ : TangentBundle I N)) atTop (𝓝 ⟨xw, wI⟩) := hW
  have hyι : Tendsto (fun k => yt (ι k)) atTop (𝓝 yI) := hyconv
  -- scalar limits
  have hrxlim : Tendsto (fun k => dist (Φ (x (ι k))).snd z₀) atTop (𝓝 (dist (Φ xw).snd z₀)) :=
    (hrrc.tendsto _).comp hxι
  have hrylim : Tendsto (fun k => dist (Φ (yt (ι k))).snd z₀) atTop (𝓝 (dist (Φ yI).snd z₀)) :=
    (hrrc.tendsto _).comp hyι
  have hdxy : Tendsto (fun k => dist (x (ι k)) (yt (ι k))) atTop (𝓝 (dist xw yI)) :=
    hxι.dist hyι
  have hdiff : Tendsto (fun k => dist (j (ψ (ι k)) (x (ι k))) (y (ι k)) -
      dist (x (ι k)) (yt (ι k))) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨k₁, hk₁⟩ := eventually_atTop.mp (hψι.tendsto_atTop.eventually (hdist (72 * Δ) ε hε))
    refine ⟨k₁, fun k hk => ?_⟩
    have hxk : x (ι k) ∈ ball q (72 * Δ) := by
      have := hx18 (ι k); rw [mem_ball] at this ⊢; linarith
    have hyk : yt (ι k) ∈ ball q (72 * Δ) := by
      have := hyt (ι k); rw [mem_ball] at this ⊢; linarith
    have h1 := hk₁ k hk (x (ι k)) hxk (yt (ι k)) hyk
    rw [hjyt] at h1
    rwa [Real.dist_eq, sub_zero]
  have hℓlim : Tendsto (fun k => dist (j (ψ (ι k)) (x (ι k))) (y (ι k))) atTop
      (𝓝 (dist xw yI)) := by
    have h := hdiff.add hdxy
    rw [zero_add] at h
    exact h.congr fun k => by ring
  have hℓup : dist xw yI ≤ dist (Φ xw).snd z₀ + (h' + 6 * τ) * Δ :=
    le_of_tendsto_of_tendsto' hℓlim (hrxlim.add_const _) fun k => (hP1 (ι k)).1
  have hℓlo : dist (Φ xw).snd z₀ - (h' + 6 * τ) * Δ ≤ dist xw yI :=
    le_of_tendsto_of_tendsto' (hrxlim.sub_const _) hℓlim fun k => (hP1 (ι k)).2
  have hrylo : 2 * dist (Φ xw).snd z₀ - (3 * h' + 13 * τ) * Δ ≤ dist (Φ yI).snd z₀ :=
    le_of_tendsto_of_tendsto' ((hrxlim.const_mul 2).sub_const _) hrylim fun k => hP2 (ι k)
  have hrx1 : 5 / 2 * Δ ≤ dist (Φ xw).snd z₀ := ge_of_tendsto' hrxlim fun k => hxr1 (ι k)
  have hrx2 : dist (Φ xw).snd z₀ ≤ 13 / 2 * Δ := le_of_tendsto' hrxlim fun k => hxr2 (ι k)
  -- the limit of the bad quantity
  have hsubι := tendsto_tangentBundle_sub hUι hVι
  have hGbad := tendsto_inner_of_tendsto_tangentBundle hr1 G hsubι hsubι
  have hge : c ^ 2 ≤ G.inner xw (uI - vI) (uI - vI) :=
    ge_of_tendsto' hGbad fun k => (hbadk (ι k)).le
  -- norms on the limit fibre
  have hnorm : ∀ a : TangentSpace I xw, ‖a‖ = Real.sqrt (G.inner xw a a) := fun a => by
    have h1 := hGnorm xw a
    rw [← ofReal_norm] at h1
    exact (ENNReal.ofReal_eq_ofReal_iff (norm_nonneg _) (Real.sqrt_nonneg _)).mp h1
  have hc0 : 0 < c := lt_of_le_of_lt (by positivity) hc
  have hvS : vI ∈ G.finiteMinimizingDirectionsTo S xw :=
    ContMDiffRiemannianMetric.mem_finiteMinimizingDirectionsTo_of_tendsto G hr hGnorm hSc
      (p := fun k => (⟨x (ι k), v (ι k)⟩ : TangentBundle I N)) (fun k => hv (ι k)) hVι
  have huunit : G.inner xw uI uI = 1 := hUunit
  have hlt : ‖uI - vI‖ < c := by
    have hvunit : G.inner xw vI vI = 1 := hvS.1
    by_cases hbig : 1 / 400 ≤ h + τ
    · have h20 : 1 / 20 ≤ Real.sqrt (h + τ) := Real.le_sqrt_of_sq_le (by norm_num; linarith)
      have hu1 : ‖uI‖ = 1 := by rw [hnorm, huunit, Real.sqrt_one]
      have hv1 : ‖vI‖ = 1 := by rw [hnorm, hvunit, Real.sqrt_one]
      calc ‖uI - vI‖ ≤ ‖uI‖ + ‖vI‖ := norm_sub_le _ _
        _ = 2 := by rw [hu1, hv1]; norm_num
        _ < c := by linarith
    have hbig' : h + τ < 1 / 400 := lt_of_not_ge hbig
    have hτs : τ < 1 / 400 := by linarith
    have hτΔs : τ * Δ ≤ Δ / 400 := by nlinarith
    have hhΔs : h * Δ ≤ Δ / 400 := by nlinarith
    have hh'Δ : h' * Δ = 2 * (h * Δ) + τ * Δ := by rw [hh']; ring
    have hτΔ0 : 0 ≤ τ * Δ := by positivity
    have hhΔ0 : 0 ≤ h * Δ := by positivity
    -- source estimate at every index, transferred to the limit
    have hsrck : ∀ k, (g (ψ k)).inner (j (ψ k) (x k)) (vi k + w k) (vi k + w k) ≤ 49 * τ :=
      fun k => by
      have h2 := abs_le.mp (ha k)
      have h3 := abs_le.mp (hb k)
      have hwk : w k ∈ ContMDiffRiemannianMetric.finiteMinimizingDirectionsTo (g (ψ k)) {y k}
          (j (ψ k) (x k)) := by
        rw [← hjyt k]
        exact hw k
      exact inner_add_le_of_coarseBorder_outward (g (ψ k)) (hmetric _) hΔ hτ hτs hk hkΔ (hsec _)
        (hjx k) (by linarith [hxr1 k]) (by linarith [hxr2 k]) (hy1 k) (hy2 k) (hvi k) hwk
    have hsrc : G.inner xw (uI + wI) (uI + wI) ≤ 49 * τ := by
      have hadd := tendsto_tangentBundle_add hUι hWι
      have hT3 := tendsto_pullback_inner_of_tendsto hr1 G g hK1 j hexh hconv
        hψι.tendsto_atTop hadd hadd
      refine le_of_tendsto' hT3 fun k => ?_
      have hdj : mfderiv I I (j (ψ (ι k)) : N → M (ψ (ι k))) (x (ι k))
          (mfderiv I I ((j (ψ (ι k))).symm : M (ψ (ι k)) → N) (j (ψ (ι k)) (x (ι k)))
            (vi (ι k)) +
            mfderiv I I ((j (ψ (ι k))).symm : M (ψ (ι k)) → N) (j (ψ (ι k)) (x (ι k)))
              (w (ι k))) = vi (ι k) + w (ι k) := by
        refine (map_add (mfderiv I I (j (ψ (ι k)) : N → M (ψ (ι k))) (x (ι k))) _ _).trans ?_
        rw [mfderiv_apply_mfderiv_symm_of_mem_source hK1 (j (ψ (ι k))) (hxsrc (ι k)),
          mfderiv_apply_mfderiv_symm_of_mem_source hK1 (j (ψ (ι k))) (hxsrc (ι k))]
      convert hsrck (ι k) using 3 <;> exact hdj
    -- model estimate at the limit
    have hmod : G.inner xw (vI + wI) (vI + wI) ≤ 49 * (h + τ) := by
      have e1 : (h' + 6 * τ) * Δ = 2 * (h * Δ) + 7 * (τ * Δ) := by rw [hh']; ring
      have e2 : (3 * h' + 13 * τ) * Δ = 6 * (h * Δ) + 16 * (τ * Δ) := by rw [hh']; ring
      have e3 : 23 * (h + τ) * Δ = 23 * (h * Δ) + 23 * (τ * Δ) := by ring
      exact inner_add_le_of_axis_hinge hr G hGnorm hGsec Φ z₀ hvS hvwdir hΔ hhτ.le
        (by linarith) (by linarith) (by linarith)
    have hsq7 : Real.sqrt 49 = 7 := by
      rw [show (49 : ℝ) = 7 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    have hτh : Real.sqrt τ ≤ Real.sqrt (h + τ) := Real.sqrt_le_sqrt (by linarith)
    have hpos : 0 < Real.sqrt (h + τ) := Real.sqrt_pos.mpr hhτ
    calc ‖uI - vI‖ = ‖(uI + wI) - (vI + wI)‖ := by congr 1; abel
      _ ≤ ‖uI + wI‖ + ‖vI + wI‖ := norm_sub_le _ _
      _ ≤ Real.sqrt (49 * τ) + Real.sqrt (49 * (h + τ)) := by
          rw [hnorm, hnorm]
          exact add_le_add (Real.sqrt_le_sqrt hsrc) (Real.sqrt_le_sqrt hmod)
      _ ≤ 7 * Real.sqrt (h + τ) + 7 * Real.sqrt (h + τ) := by
          rw [Real.sqrt_mul (by norm_num), Real.sqrt_mul (by norm_num), hsq7]
          linarith
      _ < c := by linarith
  have hlt2 : G.inner xw (uI - vI) (uI - vI) < c ^ 2 := by
    have h1 := hnorm (uI - vI)
    have h2 : G.inner xw (uI - vI) (uI - vI) = ‖uI - vI‖ ^ 2 := by
      rw [h1, Real.sq_sqrt (finite_inner_self_nonneg G xw _)]
    rw [h2]
    exact pow_lt_pow_left₀ hlt (norm_nonneg _) two_ne_zero
  linarith

end Row

end DifferentialGeometry.Geometry.Riemannian.Geodesic
