import DifferentialGeometry.Geometry.Metric.Approximation.BoundedConeScale
import DifferentialGeometry.Geometry.Metric.Approximation.ConeAtInfinity
import DifferentialGeometry.Geometry.Metric.Comparison.DistanceScaling

/-!
# Riemannian bindings of LC21–LC23: metric rescaling is tensor rescaling

Blueprint 207A, LC21 (A:20789), LC22 (A:20820), LC23 (A:20853). The metric statements divide
distances by `R`; on a Riemannian manifold this is the metric tensor divided by `R²`
("The notation `R⁻¹N` divides distances by `R`; a Riemannian metric tensor is divided by `R²`").
Here the sources are smooth manifolds whose metric-space distance realizes the `g`-length
distance (`hmetric`), and the conclusions are stated for the metric rescaling on the same
carrier, together with the identity showing that its distance realizes `riemannianEDistOf` of the
scaled tensor.

* `riemannianEDistOf_scaleMetric_inv_sq_eq_rescale`: the distance of `c⁻² g` is the metric
  rescaling by `c⁻¹`.
* `eventually_riemannian_rescaled_approx_fixed_target` (LC22 binding).
* `exists_riemannian_bounded_cone_scale` (LC23 binding; the metric content of LC24 at an
  arbitrary positive scale function).
* `exists_riemannian_point_cone_of_compactSpace` (LC21 binding: compact manifolds have the point
  cone at infinity).
-/

set_option autoImplicit false

noncomputable section
open Set Filter
open scoped Manifold ContDiff ENNReal Topology
open GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

universe u w z

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

/-- The distance of the metric tensor `c⁻² g` is the rescaled distance `c⁻¹ d_g`. -/
theorem riemannianEDistOf_scaleMetric_inv_sq_eq_rescale {M : Type*} [m : MetricSpace M]
    [ChartedSpace H M] [IsManifold I ∞ M] (g : SmoothRiemannianMetric I M)
    (hmetric : ∀ a b, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
    {c : ℝ} (hc : 0 < c) (a b : M) :
    riemannianEDistOf (scaleMetric (c⁻¹ ^ 2) (pow_pos (inv_pos.mpr hc) 2) g) a b =
      ENNReal.ofReal (@dist M (m.rescale c⁻¹ (inv_pos.mpr hc)).toDist a b) := by
  rw [edistOf_scale, hmetric, MetricSpace.rescale_dist, Real.sqrt_sq (inv_pos.mpr hc).le,
    ← ENNReal.ofReal_mul (inv_pos.mpr hc).le]

/-- LC22, Riemannian binding: if Riemannian sources converge pointedly to `(N, n)` and
`(R⁻¹ N, n)` has an actual Kleiner–Lott map at the LC22 threshold to a fixed `(C, o)`, then
eventually the sources with metric tensor `R⁻² g_i` (the metric rescaling, which realizes its
distance) admit actual Kleiner–Lott `δ`-maps to the same `(C, o)`. -/
theorem eventually_riemannian_rescaled_approx_fixed_target {X : ℕ → Type u}
    [mX : ∀ i, MetricSpace (X i)] [∀ i, ChartedSpace H (X i)] [∀ i, IsManifold I ∞ (X i)]
    (g : ∀ i, SmoothRiemannianMetric I (X i))
    (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
    {N : Type w} [mN : MetricSpace N] {p : ∀ i, X i} {n : N} (h : PointedGHConverges p n)
    (R : ℝ) (hR : 0 < R) {C : Type z} [MetricSpace C] {o : C} {δ : ℝ} (hδ : 0 < δ)
    (hδone : δ < 1)
    (G : @KleinerLottApprox N C (mN.rescale R⁻¹ (inv_pos.mpr hR)) _ n o
      (min (δ / 100) (1 / (2 * (2 * (δ⁻¹ + δ) + 4))))) :
    ∀ᶠ i in atTop,
      (∀ a b, riemannianEDistOf (scaleMetric (R⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2) (g i)) a b =
        ENNReal.ofReal (@dist (X i) ((mX i).rescale R⁻¹ (inv_pos.mpr hR)).toDist a b)) ∧
      Nonempty (@KleinerLottApprox (X i) C ((mX i).rescale R⁻¹ (inv_pos.mpr hR)) _ (p i) o δ) := by
  filter_upwards [h.eventually_rescaled_approx_fixed_target R hR hδ hδone G] with i hi
  exact ⟨riemannianEDistOf_scaleMetric_inv_sq_eq_rescale (g i) (hmetric i) hR, hi⟩

/-- LC23, Riemannian binding (the metric content of LC24 at an arbitrary positive scale
function `ρ`): under the sequential model property for the normalized manifolds `ρ⁻² g` (stated
for the metric rescalings, which realize them by
`riemannianEDistOf_scaleMetric_inv_sq_eq_rescale`) and LC21 approximation clauses for the
models, every `0 < δ < 1`, `T > 0` admit `V ≥ T` and a tail on which every point has a scale
`s ∈ [T, V]`, a model index and an actual Kleiner–Lott `δ`-map from the manifold with metric
tensor `(s ρ_α(p))⁻² g_α` (its metric rescaling, which realizes that distance). -/
theorem exists_riemannian_bounded_cone_scale {M : ℕ → Type u} [mM : ∀ α, MetricSpace (M α)]
    [∀ α, ChartedSpace H (M α)] [∀ α, IsManifold I ∞ (M α)]
    (g : ∀ α, SmoothRiemannianMetric I (M α))
    (hmetric : ∀ α a b, riemannianEDistOf (g α) a b = ENNReal.ofReal (dist a b))
    (ρ : ∀ α, M α → ℝ) (hρ : ∀ α x, 0 < ρ α x)
    {ι : Type w} {N C : ι → Type z} [mN : ∀ b, MetricSpace (N b)] [mC : ∀ b, MetricSpace (C b)]
    (n : ∀ b, N b) (o : ∀ b, C b)
    (hmodel : ∀ a : ℕ → ℕ, Tendsto a atTop atTop → ∀ z : ∀ j, M (a j),
      ∃ b : ι, ∃ k : ℕ → ℕ, StrictMono k ∧
        @PointedGHConverges (fun j => M (a (k j)))
          (fun j => (mM (a (k j))).rescale (ρ (a (k j)) (z (k j)))⁻¹ (inv_pos.mpr (hρ _ _)))
          (N b) (mN b) (fun j => z (k j)) (n b))
    (hcone : ∀ b : ι, ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ R₀ : ℝ, ∀ R : ℝ, ∀ hR : 0 < R, R₀ ≤ R →
        Nonempty (@KleinerLottApprox (N b) (C b)
          ((mN b).rescale R⁻¹ (inv_pos.mpr hR)) (mC b) (n b) (o b) ε))
    {δ T : ℝ} (hδ : 0 < δ) (hδone : δ < 1) (hT : 0 < T) :
    ∃ V : ℝ, T ≤ V ∧ ∃ α₀ : ℕ, ∀ α : ℕ, α₀ < α → ∀ p : M α,
      ∃ s : ℝ, ∃ hs : 0 < s, T ≤ s ∧ s ≤ V ∧ ∃ b : ι,
        (∀ x y, riemannianEDistOf (scaleMetric ((s * ρ α p)⁻¹ ^ 2)
            (pow_pos (inv_pos.mpr (mul_pos hs (hρ α p))) 2) (g α)) x y =
          ENNReal.ofReal (@dist (M α) ((mM α).rescale (s * ρ α p)⁻¹
            (inv_pos.mpr (mul_pos hs (hρ α p)))).toDist x y)) ∧
        Nonempty (@KleinerLottApprox (M α) (C b) ((mM α).rescale (s * ρ α p)⁻¹
          (inv_pos.mpr (mul_pos hs (hρ α p)))) (mC b) p (o b) δ) := by
  obtain ⟨V, hTV, α₀, hα₀⟩ := exists_bounded_cone_scale ρ hρ n o hmodel hcone hδ hδone hT
  refine ⟨V, hTV, α₀, fun α hα p => ?_⟩
  obtain ⟨s, hs, hTs, hsV, b, hb⟩ := hα₀ α hα p
  exact ⟨s, hs, hTs, hsV, b,
    riemannianEDistOf_scaleMetric_inv_sq_eq_rescale (g α) (hmetric α) (mul_pos hs (hρ α p)), hb⟩

/-- LC21, Riemannian binding: a compact Riemannian manifold has the one-point cone at infinity;
for every `0 < ε < 1` there is `R₀` such that for `R ≥ R₀` the manifold with metric tensor
`R⁻² g` (its metric rescaling, which realizes that distance) has an actual Kleiner–Lott
`ε`-map to the point. -/
theorem exists_riemannian_point_cone_of_compactSpace {M : Type*} [m : MetricSpace M]
    [ChartedSpace H M] [IsManifold I ∞ M] [CompactSpace M] (g : SmoothRiemannianMetric I M)
    (hmetric : ∀ a b, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)) (p : M) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ R₀ : ℝ, ∀ R : ℝ, ∀ hR : 0 < R, R₀ ≤ R →
      (∀ x y, riemannianEDistOf (scaleMetric (R⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2) g) x y =
        ENNReal.ofReal (@dist M (m.rescale R⁻¹ (inv_pos.mpr hR)).toDist x y)) ∧
      Nonempty (@KleinerLottApprox M PUnit (m.rescale R⁻¹ (inv_pos.mpr hR)) _ p PUnit.unit ε) := by
  obtain ⟨R₀, hR₀⟩ := exists_kleinerLottApprox_rescale_point_of_compactSpace p hε hε1
  exact ⟨R₀, fun R hR hRR => ⟨riemannianEDistOf_scaleMetric_inv_sq_eq_rescale g hmetric hR,
    hR₀ R hR hRR⟩⟩

end DifferentialGeometry.Geometry.Collapse
