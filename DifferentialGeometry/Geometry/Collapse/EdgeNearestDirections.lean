import DifferentialGeometry.Geometry.Collapse.AnnularDirections
import DifferentialGeometry.Geometry.Collapse.SublevelCore.Defs
import DifferentialGeometry.Geometry.Metric.Approximation.CoarseBorderDistance
import DifferentialGeometry.Analysis.SpecialFunctions.Trigonometric.HyperbolicEstimates
import DifferentialGeometry.Geometry.Comparison.TriangleExcessAngle

/-!
# LFR25.4 and LFR34.1: a coarse border controls every nearest direction (Riemannian binding)

Blueprint 207A, LFR25 (`lem:collapse-edge-closed-set-directions`, A:27011–27077) and the first part of
LFR34 (`lem:collapse-edge-low-collar-smoothing`, A:27872–27902). On a complete Riemannian manifold with a
coarse-border chart (LFR25.1, unbundled, see `CoarseBorderDistance`) and `sec ≥ -κ²` on `B(p, 1000Δ)`,
`κΔ ≤ 1/100`, at every `x ∈ B(p, 30Δ)` with `Δ/2 ≤ d_A(x) ≤ 12Δ` the outward point `y` of LFR25.3 satisfies
`‖v + w‖² ≤ 200τ` for EVERY nearest direction `v ∈ V_x(A)` (`minimizingDirectionsTo g hEnorm A x`) and
EVERY minimizing unit direction `w` from `x` to `y` (`inwardMinimizingDirections g hEnorm y x`); hence
`diam V_x(A) ≤ 2√(200τ) < 30√τ`. With `Δ/50 ≤ d_A(x)` (LFR34.1): `‖v + w‖² ≤ 4600τ`, diameter `< 140√τ`.

Route: `one_add_inner_le_of_nearest_direction` applies the proved Riemannian hinge comparison
`hyperbolicComparisonAngle_le_arccos_inner_of_sectional_lower_bound_on_minimizing_lenses` (the local
comparison input AC02) to the pair of minimizing arms from `x` to an actual nearest point `z = γ_v(d_A(x))`
of `A` and to `y`, with curvature parameter `k = 1/(100Δ) ≥ κ` (so `κ = 0` needs no limit), and the model
estimate `one_add_cos_comparisonAngle_le_excess`; the excess is bounded through `d(z, y) ≥ d_A(y)`.
No nearest-point choice, noncollapse or upper curvature bound enters; every pair of arms is tested.
-/

set_option autoImplicit false

noncomputable section
open Bundle Manifold Set Real Metric
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Comparison.Toponogov
open DifferentialGeometry.Geometry.Topology
open GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

/-- Hinge comparison for a nearest direction to a set: if `sec ≥ -k²` on `B(p, R)` and
`d(x,p) + 2 d_A(x) + d(x,y) < R`, then for every `v ∈ V_x(A)` and every minimizing unit direction `w`
from `x` to `y`, `1 + ⟨v, w⟩ ≤ cosh (k (a + ℓ)) (a + ℓ - d_A(y)) (a + ℓ) / (a ℓ)` with `a = d_A(x)`,
`ℓ = d(x, y)`. -/
theorem one_add_inner_le_of_nearest_direction (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm g) {p x y : M} {A : Set M} {k R : ℝ} (hk : 0 < k)
    (hsec : ∀ z ∈ ball p R, SectionalBoundedBelowAt g z (-k ^ 2))
    (ha : 0 < infDist x A) (hℓ : 0 < dist x y)
    (hR : dist x p + 2 * infDist x A + dist x y < R)
    {v w : TangentSpace I x} (hv : v ∈ minimizingDirectionsTo g hEnorm A x)
    (hw : w ∈ inwardMinimizingDirections (I := I) g hEnorm y x) :
    1 + g.inner x v w ≤ cosh (k * (infDist x A + dist x y)) *
      (infDist x A + dist x y - infDist y A) * (infDist x A + dist x y) /
        (infDist x A * dist x y) := by
  set a := infDist x A with ha_def
  set ℓ := dist x y with hℓ_def
  obtain ⟨hvu, hvA⟩ := hv
  obtain ⟨hwu, hwend⟩ := hw
  rw [dist_comm y x] at hwend
  set z := intrinsicGeodesic g hEnorm x v a with hz_def
  have hxz : dist x z = a := by
    refine le_antisymm ?_ (infDist_le_dist_of_mem hvA)
    have h := dist_intrinsicGeodesic_le_mul g hEnorm x v (s := 0) (t := a) ha.le
    rwa [intrinsicGeodesic_zero, hvu, Real.sqrt_one, one_mul, sub_zero] at h
  have hminA : (riemannianEDist I x (intrinsicGeodesic g hEnorm x v a)).toReal = a := by
    rw [toReal_riemannianEDist_eq_dist]
    exact hxz
  have hminB : (riemannianEDist I x (intrinsicGeodesic g hEnorm x w ℓ)).toReal = ℓ := by
    rw [hwend, toReal_riemannianEDist_eq_dist]
  have hlens : ∀ s ∈ Icc (0 : ℝ) a, ∀ t ∈ Icc (0 : ℝ) ℓ, ∀ y' : M,
      riemannianEDist I (intrinsicGeodesic g hEnorm x v s) y' +
        riemannianEDist I y' (intrinsicGeodesic g hEnorm x w t) =
        riemannianEDist I (intrinsicGeodesic g hEnorm x v s)
          (intrinsicGeodesic g hEnorm x w t) →
      SectionalBoundedBelowAt g y' (-k ^ 2) := by
    intro s hs t ht y' hy
    rw [← IsRiemannianManifold.out (I := I), ← IsRiemannianManifold.out (I := I),
      ← IsRiemannianManifold.out (I := I), edist_dist, edist_dist, edist_dist,
      ← ENNReal.ofReal_add dist_nonneg dist_nonneg,
      ENNReal.ofReal_eq_ofReal_iff (add_nonneg dist_nonneg dist_nonneg) dist_nonneg] at hy
    have hP : dist x (intrinsicGeodesic g hEnorm x v s) ≤ s := by
      simpa only [intrinsicGeodesic_zero, hvu, Real.sqrt_one, one_mul, sub_zero] using
        dist_intrinsicGeodesic_le_mul g hEnorm x v hs.1
    have hQ : dist x (intrinsicGeodesic g hEnorm x w t) ≤ t := by
      simpa only [intrinsicGeodesic_zero, hwu, Real.sqrt_one, one_mul, sub_zero] using
        dist_intrinsicGeodesic_le_mul g hEnorm x w ht.1
    apply hsec y'
    rw [Metric.mem_ball, dist_comm]
    have h1 := dist_triangle p x (intrinsicGeodesic g hEnorm x v s)
    have h2 := dist_triangle p (intrinsicGeodesic g hEnorm x v s) y'
    have h3 := dist_triangle (intrinsicGeodesic g hEnorm x v s) x
      (intrinsicGeodesic g hEnorm x w t)
    rw [dist_comm (intrinsicGeodesic g hEnorm x v s) x] at h3
    have hy0 := dist_nonneg (x := y') (y := intrinsicGeodesic g hEnorm x w t)
    rw [dist_comm p x] at h1
    nlinarith [hs.2, ht.2]
  have hhinge :=
    hyperbolicComparisonAngle_le_arccos_inner_of_sectional_lower_bound_on_minimizing_lenses
      g hEnorm x v w hk ha hℓ hvu hwu hminA hminB hlens
  rw [hwend, toReal_riemannianEDist_eq_dist] at hhinge
  set c := dist z y with hc_def
  have hhi : c ≤ a + ℓ := by
    have h := dist_triangle z x y
    rw [dist_comm z x, hxz] at h
    exact h
  have hlo : |a - ℓ| ≤ c := by
    have h := abs_dist_sub_le z y x
    rw [dist_comm z x, hxz, dist_comm y x] at h
    exact h
  have hrel : hyperbolicComparisonAngle k a ℓ c = comparisonAngleNegCurvature (k ^ 2) a ℓ c := by
    rw [comparisonAngleNegCurvature, ite_eq_right (pow_ne_zero 2 hk.ne'), Real.sqrt_sq hk.le]
    rfl
  rw [hrel] at hhinge
  have hcs := abs_inner_le_sqrt_mul_sqrt g x v w
  rw [hvu, hwu, Real.sqrt_one, mul_one] at hcs
  have hcos : g.inner x v w ≤ cos (comparisonAngleNegCurvature (k ^ 2) a ℓ c) := by
    have h := Real.cos_le_cos_of_nonneg_of_le_pi
      (comparisonAngleNegCurvature_mem_Icc (k ^ 2) a ℓ c).1 (Real.arccos_le_pi _) hhinge
    rwa [Real.cos_arccos (abs_le.mp hcs).1 (abs_le.mp hcs).2] at h
  have hmodel := one_add_cos_comparisonAngle_le_excess hk.le ha hℓ hlo hhi
  have hdy : infDist y A ≤ c := by
    rw [hc_def, dist_comm]
    exact infDist_le_dist_of_mem hvA
  have hcpos : 0 < cosh (k * (a + ℓ)) := Real.cosh_pos _
  calc 1 + g.inner x v w ≤ 1 + cos (comparisonAngleNegCurvature (k ^ 2) a ℓ c) := by linarith
    _ ≤ cosh (k * (a + ℓ)) * (a + ℓ - c) * (a + ℓ) / (a * ℓ) := hmodel
    _ ≤ cosh (k * (a + ℓ)) * (a + ℓ - infDist y A) * (a + ℓ) / (a * ℓ) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left (by linarith) hcpos.le

/-- LFR25.3 + LFR25.4 in general form: at `x ∈ B(p, 30Δ)` with `4τΔ < d_A(x) ≤ 12Δ` the outward point `y`
satisfies `g(v + w, v + w) ≤ 44 τΔ (1/d_A(x) + 1/d(x,y))` for every nearest direction `v` and every
minimizing unit direction `w` from `x` to `y`. -/
theorem exists_coarseBorder_outward_hinge (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm g) {Q : M → WithLp 2 (ℝ × ℝ)} {p : M} {A : Set M} {Δ τ κ : ℝ}
    (hΔ : 0 < Δ) (hτ : τ ≤ 1) (hQp : Q p = 0)
    (hdist : ∀ x ∈ ball p (200 * Δ), ∀ y ∈ ball p (200 * Δ),
      |dist (Q x) (Q y) - dist x y| ≤ τ * Δ)
    (hheight : ∀ x ∈ ball p (200 * Δ), 0 ≤ (Q x).snd)
    (hcover : ∀ z : WithLp 2 (ℝ × ℝ), |z.fst| ≤ 100 * Δ → z.snd ∈ Icc 0 (100 * Δ) →
      ∃ x ∈ ball p (200 * Δ), dist (Q x) z ≤ τ * Δ)
    (hpA : p ∈ A)
    (hborder : ∀ a ∈ A ∩ ball p (190 * Δ), (Q a).snd ≤ τ * Δ)
    (hbordercover : ∀ t : ℝ, |t| ≤ 100 * Δ →
      ∃ a ∈ A ∩ ball p (190 * Δ), dist (Q a) (WithLp.toLp 2 (t, (0 : ℝ))) ≤ τ * Δ)
    (hκ : 0 ≤ κ) (hκΔ : κ * Δ ≤ 1 / 100)
    (hsec : ∀ z ∈ ball p (1000 * Δ), SectionalBoundedBelowAt g z (-κ ^ 2))
    {x : M} (hx : x ∈ ball p (30 * Δ)) (hlo : 4 * (τ * Δ) < infDist x A)
    (hhi : infDist x A ≤ 12 * Δ) :
    ∃ y ∈ ball p (70 * Δ), |dist x y - infDist x A| ≤ 4 * (τ * Δ) ∧
      |infDist y A - 2 * infDist x A| ≤ 7 * (τ * Δ) ∧ 0 < dist x y ∧
      ∀ w ∈ inwardMinimizingDirections (I := I) g hEnorm y x,
        ∀ v ∈ minimizingDirectionsTo g hEnorm A x,
          g.inner x (v + w) (v + w) ≤ 44 * (τ * Δ) * (1 / infDist x A + 1 / dist x y) := by
  obtain ⟨y, hy, hxy, hay⟩ := exists_coarseBorder_outward_point hΔ hτ hQp hdist hheight hcover hpA
    hborder hbordercover hx hhi
  have hp : p ∈ ball p (200 * Δ) := mem_ball_self (by positivity)
  have hτ0 : 0 ≤ τ * Δ := by simpa using hdist p hp p hp
  set a := infDist x A with ha_def
  set ℓ := dist x y with hℓ_def
  obtain ⟨hxy1, hxy2⟩ := abs_le.mp hxy
  obtain ⟨hay1, hay2⟩ := abs_le.mp hay
  have ha : 0 < a := lt_of_le_of_lt (by positivity) hlo
  have hℓ : 0 < ℓ := by linarith
  refine ⟨y, hy, hxy, hay, hℓ, fun w hw v hv => ?_⟩
  set k : ℝ := 1 / (100 * Δ) with hk_def
  have hk : 0 < k := by positivity
  have hκk : κ ≤ k := by
    rw [hk_def, le_div_iff₀ (by positivity)]
    linarith
  have hsq : -k ^ 2 ≤ -κ ^ 2 := by nlinarith
  have hsec' : ∀ z ∈ ball p (1000 * Δ), SectionalBoundedBelowAt g z (-k ^ 2) :=
    fun z hz => SectionalBoundedBelowAt.mono (hsec z hz) hsq
  have hxp : dist x p < 30 * Δ := hx
  have hτΔ : τ * Δ ≤ Δ := by nlinarith
  have hR : dist x p + 2 * a + ℓ < 1000 * Δ := by linarith
  have hmain := one_add_inner_le_of_nearest_direction g hEnorm hk hsec' ha hℓ hR hv hw
  have hkal : k * (a + ℓ) ≤ 1 := by
    rw [hk_def, div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]
    linarith
  have hcosh : cosh (k * (a + ℓ)) ≤ 2 := by
    have ht0 : 0 ≤ k * (a + ℓ) := by positivity
    have h := Real.cosh_sub_one_le_sq ht0 hkal
    have ht2 : (k * (a + ℓ)) ^ 2 ≤ 1 := by nlinarith
    linarith
  have hdy : infDist y A ≤ a + ℓ := by
    have h := infDist_le_infDist_add_dist (x := y) (y := x) (s := A)
    rw [dist_comm y x] at h
    exact h
  have hexcess : a + ℓ - infDist y A ≤ 11 * (τ * Δ) := by linarith
  have hbound : cosh (k * (a + ℓ)) * (a + ℓ - infDist y A) * (a + ℓ) / (a * ℓ) ≤
      22 * (τ * Δ) * (1 / a + 1 / ℓ) := by
    rw [div_le_iff₀ (by positivity)]
    have he : 22 * (τ * Δ) * (1 / a + 1 / ℓ) * (a * ℓ) = 2 * (11 * (τ * Δ)) * (a + ℓ) := by
      field_simp
      ring
    rw [he]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul hcosh hexcess (by linarith) (by norm_num)
  have hexp : g.inner x (v + w) (v + w) = g.inner x v v + 2 * g.inner x v w + g.inner x w w := by
    simp only [map_add, add_apply, g.symm x w v]
    ring
  rw [hexp, hv.1, hw.1]
  linarith

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [MetricSpace M]
  [SigmaCompactSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)] in
/-- Two unit vectors each within `g`-norm `r` of `-w` are within `2r` of each other. -/
theorem sqrt_gInner_sub_le_of_sum_bounds {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [RiemannianBundle (fun x : M => TangentSpace I x)]
    {g : SmoothRiemannianMetric I M} (hEnorm : IsMetricNorm g) {x : M}
    {v v' w : TangentSpace I x} {r : ℝ}
    (hv : g.inner x (v + w) (v + w) ≤ r ^ 2) (hv' : g.inner x (v' + w) (v' + w) ≤ r ^ 2)
    (hr : 0 ≤ r) :
    Real.sqrt (g.inner x (v - v') (v - v')) ≤ 2 * r := by
  have htri : ‖v - v'‖ ≤ ‖v + w‖ + ‖v' + w‖ := by
    have hsplit : v - v' = (v + w) - (v' + w) := by abel
    rw [hsplit]
    exact norm_sub_le _ _
  rw [norm_tangent_eq_sqrt_gInner hEnorm, norm_tangent_eq_sqrt_gInner hEnorm,
    norm_tangent_eq_sqrt_gInner hEnorm] at htri
  have h1 := Real.sqrt_le_sqrt hv
  have h2 := Real.sqrt_le_sqrt hv'
  rw [Real.sqrt_sq hr] at h1 h2
  linarith

/-- **LFR25** (25.3 and 25.4). Coarse-border chart, `0 < τ < 10⁻⁴`, `sec ≥ -κ²` on `B(p, 1000Δ)`,
`κΔ ≤ 1/100`, `x ∈ B(p, 30Δ)`, `Δ/2 ≤ d_A(x) ≤ 12Δ`: an actual `y ∈ B(p, 70Δ)` with (LFR25.3), and
`‖v + w‖² ≤ 200τ` for every nearest direction `v` and every minimizing unit direction `w` from `x` to `y`;
`diam V_x(A) ≤ 2√(200τ) < 30√τ`. -/
theorem coarseBorder_nearest_directions (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm g) {Q : M → WithLp 2 (ℝ × ℝ)} {p : M} {A : Set M} {Δ τ κ : ℝ}
    (hΔ : 0 < Δ) (hτ : 0 < τ) (hτsmall : τ < 1 / 10000) (hQp : Q p = 0)
    (hdist : ∀ x ∈ ball p (200 * Δ), ∀ y ∈ ball p (200 * Δ),
      |dist (Q x) (Q y) - dist x y| ≤ τ * Δ)
    (hheight : ∀ x ∈ ball p (200 * Δ), 0 ≤ (Q x).snd)
    (hcover : ∀ z : WithLp 2 (ℝ × ℝ), |z.fst| ≤ 100 * Δ → z.snd ∈ Icc 0 (100 * Δ) →
      ∃ x ∈ ball p (200 * Δ), dist (Q x) z ≤ τ * Δ)
    (hpA : p ∈ A)
    (hborder : ∀ a ∈ A ∩ ball p (190 * Δ), (Q a).snd ≤ τ * Δ)
    (hbordercover : ∀ t : ℝ, |t| ≤ 100 * Δ →
      ∃ a ∈ A ∩ ball p (190 * Δ), dist (Q a) (WithLp.toLp 2 (t, (0 : ℝ))) ≤ τ * Δ)
    (hκ : 0 ≤ κ) (hκΔ : κ * Δ ≤ 1 / 100)
    (hsec : ∀ z ∈ ball p (1000 * Δ), SectionalBoundedBelowAt g z (-κ ^ 2))
    {x : M} (hx : x ∈ ball p (30 * Δ)) (hlo : Δ / 2 ≤ infDist x A)
    (hhi : infDist x A ≤ 12 * Δ) :
    (∃ y ∈ ball p (70 * Δ), |dist x y - infDist x A| ≤ 4 * (τ * Δ) ∧
      |infDist y A - 2 * infDist x A| ≤ 7 * (τ * Δ) ∧
      ∀ w ∈ inwardMinimizingDirections (I := I) g hEnorm y x,
        ∀ v ∈ minimizingDirectionsTo g hEnorm A x, g.inner x (v + w) (v + w) ≤ 200 * τ) ∧
    (∀ v ∈ minimizingDirectionsTo g hEnorm A x, ∀ v' ∈ minimizingDirectionsTo g hEnorm A x,
      Real.sqrt (g.inner x (v - v') (v - v')) ≤ 2 * Real.sqrt (200 * τ)) ∧
    2 * Real.sqrt (200 * τ) < 30 * Real.sqrt τ := by
  have hτΔ : τ * Δ < Δ / 10000 := by nlinarith
  have hτΔ0 : 0 < τ * Δ := by positivity
  obtain ⟨y, hy, hxy, hay, hℓ, hdir⟩ := exists_coarseBorder_outward_hinge g hEnorm hΔ
    (by linarith) hQp hdist hheight hcover hpA hborder hbordercover hκ hκΔ hsec hx
    (by linarith) hhi
  obtain ⟨hxy1, hxy2⟩ := abs_le.mp hxy
  have hnum : 44 * (τ * Δ) * (1 / infDist x A + 1 / dist x y) ≤ 200 * τ := by
    have ha : 1 / infDist x A ≤ 2 / Δ := by
      rw [div_le_div_iff₀ (by linarith) hΔ]
      linarith
    have hℓ' : 1 / dist x y ≤ (100 / 49) / Δ := by
      rw [div_le_div_iff₀ hℓ hΔ]
      nlinarith
    have hsum : 1 / infDist x A + 1 / dist x y ≤ (2 + 100 / 49) / Δ := by
      rw [add_div]
      linarith
    calc 44 * (τ * Δ) * (1 / infDist x A + 1 / dist x y) ≤ 44 * (τ * Δ) * ((2 + 100 / 49) / Δ) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = 44 * (2 + 100 / 49) * τ := by field_simp
      _ ≤ 200 * τ := by nlinarith
  have hbound : ∀ w ∈ inwardMinimizingDirections (I := I) g hEnorm y x,
      ∀ v ∈ minimizingDirectionsTo g hEnorm A x, g.inner x (v + w) (v + w) ≤ 200 * τ :=
    fun w hw v hv => (hdir w hw v hv).trans hnum
  have hyx : y ≠ x := fun h => by rw [h, dist_self] at hℓ; exact lt_irrefl 0 hℓ
  obtain ⟨w, hw⟩ := inwardMinimizingDirections_nonempty (I := I) g hEnorm hyx
  have hr : 0 ≤ Real.sqrt (200 * τ) := Real.sqrt_nonneg _
  have hsq : Real.sqrt (200 * τ) ^ 2 = 200 * τ := Real.sq_sqrt (by positivity)
  refine ⟨⟨y, hy, hxy, hay, hbound⟩, fun v hv v' hv' => ?_, ?_⟩
  · exact sqrt_gInner_sub_le_of_sum_bounds hEnorm ((hbound w hw v hv).trans hsq.symm.le)
      ((hbound w hw v' hv').trans hsq.symm.le) hr
  · rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 200)]
    have h200 : Real.sqrt 200 < 15 := by
      rw [Real.sqrt_lt' (by norm_num)]
      norm_num
    have hτs : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ
    nlinarith

/-- **LFR34.1**: the same outward-point and triangle argument for `Δ/50 ≤ d_A(x) ≤ 12Δ` gives
`‖v + w‖² ≤ 4600τ` and `diam V_x(A) ≤ 2√(4600τ) < 140√τ`. -/
theorem coarseBorder_nearest_directions_low (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm g) {Q : M → WithLp 2 (ℝ × ℝ)} {p : M} {A : Set M} {Δ τ κ : ℝ}
    (hΔ : 0 < Δ) (hτ : 0 < τ) (hτsmall : τ < 1 / 10000) (hQp : Q p = 0)
    (hdist : ∀ x ∈ ball p (200 * Δ), ∀ y ∈ ball p (200 * Δ),
      |dist (Q x) (Q y) - dist x y| ≤ τ * Δ)
    (hheight : ∀ x ∈ ball p (200 * Δ), 0 ≤ (Q x).snd)
    (hcover : ∀ z : WithLp 2 (ℝ × ℝ), |z.fst| ≤ 100 * Δ → z.snd ∈ Icc 0 (100 * Δ) →
      ∃ x ∈ ball p (200 * Δ), dist (Q x) z ≤ τ * Δ)
    (hpA : p ∈ A)
    (hborder : ∀ a ∈ A ∩ ball p (190 * Δ), (Q a).snd ≤ τ * Δ)
    (hbordercover : ∀ t : ℝ, |t| ≤ 100 * Δ →
      ∃ a ∈ A ∩ ball p (190 * Δ), dist (Q a) (WithLp.toLp 2 (t, (0 : ℝ))) ≤ τ * Δ)
    (hκ : 0 ≤ κ) (hκΔ : κ * Δ ≤ 1 / 100)
    (hsec : ∀ z ∈ ball p (1000 * Δ), SectionalBoundedBelowAt g z (-κ ^ 2))
    {x : M} (hx : x ∈ ball p (30 * Δ)) (hlo : Δ / 50 ≤ infDist x A)
    (hhi : infDist x A ≤ 12 * Δ) :
    (∃ y ∈ ball p (70 * Δ), |dist x y - infDist x A| ≤ 4 * (τ * Δ) ∧
      |infDist y A - 2 * infDist x A| ≤ 7 * (τ * Δ) ∧
      ∀ w ∈ inwardMinimizingDirections (I := I) g hEnorm y x,
        ∀ v ∈ minimizingDirectionsTo g hEnorm A x, g.inner x (v + w) (v + w) ≤ 4600 * τ) ∧
    (∀ v ∈ minimizingDirectionsTo g hEnorm A x, ∀ v' ∈ minimizingDirectionsTo g hEnorm A x,
      Real.sqrt (g.inner x (v - v') (v - v')) ≤ 2 * Real.sqrt (4600 * τ)) ∧
    2 * Real.sqrt (4600 * τ) < 140 * Real.sqrt τ := by
  have hτΔ : τ * Δ < Δ / 10000 := by nlinarith
  have hτΔ0 : 0 < τ * Δ := by positivity
  obtain ⟨y, hy, hxy, hay, hℓ, hdir⟩ := exists_coarseBorder_outward_hinge g hEnorm hΔ
    (by linarith) hQp hdist hheight hcover hpA hborder hbordercover hκ hκΔ hsec hx
    (by linarith) hhi
  obtain ⟨hxy1, hxy2⟩ := abs_le.mp hxy
  have hnum : 44 * (τ * Δ) * (1 / infDist x A + 1 / dist x y) ≤ 4600 * τ := by
    have ha : 1 / infDist x A ≤ 50 / Δ := by
      rw [div_le_div_iff₀ (by linarith) hΔ]
      linarith
    have hℓ' : 1 / dist x y ≤ (2500 / 49) / Δ := by
      rw [div_le_div_iff₀ hℓ hΔ]
      nlinarith
    have hsum : 1 / infDist x A + 1 / dist x y ≤ (50 + 2500 / 49) / Δ := by
      rw [add_div]
      linarith
    calc 44 * (τ * Δ) * (1 / infDist x A + 1 / dist x y) ≤
          44 * (τ * Δ) * ((50 + 2500 / 49) / Δ) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = 44 * (50 + 2500 / 49) * τ := by field_simp
      _ ≤ 4600 * τ := by nlinarith
  have hbound : ∀ w ∈ inwardMinimizingDirections (I := I) g hEnorm y x,
      ∀ v ∈ minimizingDirectionsTo g hEnorm A x, g.inner x (v + w) (v + w) ≤ 4600 * τ :=
    fun w hw v hv => (hdir w hw v hv).trans hnum
  have hyx : y ≠ x := fun h => by rw [h, dist_self] at hℓ; exact lt_irrefl 0 hℓ
  obtain ⟨w, hw⟩ := inwardMinimizingDirections_nonempty (I := I) g hEnorm hyx
  have hr : 0 ≤ Real.sqrt (4600 * τ) := Real.sqrt_nonneg _
  have hsq : Real.sqrt (4600 * τ) ^ 2 = 4600 * τ := Real.sq_sqrt (by positivity)
  refine ⟨⟨y, hy, hxy, hay, hbound⟩, fun v hv v' hv' => ?_, ?_⟩
  · exact sqrt_gInner_sub_le_of_sum_bounds hEnorm ((hbound w hw v hv).trans hsq.symm.le)
      ((hbound w hw v' hv').trans hsq.symm.le) hr
  · rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4600)]
    have h4600 : Real.sqrt 4600 < 70 := by
      rw [Real.sqrt_lt' (by norm_num)]
      norm_num
    have hτs : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ
    nlinarith

end DifferentialGeometry.Geometry.Collapse
