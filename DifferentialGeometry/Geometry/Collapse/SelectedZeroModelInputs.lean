import DifferentialGeometry.Geometry.Collapse.RiemannianConeAtInfinity
import DifferentialGeometry.Geometry.Collapse.CurvatureScaleBalls
import DifferentialGeometry.Geometry.Comparison.SectionalLowerBound
import DifferentialGeometry.Geometry.Metric.Comparison.DistanceScaling
import DifferentialGeometry.Geometry.Metric.Scaling.Rescale

/-!
# LCP04's model clauses and original buffer from LC58's data (LC80 item 2, obligations (ii), (iii))

Master207A, LC80 (A:24719) and LCP04 (A:30123). LCP04
(`exists_selected_zero_packets_of_original_buffer`) asks, at every selected center `i`, for
(ii) a model `N i` that is proper, geodesic and nonnegatively curved in the four-point sense, and
(iii) the ORIGINAL curvature buffer `sec_g ≥ -(1/60)² r_i⁻²` on `B_g(i, 400 r_i)`. The LC58 binding
(`exists_uniform_scale_interval_joint_witnesses`) supplies smooth complete models with `sec ≥ 0`
and, in its sequential hypothesis, expanding normalized curvature bounds along subsequences.

* `model_lcp04_clauses_of_sectional_nonneg` (ii): a complete Riemannian model with `sec ≥ 0`
  (metric = length distance through `IsRiemannianManifold` and `IsMetricNorm`) is proper, has
  nonnegative four-point comparison on all of `N`, and constant-speed minimizing segments.
* `eventually_original_buffer_of_sequential_curvature` (iii): if along every sequence of indices
  tending to infinity and every choice of points some subsequence has `sec_{ρ⁻² g} ≥ -H_j⁻²` on
  `B_{ρ⁻¹ d}(z_j, H_j)` with `H_j → ∞`, then for every `V` there is `α₁` such that for `α > α₁`,
  every `p` and every `0 < s ≤ V` the original buffer holds at the scale `s ρ_α(p)`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Real Filter
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Comparison.Toponogov
open GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

/-- **LCP04's model clauses (obligation (ii)).** A complete Riemannian manifold with `sec ≥ 0`,
whose distance is the length distance of its bundle metric `gN` (`IsRiemannianManifold`,
`IsMetricNorm gN`), is proper, satisfies nonnegative four-point comparison on all of `N`, and has
constant-speed minimizing segments between any two points. -/
theorem model_lcp04_clauses_of_sectional_nonneg {N : Type*} [MetricSpace N] [ChartedSpace H N]
    [IsManifold I ∞ N] [SigmaCompactSpace N] [CompleteSpace N]
    [RiemannianBundle (fun x : N => TangentSpace I x)] [IsRiemannianManifold I N]
    [IsContinuousRiemannianBundle E (fun x : N => TangentSpace I x)]
    (gN : SmoothRiemannianMetric I N) (hgN : IsMetricNorm (I := I) gN)
    (hsec : ∀ x, SectionalBoundedBelowAt gN x 0) :
    ProperSpace N ∧ fourPointComparison 0 (univ : Set N) ∧
      ∀ x y : N, ∃ f : Icc (0 : ℝ) 1 → N, Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧
        f ⟨1, by norm_num⟩ = y ∧ ∀ s t, dist (f s) (f t) = dist x y * dist s t := by
  have hmetric : ∀ a b : N, riemannianEDistOf (I := I) gN a b = ENNReal.ofReal (dist a b) := by
    intro a b
    rw [riemannianEDistOf_eq_riemannianEDist gN hgN, ← IsRiemannianManifold.out (I := I)]
    exact edist_dist a b
  exact ⟨properSpace_of_riemannianEDistOf_eq gN hmetric,
    fourPointComparison_zero_univ_of_sectional_nonneg gN hmetric hsec,
    segments_of_riemannianEDistOf_eq gN hmetric⟩

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
/-- **The original buffer at every scale `s ρ_α(p)`, `s ≤ V` (obligation (iii)).** From the
sequential normalized curvature bounds of LC56 item (4) (as they enter LC58's hypothesis): for every
`V` there is `α₁` with `sec_g ≥ -(1/60)² (s ρ_α(p))⁻²` on `B(p, 400 s ρ_α(p))` for all `α > α₁`,
all `p ∈ M^α` and all `0 < s ≤ V`. -/
theorem eventually_original_buffer_of_sequential_curvature
    {M : ℕ → Type*} [mM : ∀ α, MetricSpace (M α)] [∀ α, ChartedSpace H (M α)]
    [∀ α, IsManifold I ∞ (M α)]
    (g : ∀ α, SmoothRiemannianMetric I (M α)) (ρ : ∀ α, M α → ℝ) (hρ : ∀ α x, 0 < ρ α x)
    (hcurv : ∀ a : ℕ → ℕ, Tendsto a atTop atTop → ∀ z : ∀ j, M (a j),
      ∃ k : ℕ → ℕ, StrictMono k ∧ ∃ Hb : ℕ → ℝ, Tendsto Hb atTop atTop ∧ ∀ j,
        ∀ y ∈ @Metric.ball (M (a (k j)))
            ((mM (a (k j))).rescale (ρ (a (k j)) (z (k j)))⁻¹
              (inv_pos.mpr (hρ _ _))).toPseudoMetricSpace (z (k j)) (Hb j),
          SectionalBoundedBelowAt (scaleMetric ((ρ (a (k j)) (z (k j)))⁻¹ ^ 2)
            (pow_pos (inv_pos.mpr (hρ _ _)) 2) (g (a (k j)))) y (-((Hb j)⁻¹ ^ 2)))
    (V : ℝ) :
    ∃ α₁ : ℕ, ∀ α, α₁ < α → ∀ p : M α, ∀ s : ℝ, 0 < s → s ≤ V →
      ∀ y ∈ Metric.ball p (400 * (s * ρ α p)),
        SectionalBoundedBelowAt (g α) y (-((1 / 60) ^ 2 * (s * ρ α p)⁻¹ ^ 2)) := by
  by_contra hcon
  push Not at hcon
  have hfreq : ∃ᶠ α in atTop, ∃ p : M α, ∃ s : ℝ, 0 < s ∧ s ≤ V ∧
      ∃ y ∈ Metric.ball p (400 * (s * ρ α p)),
        ¬ SectionalBoundedBelowAt (g α) y (-((1 / 60) ^ 2 * (s * ρ α p)⁻¹ ^ 2)) := by
    rw [Filter.frequently_atTop']
    intro α₁
    obtain ⟨α, hα, hbad⟩ := hcon α₁
    exact ⟨α, hα, hbad⟩
  obtain ⟨a, ha, hbad⟩ := Filter.extraction_of_frequently_atTop hfreq
  choose z s hs hsV y hy hny using hbad
  obtain ⟨k, -, Hb, hHb, hsec⟩ := hcurv a ha.tendsto_atTop z
  obtain ⟨j, hj⟩ := (hHb.eventually_ge_atTop (max (400 * V) (60 * V))).exists
  set c : ℝ := ρ (a (k j)) (z (k j)) with hc
  have hcpos : 0 < c := hρ _ _
  have hsj := hs (k j)
  have hsVj := hsV (k j)
  have h400 : 400 * V ≤ Hb j := (le_max_left _ _).trans hj
  have h60 : 60 * V ≤ Hb j := (le_max_right _ _).trans hj
  have hyb : y (k j) ∈ @Metric.ball (M (a (k j)))
      ((mM (a (k j))).rescale c⁻¹ (inv_pos.mpr hcpos)).toPseudoMetricSpace (z (k j)) (Hb j) := by
    have hyk := hy (k j)
    rw [Metric.mem_ball] at hyk
    change c⁻¹ * dist (y (k j)) (z (k j)) < Hb j
    have : dist (y (k j)) (z (k j)) < 400 * V * c := by nlinarith
    calc c⁻¹ * dist (y (k j)) (z (k j)) < c⁻¹ * (400 * V * c) :=
          mul_lt_mul_of_pos_left this (inv_pos.mpr hcpos)
      _ = 400 * V := by field_simp
      _ ≤ Hb j := h400
  have hb := hsec j (y (k j)) hyb
  rw [sectionalBoundedBelowAt_scaleMetric_iff] at hb
  apply hny (k j)
  refine hb.mono ?_
  have hHpos : 0 < Hb j := by nlinarith
  have hinv : (Hb j)⁻¹ ≤ (60 * s (k j))⁻¹ := inv_anti₀ (by positivity) (by nlinarith)
  have hsq : (Hb j)⁻¹ ^ 2 ≤ (60 * s (k j))⁻¹ ^ 2 :=
    pow_le_pow_left₀ (inv_nonneg.mpr hHpos.le) hinv 2
  have hid : (1 / 60) ^ 2 * (s (k j) * c)⁻¹ ^ 2 = (60 * s (k j))⁻¹ ^ 2 * c⁻¹ ^ 2 := by
    rw [mul_inv, mul_inv]; ring
  rw [hid]
  have hc2 : 0 ≤ c⁻¹ ^ 2 := by positivity
  nlinarith

end DifferentialGeometry.Geometry.Collapse
