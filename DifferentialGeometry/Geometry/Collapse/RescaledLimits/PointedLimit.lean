import DifferentialGeometry.Geometry.Metric.Approximation.RiemannianExtraction
import DifferentialGeometry.Geometry.Metric.Scaling.RescaleGeometry
import DifferentialGeometry.Geometry.Collapse.CurvatureScaleBalls
import DifferentialGeometry.Geometry.Collapse.RiemannianConeScale
import DifferentialGeometry.Geometry.Comparison.RiemannianFourPoint
import DifferentialGeometry.Geometry.Metric.RiemannianShortCurves

/-!
# LC05: pointed limits of actual rescaled Riemannian sequences (the central producer)

Blueprint 207A, LC05 (`lem:collapse-rescaled-exhaustion`, A:20137). Complete Riemannian
manifolds `(X i, g i, p i)` with scales `ρ i > 0` and buffers `L i → ∞` such that
`sec_{g i} ≥ -(L i ρ i)⁻²` on `B_{g i}(p i, L i ρ i)` are rescaled to `ĝ i = ρ i⁻² g i`; a
subsequence of `(X i, ĝ i, p i)` converges in the pointed Gromov–Hausdorff sense to a complete
proper geodesic space with nonnegative four-point comparison and Hausdorff dimension at most
`dim X i`.

The sources carry a metric-space structure whose distance realizes the `g i`-length distance
(`hmetric`, the aligned convention of `RiemannianExtraction.lean`). The rescaled sources are the
same carriers with the metric `ρ i⁻¹ d` (`MetricSpace.rescale`), whose distance realizes the
length distance of `ρ i⁻² g i` (`riemannianEDistOf_scaleMetric_inv_sq_eq_rescale`, lane W3-F4,
`Geometry/Collapse/RiemannianConeScale.lean`).

* `sectionalBoundedBelowAt_rescaled_ball`: the buffered bound becomes `sec ≥ -L⁻²` on the
  rescaled ball of radius `L`.
* `exists_rescaled_pointed_limit_of_sectional_buffer`: LC05 (the central producer).
* `eventually_fourPointComparison_rescaled_ball`, `exists_arbitrarily_short_rescaled_curve`:
  the source-side comparison and short curves of the rescaled sequence, as consumed by the
  LC06/LC07/LC11–LC15 kernels.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter
open scoped Manifold ContDiff ENNReal Topology
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Comparison.Toponogov
open GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

universe u

section Single

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [m : MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The buffered curvature bound `sec_g ≥ -(L ρ)⁻²` on `B_g(p, L ρ)` is the bound
`sec_{ρ⁻² g} ≥ -L⁻²` on the rescaled metric ball of radius `L`. -/
theorem sectionalBoundedBelowAt_rescaled_ball (g : SmoothRiemannianMetric I M)
    (hmetric : ∀ a b, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
    (p : M) {ρ L : ℝ} (hρ : 0 < ρ)
    (hsec : ∀ y ∈ riemannianBallOf g p (L * ρ),
      SectionalBoundedBelowAt g y (-((L * ρ) ^ 2)⁻¹))
    (y : M)
    (hy : y ∈ @Metric.ball M (m.rescale ρ⁻¹ (inv_pos.mpr hρ)).toPseudoMetricSpace p L) :
    SectionalBoundedBelowAt (scaleMetric (ρ⁻¹ ^ 2) (pow_pos (inv_pos.mpr hρ) 2) g) y
      (-(L ^ 2)⁻¹) := by
  rw [sectionalBoundedBelowAt_scaleMetric_iff]
  have hy' : y ∈ riemannianBallOf g p (L * ρ) := by
    rw [@Metric.mem_ball, MetricSpace.rescale_dist] at hy
    change riemannianEDistOf g p y < ENNReal.ofReal (L * ρ)
    rw [hmetric, dist_comm]
    refine (ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg).mpr ?_
    rwa [inv_mul_lt_iff₀ hρ, mul_comm] at hy
  have h := hsec y hy'
  have heq : -(L ^ 2)⁻¹ * ρ⁻¹ ^ 2 = -((L * ρ) ^ 2)⁻¹ := by
    rw [mul_pow, mul_inv, inv_pow]
    ring
  rwa [heq]

end Single

section Sequence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {X : ℕ → Type u} [mX : ∀ i, MetricSpace (X i)] [∀ i, ChartedSpace H (X i)]
  [∀ i, IsManifold I ∞ (X i)] [∀ i, T2Space (TangentBundle I (X i))]
  [∀ i, SigmaCompactSpace (X i)] [∀ i, CompleteSpace (X i)]

/-- **LC05, the central producer.** Complete Riemannian manifolds with `sec ≥ -(L i ρ i)⁻²` on
`B(p i, L i ρ i)`, `ρ i > 0` and `L i → ∞`, rescaled by `ρ i⁻¹` (the tensor `ρ i⁻² g i`, see
`riemannianEDistOf_scaleMetric_inv_sq_eq_rescale`): a subsequence converges in the pointed
Gromov–Hausdorff sense to a complete proper geodesic space with nonnegative four-point
comparison, Hausdorff dimension at most `dim E`, the quadratic side comparison, and finite nets
with the displayed cardinality bound. -/
theorem exists_rescaled_pointed_limit_of_sectional_buffer
    (g : ∀ i, SmoothRiemannianMetric I (X i))
    (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
    (p : ∀ i, X i) {ρ L : ℕ → ℝ} (hρ : ∀ i, 0 < ρ i) (hL : Tendsto L atTop atTop)
    (hsec : ∀ i, ∀ y ∈ riemannianBallOf (g i) (p i) (L i * ρ i),
      SectionalBoundedBelowAt (g i) y (-((L i * ρ i) ^ 2)⁻¹)) :
    ∃ (Y : Type) (m : MetricSpace Y),
      letI := m
      ∃ (q : Y) (φ : ℕ → ℕ), StrictMono φ ∧ CompleteSpace Y ∧ ProperSpace Y ∧
        @PointedGHConverges (fun i => X (φ i))
          (fun i => (mX (φ i)).rescale (ρ (φ i))⁻¹ (inv_pos.mpr (hρ (φ i)))) Y m
          (fun i => p (φ i)) q ∧
        dimH (univ : Set Y) ≤ Module.finrank ℝ E ∧ fourPointComparison 0 (univ : Set Y) ∧
        (∀ a b : Y, ∃ f : Icc (0 : ℝ) 1 → Y, Continuous f ∧
          f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
          ∀ s t, dist (f s) (f t) = dist a b * dist s t) ∧
        (∀ a b z v : Y, ∀ t ∈ Icc (0 : ℝ) 1,
          dist a z = t * dist a b → dist z b = (1 - t) * dist a b →
          (1 - t) * dist v a ^ 2 + t * dist v b ^ 2 -
            t * (1 - t) * dist a b ^ 2 ≤ dist v z ^ 2) ∧
        ∀ R : ℝ, 0 < R → ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∃ T : Finset Y,
          (T.card : ℝ) ≤
            (2 + 64 * Real.sqrt (Module.finrank ℝ E) * Real.sinh (2 * (R + 1))) ^
              Module.finrank ℝ E * δ ^ (-(Module.finrank ℝ E : ℝ)) ∧
          (∀ y ∈ T, dist y q ≤ R) ∧
          ∀ y : Y, dist y q ≤ R → ∃ z ∈ T, dist y z < δ := by
  let m' : ∀ i, MetricSpace (X i) := fun i => (mX i).rescale (ρ i)⁻¹ (inv_pos.mpr (hρ i))
  have hcomplete' : ∀ i, @CompleteSpace (X i) (m' i).toUniformSpace := fun i =>
    ((mX i).rescale_completeSpace_iff (ρ i)⁻¹ (inv_pos.mpr (hρ i))).mpr inferInstance
  have hκ : ∀ i, 0 ≤ (L i ^ 2)⁻¹ := fun i => inv_nonneg.mpr (sq_nonneg _)
  have hκzero : Tendsto (fun i => (L i ^ 2)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop two_ne_zero).comp hL)
  exact @exists_pointed_limit_of_growing_sectional_lower_bound E H _ _ _ _ _ I _ X m'
    _ _ _ _ hcomplete'
    (fun i => scaleMetric ((ρ i)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (hρ i)) 2) (g i))
    (fun i => riemannianEDistOf_scaleMetric_inv_sq_eq_rescale (m := mX i) (g i) (hmetric i)
      (hρ i)) p
    (fun i => (L i ^ 2)⁻¹) L hκ hκzero hL
    (fun i => sectionalBoundedBelowAt_rescaled_ball (m := mX i) (g i) (hmetric i) (p i) (hρ i)
      (hsec i))

omit [∀ i, T2Space (TangentBundle I (X i))] in
/-- LC05, source side: on every fixed rescaled ball the rescaled sources eventually satisfy the
four-point comparison with the curvature constant `L i⁻²`. -/
theorem eventually_fourPointComparison_rescaled_ball_buffer
    (g : ∀ i, SmoothRiemannianMetric I (X i))
    (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
    (p : ∀ i, X i) {ρ L : ℕ → ℝ} (hρ : ∀ i, 0 < ρ i) (hL : Tendsto L atTop atTop)
    (hsec : ∀ i, ∀ y ∈ riemannianBallOf (g i) (p i) (L i * ρ i),
      SectionalBoundedBelowAt (g i) y (-((L i * ρ i) ^ 2)⁻¹)) (R : ℝ) :
    ∀ᶠ i in atTop,
      @fourPointComparison (X i) ((mX i).rescale (ρ i)⁻¹ (inv_pos.mpr (hρ i))) (L i ^ 2)⁻¹
        (@Metric.ball (X i) ((mX i).rescale (ρ i)⁻¹ (inv_pos.mpr (hρ i))).toPseudoMetricSpace
          (p i) R) := by
  filter_upwards [hL.eventually (eventually_ge_atTop (8 * R))] with i hi
  let : MetricSpace (X i) := (mX i).rescale (ρ i)⁻¹ (inv_pos.mpr (hρ i))
  have : CompleteSpace (X i) :=
    ((mX i).rescale_completeSpace_iff (ρ i)⁻¹ (inv_pos.mpr (hρ i))).mpr inferInstance
  exact fourPointComparison_of_sectional_lower_bound_on_eight_ball
    (scaleMetric ((ρ i)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (hρ i)) 2) (g i))
    (riemannianEDistOf_scaleMetric_inv_sq_eq_rescale (m := mX i) (g i) (hmetric i) (hρ i))
    (p i) (inv_nonneg.mpr (sq_nonneg _)) fun y hy =>
      sectionalBoundedBelowAt_rescaled_ball (m := mX i) (g i) (hmetric i) (p i) (hρ i) (hsec i)
        y (ball_subset_ball hi hy)

omit [∀ i, T2Space (TangentBundle I (X i))] in
/-- LC05, source side, in the form consumed by the LC06/LC11–LC15 kernels: eventually the
four-point comparison with constant `1` on every fixed rescaled ball. -/
theorem eventually_fourPointComparison_rescaled_ball
    (g : ∀ i, SmoothRiemannianMetric I (X i))
    (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
    (p : ∀ i, X i) {ρ L : ℕ → ℝ} (hρ : ∀ i, 0 < ρ i) (hL : Tendsto L atTop atTop)
    (hsec : ∀ i, ∀ y ∈ riemannianBallOf (g i) (p i) (L i * ρ i),
      SectionalBoundedBelowAt (g i) y (-((L i * ρ i) ^ 2)⁻¹)) (R : ℝ) :
    ∀ᶠ i in atTop,
      @fourPointComparison (X i) ((mX i).rescale (ρ i)⁻¹ (inv_pos.mpr (hρ i))) 1
        (@Metric.ball (X i) ((mX i).rescale (ρ i)⁻¹ (inv_pos.mpr (hρ i))).toPseudoMetricSpace
          (p i) R) := by
  filter_upwards [hL.eventually (eventually_ge_atTop (max 1 (8 * R)))] with i hi
  let : MetricSpace (X i) := (mX i).rescale (ρ i)⁻¹ (inv_pos.mpr (hρ i))
  have : CompleteSpace (X i) :=
    ((mX i).rescale_completeSpace_iff (ρ i)⁻¹ (inv_pos.mpr (hρ i))).mpr inferInstance
  have h1 : 1 ≤ L i := (le_max_left _ _).trans hi
  have hκ : -1 ≤ -(L i ^ 2)⁻¹ := neg_le_neg (inv_le_one_of_one_le₀ (one_le_pow₀ h1))
  exact fourPointComparison_of_sectional_lower_bound_on_eight_ball
    (scaleMetric ((ρ i)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (hρ i)) 2) (g i))
    (riemannianEDistOf_scaleMetric_inv_sq_eq_rescale (m := mX i) (g i) (hmetric i) (hρ i))
    (p i) zero_le_one fun y hy =>
      (sectionalBoundedBelowAt_rescaled_ball (m := mX i) (g i) (hmetric i) (p i) (hρ i) (hsec i)
        y (ball_subset_ball ((le_max_right _ _).trans hi) hy)).mono hκ

/-- LC05, source side: the rescaled sources have arbitrarily short curves (they are length
spaces), in the form consumed by the LC06/LC11–LC15 kernels. -/
theorem exists_arbitrarily_short_rescaled_curve
    (g : ∀ i, SmoothRiemannianMetric I (X i))
    (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
    {ρ : ℕ → ℝ} (hρ : ∀ i, 0 < ρ i) :
    letI : ∀ i, MetricSpace (X i) := fun i => (mX i).rescale (ρ i)⁻¹ (inv_pos.mpr (hρ i))
    ∀ i, ∀ a b : X i, ∀ η : ℝ, 0 < η → ∃ c : unitInterval → X i, Continuous c ∧
      c 0 = a ∧ c 1 = b ∧ eVariationOn c univ < ENNReal.ofReal (dist a b + η) := by
  intro i a b η hη
  let : MetricSpace (X i) := (mX i).rescale (ρ i)⁻¹ (inv_pos.mpr (hρ i))
  have : CompleteSpace (X i) :=
    ((mX i).rescale_completeSpace_iff (ρ i)⁻¹ (inv_pos.mpr (hρ i))).mpr inferInstance
  exact DifferentialGeometry.Geometry.Metric.exists_arbitrarily_short_riemannian_curve
    (scaleMetric ((ρ i)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (hρ i)) 2) (g i))
    (riemannianEDistOf_scaleMetric_inv_sq_eq_rescale (m := mX i) (g i) (hmetric i) (hρ i))
    a b hη

/-- LC05, source side: eventual finite nets of the rescaled balls with the ceiling cardinality
bound of the growing-ball comparison, in the form consumed by
`PointedGHConverges.dimH_le_of_ceil_covering`. -/
theorem eventually_rescaled_ceil_nets
    (g : ∀ i, SmoothRiemannianMetric I (X i))
    (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
    (p : ∀ i, X i) {ρ L : ℕ → ℝ} (hρ : ∀ i, 0 < ρ i) (hL : Tendsto L atTop atTop)
    (hsec : ∀ i, ∀ y ∈ riemannianBallOf (g i) (p i) (L i * ρ i),
      SectionalBoundedBelowAt (g i) y (-((L i * ρ i) ^ 2)⁻¹)) :
    letI : ∀ i, MetricSpace (X i) := fun i => (mX i).rescale (ρ i)⁻¹ (inv_pos.mpr (hρ i))
    ∀ R : ℝ, 0 < R → ∀ η : ℝ, 0 < η →
      ∀ᶠ i in atTop, ∃ F : Finset (X i),
        F.card ≤ (1 + ⌈4 * (2 : ℝ) ^ 2 * Real.sqrt (Module.finrank ℝ E) *
          Real.sinh (2 * R) / η⌉₊) ^ Module.finrank ℝ E ∧
        (∀ x ∈ F, dist x (p i) ≤ R) ∧
          ∀ x : X i, dist x (p i) ≤ R → ∃ y ∈ F, dist x y ≤ η := by
  intro R hR η hη
  let m' : ∀ i, MetricSpace (X i) := fun i => (mX i).rescale (ρ i)⁻¹ (inv_pos.mpr (hρ i))
  have hcomplete' : ∀ i, CompleteSpace (X i) := fun i =>
    ((mX i).rescale_completeSpace_iff (ρ i)⁻¹ (inv_pos.mpr (hρ i))).mpr inferInstance
  have hκzero : Tendsto (fun i => (L i ^ 2)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop two_ne_zero).comp hL)
  filter_upwards [@eventual_internal_nets_of_growing_sectional_lower_bound E H _ _ _ _ _ I _ X
    m' _ _ _ _ hcomplete'
    (fun i => scaleMetric ((ρ i)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (hρ i)) 2) (g i))
    (fun i => riemannianEDistOf_scaleMetric_inv_sq_eq_rescale (m := mX i) (g i) (hmetric i)
      (hρ i)) p
    (fun i => (L i ^ 2)⁻¹) L hκzero hL
    (fun i => sectionalBoundedBelowAt_rescaled_ball (m := mX i) (g i) (hmetric i) (p i) (hρ i)
      (hsec i)) R η hR hη] with i hi
  obtain ⟨T, hcard, hT, hnet⟩ := hi
  refine ⟨T, hcard, fun x hx => hT hx, fun x hx => ?_⟩
  obtain ⟨y, hy, hxy⟩ := hnet x hx
  exact ⟨y, hy, hxy.le⟩

end Sequence

end DifferentialGeometry.Geometry.Collapse
