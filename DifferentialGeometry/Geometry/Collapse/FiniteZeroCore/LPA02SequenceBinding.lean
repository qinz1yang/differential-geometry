import DifferentialGeometry.Geometry.Collapse.SimultaneousProductionBindings
import DifferentialGeometry.Geometry.Collapse.RiemannianConeScale
import DifferentialGeometry.Geometry.Curvature.Metric.DerivativeNormCompatibility

/-!
# LPA02, first paragraph: LFR14's hypotheses for EVERY normalized sequence

Frozen blueprint master207A, LPA02 (A:30349): "LPA01 gives noncollapse at radius one by `v_* > 0`,
eventual bounds by the FIXED `𝒜(R)`, and expanding lower-curvature balls `H_{α_i} → ∞`." For the
standing data of LPA01 (`eventually_simultaneous_analytic_data`) and ANY sequence of indices
`a j → ∞`, radii `r_j ≤ 2 r_{z_j}(w')` and centres `z_j`, the normalized sources
`(M^{a j}, h_j = r_j^{-2} g, z_j)` — with the rescaled distance `r_j⁻¹ d`, which is the distance of
`h_j` — satisfy LFR14's eventual hypotheses (the form of
`exists_finite_cheeger_gromov_limit_with_nonneg_sectional_of_eventual_bounds`):
* volume `≥ v_*` of the unit `h_j`-ball;
* `|∇^k Rm|_{h_j} ≤ 2^{K+2} A(2R+2, w')` on `h_j`-balls of radius `R`, for every `R`, eventually;
* `sec_{h_j} ≥ -H_j⁻²` on the `h_j`-ball of radius `H_j = α_{a j}/4 → ∞`.

`lpa02_normalized_sequence_hypotheses` is this binding.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter Real Bundle Manifold
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff ENNReal Topology NNReal

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

universe u

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {X : ℕ → Type u} [mX : ∀ i, MetricSpace (X i)] [∀ i, ChartedSpace H (X i)]
  [∀ i, IsManifold I ∞ (X i)] [∀ i, CompactSpace (X i)]

omit [FiniteDimensional ℝ E] [I.Boundaryless] in
/-- The normalized metric `(r²)⁻¹ g` in the `scaleMetric (r⁻¹ ^ 2)` form of the LC57/LC58 kernels. -/
theorem normalizedCenterMetric_eq_scaleMetric {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I ∞ M] (g : SmoothRiemannianMetric I M) {r : ℝ} (hr : 0 < r) :
    normalizedCenterMetric g r hr = scaleMetric (r⁻¹ ^ 2) (pow_pos (inv_pos.mpr hr) 2) g := by
  unfold normalizedCenterMetric
  congr 1
  rw [inv_pow]

omit [FiniteDimensional ℝ E] [I.Boundaryless] in
/-- The distance of the normalized metric `r⁻² g` is the rescaled distance `r⁻¹ d`. -/
theorem riemannianEDistOf_normalizedCenterMetric {M : Type*} [m : MetricSpace M]
    [ChartedSpace H M] [IsManifold I ∞ M] (g : SmoothRiemannianMetric I M)
    (hmetric : ∀ a b, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)) {r : ℝ} (hr : 0 < r)
    (a b : M) :
    riemannianEDistOf (normalizedCenterMetric g r hr) a b =
      ENNReal.ofReal (@dist M (m.rescale r⁻¹ (inv_pos.mpr hr)).toDist a b) := by
  rw [normalizedCenterMetric_eq_scaleMetric]
  exact riemannianEDistOf_scaleMetric_inv_sq_eq_rescale g hmetric hr a b

/-- **LPA02, first paragraph.** LFR14's eventual hypotheses for every normalized sequence of
LPA01's standing data. -/
theorem lpa02_normalized_sequence_hypotheses (hdim : Module.finrank ℝ E = 3)
    (g : ∀ i, SmoothRiemannianMetric I (X i))
    (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
    {α : ℕ → ℝ} (hα : Tendsto α atTop atTop)
    (hstand : ∀ i (p : X i), ENNReal.ofReal (α i * firstVolumeScale (g i) p (α i)⁻¹) ≤
      curvatureRadius (g i) p) (K : ℕ) (A : ℝ → ℝ → ℝ)
    (hA : ∀ C v, 0 < C → 0 < v → v < 4 * Real.pi / 3 → 0 < A C v)
    (hder : ∀ i (p : X i) v, 0 < v → v < 4 * Real.pi / 3 → (α i)⁻¹ ≤ v →
      ∀ C, 0 < C → C < α i → ∀ k ≤ K,
      ∀ y ∈ riemannianBallOf (g i) p (C * firstVolumeScale (g i) p v),
        curvatureDerivativeNorm (g i) k y ≤
          A C v * (firstVolumeScale (g i) p v ^ (k + 2))⁻¹)
    {Λ w : ℝ} (hΛ : 0 < Λ) (hw : 0 < w) (hwc : w < 4 * Real.pi / 3)
    (a : ℕ → ℕ) (ha : Tendsto a atTop atTop) (z : ∀ j, X (a j)) (r : ℕ → ℝ) (hr : ∀ j, 0 < r j)
    (hrz : ∀ j, r j ≤ 2 * firstVolumeScale (g (a j)) (z j) (w / (2 * (1 + 2 * Λ⁻¹) ^ 3))) :
    (∀ j a' b', riemannianEDistOf (normalizedCenterMetric (g (a j)) (r j) (hr j)) a' b' =
      ENNReal.ofReal (@dist (X (a j)) ((mX (a j)).rescale (r j)⁻¹ (inv_pos.mpr (hr j))).toDist
        a' b')) ∧
    0 < (w / (2 * (1 + 2 * Λ⁻¹) ^ 3)) / (24 * ∫ t in (0 : ℝ)..1, sinh t ^ 2) ∧
    (∀ᶠ j in atTop, ENNReal.ofReal ((w / (2 * (1 + 2 * Λ⁻¹) ^ 3)) /
        (24 * ∫ t in (0 : ℝ)..1, sinh t ^ 2)) ≤
      riemannianVolumeMeasure I (X (a j)) (normalizedCenterMetric (g (a j)) (r j) (hr j))
        (riemannianBallOf (normalizedCenterMetric (g (a j)) (r j) (hr j)) (z j) 1)) ∧
    (∀ R > 0, ∀ᶠ j in atTop, ∀ k ≤ K,
      ∀ y ∈ riemannianBallOf (normalizedCenterMetric (g (a j)) (r j) (hr j)) (z j) R,
        curvDerivNorm k (normalizedCenterMetric (g (a j)) (r j) (hr j)) y ≤
          (2 : ℝ) ^ (K + 2) * A (2 * R + 2) (w / (2 * (1 + 2 * Λ⁻¹) ^ 3))) ∧
    Tendsto (fun j => ((α (a j) / 4) ^ 2)⁻¹) atTop (𝓝 0) ∧
    Tendsto (fun j => α (a j) / 4) atTop atTop ∧
    (∀ᶠ j in atTop, ∀ y ∈ riemannianBallOf (normalizedCenterMetric (g (a j)) (r j) (hr j))
        (z j) (α (a j) / 4),
      SectionalBoundedBelowAt (normalizedCenterMetric (g (a j)) (r j) (hr j)) y
        (-((α (a j) / 4) ^ 2)⁻¹)) := by
  have hdata := ha.eventually
    (eventually_simultaneous_analytic_data hdim g hmetric hα hstand K A hA hder hΛ hw hwc)
  have hαa : Tendsto (fun j => α (a j)) atTop atTop := hα.comp ha
  have hH : Tendsto (fun j => α (a j) / 4) atTop atTop :=
    hαa.atTop_div_const (by norm_num : (0 : ℝ) < 4)
  have hHinv : Tendsto (fun j => ((α (a j) / 4) ^ 2)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop (two_ne_zero)).comp hH)
  have hv0 : 0 < (w / (2 * (1 + 2 * Λ⁻¹) ^ 3)) / (24 * ∫ t in (0 : ℝ)..1, sinh t ^ 2) := by
    obtain ⟨j, hj⟩ := hdata.exists
    exact (hj.2.2.2 (z j) (r j) (hr j) (hrz j)).1
  refine ⟨fun j => riemannianEDistOf_normalizedCenterMetric (g (a j)) (hmetric (a j)) (hr j),
    hv0, ?_, fun R hR => ?_, hHinv, hH, ?_⟩
  · filter_upwards [hdata] with j hj
    have h := (hj.2.2.2 (z j) (r j) (hr j) (hrz j)).2.1
    refine (ENNReal.ofReal_le_ofReal h).trans ?_
    exact ENNReal.ofReal_toReal_le
  · filter_upwards [hdata, hαa.eventually_gt_atTop (2 * R + 2)] with j hj hjα k hk y hy
    rw [← curvatureDerivativeNorm_eq_curvDerivNorm]
    exact (hj.2.2.2 (z j) (r j) (hr j) (hrz j)).2.2.2 R hR hjα k hk y hy
  · filter_upwards [hdata] with j hj y hy
    exact (hj.2.2.2 (z j) (r j) (hr j) (hrz j)).2.2.1 y hy

end DifferentialGeometry.Geometry.Collapse
