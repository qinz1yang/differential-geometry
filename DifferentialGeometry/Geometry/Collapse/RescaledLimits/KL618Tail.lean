import DifferentialGeometry.Geometry.Collapse.RescaledLimits.UniformMetricModel
import DifferentialGeometry.Geometry.Comparison.Volume.FirstCrossingScale

/-!
# LC09: KL 6.18 with its suppressed tail restored

Blueprint 207A, LC09 (`cor:collapse-kl618-tail`, A:20245). Fix `Λ > 0` and `0 < σ < 1`. There is
`w₀ > 0` such that for every fixed `0 < w < min {w₀, c₃}` and every standing closed sequence
(`R_p ≥ α r_p(1/α)` for every `p ∈ M^α`, `α → ∞`) there is a tail of indices on which, for
every point `p` and every scale `ρ` with `r_p(w)/2 ≤ ρ ≤ 2 r_p(w')`,
`w' = w / (2 (1 + 2Λ⁻¹)³)` (LC02's bounds), `(M^α, ρ⁻² g, p)` has LC08's low-dimensional metric
model. The tail may depend on `w`; `w₀` depends only on `σ`.

The standing sequence is a sequence of closed manifolds whose metrics realize `g i`, with
`α : ℕ → ℝ` tending to infinity and the KL standing curvature-scale bound `hstand` (the
curvature scale `R_p = curvatureRadius (g i) p ∈ [0, ∞]` may be infinite, which the convention
`sectionalBoundedBelowAt_of_ofReal_le_curvatureRadius` handles without dividing by `∞`).

Proof as in the blueprint: on the tail `α ≥ max (2 L₀) w'⁻¹`, LC01's antitonicity gives
`ρ ≤ 2 r_p(w') ≤ 2 r_p(1/α)`, so `L₀ ρ ≤ α r_p(1/α) ≤ R_p`; the curvature-scale convention gives
`sec ≥ -(L₀ ρ)⁻²` on `B(p, L₀ ρ)`, LC01 gives the attained level `w` at `r_p(w) ≤ 2ρ`, and LC08
applies.
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

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

/-- **LC09**, KL 6.18 with the tail restored: LC08's metric model at every scale satisfying LC02's
bounds, at every point, on a tail of a standing closed sequence. -/
theorem exists_kl618_metric_model_tail (hdim : Module.finrank ℝ E = 3) {σ Λ : ℝ} (hσ : 0 < σ)
    (hσ1 : σ < 1) (hΛ : 0 < Λ) :
    ∃ w₀ : ℝ, 0 < w₀ ∧ ∀ w : ℝ, 0 < w → w < w₀ → w < 4 * Real.pi / 3 →
      ∀ (X : ℕ → Type u) [mX : ∀ i, MetricSpace (X i)] [∀ i, ChartedSpace H (X i)]
        [∀ i, IsManifold I ∞ (X i)] [∀ i, CompactSpace (X i)]
        (g : ∀ i, SmoothRiemannianMetric I (X i)),
        (∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b)) →
        ∀ α : ℕ → ℝ, Tendsto α atTop atTop →
        (∀ i (p : X i), ENNReal.ofReal (α i * firstVolumeScale (g i) p (α i)⁻¹) ≤
          curvatureRadius (g i) p) →
        ∀ᶠ i in atTop, ∀ (p : X i) (ρ : ℝ) (hρ : 0 < ρ), firstVolumeScale (g i) p w / 2 ≤ ρ →
          ρ ≤ 2 * firstVolumeScale (g i) p (w / (2 * (1 + 2 * Λ⁻¹) ^ 3)) →
          ∃ (Y : Type) (mY : MetricSpace Y),
            letI := mY
            ∃ q : Y, CompleteSpace Y ∧ ProperSpace Y ∧ dimH (univ : Set Y) ≤ 2 ∧
              fourPointComparison 0 (univ : Set Y) ∧
              (∀ a b : Y, ∃ f : Icc (0 : ℝ) 1 → Y, Continuous f ∧
                f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
                ∀ s t, dist (f s) (f t) = dist a b * dist s t) ∧
              Nonempty (@KleinerLottApprox (X i) Y ((mX i).rescale ρ⁻¹ (inv_pos.mpr hρ)) mY p q
                σ) := by
  obtain ⟨w₀, hw₀, -, L₀, hL₀, hmodel⟩ := exists_uniform_metric_model (I := I) hdim hσ hσ1
  refine ⟨w₀, hw₀, fun w hw hww hwc X mX _ _ _ g hmetric α hα hstand => ?_⟩
  set w' := w / (2 * (1 + 2 * Λ⁻¹) ^ 3) with hw'def
  have hS : 1 < 2 * (1 + 2 * Λ⁻¹) ^ 3 := by
    have h1 : 1 ≤ (1 + 2 * Λ⁻¹) ^ 3 := one_le_pow₀ (by linarith [inv_pos.mpr hΛ])
    linarith
  have hw' : 0 < w' := div_pos hw (by linarith)
  have hw'w : w' < w := div_lt_self hw hS
  have hw'c : w' < 4 * Real.pi / 3 := hw'w.trans hwc
  filter_upwards [hα.eventually (eventually_ge_atTop (2 * L₀)),
    hα.eventually (eventually_ge_atTop w'⁻¹)] with i hi1 hi2 p ρ hρ hlow hup
  have hαpos : 0 < α i := (inv_pos.mpr hw').trans_le hi2
  have hαinv : (α i)⁻¹ ≤ w' := by
    rw [inv_le_comm₀ hαpos hw']
    exact hi2
  have hanti := firstVolumeScale_strictAntiOn (g i) hdim p
  have hu : firstVolumeScale (g i) p w' ≤ firstVolumeScale (g i) p (α i)⁻¹ :=
    hanti.antitoneOn ⟨inv_pos.mpr hαpos, hαinv.trans_lt hw'c⟩ ⟨hw', hw'c⟩ hαinv
  have hrw := firstVolumeScale_spec (g i) hdim p hw hwc
  have hu0 := (firstVolumeScale_spec (g i) hdim p (inv_pos.mpr hαpos)
    (hαinv.trans_lt hw'c)).1
  have hL₀ρ : L₀ * ρ ≤ α i * firstVolumeScale (g i) p (α i)⁻¹ := by
    have h1 : ρ ≤ 2 * firstVolumeScale (g i) p (α i)⁻¹ := hup.trans (by linarith)
    calc L₀ * ρ ≤ L₀ * (2 * firstVolumeScale (g i) p (α i)⁻¹) :=
          mul_le_mul_of_nonneg_left h1 (by linarith)
      _ = 2 * L₀ * firstVolumeScale (g i) p (α i)⁻¹ := by ring
      _ ≤ α i * firstVolumeScale (g i) p (α i)⁻¹ := mul_le_mul_of_nonneg_right hi1 hu0.le
  have hsec : ∀ y ∈ riemannianBallOf (g i) p (L₀ * ρ),
      SectionalBoundedBelowAt (g i) y (-((L₀ * ρ) ^ 2)⁻¹) :=
    sectionalBoundedBelowAt_of_ofReal_le_curvatureRadius (g i) (by positivity)
      ((ENNReal.ofReal_le_ofReal hL₀ρ).trans (hstand i p))
  exact hmodel (X i) (g i) (hmetric i) p ρ w (firstVolumeScale (g i) p w) hρ hw hww hrw.1
    (by linarith) (ballVolume_firstVolumeScale (g i) hdim p hw hwc) hsec

end DifferentialGeometry.Geometry.Collapse
