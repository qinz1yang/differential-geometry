import DifferentialGeometry.Geometry.Collapse.RescaledLimits.KL618Tail
import DifferentialGeometry.Geometry.Metric.Approximation.LowDimensionalRankApplications

/-!
# Curvature-volume and standing-tail exclusion of a three-splitting

LC19 and LC20 consume the actual LC08 and LC09 model producers at half of one fixed
LC18 threshold. The model and approximation witnesses are constructed inside the proofs.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter
open scoped Manifold ContDiff ENNReal Topology
open GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace DifferentialGeometry.Geometry.Collapse

universe u v

def threeSplittingExclusionThreshold : ℝ :=
  Classical.choose (exists_uniform_three_splitting_exclusion.{u, 0, v})

theorem threeSplittingExclusionThreshold_pos : 0 < threeSplittingExclusionThreshold.{u, v} :=
  (Classical.choose_spec (exists_uniform_three_splitting_exclusion.{u, 0, v})).1

theorem threeSplittingExclusionThreshold_lt : threeSplittingExclusionThreshold.{u, v} < 1 / 10 :=
  (Classical.choose_spec (exists_uniform_three_splitting_exclusion.{u, 0, v})).2.1

theorem threeSplittingExclusionThreshold_excludes
    {Z : Type u} [MetricSpace Z] {z : Z} {Y : Type} [MetricSpace Y] [CompleteSpace Y]
    (q : Y)
    (hseg : ∀ x y : Y, ∃ γ : Icc (0 : ℝ) 1 → Y, Continuous γ ∧
      γ ⟨0, by norm_num⟩ = x ∧ γ ⟨1, by norm_num⟩ = y ∧
      ∀ s t, dist (γ s) (γ t) = dist x y * dist s t)
    (hdim : dimH (univ : Set Y) ≤ 2) (hcomp : fourPointComparison 0 (univ : Set Y))
    {σ β : ℝ} (hσ : σ ≤ threeSplittingExclusionThreshold.{u, v})
    (hβ : β ≤ threeSplittingExclusionThreshold.{u, v}) (f : KleinerLottApprox z q σ) :
    ¬ HasEuclideanSplitting.{u, v} z 3 β :=
  (Classical.choose_spec (exists_uniform_three_splitting_exclusion.{u, 0, v})).2.2
    Z z Y q hseg hdim hcomp σ β hσ hβ f

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

theorem exists_local_rank_exclusion_of_attained_volume (hdim : Module.finrank ℝ E = 3) :
    ∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < 4 * Real.pi / 3 ∧ ∃ L₀ : ℝ, 4 ≤ L₀ ∧
      ∀ (M : Type u) [m : MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
        [SigmaCompactSpace M] [CompleteSpace M] (g : SmoothRiemannianMetric I M),
      (∀ a b, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)) →
      ∀ (p : M) (ρ w r : ℝ) (hρ : 0 < ρ), 0 < w → w < w₀ → 0 < r → r ≤ 2 * ρ →
      ballVolume g p r = ENNReal.ofReal (w * r ^ 3) →
      (∀ y ∈ riemannianBallOf g p (L₀ * ρ),
        SectionalBoundedBelowAt g y (-((L₀ * ρ) ^ 2)⁻¹)) →
      (∀ ε : ℝ, ε ≤ threeSplittingExclusionThreshold.{u, v} →
        ¬ @HasEuclideanSplitting.{u, v} M (m.rescale ρ⁻¹ (inv_pos.mpr hρ)) p 3 ε) ∧
      ∀ β : ℕ → ℝ, β 3 ≤ threeSplittingExclusionThreshold.{u, v} →
        @splittingRank.{u, v} M (m.rescale ρ⁻¹ (inv_pos.mpr hρ)) p β 3 ≤ 2 := by
  have hη := threeSplittingExclusionThreshold_pos.{u, v}
  have hηsmall := threeSplittingExclusionThreshold_lt.{u, v}
  obtain ⟨w₀, hw₀, hw₀small, L₀, hL₀, hmodel⟩ :=
    exists_uniform_metric_model (I := I) hdim (half_pos hη) (by linarith)
  refine ⟨w₀, hw₀, hw₀small, L₀, hL₀, ?_⟩
  intro M m cM iM sM kM g hmetric p ρ w r hρ hw hww hr hrρ hvol hsec
  obtain ⟨Y, mY, q, hc, hp, hdimY, hcomp, hseg, ⟨f⟩⟩ :=
    hmodel M g hmetric p ρ w r hρ hw hww hr hrρ hvol hsec
  let := mY
  let := hc
  let : MetricSpace M := m.rescale ρ⁻¹ (inv_pos.mpr hρ)
  have hno (ε : ℝ) (hε : ε ≤ threeSplittingExclusionThreshold.{u, v}) :
      ¬ HasEuclideanSplitting.{u, v} p 3 ε :=
    threeSplittingExclusionThreshold_excludes q hseg hdimY hcomp (by linarith) hε f
  exact ⟨hno, fun β hβ => splittingRank_le_two_of_no_three p β (hno (β 3) hβ)⟩

theorem exists_eventual_rank_exclusion (hdim : Module.finrank ℝ E = 3)
    {Λ : ℝ} (hΛ : 0 < Λ) :
    ∃ w₀ : ℝ, 0 < w₀ ∧ ∀ w : ℝ, 0 < w → w < w₀ → w < 4 * Real.pi / 3 →
      ∀ (X : ℕ → Type u) [mX : ∀ i, MetricSpace (X i)] [∀ i, ChartedSpace H (X i)]
        [∀ i, IsManifold I ∞ (X i)] [∀ i, CompactSpace (X i)]
        (g : ∀ i, SmoothRiemannianMetric I (X i)),
      (∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b)) →
      ∀ α : ℕ → ℝ, Tendsto α atTop atTop →
      (∀ i (p : X i), ENNReal.ofReal (α i * firstVolumeScale (g i) p (α i)⁻¹) ≤
        curvatureRadius (g i) p) →
      ∀ᶠ i in atTop, ∀ (p : X i) (ρ : ℝ) (hρ : 0 < ρ),
        firstVolumeScale (g i) p w / 2 ≤ ρ →
        ρ ≤ 2 * firstVolumeScale (g i) p (w / (2 * (1 + 2 * Λ⁻¹) ^ 3)) →
        (∀ ε : ℝ, ε ≤ threeSplittingExclusionThreshold.{u, v} →
          ¬ @HasEuclideanSplitting.{u, v} (X i)
            ((mX i).rescale ρ⁻¹ (inv_pos.mpr hρ)) p 3 ε) ∧
        ∀ β : ℕ → ℝ, β 3 ≤ threeSplittingExclusionThreshold.{u, v} →
          @splittingRank.{u, v} (X i) ((mX i).rescale ρ⁻¹ (inv_pos.mpr hρ)) p β 3 ≤ 2 := by
  have hη := threeSplittingExclusionThreshold_pos.{u, v}
  have hηsmall := threeSplittingExclusionThreshold_lt.{u, v}
  obtain ⟨w₀, hw₀, htail⟩ := exists_kl618_metric_model_tail (I := I) hdim
    (half_pos hη) (by linarith) hΛ
  refine ⟨w₀, hw₀, ?_⟩
  intro w hw hww hwc X mX cX iX kX g hmetric α hα hstand
  filter_upwards [htail w hw hww hwc X g hmetric α hα hstand] with i hi p ρ hρ hlow hup
  obtain ⟨Y, mY, q, hc, hp, hdimY, hcomp, hseg, ⟨f⟩⟩ := hi p ρ hρ hlow hup
  let := mY
  let := hc
  let : MetricSpace (X i) := (mX i).rescale ρ⁻¹ (inv_pos.mpr hρ)
  have hno (ε : ℝ) (hε : ε ≤ threeSplittingExclusionThreshold.{u, v}) :
      ¬ HasEuclideanSplitting.{u, v} p 3 ε :=
    threeSplittingExclusionThreshold_excludes q hseg hdimY hcomp (by linarith) hε f
  exact ⟨hno, fun β hβ => splittingRank_le_two_of_no_three p β (hno (β 3) hβ)⟩

end DifferentialGeometry.Geometry.Collapse
