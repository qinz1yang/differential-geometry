import DifferentialGeometry.Geometry.Collapse.RescaledLimits.RankExclusion

/-!
# First volume scales and actual finite strata on the collapsed tail

The local consumer derives first-scale attainment on closed manifolds. The standing-sequence
consumer keeps all admissible pointwise scales and gives an explicit tail with empty rank three.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter
open scoped Manifold ContDiff ENNReal Topology
open GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian

namespace DifferentialGeometry.Geometry.Collapse

universe u v

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

theorem exists_local_rank_exclusion_at_firstVolumeScale (hdim : Module.finrank ℝ E = 3) :
    ∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < 4 * Real.pi / 3 ∧ ∃ L₀ : ℝ, 4 ≤ L₀ ∧
      ∀ (M : Type u) [m : MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
        [SigmaCompactSpace M] [CompleteSpace M] (g : SmoothRiemannianMetric I M),
      (∀ a b, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)) →
      ∀ (p : M) (ρ w : ℝ) (hρ : 0 < ρ), 0 < w → w < w₀ →
      0 < firstVolumeScale g p w → firstVolumeScale g p w ≤ 2 * ρ →
      ballVolume g p (firstVolumeScale g p w) =
        ENNReal.ofReal (w * firstVolumeScale g p w ^ 3) →
      (∀ y ∈ riemannianBallOf g p (L₀ * ρ),
        SectionalBoundedBelowAt g y (-((L₀ * ρ) ^ 2)⁻¹)) →
      (∀ ε : ℝ, ε ≤ threeSplittingExclusionThreshold.{u, v} →
        ¬ @HasEuclideanSplitting.{u, v} M (m.rescale ρ⁻¹ (inv_pos.mpr hρ)) p 3 ε) ∧
      ∀ β : ℕ → ℝ, β 3 ≤ threeSplittingExclusionThreshold.{u, v} →
        @splittingRank.{u, v} M (m.rescale ρ⁻¹ (inv_pos.mpr hρ)) p β 3 ≤ 2 := by
  obtain ⟨w₀, hw₀, hw₀small, L₀, hL₀, hlocal⟩ :=
    exists_local_rank_exclusion_of_attained_volume.{u, v} (I := I) hdim
  refine ⟨w₀, hw₀, hw₀small, L₀, hL₀, ?_⟩
  intro M m cM iM sM kM g hmetric p ρ w hρ hw hww hr hrρ hvol hsec
  exact hlocal M g hmetric p ρ w (firstVolumeScale g p w) hρ hw hww hr hrρ hvol hsec

theorem exists_closed_firstVolumeScale_rank_exclusion (hdim : Module.finrank ℝ E = 3) :
    ∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < 4 * Real.pi / 3 ∧ ∃ L₀ : ℝ, 4 ≤ L₀ ∧
      ∀ (M : Type u) [m : MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
        [CompactSpace M] (g : SmoothRiemannianMetric I M),
      (∀ a b, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)) →
      ∀ (p : M) (ρ w : ℝ) (hρ : 0 < ρ), 0 < w → w < w₀ →
      firstVolumeScale g p w ≤ 2 * ρ →
      (∀ y ∈ riemannianBallOf g p (L₀ * ρ),
        SectionalBoundedBelowAt g y (-((L₀ * ρ) ^ 2)⁻¹)) →
      (∀ ε : ℝ, ε ≤ threeSplittingExclusionThreshold.{u, v} →
        ¬ @HasEuclideanSplitting.{u, v} M (m.rescale ρ⁻¹ (inv_pos.mpr hρ)) p 3 ε) ∧
      ∀ β : ℕ → ℝ, β 3 ≤ threeSplittingExclusionThreshold.{u, v} →
        @splittingRank.{u, v} M (m.rescale ρ⁻¹ (inv_pos.mpr hρ)) p β 3 ≤ 2 := by
  obtain ⟨w₀, hw₀, hw₀small, L₀, hL₀, hlocal⟩ :=
    exists_local_rank_exclusion_at_firstVolumeScale.{u, v} (I := I) hdim
  refine ⟨w₀, hw₀, hw₀small, L₀, hL₀, ?_⟩
  intro M m cM iM kM g hmetric p ρ w hρ hw hww hrρ hsec
  have hwc := hww.trans hw₀small
  exact hlocal M g hmetric p ρ w hρ hw hww
    (firstVolumeScale_spec g hdim p hw hwc).1 hrρ
    (ballVolume_firstVolumeScale g hdim p hw hwc) hsec

theorem exists_eventual_scaled_strata_without_three (hdim : Module.finrank ℝ E = 3)
    {Λ : ℝ} (hΛ : 0 < Λ) :
    ∃ w₀ : ℝ, 0 < w₀ ∧ ∀ w : ℝ, 0 < w → w < w₀ → w < 4 * Real.pi / 3 →
      ∀ (X : ℕ → Type u) [mX : ∀ i, MetricSpace (X i)] [∀ i, ChartedSpace H (X i)]
        [∀ i, IsManifold I ∞ (X i)] [∀ i, CompactSpace (X i)]
        (g : ∀ i, SmoothRiemannianMetric I (X i)),
      (∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b)) →
      ∀ α : ℕ → ℝ, Tendsto α atTop atTop →
      (∀ i (p : X i), ENNReal.ofReal (α i * firstVolumeScale (g i) p (α i)⁻¹) ≤
        curvatureRadius (g i) p) →
      ∃ i₀ : ℕ, ∀ i : ℕ, i₀ ≤ i → ∀ (ρ : X i → ℝ) (hρ : ∀ p, 0 < ρ p),
        (∀ p, firstVolumeScale (g i) p w / 2 ≤ ρ p) →
        (∀ p, ρ p ≤ 2 * firstVolumeScale (g i) p (w / (2 * (1 + 2 * Λ⁻¹) ^ 3))) →
        ∀ β : ℕ → ℝ, β 3 ≤ threeSplittingExclusionThreshold.{u, v} →
        (∀ p, @scaledSplittingRank.{u, v} (X i) (mX i) ρ hρ β p ≤ 2) ∧
        @scaledSplittingStratum.{u, v} (X i) (mX i) ρ hρ β ⟨3, by decide⟩ = ∅ := by
  obtain ⟨w₀, hw₀, htail⟩ := exists_eventual_rank_exclusion.{u, v} (I := I) hdim hΛ
  refine ⟨w₀, hw₀, ?_⟩
  intro w hw hww hwc X mX cX iX kX g hmetric α hα hstand
  obtain ⟨i₀, hi₀⟩ := eventually_atTop.mp (htail w hw hww hwc X g hmetric α hα hstand)
  refine ⟨i₀, ?_⟩
  intro i hi ρ hρ hlow hup β hβ
  have hbound (p : X i) : @scaledSplittingRank.{u, v} (X i) (mX i) ρ hρ β p ≤ 2 :=
    (hi₀ i hi p (ρ p) (hρ p) (hlow p) (hup p)).2 β hβ
  refine ⟨hbound, ?_⟩
  apply eq_empty_iff_forall_notMem.mpr
  intro p hp
  change @scaledSplittingRank.{u, v} (X i) (mX i) ρ hρ β p = 3 at hp
  have hpbound := hbound p
  omega

end DifferentialGeometry.Geometry.Collapse
