import DifferentialGeometry.Geometry.Collapse.FiniteSurface.SlimFibreTypeThresholdApplications
import DifferentialGeometry.Geometry.Collapse.FiniteSurface.SlimModelEmbeddingThreshold

/-!
# LC85 in full, threshold form: slim packet with its LC81 product model

`exists_slimPacket_with_model_threshold`: under LFR20's hypotheses (oriented sources), for `β < β₀`
every normalized `(1, β)`-splitting with factor diameter `≤ 10³Δ` carries an LC85 slim packet
(`SlimPacket`: LFR19 coordinate, enclosure, proper buffered restriction trivial over the interval,
cutoff, entire zero fibre connected and `≃ₜ S²` or `T²`) together with its LC81 comparison
with `ℝ × Z` (`SlimProductModel`: LFR20 item 3).
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter Metric WithLp Manifold
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.MetricSmoothing
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Integral.Measure
open GC.MetricGeometry

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

local notation "E3" => EuclideanSpace ℝ (Fin 3)

local instance nezero_finrank_euclidean_three_modelApp_F7LFR20b :
    NeZero (Module.finrank ℝ E3) :=
  ⟨by rw [finrank_euclideanSpace_fin]; decide⟩

universe u w

/-- **LC85 with its LC81 product model, threshold form.** -/
theorem exists_slimPacket_with_model_threshold {Δ σ : ℝ} (hΔ : 1 ≤ Δ) (hσ : 0 < σ)
    (hσ1 : σ ≤ 1 / 100) (K : ℕ) (hK : 5 ≤ K) {r v : ℝ} (hr : 0 < r) (hv : 0 < v)
    (A : ℝ → ℝ) :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β : ℝ, 0 < β → β < β₀ →
      ∀ (M : Type u) [MetricSpace M] [ChartedSpace E3 M] [IsManifold 𝓘(ℝ, E3) ∞ M]
        [SigmaCompactSpace M] [T2Space (TangentBundle 𝓘(ℝ, E3) M)] [CompleteSpace M]
        [ConnectedSpace M] [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E3) x)]
        [IsRiemannianManifold 𝓘(ℝ, E3) M]
        [IsContinuousRiemannianBundle E3 (fun x : M => TangentSpace 𝓘(ℝ, E3) x)]
        (g : SmoothRiemannianMetric 𝓘(ℝ, E3) M) (hEnorm : IsMetricNorm g),
        ManifoldOrientation (𝓡 3) M 3 → ∀ p : M,
        ENNReal.ofReal v ≤ riemannianVolumeMeasure 𝓘(ℝ, E3) M g (ball p r) →
        (∀ R, 0 < R → R < β⁻¹ → ∀ k ≤ K, ∀ y ∈ ball p R, curvDerivNorm k g y ≤ A R) →
        (∀ y ∈ ball p β⁻¹, SectionalBoundedBelowAt g y (-β ^ 2)) →
        ∀ (Y : Type w) [MetricSpace Y] (y₀ : Y)
          (α : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), y₀)) β),
        (∀ y z : Y, dist y z ≤ 10 ^ 3 * Δ) →
        ∃ P : SlimPacket g hEnorm Δ σ α, Nonempty (SlimProductModel P.toSlimChart K) := by
  obtain ⟨β₁, hβ₁, hpk⟩ := exists_slimPacket_threshold.{u, w} hΔ hσ hσ1 K hK hr hv A
  obtain ⟨β₂, hβ₂, hmod⟩ := slimChart_model_embedding_threshold.{u, w} hΔ hσ hσ1 K hK hr hv A
  refine ⟨min β₁ β₂, lt_min hβ₁ hβ₂, ?_⟩
  intro β hβ hβ₀ M _ _ _ _ _ _ _ _ _ _ g hEnorm o p hvol hcurv hsec Y _ y₀ α hD
  obtain ⟨⟨P⟩, -⟩ := hpk β hβ (hβ₀.trans_le (min_le_left _ _)) M g hEnorm o p hvol hcurv hsec Y y₀
    α hD
  exact ⟨P, hmod β hβ (hβ₀.trans_le (min_le_right _ _)) M g hEnorm o p hvol hcurv hsec Y y₀ α hD
    P.toSlimChart⟩

end DifferentialGeometry.Geometry.Collapse
