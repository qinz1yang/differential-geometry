import DifferentialGeometry.Geometry.Collapse.FiniteSurface.SlimSurfaceFactorProducer
import DifferentialGeometry.Geometry.Collapse.FiniteSurface.SlimModelComparisonThreshold
import DifferentialGeometry.Geometry.Collapse.FiniteSurface.ClosedSurfaceType

/-!
# Consumers of the slim surface factor: LFR17 on the factor of the SAME model

* `SlimSurfaceFactor.sphere_or_flat_torus`: the surface of a `SlimSurfaceFactor P` (`K ≥ 3`) is
  diffeomorphic to the round `S²`, or to `ℝ²/ℤ²` with `κ` flat (LFR17,
  `finiteSurface_sphere_or_flat_torus`, with the factor's own orientation and metric).
* `slimChart_model_surface_threshold`: LFR20 item 3 in full, threshold form — every slim chart
  has a product model `P` with the comparison clauses of `slimChart_model_comparison_threshold`
  (tolerance `ε` and buffer `R` fixed before `β₀`) and a surface factor `Q : SlimSurfaceFactor P`
  whose surface is `S²` or a flat `T²`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter Metric WithLp Manifold
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.MetricSmoothing
open DifferentialGeometry.Geometry.Riemannian
open GC.MetricGeometry
open DifferentialGeometry.Integral.Measure

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] SlimProductModel.instMetricN SlimProductModel.instChartedN
  SlimProductModel.instManifoldN SlimProductModel.instProperN SlimProductModel.instConnectedN
  SlimProductModel.instBundleN SlimProductModel.instRiemannianN SlimProductModel.instMetricW
  SlimProductModel.instCompactW

attribute [local instance] SlimSurfaceFactor.instMetricS SlimSurfaceFactor.instChartedS
  SlimSurfaceFactor.instManifoldS SlimSurfaceFactor.instBundleS SlimSurfaceFactor.instRiemannianS

local notation "E3" => EuclideanSpace ℝ (Fin 3)

local instance nezero_finrank_euclidean_three_surfaceApp_LFR20CMP :
    NeZero (Module.finrank ℝ E3) :=
  ⟨by rw [finrank_euclideanSpace_fin]; decide⟩

universe u w

section Deterministic

variable {M : Type*} [MetricSpace M] [ChartedSpace E3 M] [IsManifold 𝓘(ℝ, E3) ∞ M]
  [SigmaCompactSpace M] [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E3) x)]
  [IsRiemannianManifold 𝓘(ℝ, E3) M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E3 (fun x : M => TangentSpace 𝓘(ℝ, E3) x)]

/-- **LFR17 on the surface factor of a slim product model.** -/
theorem SlimSurfaceFactor.sphere_or_flat_torus {g : SmoothRiemannianMetric 𝓘(ℝ, E3) M}
    {hEnorm : IsMetricNorm g} {Δ σ : ℝ} {Y : Type*} [MetricSpace Y] {p : M} {y₀ : Y} {β : ℝ}
    {α : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), y₀)) β} {c : SlimChart g hEnorm Δ σ α}
    {K : ℕ} (hK : 3 ≤ K) {P : SlimProductModel c K} (Q : SlimSurfaceFactor P) :
    Nonempty (Q.S ≃ₘ⟮𝓡 2, 𝓡 2⟯ Metric.sphere (0 : E3) 1) ∨
      (Nonempty (Q.S ≃ₘ⟮𝓡 2, 𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)⟯ (AddCircle (1 : ℝ) × AddCircle (1 : ℝ))) ∧
        ∀ (x : Q.S) (v w : TangentSpace (𝓡 2) x), Q.κ.sectionalCurvature x v w = 0) := by
  have _ := Q.compactSpace
  have _ := Q.connectedSpace
  exact finiteSurface_sphere_or_flat_torus Q.orientation
    (by exact_mod_cast (show 2 ≤ K - 1 by omega)) Q.κ Q.sectional_nonneg

end Deterministic

/-- **LFR20 item 3 in full, threshold form.** The comparison tolerance `ε` and the buffer radius
`R` are fixed before `β₀`; the model has the comparison clauses for its own `j` and its compact
factor is a smooth surface (`SlimSurfaceFactor`) diffeomorphic to `S²` or to a flat `T²`. -/
theorem slimChart_model_surface_threshold {Δ σ : ℝ} (hΔ : 1 ≤ Δ) (hσ : 0 < σ)
    (hσ1 : σ ≤ 1 / 100) (K : ℕ) (hK : 5 ≤ K) {r v : ℝ} (hr : 0 < r) (hv : 0 < v)
    (A : ℝ → ℝ) {ε : ℝ} (hε : 0 < ε) (R : ℝ) :
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
        ∀ c : SlimChart g hEnorm Δ σ α, ∃ P : SlimProductModel c K,
          closedBall P.q R ⊆ P.j.source ∧
          (∀ x y : P.N, (|(P.e x).fst| ≤ 95 / 100 * (10 ^ 6 * Δ) ∨ dist x P.q ≤ R) →
            (|(P.e y).fst| ≤ 95 / 100 * (10 ^ 6 * Δ) ∨ dist y P.q ≤ R) →
            |dist (P.j x) (P.j y) - dist x y| < ε) ∧
          ∃ Q : SlimSurfaceFactor P,
            Nonempty (Q.S ≃ₘ⟮𝓡 2, 𝓡 2⟯ Metric.sphere (0 : E3) 1) ∨
              (Nonempty (Q.S ≃ₘ⟮𝓡 2, 𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)⟯
                  (AddCircle (1 : ℝ) × AddCircle (1 : ℝ))) ∧
                ∀ (x : Q.S) (v w : TangentSpace (𝓡 2) x), Q.κ.sectionalCurvature x v w = 0) := by
  obtain ⟨β₀, hβ₀, h⟩ := slimChart_model_comparison_threshold.{u, w} hΔ hσ hσ1 K hK hr hv A hε R
  refine ⟨β₀, hβ₀, fun β hβ hββ₀ M _ _ _ _ _ _ _ _ _ _ g hEnorm o p hvol hcurv hsec Y _ y₀ α hD c =>
    ?_⟩
  obtain ⟨P, ⟨oN, -⟩, hsrc, hdist, -⟩ := h β hβ hββ₀ M g hEnorm o p hvol hcurv hsec Y y₀ α hD c
  obtain ⟨Q⟩ := nonempty_slimSurfaceFactor (by omega) P oN
  exact ⟨P, hsrc, hdist, Q, Q.sphere_or_flat_torus (by omega)⟩

end DifferentialGeometry.Geometry.Collapse
