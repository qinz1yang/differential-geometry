import DifferentialGeometry.Geometry.Collapse.FiniteSurface.SlimFibreDiffeomorph

/-!
# LFR20 in full, threshold form: comparison, surface factor and smooth fibre type

`slimChart_zeroFibre_smooth_type_threshold`: for `Δ ≥ 1`, `0 < σ ≤ 1/100`, `K ≥ 5`, `r, v > 0`, `A`,
a comparison tolerance `ε > 0` and a buffer radius `R` (all fixed BEFORE `β₀`), every slim chart of
an LFR20 source has an LC81 product model `P` with
* the comparison clauses of `slimChart_model_comparison_threshold` for its own `j` (buffer
  `{|t| ≤ 19L/20} ∪ B̄(q, R)`: source inclusion, pointed distances, finite chart atlas with the
  `C^{K-1}` coefficient bound),
* a surface factor `Q : SlimSurfaceFactor P` (the compact factor of `P.e` as a smooth oriented
  nonnegatively curved `C^{K-1}` surface, `N = ℝ × S`),
* the entire zero fibre, with `SlimChart.trivial`'s regular-fibre structure, smoothly
  diffeomorphic to `Q.S`, and to the round `S²` or to `AddCircle 1 × AddCircle 1` (LFR20 item 2).

This is the export consumed by the reordered simultaneous chain (lane LFR20-CMP, group 4).
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter Function Metric WithLp Manifold
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.MetricSmoothing
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Integral.Measure GC.MetricGeometry

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] SlimProductModel.instMetricN SlimProductModel.instChartedN
  SlimProductModel.instManifoldN SlimProductModel.instProperN SlimProductModel.instConnectedN
  SlimProductModel.instBundleN SlimProductModel.instRiemannianN SlimProductModel.instMetricW
  SlimProductModel.instCompactW

attribute [local instance] SlimSurfaceFactor.instMetricS SlimSurfaceFactor.instChartedS
  SlimSurfaceFactor.instManifoldS SlimSurfaceFactor.instBundleS SlimSurfaceFactor.instRiemannianS

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "P2" => Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) - Module.finrank ℝ ℝ) → ℝ

local instance nezero_finrank_euclidean_three_fibreApp_LFR20CMP :
    NeZero (Module.finrank ℝ E3) :=
  ⟨by rw [finrank_euclideanSpace_fin]; decide⟩

universe u w

/-- **LFR20 in full, threshold form.** See the module docstring. -/
theorem slimChart_zeroFibre_smooth_type_threshold {Δ σ : ℝ} (hΔ : 1 ≤ Δ) (hσ : 0 < σ)
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
          (∃ (S : Finset P.N) (L : P.N → Set E3),
            (∀ x ∈ S, IsCompact (L x) ∧ L x ⊆ (extChartAt 𝓘(ℝ, E3) x).target ∧
              (extChartAt 𝓘(ℝ, E3) x).symm '' L x ⊆ P.j.source ∧
              ∀ k ≤ K - 1, ∀ y ∈ L x, mapDerivNorm k
                (pullbackMetricCoefficients g ((P.j : P.N → M) ∘ (extChartAt 𝓘(ℝ, E3) x).symm))
                (chartCoeff P.G x) y ≤ ε) ∧
            ∀ x : P.N, (|(P.e x).fst| ≤ 95 / 100 * (10 ^ 6 * Δ) ∨ dist x P.q ≤ R) →
              ∃ x' ∈ S, x ∈ (extChartAt 𝓘(ℝ, E3) x').source ∧
                extChartAt 𝓘(ℝ, E3) x' x ∈ interior (L x')) ∧
          ∃ Q : SlimSurfaceFactor P,
            let f := realSlabMap (ball p (10 ^ 6 * Δ)) isOpen_ball c.coord
              c.lipschitz.continuous.continuousOn (905 * 10 ^ 3 * Δ)
            let z₀ : lineBallOpens (905 * 10 ^ 3 * Δ) :=
              ⟨0, zero_mem_lineBallOpens (by positivity)⟩
            let _ := regularFiberChartedSpace f z₀
              (contMDiff_realSlabMap isOpen_ball
                (c.contMDiffOn_coord.mono (ball_subset_closedBall.trans c.closedBall_subset_domain)) _)
              (fun x _ ↦ surjective_mfderiv_realSlabMap isOpen_ball
                (c.contMDiffOn_coord.mono (ball_subset_closedBall.trans c.closedBall_subset_domain))
                c.regular x)
            Nonempty ({x // f x = z₀} ≃ₘ⟮𝓘(ℝ, P2), 𝓡 2⟯ Q.S) ∧
            (Nonempty ({x // f x = z₀} ≃ₘ⟮𝓘(ℝ, P2), 𝓡 2⟯ Metric.sphere (0 : E3) 1) ∨
              Nonempty ({x // f x = z₀} ≃ₘ⟮𝓘(ℝ, P2), 𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)⟯
                (AddCircle (1 : ℝ) × AddCircle (1 : ℝ)))) := by
  obtain ⟨β₀, hβ₀, h⟩ := slimChart_model_comparison_threshold.{u, w} hΔ hσ hσ1 K hK hr hv A hε R
  refine ⟨β₀, hβ₀, fun β hβ hββ₀ M _ _ _ _ _ _ _ _ _ _ g hEnorm o p hvol hcurv hsec Y _ y₀ α hD c =>
    ?_⟩
  obtain ⟨P, ⟨oN, -⟩, hsrc, hdist, hchart⟩ := h β hβ hββ₀ M g hEnorm o p hvol hcurv hsec Y y₀ α hD c
  obtain ⟨Q⟩ := nonempty_slimSurfaceFactor (by omega) P oN
  exact ⟨P, hsrc, hdist, hchart, Q, slimSurfaceFactor_zeroFibre_diffeomorph hK hΔ P Q⟩

end DifferentialGeometry.Geometry.Collapse
