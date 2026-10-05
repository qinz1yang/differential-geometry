import DifferentialGeometry.Geometry.Collapse.FiniteSurface.SlimFibreDiffeomorph
import DifferentialGeometry.Geometry.Collapse.FiniteSurface.SlimFactorOrientation
import DifferentialGeometry.Geometry.Collapse.FiniteSurface.SlimFibreTypeThresholdApplications

/-!
The slim comparison threshold retains its model orientation and the canonical surface orientation.
The whole zero fibre and all comparison buffers use the same model and splitting.
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
open DifferentialGeometry.Geometry.ExactSplitting Module

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] SlimProductModel.instMetricN SlimProductModel.instChartedN
  SlimProductModel.instManifoldN SlimProductModel.instProperN SlimProductModel.instConnectedN
  SlimProductModel.instBundleN SlimProductModel.instRiemannianN SlimProductModel.instMetricW
  SlimProductModel.instCompactW

attribute [local instance] SlimSurfaceFactor.instMetricS SlimSurfaceFactor.instChartedS
  SlimSurfaceFactor.instManifoldS SlimSurfaceFactor.instBundleS SlimSurfaceFactor.instRiemannianS

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "P2" => Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) - Module.finrank ℝ ℝ) → ℝ

local instance slimOrientationThresholdFinrank :
    NeZero (Module.finrank ℝ E3) :=
  ⟨by rw [finrank_euclideanSpace_fin]; decide⟩

universe u w

theorem slimChart_oriented_zeroFibre_threshold {Δ σ : ℝ} (hΔ : 1 ≤ Δ) (hσ : 0 < σ)
    (hσ1 : σ ≤ 1 / 100) (K : ℕ) (hK : 5 ≤ K) {r v : ℝ} (hr : 0 < r) (hv : 0 < v)
    (A : ℝ → ℝ) {ε : ℝ} (hε : 0 < ε) (R : ℝ) :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β : ℝ, 0 < β → β < β₀ →
      ∀ (M : Type u) [instMetricM : MetricSpace M] [instChartedM : ChartedSpace E3 M]
        [instManifoldM : IsManifold 𝓘(ℝ, E3) ∞ M]
        [instSigmaM : SigmaCompactSpace M] [instTangentM : T2Space (TangentBundle 𝓘(ℝ, E3) M)]
        [instCompleteM : CompleteSpace M]
        [instConnectedM : ConnectedSpace M]
        [instBundleM : RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E3) x)]
        [instRiemannianM : IsRiemannianManifold 𝓘(ℝ, E3) M]
        [instContinuousM : IsContinuousRiemannianBundle E3 (fun x : M => TangentSpace 𝓘(ℝ, E3) x)]
        (g : SmoothRiemannianMetric 𝓘(ℝ, E3) M) (hEnorm : IsMetricNorm g),
        ∀ oM : ManifoldOrientation (𝓡 3) M 3, ∀ p : M,
        ENNReal.ofReal v ≤ riemannianVolumeMeasure 𝓘(ℝ, E3) M g (ball p r) →
        (∀ R, 0 < R → R < β⁻¹ → ∀ k ≤ K, ∀ y ∈ ball p R, curvDerivNorm k g y ≤ A R) →
        (∀ y ∈ ball p β⁻¹, SectionalBoundedBelowAt g y (-β ^ 2)) →
        ∀ (Y : Type w) [instMetricY : MetricSpace Y] (y₀ : Y)
          (α : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), y₀)) β),
        (∀ y z : Y, dist y z ≤ 10 ^ 3 * Δ) →
        ∀ c : SlimChart g hEnorm Δ σ α, ∃ P : SlimProductModel c K,
          ∃ oN : ManifoldOrientation (𝓡 3) P.N 3,
          (∀ (x : P.N) (hx : x ∈ P.j.source),
            Orientation.map (Fin 3)
              ((P.j.isLocalDiffeomorphAt 𝓘(ℝ, E3) 𝓘(ℝ, E3)
                (K : ℕ∞ω) hx).mfderivToContinuousLinearEquiv
                  (by exact_mod_cast (show K ≠ 0 by omega))).toLinearEquiv
                (oN.orientation x) = oM.orientation (P.j x)) ∧
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
          ∃ Q : SlimSurfaceFactor P, ∃ L : (s : Q.S) → (ℝ × E2) ≃L[ℝ] E3,
            (∀ (s : Q.S) (v : ℝ × E2), L s v =
              mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 3)
                (fun q : ℝ × Q.S => P.e.symm (toLp 2 (q.1, Q.ψ q.2))) (0, s) v) ∧
            (∀ (s : Q.S) (b : Basis (Fin (finrank ℝ E2)) ℝ E2),
              b.orientation = (manifoldOrientationCast (by simp) Q.orientation).orientation s ↔
                (splitFrameBasis (Basis.singleton (Fin 1) ℝ) b lineSurfaceIndex
                  (L s).toLinearEquiv).orientation =
                  (manifoldOrientationCast (by simp) oN).orientation
                    (P.e.symm (toLp 2 (0, Q.ψ s)))) ∧
            let f := realSlabMap (ball p (10 ^ 6 * Δ)) isOpen_ball c.coord
              c.lipschitz.continuous.continuousOn (905 * 10 ^ 3 * Δ)
            let z₀ : lineBallOpens (905 * 10 ^ 3 * Δ) :=
              ⟨0, zero_mem_lineBallOpens (by positivity)⟩
            let _slimFibreCharts := regularFiberChartedSpace f z₀
              (contMDiff_realSlabMap isOpen_ball
                (c.contMDiffOn_coord.mono
                  (ball_subset_closedBall.trans c.closedBall_subset_domain)) _)
              (fun x _hx ↦ surjective_mfderiv_realSlabMap isOpen_ball
                (c.contMDiffOn_coord.mono (ball_subset_closedBall.trans c.closedBall_subset_domain))
                c.regular x)
            Nonempty ({x // f x = z₀} ≃ₘ⟮𝓘(ℝ, P2), 𝓡 2⟯ Q.S) ∧
            (Nonempty ({x // f x = z₀} ≃ₘ⟮𝓘(ℝ, P2), 𝓡 2⟯ Metric.sphere (0 : E3) 1) ∨
              Nonempty ({x // f x = z₀} ≃ₘ⟮𝓘(ℝ, P2), 𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)⟯
                (AddCircle (1 : ℝ) × AddCircle (1 : ℝ)))) := by
  obtain ⟨β₀, hβ₀, H⟩ :=
    slimChart_model_comparison_threshold.{u, w} hΔ hσ hσ1 K hK hr hv A hε R
  refine ⟨β₀, hβ₀, ?_⟩
  intro β hβ hββ₀ M instMetricM instChartedM instManifoldM instSigmaM instTangentM
    instCompleteM instConnectedM instBundleM instRiemannianM instContinuousM
    g hEnorm oM p hvol hcurv hsec Y instMetricY y₀ α hD c
  obtain ⟨P, ⟨oN, hoN⟩, hsrc, hdist, hchart⟩ :=
    H β hβ hββ₀ M g hEnorm oM p hvol hcurv hsec Y y₀ α hD c
  obtain ⟨Q, L, hL, hO⟩ := exists_slimSurfaceFactor_orientation (by omega) P oN
  exact ⟨P, oN, hoN, hsrc, hdist, hchart, Q, L, hL, hO,
    slimSurfaceFactor_zeroFibre_diffeomorph hK hΔ P Q⟩

theorem slimChart_oriented_packet_threshold {Δ σ : ℝ} (hΔ : 1 ≤ Δ) (hσ : 0 < σ)
    (hσ1 : σ ≤ 1 / 100) (K : ℕ) (hK : 5 ≤ K) {r v : ℝ} (hr : 0 < r) (hv : 0 < v)
    (A : ℝ → ℝ) {ε : ℝ} (hε : 0 < ε) (R : ℝ) :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β : ℝ, 0 < β → β < β₀ →
      ∀ (M : Type u) [instMetricM : MetricSpace M] [instChartedM : ChartedSpace E3 M]
        [instManifoldM : IsManifold 𝓘(ℝ, E3) ∞ M]
        [instSigmaM : SigmaCompactSpace M] [instTangentM : T2Space (TangentBundle 𝓘(ℝ, E3) M)]
        [instCompleteM : CompleteSpace M]
        [instConnectedM : ConnectedSpace M]
        [instBundleM : RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E3) x)]
        [instRiemannianM : IsRiemannianManifold 𝓘(ℝ, E3) M]
        [instContinuousM : IsContinuousRiemannianBundle E3 (fun x : M => TangentSpace 𝓘(ℝ, E3) x)]
        (g : SmoothRiemannianMetric 𝓘(ℝ, E3) M) (hEnorm : IsMetricNorm g),
        ∀ oM : ManifoldOrientation (𝓡 3) M 3, ∀ p : M,
        ENNReal.ofReal v ≤ riemannianVolumeMeasure 𝓘(ℝ, E3) M g (ball p r) →
        (∀ R, 0 < R → R < β⁻¹ → ∀ k ≤ K, ∀ y ∈ ball p R, curvDerivNorm k g y ≤ A R) →
        (∀ y ∈ ball p β⁻¹, SectionalBoundedBelowAt g y (-β ^ 2)) →
        ∀ (Y : Type w) [instMetricY : MetricSpace Y] (y₀ : Y)
          (α : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), y₀)) β),
        (∀ y z : Y, dist y z ≤ 10 ^ 3 * Δ) →
        ∀ c : SlimChart g hEnorm Δ σ α,
          (∃ S : SlimPacket g hEnorm Δ σ α, S.toSlimChart = c) ∧
          ∃ P : SlimProductModel c K,
          ∃ oN : ManifoldOrientation (𝓡 3) P.N 3,
          (∀ (x : P.N) (hx : x ∈ P.j.source),
            Orientation.map (Fin 3)
              ((P.j.isLocalDiffeomorphAt 𝓘(ℝ, E3) 𝓘(ℝ, E3)
                (K : ℕ∞ω) hx).mfderivToContinuousLinearEquiv
                  (by exact_mod_cast (show K ≠ 0 by omega))).toLinearEquiv
                (oN.orientation x) = oM.orientation (P.j x)) ∧
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
          ∃ Q : SlimSurfaceFactor P, ∃ L : (s : Q.S) → (ℝ × E2) ≃L[ℝ] E3,
            (∀ (s : Q.S) (v : ℝ × E2), L s v =
              mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 3)
                (fun q : ℝ × Q.S => P.e.symm (toLp 2 (q.1, Q.ψ q.2))) (0, s) v) ∧
            (∀ (s : Q.S) (b : Basis (Fin (finrank ℝ E2)) ℝ E2),
              b.orientation = (manifoldOrientationCast (by simp) Q.orientation).orientation s ↔
                (splitFrameBasis (Basis.singleton (Fin 1) ℝ) b lineSurfaceIndex
                  (L s).toLinearEquiv).orientation =
                  (manifoldOrientationCast (by simp) oN).orientation
                    (P.e.symm (toLp 2 (0, Q.ψ s)))) ∧
            let f := realSlabMap (ball p (10 ^ 6 * Δ)) isOpen_ball c.coord
              c.lipschitz.continuous.continuousOn (905 * 10 ^ 3 * Δ)
            let z₀ : lineBallOpens (905 * 10 ^ 3 * Δ) :=
              ⟨0, zero_mem_lineBallOpens (by positivity)⟩
            let _slimFibreCharts := regularFiberChartedSpace f z₀
              (contMDiff_realSlabMap isOpen_ball
                (c.contMDiffOn_coord.mono
                  (ball_subset_closedBall.trans c.closedBall_subset_domain)) _)
              (fun x _hx ↦ surjective_mfderiv_realSlabMap isOpen_ball
                (c.contMDiffOn_coord.mono (ball_subset_closedBall.trans c.closedBall_subset_domain))
                c.regular x)
            Nonempty ({x // f x = z₀} ≃ₘ⟮𝓘(ℝ, P2), 𝓡 2⟯ Q.S) ∧
            (Nonempty ({x // f x = z₀} ≃ₘ⟮𝓘(ℝ, P2), 𝓡 2⟯ Metric.sphere (0 : E3) 1) ∨
              Nonempty ({x // f x = z₀} ≃ₘ⟮𝓘(ℝ, P2), 𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)⟯
                (AddCircle (1 : ℝ) × AddCircle (1 : ℝ)))) := by
  obtain ⟨βpacket, hβpacket, Hpacket⟩ :=
    exists_slimPacket_threshold.{u, w} hΔ hσ hσ1 K hK hr hv A
  obtain ⟨βmodel, hβmodel, Hmodel⟩ :=
    slimChart_oriented_zeroFibre_threshold.{u, w} hΔ hσ hσ1 K hK hr hv A hε R
  refine ⟨min βpacket βmodel, lt_min hβpacket hβmodel, ?_⟩
  intro β hβ hβb M instMetricM instChartedM instManifoldM instSigmaM instTangentM
    instCompleteM instConnectedM instBundleM instRiemannianM instContinuousM
    g hEnorm oM p hvol hcurv hsec Y instMetricY y₀ α hD c
  exact ⟨(Hpacket β hβ (hβb.trans_le (min_le_left _ _)) M g hEnorm oM p
      hvol hcurv hsec Y y₀ α hD).2 c,
    Hmodel β hβ (hβb.trans_le (min_le_right _ _)) M g hEnorm oM p
      hvol hcurv hsec Y y₀ α hD c⟩

end DifferentialGeometry.Geometry.Collapse
