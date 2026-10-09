import DifferentialGeometry.Geometry.Collapse.SimultaneousSlimComparisonReordered

/-!
# Consumers of the reordered slim bracket with LFR20's comparison (LFR20 group 4)

* `slimCentre_zeroFibre_smooth_type_of_comparison`: the per-centre conclusion of
  `slimCentre_comparison_upgrade_threshold` gives the smooth type of the entire zero fibre of the
  same slim chart (round `S²` or flat torus `AddCircle 1 × AddCircle 1`).
* `eventually_slim_zero_fibres_smooth_sphere_or_torus_reordered` (of
  `eventually_simultaneous_slim_packets_with_comparison_reordered` at `εm = 1`, `Rm = 0`): the
  smooth upgrade of `eventually_slim_zero_fibres_sphere_or_torus_reordered` — on ONE tail of
  LPA04's reordered chain (same quantifier order as the topological version) every slim centre `j`
  carries a slim chart `c` whose entire zero fibre, with `SlimChart.trivial`'s regular-fibre
  structure, is smoothly diffeomorphic to the round `S²` or to the flat torus.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology NNReal
open DifferentialGeometry.Topology.Ehresmann
open DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open GC.MetricGeometry DifferentialGeometry.Geometry.Comparison.Toponogov
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Topology
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.MetricSmoothing
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis
open DifferentialGeometry.Analysis.Calculus

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "P2" => Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) - Module.finrank ℝ ℝ) → ℝ

universe u

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] SlimProductModel.instMetricN SlimProductModel.instChartedN
  SlimProductModel.instManifoldN SlimProductModel.instProperN SlimProductModel.instConnectedN
  SlimProductModel.instBundleN SlimProductModel.instRiemannianN SlimProductModel.instMetricW
  SlimProductModel.instCompactW

attribute [local instance] SlimSurfaceFactor.instMetricS SlimSurfaceFactor.instChartedS
  SlimSurfaceFactor.instManifoldS SlimSurfaceFactor.instBundleS SlimSurfaceFactor.instRiemannianS

/-- `finrank ℝ ℝ³ ≠ 0`, for the chain theorems' `NeZero` argument. -/
local instance nezero_finrank_euclideanThree_apps_CH13CLOSE2 : NeZero (Module.finrank ℝ E3) :=
  ⟨by rw [finrank_euclideanSpace_fin]; decide⟩


/-- **Per-centre consumer.** The slim-centre conclusion of
`slimCentre_comparison_upgrade_threshold` (equivalently, of
`eventually_simultaneous_slim_packets_with_comparison_reordered` at a slim centre) gives, for the
same `Z`, `αs` and slim chart `c`, the smooth type of the entire zero fibre `{η_c = 0}` (with
`SlimChart.trivial`'s regular-fibre structure): the round `S²` or the flat torus. -/
theorem slimCentre_zeroFibre_smooth_type_of_comparison {Δ σs : ℝ} (hΔ1 : 1 ≤ Δ) (K : ℕ)
    {εm Rm β₁ : ℝ} (X : Type u) [mX : MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
    (hmetric : ∀ a b, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
    (ρ : X → ℝ) (hρpos : ∀ p, 0 < ρ p) (j : X) :
      (∃ (Z : Type) (mZ : MetricSpace Z) (z : Z), letI := mZ
        (∀ y y' : Z, dist y y' ≤ 10 ^ 3 * Δ) ∧
        ∃ αs : @KleinerLottApprox X (WithLp 2 (ℝ × Z))
            (mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρpos j))) _ j
            (WithLp.toLp 2 ((0 : ℝ), z)) β₁,
        let hMc : CompleteSpace X := complete_of_compact
        letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
        letI := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
        letI : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
          radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
        letI : IsRiemannianManifold 𝓘(ℝ, E3) X :=
          radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
        letI : CompleteSpace X :=
          (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρpos j))).mpr hMc
        let gR : SmoothRiemannianMetric 𝓘(ℝ, E3) X :=
          scaleMetric ((ρ j)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (hρpos j)) 2) g
        have hnR : IsMetricNorm (I :=
          𝓘(ℝ, E3)) (M := X) gR := isMetricNorm_of_riemannianBundle gR
        ∃ c : SlimChart gR hnR Δ σs αs,
          @ball X mX.toPseudoMetricSpace j (2 * (Δ * ρ j)) ⊆
            (realSlabOpens (ball j (10 ^ 6 * Δ)) isOpen_ball c.coord
              c.lipschitz.continuous.continuousOn (905 * 10 ^ 3 * Δ) : Set X) ∩
              {x | c.cutoff x = 1} ∧
          (∀ x ∈ @ball X mX.toPseudoMetricSpace j (2 * (Δ * ρ j)),
            |c.coord x| < 3 * Δ) ∧
          tsupport c.cutoff ⊆ (realSlabOpens (ball j (10 ^ 6 * Δ)) isOpen_ball c.coord
              c.lipschitz.continuous.continuousOn (905 * 10 ^ 3 * Δ) : Set X) ∧
          tsupport c.cutoff ⊆
            @ball X mX.toPseudoMetricSpace j (2000000 * (Δ * ρ j)) ∧
          (∃ P : SlimPacket gR hnR Δ σs αs, P.toSlimChart = c) ∧
          ∃ P : SlimProductModel c K,
            closedBall P.q Rm ⊆ P.j.source ∧
            (∀ x y : P.N, (|(P.e x).fst| ≤ 95 / 100 * (10 ^ 6 * Δ) ∨ dist x P.q ≤ Rm) →
                (|(P.e y).fst| ≤ 95 / 100 * (10 ^ 6 * Δ) ∨ dist y P.q ≤ Rm) →
                |dist (P.j x) (P.j y) - dist x y| < εm) ∧
              (∃ (S : Finset P.N) (L : P.N → Set E3),
                (∀ x ∈ S, IsCompact (L x) ∧ L x ⊆ (extChartAt 𝓘(ℝ, E3) x).target ∧
                  (extChartAt 𝓘(ℝ, E3) x).symm '' L x ⊆ P.j.source ∧
                  ∀ k ≤ K - 1, ∀ y ∈ L x, mapDerivNorm k
                    (pullbackMetricCoefficients gR
                      ((P.j : P.N → X) ∘ (extChartAt 𝓘(ℝ, E3) x).symm))
                    (chartCoeff P.G x) y ≤ εm) ∧
                ∀ x : P.N, (|(P.e x).fst| ≤ 95 / 100 * (10 ^ 6 * Δ) ∨ dist x P.q ≤ Rm) →
                  ∃ x' ∈ S, x ∈ (extChartAt 𝓘(ℝ, E3) x').source ∧
                    extChartAt 𝓘(ℝ, E3) x' x ∈ interior (L x')) ∧
              ∃ Q : SlimSurfaceFactor P,
                let f := realSlabMap (ball j (10 ^ 6 * Δ)) isOpen_ball c.coord
                  c.lipschitz.continuous.continuousOn (905 * 10 ^ 3 * Δ)
                let z₀ : lineBallOpens (905 * 10 ^ 3 * Δ) :=
                  ⟨0, zero_mem_lineBallOpens (by positivity)⟩
                let _ := regularFiberChartedSpace f z₀
                  (contMDiff_realSlabMap isOpen_ball
                    (c.contMDiffOn_coord.mono
                      (ball_subset_closedBall.trans c.closedBall_subset_domain)) _)
                  (fun x _ ↦ surjective_mfderiv_realSlabMap isOpen_ball
                    (c.contMDiffOn_coord.mono
                      (ball_subset_closedBall.trans c.closedBall_subset_domain))
                    c.regular x)
                Nonempty ({x // f x = z₀} ≃ₘ⟮𝓘(ℝ, P2), 𝓡 2⟯ Q.S) ∧
                (Nonempty ({x // f x = z₀} ≃ₘ⟮𝓘(ℝ, P2), 𝓡 2⟯ Metric.sphere (0 : E3) 1) ∨
                  Nonempty ({x // f x = z₀} ≃ₘ⟮𝓘(ℝ, P2), 𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)⟯
                    (AddCircle (1 : ℝ) × AddCircle (1 : ℝ))))) →
      ∃ (Z : Type) (mZ : MetricSpace Z) (z : Z), letI := mZ
        ∃ αs : @KleinerLottApprox X (WithLp 2 (ℝ × Z))
            (mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρpos j))) _ j
            (WithLp.toLp 2 ((0 : ℝ), z)) β₁,
        let hMc : CompleteSpace X := complete_of_compact
        letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
        letI := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
        letI : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
          radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
        letI : IsRiemannianManifold 𝓘(ℝ, E3) X :=
          radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
        letI : CompleteSpace X :=
          (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρpos j))).mpr hMc
        let gR : SmoothRiemannianMetric 𝓘(ℝ, E3) X :=
          scaleMetric ((ρ j)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (hρpos j)) 2) g
        have hnR : IsMetricNorm (I :=
          𝓘(ℝ, E3)) (M := X) gR := isMetricNorm_of_riemannianBundle gR
        ∃ c : SlimChart gR hnR Δ σs αs,
          let f := realSlabMap (ball j (10 ^ 6 * Δ)) isOpen_ball c.coord
            c.lipschitz.continuous.continuousOn (905 * 10 ^ 3 * Δ)
          let z₀ : lineBallOpens (905 * 10 ^ 3 * Δ) :=
            ⟨0, zero_mem_lineBallOpens (by positivity)⟩
          let _ := regularFiberChartedSpace f z₀
            (contMDiff_realSlabMap isOpen_ball
              (c.contMDiffOn_coord.mono
                (ball_subset_closedBall.trans c.closedBall_subset_domain)) _)
            (fun x _ ↦ surjective_mfderiv_realSlabMap isOpen_ball
              (c.contMDiffOn_coord.mono
                (ball_subset_closedBall.trans c.closedBall_subset_domain))
              c.regular x)
          Nonempty ({x // f x = z₀} ≃ₘ⟮𝓘(ℝ, P2), 𝓡 2⟯ Metric.sphere (0 : E3) 1) ∨
            Nonempty ({x // f x = z₀} ≃ₘ⟮𝓘(ℝ, P2), 𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)⟯
              (AddCircle (1 : ℝ) × AddCircle (1 : ℝ))) := by
  intro h
  obtain ⟨Z, mZ, z, -, αs, c, -, -, -, -, -, _, -, -, -, _, -, htype⟩ := h
  exact ⟨Z, mZ, z, αs, c, htype⟩

/-- **Consumer of `eventually_simultaneous_slim_packets_with_comparison_reordered`: on ONE tail
every slim centre's entire zero fibre is smoothly the round `S²` or the flat torus.** The smooth
upgrade of `eventually_slim_zero_fibres_sphere_or_torus_reordered` (comparison data at `εm = 1`,
`Rm = 0`, discarded). -/
theorem eventually_slim_zero_fibres_smooth_sphere_or_torus_reordered
    {σs : ℝ} (hσs : 0 < σs) (hσs1 : σs ≤ 1 / 100) (K : ℕ) (hK : 5 ≤ K) (A : ℝ → ℝ → ℝ)
    (hA : ∀ C v, 0 < C → 0 < v → v < 4 * Real.pi / 3 → 0 < A C v) :
    ∃ a₂ : ℝ, 0 < a₂ ∧ ∀ γ : ℝ, 0 < γ → γ < 1 / 10 → ∃ β₀ : ℝ, 0 < β₀ ∧ β₀ ≤ a₂ ∧
      ∀ βc γc : ℝ, 0 < βc → βc < γc / 1000 → 0 < γc → γc < 1 / 100 →
      ∃ σ₀ : ℝ, 0 < σ₀ ∧ ∃ Δ₀ : ℝ, 0 < Δ₀ ∧
      ∀ β₂ Δ : ℝ, ∀ hβ₂pos : 0 < β₂, β₂ ≤ β₀ → β₂ < 1 / 100 → ∀ hΔβ₂ : 100 / β₂ < Δ, Δ₀ ≤ Δ →
      ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∃ bc₀ : ℝ, 0 < bc₀ ∧
      ∀ σc ε μ τ : ℝ, 0 < σc → σc ≤ σ₀ → σc < 1 → 0 < ε → ε < 1 / 100 → 0 < μ → μ ≤ 1 / 1000000 →
        0 < τ → τ ≤ τ₀ → 140 * Real.sqrt τ < ε ^ 2 / 20 →
      ∀ s b' s' : ℝ, 0 < s → s < 1 / 100 → s < b' / 100000 → s < s' / 100000 →
        b' < 1 / (1000000 * Δ) → s' < 1 / (1000000 * Δ) →
        b' < τ * Δ / 1000000000 → s' < τ * Δ / 1000000000 → ∃ a₀ b₁ : ℝ, 0 < a₀ ∧ 0 < b₁ ∧
      ∀ σ : ℝ, 0 < σ → σ ≤ a₂ → σ ≤ threeSplittingExclusionThreshold.{u, 0} → σ ≤ a₀ →
      ∀ Λ : ℝ, 0 < Λ → Δ * Λ * 2000000 ≤ 1 / 100 → Λ < 1 / (1000000 * Δ) →
        100 * Δ * Λ ≤ 1 / 1000000 →
        2 * ε + 300 * Δ * Λ + Real.sqrt (504000 / Δ + 3780 * τ) < γc / 1000 →
        Λ < s' / (100000000 * Δ ^ 2) →
      ∃ w₀ : ℝ, 0 < w₀ ∧ ∀ w : ℝ, 0 < w → w < w₀ → w < 4 * Real.pi / 3 →
      ∀ b : ℝ, 0 < b → b < s / 100000 → b < bc₀ → b < b₁ → 100 * Δ < b⁻¹ → ∃ b₀ : ℝ, 0 < b₀ ∧
      ∀ β : ℕ → ℝ, β 2 = β₂ → 0 < β 1 → β 1 < b₀ → β 1 < 1 →
        β 3 ≤ threeSplittingExclusionThreshold.{u, 0} →
      ∀ ζ : ℝ, β 1 < ζ → ζ < 1 →
      ∃ εz δ' Λ' : ℝ, 0 < εz ∧ 0 < δ' ∧ 0 < Λ' ∧
      ∀ T V : ℝ, 0 < T → 20 * Λ' ≤ T → T ≤ V →
      ∀ (X : ℕ → Type u) [mX : ∀ i, MetricSpace (X i)] [∀ i, ChartedSpace E3 (X i)]
        [∀ i, IsManifold 𝓘(ℝ, E3) ∞ (X i)] [∀ i, CompactSpace (X i)]
        (g : ∀ i, SmoothRiemannianMetric 𝓘(ℝ, E3) (X i))
        (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
        (α : ℕ → ℝ), Tendsto α atTop atTop →
        (∀ i (p : X i), ENNReal.ofReal (α i * firstVolumeScale (g i) p (α i)⁻¹) ≤
          curvatureRadius (g i) p) →
        (∀ i (p : X i) v, 0 < v → v < 4 * Real.pi / 3 → (α i)⁻¹ ≤ v →
          ∀ C, 0 < C → C < α i → ∀ k ≤ K,
          ∀ y ∈ riemannianBallOf (g i) p (C * firstVolumeScale (g i) p v),
            curvatureDerivativeNorm (g i) k y ≤
              A C v * (firstVolumeScale (g i) p v ^ (k + 2))⁻¹) →
        (∀ i, ManifoldOrientation (𝓡 3) (X i) 3) →
      ∀ᶠ i in atTop, ∃ ρ : X i → ℝ, ∃ hρpos : ∀ p, 0 < ρ p, ∃ Js : Set (X i), Js.Finite ∧
        ∀ j ∈ Js, ∃ (Z : Type) (mZ : MetricSpace Z) (z : Z), letI := mZ
          ∃ αs : @KleinerLottApprox (X i) (WithLp 2 (ℝ × Z))
              ((mX i).rescale (ρ j)⁻¹ (inv_pos.mpr (hρpos j))) _ j
              (WithLp.toLp 2 ((0 : ℝ), z)) (β 1),
          let hMc : CompleteSpace (X i) := complete_of_compact
          letI := (mX i).rescale (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
          letI := radialScaledBundle (g i) (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
          letI : IsContinuousRiemannianBundle E3 (fun x : X i => TangentSpace 𝓘(ℝ, E3) x) :=
            radialScaledContinuous (g i) (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
          letI : IsRiemannianManifold 𝓘(ℝ, E3) (X i) :=
            radialScaledManifold (m := mX i) (g i) (hmetric i) (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
          letI : CompleteSpace (X i) :=
            ((mX i).rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρpos j))).mpr hMc
          let gR : SmoothRiemannianMetric 𝓘(ℝ, E3) (X i) :=
            scaleMetric ((ρ j)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (hρpos j)) 2) (g i)
          have hnR : IsMetricNorm (I :=
            𝓘(ℝ, E3)) (M := X i) gR := isMetricNorm_of_riemannianBundle gR
          ∃ c : SlimChart gR hnR Δ σs αs,
            let f := realSlabMap (ball j (10 ^ 6 * Δ)) isOpen_ball c.coord
              c.lipschitz.continuous.continuousOn (905 * 10 ^ 3 * Δ)
            let z₀ : lineBallOpens (905 * 10 ^ 3 * Δ) :=
              ⟨0, zero_mem_lineBallOpens (mul_pos (by norm_num)
                ((div_pos (by norm_num) hβ₂pos).trans hΔβ₂))⟩
            let _ := regularFiberChartedSpace f z₀
              (contMDiff_realSlabMap isOpen_ball
                (c.contMDiffOn_coord.mono
                  (ball_subset_closedBall.trans c.closedBall_subset_domain)) _)
              (fun x _ ↦ surjective_mfderiv_realSlabMap isOpen_ball
                (c.contMDiffOn_coord.mono
                  (ball_subset_closedBall.trans c.closedBall_subset_domain))
                c.regular x)
            Nonempty ({x // f x = z₀} ≃ₘ⟮𝓘(ℝ, P2), 𝓡 2⟯ Metric.sphere (0 : E3) 1) ∨
              Nonempty ({x // f x = z₀} ≃ₘ⟮𝓘(ℝ, P2), 𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)⟯
                (AddCircle (1 : ℝ) × AddCircle (1 : ℝ))) := by
  have H := eventually_simultaneous_slim_packets_with_comparison_reordered.{u} hσs hσs1 K hK A hA
  refine Exists.elim H fun a₂ H => ⟨a₂, H.1, fun γ hγ hγ1 => ?_⟩
  refine Exists.elim (H.2 γ hγ hγ1) fun β₀ H =>
    ⟨β₀, H.1, H.2.1, fun βc γc hβc hβγ hγc hγc1 => ?_⟩
  refine Exists.elim (H.2.2 βc γc hβc hβγ hγc hγc1) fun σ₀ H => ⟨σ₀, H.1, ?_⟩
  refine Exists.elim H.2 fun Δ₀ H =>
    ⟨Δ₀, H.1, fun β₂ Δ hβ₂ hβ₂β₀ hβ₂small hΔ hΔ₀Δ => ?_⟩
  have hΔ1 : 1 ≤ Δ := by
    have h100 : 100 < 100 / β₂ := (lt_div_iff₀ hβ₂).mpr (by linarith)
    linarith
  refine Exists.elim (H.2 β₂ Δ hβ₂ hβ₂β₀ hβ₂small hΔ hΔ₀Δ) fun τ₀ H => ⟨τ₀, H.1, ?_⟩
  refine Exists.elim H.2 fun bc₀ H => ⟨bc₀, H.1, fun σc ε μ τ hσc hσcσ₀ hσc1 hε hε1 hμ hμ1 hτ
    hττ₀ hθ s b' s' hs hssmall hsb' hss' hb'd hs'd hb'e hs'e => ?_⟩
  refine Exists.elim (H.2 σc ε μ τ hσc hσcσ₀ hσc1 hε hε1 hμ hμ1 hτ hττ₀ hθ s b' s' hs hssmall
    hsb' hss' hb'd hs'd hb'e hs'e) fun a₀ H => Exists.elim H fun b₁ H =>
    ⟨a₀, b₁, H.1, H.2.1, fun σ hσ hσa hση hσa₀ Λ hΛ hΛΔ hΛ44 hlam hbudget hend => ?_⟩
  refine Exists.elim (H.2.2 σ hσ hσa hση hσa₀ Λ hΛ hΛΔ hΛ44 hlam hbudget hend) fun w₀ H =>
    ⟨w₀, H.1, fun w hw hww hwc b hb hbs hbc hbb₁ hsource => ?_⟩
  refine Exists.elim (H.2 w hw hww hwc b hb hbs hbc hbb₁ hsource 1 0 one_pos) fun b₀ H =>
    ⟨b₀, H.1, fun β hβ2 hβ1 hβ1b hβone hβ3 ζ hβζ hζone => ?_⟩
  refine Exists.elim (H.2 β hβ2 hβ1 hβ1b hβone hβ3 ζ hβζ hζone)
    fun εz H => Exists.elim H fun δ' H => Exists.elim H fun Λ' H => ⟨εz, δ', Λ', H.1, H.2.1,
      H.2.2.1, fun T V hT hTΛ hTV X mX _ _ _ g hmetric α hα hstand hder o => ?_⟩
  exact (H.2.2.2 T V hT hTΛ hTV X g hmetric α hα hstand hder o).mono fun i hi =>
    Exists.elim hi fun ρ hi => Exists.elim hi fun hρpos hi =>
      ⟨ρ, hρpos, Exists.elim hi.2.2.2.2 fun Js hJ => ⟨Js, hJ.1, fun j hj =>
        slimCentre_zeroFibre_smooth_type_of_comparison hΔ1 K (X i) (g i) (hmetric i) ρ hρpos j
          (hJ.2.2.2.2.2.1 j hj)⟩⟩

end DifferentialGeometry.Geometry.Collapse
