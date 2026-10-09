import DifferentialGeometry.Geometry.Collapse.SimultaneousSlimComparisonReordered
import DifferentialGeometry.Geometry.Collapse.FiniteSurface.SlimOrientationThreshold
import DifferentialGeometry.Geometry.Collapse.FiniteZeroCore.LPA02SequenceBinding

/-!
The reordered slim tail retains the orientation of its own comparison map and surface product.
The original cover, packet, edge and analytic data are preserved on a common smaller threshold.
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
local notation "E2" => EuclideanSpace ℝ (Fin 2)
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

open Module WithLp DifferentialGeometry.Manifold

local instance slimOrientationReorderedFinrank : NeZero (Module.finrank ℝ E3) :=
  ⟨by rw [finrank_euclideanSpace_fin]; decide⟩

private theorem slimOrientation_normalized_bounds
    {X : Type u} [slimMetricX : MetricSpace X] [slimChartedX : ChartedSpace E3 X]
    [slimManifoldX : IsManifold (𝓡 3) ∞ X] [slimSigmaX : SigmaCompactSpace X]
    (g : SmoothRiemannianMetric (𝓡 3) X)
    (hmetric : ∀ x y, riemannianEDistOf g x y = ENNReal.ofReal (dist x y))
    (p : X) {r β a v : ℝ} (hr : 0 < r) (hβ : 0 < β)
    (ha : 4 * β⁻¹ + 4 < a) (K : ℕ) (A : ℝ → ℝ)
    (hvol : v ≤ (ballVolume (normalizedCenterMetric g r hr) p 1).toReal)
    (hsec : ∀ y ∈ riemannianBallOf (normalizedCenterMetric g r hr) p (a / 4),
      SectionalBoundedBelowAt (normalizedCenterMetric g r hr) y (-((a / 4) ^ 2)⁻¹))
    (hder : ∀ R, 0 < R → 2 * R + 2 < a → ∀ k ≤ K,
      ∀ y ∈ riemannianBallOf (normalizedCenterMetric g r hr) p R,
        curvatureDerivativeNorm (normalizedCenterMetric g r hr) k y ≤ A R) :
    letI _slimMetricR := slimMetricX.rescale r⁻¹ (inv_pos.mpr hr)
    letI _slimBundleR := radialScaledBundle g r⁻¹ (inv_pos.mpr hr)
    letI _slimContinuousR := radialScaledContinuous g r⁻¹ (inv_pos.mpr hr)
    letI _slimRiemannianR := radialScaledManifold (m := slimMetricX) g hmetric
      r⁻¹ (inv_pos.mpr hr)
    let gR := scaleMetric (r⁻¹ ^ 2) (pow_pos (inv_pos.mpr hr) 2) g
    ENNReal.ofReal v ≤ riemannianVolumeMeasure (𝓡 3) X gR (ball p 1) ∧
    (∀ R, 0 < R → R < β⁻¹ → ∀ k ≤ K, ∀ y ∈ ball p R, curvDerivNorm k gR y ≤ A R) ∧
    (∀ y ∈ ball p β⁻¹, SectionalBoundedBelowAt gR y (-β ^ 2)) := by
  let slimMetricR := slimMetricX.rescale r⁻¹ (inv_pos.mpr hr)
  let slimBundleR := radialScaledBundle g r⁻¹ (inv_pos.mpr hr)
  let slimContinuousR := radialScaledContinuous g r⁻¹ (inv_pos.mpr hr)
  let slimRiemannianR := radialScaledManifold (m := slimMetricX) g hmetric r⁻¹ (inv_pos.mpr hr)
  let gR := scaleMetric (r⁻¹ ^ 2) (pow_pos (inv_pos.mpr hr) 2) g
  have hn : IsMetricNorm (I := 𝓡 3) (M := X) gR := isMetricNorm_of_riemannianBundle gR
  have hb (R : ℝ) : riemannianBallOf gR p R = ball p R :=
    Geometry.Metric.riemannianBallOf_eq_ball_of_isMetricNorm gR hn p R
  rw [normalizedCenterMetric_eq_scaleMetric] at hvol hsec hder
  refine ⟨?_, ?_, ?_⟩
  · change ENNReal.ofReal v ≤ riemannianVolumeMeasure (𝓡 3) X gR (ball p 1)
    rw [← hb 1]
    exact (ENNReal.ofReal_le_ofReal hvol).trans ENNReal.ofReal_toReal_le
  · intro R hR hRb k hk y hy
    have hyR : y ∈ riemannianBallOf gR p R := (hb R).symm ▸ hy
    have hd := hder R hR (by linarith) k hk y hyR
    exact curvatureDerivativeNorm_eq_curvDerivNorm gR k y ▸ hd
  · intro y hy
    have hba : β⁻¹ ≤ a / 4 := by linarith
    have hyR : y ∈ riemannianBallOf gR p (a / 4) :=
      (hb (a / 4)).symm ▸ ball_subset_ball hba hy
    apply (hsec y hyR).mono
    rw [neg_le_neg_iff, ← inv_pow]
    have ha0 : 0 < a / 4 := (inv_pos.mpr hβ).trans_le hba
    exact pow_le_pow_left₀ (inv_pos.mpr ha0).le
      ((inv_le_comm₀ ha0 hβ).mpr hba) 2

theorem slimCentre_orientation_upgrade_threshold {Δ σs : ℝ} (hΔ1 : 1 ≤ Δ) (hσs : 0 < σs)
    (hσs1 : σs ≤ 1 / 100) (K : ℕ) (hK : 5 ≤ K) {v : ℝ} (hv : 0 < v) (𝒜 : ℝ → ℝ) {εm : ℝ}
    (hεm : 0 < εm) (Rm : ℝ) :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β₁ : ℝ, 0 < β₁ → β₁ < β₀ →
      ∀ (X : Type u) [mX : MetricSpace X] [slimInst1 : ChartedSpace E3 X] [slimInst2 : IsManifold
        𝓘(ℝ, E3) ∞ X]
        [slimInst3 : CompactSpace X] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
        (hmetric : ∀ a b, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)),
        ∀ oM : ManifoldOrientation (𝓡 3) X 3,
      ∀ (ρ : X → ℝ) (hρpos : ∀ p, 0 < ρ p) (j : X) (a : ℝ), 4 * β₁⁻¹ + 4 < a →
        (0 < v ∧ v ≤ (ballVolume (normalizedCenterMetric g (ρ j) (hρpos j)) j 1).toReal ∧
          (∀ y ∈ riemannianBallOf (normalizedCenterMetric g (ρ j) (hρpos j)) j (a / 4),
            SectionalBoundedBelowAt (normalizedCenterMetric g (ρ j) (hρpos j)) y
              (-((a / 4) ^ 2)⁻¹)) ∧
          ∀ R, 0 < R → 2 * R + 2 < a → ∀ k ≤ K,
            ∀ y ∈ riemannianBallOf (normalizedCenterMetric g (ρ j) (hρpos j)) j R,
              curvatureDerivativeNorm (normalizedCenterMetric g (ρ j) (hρpos j)) k y ≤ 𝒜 R) →
        (∃ (Z : Type) (mZ : MetricSpace Z) (z : Z), letI _slimScale1 := mZ
          (∀ y y' : Z, dist y y' ≤ 10 ^ 3 * Δ) ∧
          ∃ αs : @KleinerLottApprox X (WithLp 2 (ℝ × Z))
              (mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρpos j))) _ j
              (WithLp.toLp 2 ((0 : ℝ), z)) β₁,
          let hMc : CompleteSpace X := complete_of_compact
          letI _slimScale2 := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
          letI _slimScale3 := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
          letI _slimScale4 : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3)
            x) :=
            radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
          letI _slimScale5 : IsRiemannianManifold 𝓘(ℝ, E3) X :=
            radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
          letI _slimScale6 : CompleteSpace X :=
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
              @ball X mX.toPseudoMetricSpace j (2000000 * (Δ * ρ j))) →
      ∃ (Z : Type) (mZ : MetricSpace Z) (z : Z), letI _slimScale7 := mZ
        (∀ y y' : Z, dist y y' ≤ 10 ^ 3 * Δ) ∧
        ∃ αs : @KleinerLottApprox X (WithLp 2 (ℝ × Z))
            (mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρpos j))) _ j
            (WithLp.toLp 2 ((0 : ℝ), z)) β₁,
        let hMc : CompleteSpace X := complete_of_compact
        letI _slimScale8 := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
        letI _slimScale9 := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
        letI _slimScale10 : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x)
          :=
          radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
        letI _slimScale11 : IsRiemannianManifold 𝓘(ℝ, E3) X :=
          radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
        letI _slimScale12 : CompleteSpace X :=
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
            ∃ oN : ManifoldOrientation (𝓡 3) P.N 3,
            (∀ (x : P.N) (hx : x ∈ P.j.source),
              Orientation.map (Fin 3)
                ((P.j.isLocalDiffeomorphAt 𝓘(ℝ, E3) 𝓘(ℝ, E3)
                  (K : ℕ∞ω) hx).mfderivToContinuousLinearEquiv
                    (by exact_mod_cast (show K ≠ 0 by omega))).toLinearEquiv
                  (oN.orientation x) = oM.orientation (P.j x)) ∧
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
              ∃ L : (s : Q.S) → (ℝ × E2) ≃L[ℝ] E3,
              (∀ (s : Q.S) (v : ℝ × E2), L s v =
                mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 3)
                  (fun q : ℝ × Q.S => P.e.symm (toLp 2 (q.1, Q.ψ q.2))) (0, s) v) ∧
              (∀ (s : Q.S) (b : Basis (Fin (finrank ℝ E2)) ℝ E2),
                b.orientation = (manifoldOrientationCast (by simp) Q.orientation).orientation s ↔
                  (splitFrameBasis (Basis.singleton (Fin 1) ℝ) b lineSurfaceIndex
                    (L s).toLinearEquiv).orientation =
                    (manifoldOrientationCast (by simp) oN).orientation
                      (P.e.symm (toLp 2 (0, Q.ψ s)))) ∧
              let f := realSlabMap (ball j (10 ^ 6 * Δ)) isOpen_ball c.coord
                c.lipschitz.continuous.continuousOn (905 * 10 ^ 3 * Δ)
              let z₀ : lineBallOpens (905 * 10 ^ 3 * Δ) :=
                ⟨0, zero_mem_lineBallOpens (by positivity)⟩
              let _slimFibreCharts := regularFiberChartedSpace f z₀
                (contMDiff_realSlabMap isOpen_ball
                  (c.contMDiffOn_coord.mono
                    (ball_subset_closedBall.trans c.closedBall_subset_domain)) _)
                (fun x _hx ↦ surjective_mfderiv_realSlabMap isOpen_ball
                  (c.contMDiffOn_coord.mono
                    (ball_subset_closedBall.trans c.closedBall_subset_domain))
                  c.regular x)
              Nonempty ({x // f x = z₀} ≃ₘ⟮𝓘(ℝ, P2), 𝓡 2⟯ Q.S) ∧
              (Nonempty ({x // f x = z₀} ≃ₘ⟮𝓘(ℝ, P2), 𝓡 2⟯ Metric.sphere (0 : E3) 1) ∨
                Nonempty ({x // f x = z₀} ≃ₘ⟮𝓘(ℝ, P2), 𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)⟯
                  (AddCircle (1 : ℝ) × AddCircle (1 : ℝ)))) := by
  obtain ⟨βnew, hβnew, Hnew⟩ :=
    slimChart_oriented_packet_threshold.{u, 0} hΔ1 hσs hσs1 K hK one_pos hv 𝒜 hεm Rm
  refine ⟨βnew, hβnew, ?_⟩
  intro β₁ hβ hβb X mX slimInst1 slimInst2 slimInst3 g hmetric oM ρ hρpos j a ha hdata hslim
  obtain ⟨Z, mZ, z, hD, αs, c, hc1, hc2, hc3, hc4⟩ := hslim
  let slimConnectedX := connectedSpace_of_aligned_metric g hmetric j
  let slimCompleteX : CompleteSpace X := complete_of_compact
  have Hdata := slimOrientation_normalized_bounds g hmetric j (hρpos j) hβ ha K 𝒜
    hdata.2.1 hdata.2.2.1 hdata.2.2.2
  let slimMetricR : MetricSpace X := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
  let slimBundleR := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
  let slimContinuousR : IsContinuousRiemannianBundle E3
      (fun x : X => TangentSpace (𝓡 3) x) :=
    radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
  let slimRiemannianR : IsRiemannianManifold (𝓡 3) X :=
    radialScaledManifold (m := mX) g hmetric
    (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
  let slimCompleteR : CompleteSpace X := (mX.rescale_completeSpace_iff
    (ρ j)⁻¹ (inv_pos.mpr (hρpos j))).mpr slimCompleteX
  let gR : SmoothRiemannianMetric (𝓡 3) X :=
    scaleMetric ((ρ j)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (hρpos j)) 2) g
  have hnR : IsMetricNorm (I := 𝓡 3) (M := X) gR := isMetricNorm_of_riemannianBundle gR
  let slimManifoldOne : IsManifold (𝓡 3) 1 X := IsManifold.of_le (by decide : 1 ≤ ∞)
  let slimTangentT2 : T2Space (TangentBundle (𝓡 3) X) := inferInstance
  have Hout := Hnew β₁ hβ hβb X gR hnR oM j Hdata.1 Hdata.2.1 Hdata.2.2 Z z αs hD c
  exact ⟨Z, mZ, z, hD, αs, c, hc1, hc2, hc3, hc4, Hout.1, Hout.2⟩


private def slimOrientationTailBound {Δ σs : ℝ} (hΔ1 : 1 ≤ Δ) (hσs : 0 < σs)
    (hσs1 : σs ≤ 1 / 100) (K : ℕ) (hK : 5 ≤ K) {v : ℝ} (hv : 0 < v)
    (A : ℝ → ℝ) {εm : ℝ} (hεm : 0 < εm) (Rm : ℝ) : ℝ :=
  Classical.choose (slimCentre_orientation_upgrade_threshold.{u}
    hΔ1 hσs hσs1 K hK hv A hεm Rm)

private theorem slimOrientationTailBound_pos {Δ σs : ℝ} (hΔ1 : 1 ≤ Δ) (hσs : 0 < σs)
    (hσs1 : σs ≤ 1 / 100) (K : ℕ) (hK : 5 ≤ K) {v : ℝ} (hv : 0 < v)
    (A : ℝ → ℝ) {εm : ℝ} (hεm : 0 < εm) (Rm : ℝ) :
    0 < slimOrientationTailBound.{u} hΔ1 hσs hσs1 K hK hv A hεm Rm :=
  (Classical.choose_spec (slimCentre_orientation_upgrade_threshold.{u}
    hΔ1 hσs hσs1 K hK hv A hεm Rm)).1

private theorem slimOrientationTailBound_apply {Δ σs : ℝ} (hΔ1 : 1 ≤ Δ) (hσs : 0 < σs)
    (hσs1 : σs ≤ 1 / 100) (K : ℕ) (hK : 5 ≤ K) {v : ℝ} (hv : 0 < v)
    (𝒜 : ℝ → ℝ) {εm : ℝ} (hεm : 0 < εm) (Rm : ℝ) {β₁ : ℝ} (hβ : 0 < β₁)
    (hβm : β₁ < slimOrientationTailBound.{u} hΔ1 hσs hσs1 K hK hv 𝒜 hεm Rm) :
      ∀ (X : Type u) [mX : MetricSpace X] [slimInst1 : ChartedSpace E3 X] [slimInst2 : IsManifold
        𝓘(ℝ, E3) ∞ X]
        [slimInst3 : CompactSpace X] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
        (hmetric : ∀ a b, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)),
        ∀ oM : ManifoldOrientation (𝓡 3) X 3,
      ∀ (ρ : X → ℝ) (hρpos : ∀ p, 0 < ρ p) (j : X) (a : ℝ), 4 * β₁⁻¹ + 4 < a →
        (0 < v ∧ v ≤ (ballVolume (normalizedCenterMetric g (ρ j) (hρpos j)) j 1).toReal ∧
          (∀ y ∈ riemannianBallOf (normalizedCenterMetric g (ρ j) (hρpos j)) j (a / 4),
            SectionalBoundedBelowAt (normalizedCenterMetric g (ρ j) (hρpos j)) y
              (-((a / 4) ^ 2)⁻¹)) ∧
          ∀ R, 0 < R → 2 * R + 2 < a → ∀ k ≤ K,
            ∀ y ∈ riemannianBallOf (normalizedCenterMetric g (ρ j) (hρpos j)) j R,
              curvatureDerivativeNorm (normalizedCenterMetric g (ρ j) (hρpos j)) k y ≤ 𝒜 R) →
        (∃ (Z : Type) (mZ : MetricSpace Z) (z : Z), letI _slimScale1 := mZ
          (∀ y y' : Z, dist y y' ≤ 10 ^ 3 * Δ) ∧
          ∃ αs : @KleinerLottApprox X (WithLp 2 (ℝ × Z))
              (mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρpos j))) _ j
              (WithLp.toLp 2 ((0 : ℝ), z)) β₁,
          let hMc : CompleteSpace X := complete_of_compact
          letI _slimScale2 := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
          letI _slimScale3 := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
          letI _slimScale4 : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3)
            x) :=
            radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
          letI _slimScale5 : IsRiemannianManifold 𝓘(ℝ, E3) X :=
            radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
          letI _slimScale6 : CompleteSpace X :=
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
              @ball X mX.toPseudoMetricSpace j (2000000 * (Δ * ρ j))) →
      ∃ (Z : Type) (mZ : MetricSpace Z) (z : Z), letI _slimScale7 := mZ
        (∀ y y' : Z, dist y y' ≤ 10 ^ 3 * Δ) ∧
        ∃ αs : @KleinerLottApprox X (WithLp 2 (ℝ × Z))
            (mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρpos j))) _ j
            (WithLp.toLp 2 ((0 : ℝ), z)) β₁,
        let hMc : CompleteSpace X := complete_of_compact
        letI _slimScale8 := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
        letI _slimScale9 := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
        letI _slimScale10 : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x)
          :=
          radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
        letI _slimScale11 : IsRiemannianManifold 𝓘(ℝ, E3) X :=
          radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
        letI _slimScale12 : CompleteSpace X :=
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
            ∃ oN : ManifoldOrientation (𝓡 3) P.N 3,
            (∀ (x : P.N) (hx : x ∈ P.j.source),
              Orientation.map (Fin 3)
                ((P.j.isLocalDiffeomorphAt 𝓘(ℝ, E3) 𝓘(ℝ, E3)
                  (K : ℕ∞ω) hx).mfderivToContinuousLinearEquiv
                    (by exact_mod_cast (show K ≠ 0 by omega))).toLinearEquiv
                  (oN.orientation x) = oM.orientation (P.j x)) ∧
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
              ∃ L : (s : Q.S) → (ℝ × E2) ≃L[ℝ] E3,
              (∀ (s : Q.S) (v : ℝ × E2), L s v =
                mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 3)
                  (fun q : ℝ × Q.S => P.e.symm (toLp 2 (q.1, Q.ψ q.2))) (0, s) v) ∧
              (∀ (s : Q.S) (b : Basis (Fin (finrank ℝ E2)) ℝ E2),
                b.orientation = (manifoldOrientationCast (by simp) Q.orientation).orientation s ↔
                  (splitFrameBasis (Basis.singleton (Fin 1) ℝ) b lineSurfaceIndex
                    (L s).toLinearEquiv).orientation =
                    (manifoldOrientationCast (by simp) oN).orientation
                      (P.e.symm (toLp 2 (0, Q.ψ s)))) ∧
              let f := realSlabMap (ball j (10 ^ 6 * Δ)) isOpen_ball c.coord
                c.lipschitz.continuous.continuousOn (905 * 10 ^ 3 * Δ)
              let z₀ : lineBallOpens (905 * 10 ^ 3 * Δ) :=
                ⟨0, zero_mem_lineBallOpens (by positivity)⟩
              let _slimFibreCharts := regularFiberChartedSpace f z₀
                (contMDiff_realSlabMap isOpen_ball
                  (c.contMDiffOn_coord.mono
                    (ball_subset_closedBall.trans c.closedBall_subset_domain)) _)
                (fun x _hx ↦ surjective_mfderiv_realSlabMap isOpen_ball
                  (c.contMDiffOn_coord.mono
                    (ball_subset_closedBall.trans c.closedBall_subset_domain))
                  c.regular x)
              Nonempty ({x // f x = z₀} ≃ₘ⟮𝓘(ℝ, P2), 𝓡 2⟯ Q.S) ∧
              (Nonempty ({x // f x = z₀} ≃ₘ⟮𝓘(ℝ, P2), 𝓡 2⟯ Metric.sphere (0 : E3) 1) ∨
                Nonempty ({x // f x = z₀} ≃ₘ⟮𝓘(ℝ, P2), 𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)⟯
                  (AddCircle (1 : ℝ) × AddCircle (1 : ℝ)))) :=
  (Classical.choose_spec (slimCentre_orientation_upgrade_threshold.{u}
    hΔ1 hσs hσs1 K hK hv 𝒜 hεm Rm)).2 β₁ hβ hβm
theorem eventually_simultaneous_slim_packets_with_orientation_reordered
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
      ∀ b : ℝ, 0 < b → b < s / 100000 → b < bc₀ → b < b₁ → 100 * Δ < b⁻¹ →
      ∀ εm Rm : ℝ, 0 < εm → ∃ b₀ : ℝ, 0 < b₀ ∧
      ∀ β : ℕ → ℝ, β 2 = β₂ → 0 < β 1 → β 1 < b₀ → β 1 < 1 →
        β 3 ≤ threeSplittingExclusionThreshold.{u, 0} →
      ∀ ζ : ℝ, β 1 < ζ → ζ < 1 →
      ∃ εz δ' Λ' : ℝ, 0 < εz ∧ 0 < δ' ∧ 0 < Λ' ∧
      ∀ T V : ℝ, 0 < T → 20 * Λ' ≤ T → T ≤ V →
      ∀ (X : ℕ → Type u) [mX : ∀ i, MetricSpace (X i)] [slimInst1 : ∀ i, ChartedSpace E3 (X i)]
        [slimInst2 : ∀ i, IsManifold 𝓘(ℝ, E3) ∞ (X i)] [slimInst3 : ∀ i, CompactSpace (X i)]
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
        ∀ oM : (i : ℕ) → ManifoldOrientation (𝓡 3) (X i) 3,
      ∀ᶠ i in atTop, ∃ ρ : X i → ℝ, ∃ hρpos : ∀ p, 0 < ρ p,
        ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ ρ ∧ LipschitzWith (Real.toNNReal Λ) ρ ∧
        (∀ p, firstVolumeScale (g i) p w / 2 < ρ p ∧
          ρ p < 2 * firstVolumeScale (g i) p (w / (2 * (1 + 2 * Λ⁻¹) ^ 3))) ∧
        (∀ p : X i,
          0 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) / (24 * ∫ t in (0 : ℝ)..1, Real.sinh t ^ 2) ∧
          w / (2 * (1 + 2 * Λ⁻¹) ^ 3) / (24 * ∫ t in (0 : ℝ)..1, Real.sinh t ^ 2) ≤
            (ballVolume (normalizedCenterMetric (g i) (ρ p) (hρpos p)) p 1).toReal ∧
          (∀ y ∈ riemannianBallOf (normalizedCenterMetric (g i) (ρ p) (hρpos p)) p (α i / 4),
            SectionalBoundedBelowAt (normalizedCenterMetric (g i) (ρ p) (hρpos p)) y
              (-((α i / 4) ^ 2)⁻¹)) ∧
          ∀ R, 0 < R → 2 * R + 2 < α i → ∀ k ≤ K,
            ∀ y ∈ riemannianBallOf (normalizedCenterMetric (g i) (ρ p) (hρpos p)) p R,
              curvatureDerivativeNorm (normalizedCenterMetric (g i) (ρ p) (hρpos p)) k y ≤
                (2 : ℝ) ^ (K + 2) * A (2 * R + 2) (w / (2 * (1 + 2 * Λ⁻¹) ^ 3))) ∧
        ∃ Js : Set (X i), Js.Finite ∧
          Js ⊆ {p | p ∈ scaledSplittingStratum.{u, 0} ρ hρpos β 1 ∧
              (∃ (Z : Type) (mZ : MetricSpace Z) (z : Z), letI _slimScale1 := mZ
                Bornology.IsBounded (univ : Set Z) ∧ diam (univ : Set Z) < 1000 * Δ ∧
                Nonempty (@KleinerLottApprox (X i) (WithLp 2 (ℝ × Z))
                  ((mX i).rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))) _ p
                  (WithLp.toLp 2 ((0 : ℝ), z)) (β 1)))} ∧
          Js.PairwiseDisjoint (fun j => ball j (Δ * ρ j / 3)) ∧
          (∀ p ∈ scaledSplittingStratum.{u, 0} ρ hρpos β 1,
              (∃ (Z : Type) (mZ : MetricSpace Z) (z : Z), letI _slimScale2 := mZ
                Bornology.IsBounded (univ : Set Z) ∧ diam (univ : Set Z) < 1000 * Δ ∧
                Nonempty (@KleinerLottApprox (X i) (WithLp 2 (ℝ × Z))
                  ((mX i).rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))) _ p
                  (WithLp.toLp 2 ((0 : ℝ), z)) (β 1))) →
            ∃ j ∈ Js, ball p (Δ * ρ p) ⊆ ball j (2 * (Δ * ρ j))) ∧
          (∀ x : X i, ((Js ∩ {j | x ∈ ball j (2000000 * (Δ * ρ j))}).ncard : ℝ) ≤
            modelVolume (-((1 / 2000000 : ℝ) ^ 2)) 3 (3 * 2000000 + 2 / 3) /
              modelVolume (-((1 / 2000000 : ℝ) ^ 2)) 3 (1 / 3)) ∧
          (∀ j ∈ Js, ∃ (Z : Type) (mZ : MetricSpace Z) (z : Z), letI _slimScale3 := mZ
            (∀ y y' : Z, dist y y' ≤ 10 ^ 3 * Δ) ∧
            ∃ αs : @KleinerLottApprox (X i) (WithLp 2 (ℝ × Z))
                ((mX i).rescale (ρ j)⁻¹ (inv_pos.mpr (hρpos j))) _ j
                (WithLp.toLp 2 ((0 : ℝ), z)) (β 1),
            let hMc : CompleteSpace (X i) := complete_of_compact
            letI _slimScale4 := (mX i).rescale (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
            letI _slimScale5 := radialScaledBundle (g i) (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
            letI _slimScale6 : IsContinuousRiemannianBundle E3 (fun x : X i => TangentSpace 𝓘(ℝ,
              E3) x) :=
              radialScaledContinuous (g i) (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
            letI _slimScale7 : IsRiemannianManifold 𝓘(ℝ, E3) (X i) :=
              radialScaledManifold (m := mX i) (g i) (hmetric i) (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
            letI _slimScale8 : CompleteSpace (X i) :=
              ((mX i).rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρpos j))).mpr hMc
            let gR : SmoothRiemannianMetric 𝓘(ℝ, E3) (X i) :=
              scaleMetric ((ρ j)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (hρpos j)) 2) (g i)
            have hnR : IsMetricNorm (I :=
              𝓘(ℝ, E3)) (M := X i) gR := isMetricNorm_of_riemannianBundle gR
            ∃ c : SlimChart gR hnR Δ σs αs,
              @ball (X i) (mX i).toPseudoMetricSpace j (2 * (Δ * ρ j)) ⊆
                (realSlabOpens (ball j (10 ^ 6 * Δ)) isOpen_ball c.coord
                  c.lipschitz.continuous.continuousOn (905 * 10 ^ 3 * Δ) : Set (X i)) ∩
                  {x | c.cutoff x = 1} ∧
              (∀ x ∈ @ball (X i) (mX i).toPseudoMetricSpace j (2 * (Δ * ρ j)),
                |c.coord x| < 3 * Δ) ∧
              tsupport c.cutoff ⊆ (realSlabOpens (ball j (10 ^ 6 * Δ)) isOpen_ball c.coord
                  c.lipschitz.continuous.continuousOn (905 * 10 ^ 3 * Δ) : Set (X i)) ∧
              tsupport c.cutoff ⊆
                @ball (X i) (mX i).toPseudoMetricSpace j (2000000 * (Δ * ρ j)) ∧
              (∃ P : SlimPacket gR hnR Δ σs αs, P.toSlimChart = c) ∧
              ∃ P : SlimProductModel c K,
                ∃ oN : ManifoldOrientation (𝓡 3) P.N 3,
                (∀ (x : P.N) (hx : x ∈ P.j.source),
                  Orientation.map (Fin 3)
                    ((P.j.isLocalDiffeomorphAt 𝓘(ℝ, E3) 𝓘(ℝ, E3)
                      (K : ℕ∞ω) hx).mfderivToContinuousLinearEquiv
                        (by exact_mod_cast (show K ≠ 0 by omega))).toLinearEquiv
                      (oN.orientation x) = (oM i).orientation (P.j x)) ∧
                closedBall P.q Rm ⊆ P.j.source ∧
                (∀ x y : P.N, (|(P.e x).fst| ≤ 95 / 100 * (10 ^ 6 * Δ) ∨ dist x P.q ≤ Rm) →
                  (|(P.e y).fst| ≤ 95 / 100 * (10 ^ 6 * Δ) ∨ dist y P.q ≤ Rm) →
                  |dist (P.j x) (P.j y) - dist x y| < εm) ∧
                (∃ (S : Finset P.N) (L : P.N → Set E3),
                  (∀ x ∈ S, IsCompact (L x) ∧ L x ⊆ (extChartAt 𝓘(ℝ, E3) x).target ∧
                    (extChartAt 𝓘(ℝ, E3) x).symm '' L x ⊆ P.j.source ∧
                    ∀ k ≤ K - 1, ∀ y ∈ L x, mapDerivNorm k
                      (pullbackMetricCoefficients gR
                        ((P.j : P.N → X i) ∘ (extChartAt 𝓘(ℝ, E3) x).symm))
                      (chartCoeff P.G x) y ≤ εm) ∧
                  ∀ x : P.N, (|(P.e x).fst| ≤ 95 / 100 * (10 ^ 6 * Δ) ∨ dist x P.q ≤ Rm) →
                    ∃ x' ∈ S, x ∈ (extChartAt 𝓘(ℝ, E3) x').source ∧
                      extChartAt 𝓘(ℝ, E3) x' x ∈ interior (L x')) ∧
                ∃ Q : SlimSurfaceFactor P,
                  ∃ L : (s : Q.S) → (ℝ × E2) ≃L[ℝ] E3,
                  (∀ (s : Q.S) (v : ℝ × E2), L s v =
                    mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 3)
                      (fun q : ℝ × Q.S => P.e.symm (toLp 2 (q.1, Q.ψ q.2))) (0, s) v) ∧
                  (∀ (s : Q.S) (b : Basis (Fin (finrank ℝ E2)) ℝ E2),
                    b.orientation = (manifoldOrientationCast (by simp) Q.orientation).orientation
                      s ↔
                      (splitFrameBasis (Basis.singleton (Fin 1) ℝ) b lineSurfaceIndex
                        (L s).toLinearEquiv).orientation =
                        (manifoldOrientationCast (by simp) oN).orientation
                          (P.e.symm (toLp 2 (0, Q.ψ s)))) ∧
                  let f := realSlabMap (ball j (10 ^ 6 * Δ)) isOpen_ball c.coord
                    c.lipschitz.continuous.continuousOn (905 * 10 ^ 3 * Δ)
                  let z₀ : lineBallOpens (905 * 10 ^ 3 * Δ) :=
                    ⟨0, zero_mem_lineBallOpens (mul_pos (by norm_num)
                      ((div_pos (by norm_num) hβ₂pos).trans hΔβ₂))⟩
                  let _slimFibreCharts := regularFiberChartedSpace f z₀
                    (contMDiff_realSlabMap isOpen_ball
                      (c.contMDiffOn_coord.mono
                        (ball_subset_closedBall.trans c.closedBall_subset_domain)) _)
                    (fun x _hx ↦ surjective_mfderiv_realSlabMap isOpen_ball
                      (c.contMDiffOn_coord.mono
                        (ball_subset_closedBall.trans c.closedBall_subset_domain))
                      c.regular x)
                  Nonempty ({x // f x = z₀} ≃ₘ⟮𝓘(ℝ, P2), 𝓡 2⟯ Q.S) ∧
                  (Nonempty ({x // f x = z₀} ≃ₘ⟮𝓘(ℝ, P2), 𝓡 2⟯ Metric.sphere (0 : E3) 1) ∨
                    Nonempty ({x // f x = z₀} ≃ₘ⟮𝓘(ℝ, P2), 𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)⟯
                      (AddCircle (1 : ℝ) × AddCircle (1 : ℝ))))) ∧
        ∃ Je : Set (X i), Je.Finite ∧
        (∀ j ∈ Je, @isEdgePoint.{u, 0} (X i)
          ((mX i).rescale (ρ j)⁻¹ (inv_pos.mpr (hρpos j))) j Δ b s) ∧
        (∀ a : X i, @isEdgePoint.{u, 0} (X i)
          ((mX i).rescale (ρ a)⁻¹ (inv_pos.mpr (hρpos a))) a Δ b s →
          ∃ j ∈ Je, dist a j < Δ * ρ j) ∧
        ∃ F : X i → ℝ, (∀ x, 0 ≤ F x) ∧ LipschitzWith (Real.toNNReal (1 + ε)) F ∧
          ∀ p ∈ Je, ∃ f : X i → ℝ, f p = 0 ∧
            (let hMc : CompleteSpace (X i) := complete_of_compact
            letI _slimScale9 := (mX i).rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
            letI _slimScale10 := radialScaledBundle (g i) (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
            letI _slimScale11 : IsContinuousRiemannianBundle E3 (fun x : X i => TangentSpace 𝓘(ℝ,
              E3) x) :=
              radialScaledContinuous (g i) (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
            letI _slimScale12 : IsRiemannianManifold 𝓘(ℝ, E3) (X i) :=
              radialScaledManifold (m := mX i) (g i) (hmetric i) (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
            letI _slimScale13 : CompleteSpace (X i) :=
              ((mX i).rescale_completeSpace_iff (ρ p)⁻¹ (inv_pos.mpr (hρpos p))).mpr hMc
            let gR : SmoothRiemannianMetric 𝓘(ℝ, E3) (X i) :=
              scaleMetric ((ρ p)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (hρpos p)) 2) (g i)
            ∃ O : Set (X i), IsOpen O ∧ closedBall p (100 * Δ) ⊆ O ∧
              ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ f O ∧
              ball p (3 * Δ) ⊆ edgeDiskDomain p Δ (fun x => f x.val)
                (fun x => F x / ρ p) (fun x => ρ x / ρ p) ∧
              EqOn ((Subtype.val : ball p (100 * Δ) → X i).extend
                (fun x => edgeCoordinateProfile (f x.val / Δ) *
                  edgeHeightProfile (F x.val / ρ p / (Δ * (ρ x.val / ρ p)))) 0) 1
                (ball p (3 * Δ)) ∧
              (∀ x ∈ ball p (100 * Δ), ∃ w : TangentSpace 𝓘(ℝ, E3) x, gR.inner x w w = 1 ∧
                1 - b - σc < mvfderiv (I := 𝓘(ℝ, E3)) f x w) ∧
              ∀ x ∈ ball p (100 * Δ), |f x| ≤ 10 * Δ → Δ / 10 ≤ F x / ρ p / (ρ x / ρ p) →
                F x / ρ p / (ρ x / ρ p) ≤ 10 * Δ →
                ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞
                  (edgeReferenceCoordinates ![f, fun z => F z / ρ p / (ρ z / ρ p)])
                  (ball x (300 * (ρ x / ρ p))) ∧
                ∀ y ∈ ball x (100 * (ρ x / ρ p)), Function.Surjective (mvfderiv (I := 𝓘(ℝ, E3))
                  (edgeReferenceCoordinates ![f, fun z => F z / ρ p / (ρ z / ρ p)]) y)) := by
  have hdim : Module.finrank ℝ E3 = 3 := finrank_euclideanSpace_fin
  have H := eventually_simultaneous_local_cover_with_regular_edge_slabs_reordered.{0, 0, u}
    (E := E3) (H := E3) (I := 𝓡 3) hdim hσs hσs1 K A hA
  refine Exists.elim H fun a₂ H => ⟨a₂, H.1, ?_⟩
  intro γ hγ hγ1
  refine Exists.elim (H.2 γ hγ hγ1) fun β₀ H => ⟨β₀, H.1, H.2.1, ?_⟩
  intro βc γc hβc hβγ hγc hγc1
  refine Exists.elim (H.2.2 βc γc hβc hβγ hγc hγc1) fun σ₀ H => ⟨σ₀, H.1, ?_⟩
  refine Exists.elim H.2 fun Δ₀ H => ⟨Δ₀, H.1, ?_⟩
  intro β₂ Δ hβ₂ hβ₂β₀ hβ₂small hΔ hΔ₀Δ
  refine Exists.elim (H.2 β₂ Δ hβ₂ hβ₂β₀ hβ₂small hΔ hΔ₀Δ) fun τ₀ H => ⟨τ₀, H.1, ?_⟩
  refine Exists.elim H.2 fun bc₀ H => ⟨bc₀, H.1, ?_⟩
  intro σc ε μ τ hσc hσcσ₀ hσc1 hε hε1 hμ hμ1 hτ hττ₀ hθ
    s b' s' hs hssmall hsb' hss' hb'd hs'd hb'e hs'e
  refine Exists.elim (H.2 σc ε μ τ hσc hσcσ₀ hσc1 hε hε1 hμ hμ1 hτ hττ₀ hθ
    s b' s' hs hssmall hsb' hss' hb'd hs'd hb'e hs'e) fun a₀ H => Exists.elim H fun b₁ H =>
      ⟨a₀, b₁, H.1, H.2.1, ?_⟩
  intro σ hσ hσa hση hσa₀ Λ hΛ hΛΔ hΛ44 hlam hbudget hend
  refine Exists.elim (H.2.2 σ hσ hσa hση hσa₀ Λ hΛ hΛΔ hΛ44 hlam hbudget hend) fun w₀ H =>
    ⟨w₀, H.1, ?_⟩
  intro w hw hww hwc b hb hbs hbc hbb₁ hsource εm Rm hεm
  have hΔ1 : 1 ≤ Δ := by
    have h100 : 100 < 100 / β₂ := (lt_div_iff₀ hβ₂).mpr (by linarith)
    linarith
  have hI : 0 < ∫ t in (0 : ℝ)..1, Real.sinh t ^ 2 := by
    refine intervalIntegral.intervalIntegral_pos_of_pos_on
      ((Real.continuous_sinh.pow 2).intervalIntegrable _ _) (fun x hx => ?_) zero_lt_one
    exact pow_pos (Real.sinh_pos_iff.mpr hx.1) 2
  have hv : 0 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) /
      (24 * ∫ t in (0 : ℝ)..1, Real.sinh t ^ 2) :=
    div_pos (div_pos hw (by positivity)) (by positivity)
  let βm := slimOrientationTailBound.{u} hΔ1 hσs hσs1 K hK hv
    (fun R => 2 ^ (K + 2) * A (2 * R + 2) (w / (2 * (1 + 2 * Λ⁻¹) ^ 3))) hεm Rm
  have hβm : 0 < βm := slimOrientationTailBound_pos.{u} hΔ1 hσs hσs1 K hK hv
    (fun R => 2 ^ (K + 2) * A (2 * R + 2) (w / (2 * (1 + 2 * Λ⁻¹) ^ 3))) hεm Rm
  refine Exists.elim (H.2 w hw hww hwc b hb hbs hbc hbb₁ hsource) fun b₀ Hβtail =>
    ⟨min b₀ βm, lt_min Hβtail.1 hβm, ?_⟩
  intro β hβ2 hβ1 hβ1b hβone hβ3 ζ hβζ hζone
  obtain ⟨εz, δ', Λ', hεz, hδ', hΛ', Htail⟩ := Hβtail.2 β hβ2 hβ1
    (hβ1b.trans_le (min_le_left _ _)) hβone hβ3 ζ hβζ hζone
  refine ⟨εz, δ', Λ', hεz, hδ', hΛ', ?_⟩
  intro T V hT hTΛ hTV X mX slimInst1 slimInst2 slimInst3 g hmetric α hα hstand hder oM
  refine (hα.eventually_gt_atTop (4 * (β 1)⁻¹ + 4)).mp
    ((Htail T V hT hTΛ hTV X g hmetric α hα hstand hder).mono fun i hi hαβ => ?_)
  exact Exists.elim hi fun ρ hi => Exists.elim hi fun hρpos hi =>
    ⟨ρ, hρpos, hi.1, hi.2.1, hi.2.2.1, hi.2.2.2.1,
      Exists.elim hi.2.2.2.2 fun Js hJ =>
        ⟨Js, hJ.1, hJ.2.1, hJ.2.2.1, hJ.2.2.2.1, hJ.2.2.2.2.1,
          fun j hj => slimOrientationTailBound_apply.{u} hΔ1 hσs hσs1 K hK hv
            (fun R => 2 ^ (K + 2) * A (2 * R + 2) (w / (2 * (1 + 2 * Λ⁻¹) ^ 3)))
            hεm Rm hβ1 (hβ1b.trans_le (min_le_right _ _)) (X i) (g i)
            (hmetric i) (oM i) ρ hρpos j (α i) hαβ (hi.2.2.2.1 j) (hJ.2.2.2.2.2.1 j hj),
          hJ.2.2.2.2.2.2⟩⟩

end DifferentialGeometry.Geometry.Collapse
