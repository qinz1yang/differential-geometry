import DifferentialGeometry.Geometry.Collapse.SimultaneousSlimFibreTypeReordered
import DifferentialGeometry.Geometry.Collapse.FiniteSurface.SlimFibreDiffeomorphApplications

/-!
# The complete slim bracket with LFR20's comparison and smooth fibre type on the reordered tail

Blueprint `master207A.tex`, LPA04 step 5 (A:30498–30507: "choose `β₁` smaller than … LFR20's slim
threshold for these same data"), LFR20 items 1–3 (comparison for the same `j`, surface factor,
smooth fibre type) and LPA06's slim packets (A:30586–30616).

`eventually_simultaneous_slim_packets_with_comparison_reordered`: the statement of
`eventually_simultaneous_slim_packets_with_models_reordered` with exactly two changes:
* a comparison tolerance `εm > 0` and a buffer radius `Rm` are quantified right after
  `100 * Δ < b⁻¹` and before `∃ b₀` (order `… w ≺ b ≺ (εm, Rm) ≺ b₀ ≺ β₁`: only `b₀` depends on
  them);
* at every slim centre the bare `Nonempty (SlimProductModel c K)` is replaced by the conclusion of
  `slimChart_zeroFibre_smooth_type_threshold` at `ε := εm`, `R := Rm`: an LC81 product model `P`
  whose own `j` is `εm`-close to an isometry on the buffer `{|t| ≤ 19L/20} ∪ B̄(q, Rm)` (source
  inclusion, pointed distances, finite chart atlas with the `C^{K-1}` coefficient bound), a
  surface factor `Q : SlimSurfaceFactor P`, and the entire zero fibre (with `SlimChart.trivial`'s
  regular-fibre structure) smoothly diffeomorphic to `Q.S` and to `S²` or `T²`.

The per-centre work is the separate lemma `slimCentre_comparison_upgrade_threshold`: LFR20's
thresholds `exists_slimPacket_threshold` and `slimChart_zeroFibre_smooth_type_threshold` at the
same data (`r = 1`, `v = v_*`, `A(R) = 2^{K+2} A'(2R + 2, w')`, `ε := εm`, `R := Rm`), applied at a
centre `j` whose normalized metric `ρ(j)⁻² g` carries LPA01's analytic data with scale
`α > 4 β₁⁻¹ + 4` (volume of `B(j, 1)`, derivative bounds on `B(j, R)` for `R < β₁⁻¹`,
`sec ≥ -β₁²` on `B(j, β₁⁻¹)`). The chain theorem threads the quantifier prefix of
`eventually_simultaneous_local_cover_with_regular_edge_slabs_reordered` and takes
`b₀ := min b₀' β₀(εm, Rm)` from that lemma.
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
local instance nezero_finrank_euclideanThree_CH13CLOSE2 : NeZero (Module.finrank ℝ E3) :=
  ⟨by rw [finrank_euclideanSpace_fin]; decide⟩


/-- **Per-centre upgrade (threshold form).** For `Δ ≥ 1`, `0 < σs ≤ 1/100`, `K ≥ 5`, `v > 0`, `𝒜`,
`εm > 0` and `Rm` there is `β₀ > 0` such that for `0 < β₁ < β₀`, at a centre `j` of a closed oriented
three-manifold carrying LPA01's normalized analytic data at `j` with scale `a > 4 β₁⁻¹ + 4`, every slim
centre conclusion of `eventually_simultaneous_local_cover_with_regular_edge_slabs_reordered` (`Z`, `αs`,
slim chart `c` with its plateau clauses) upgrades to the same data with LC85's `SlimPacket` extension
of `c` and the conclusion of `slimChart_zeroFibre_smooth_type_threshold` at `ε := εm`, `R := Rm`. -/
theorem slimCentre_comparison_upgrade_threshold {Δ σs : ℝ} (hΔ1 : 1 ≤ Δ) (hσs : 0 < σs)
    (hσs1 : σs ≤ 1 / 100) (K : ℕ) (hK : 5 ≤ K) {v : ℝ} (hv : 0 < v) (𝒜 : ℝ → ℝ) {εm : ℝ}
    (hεm : 0 < εm) (Rm : ℝ) :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β₁ : ℝ, 0 < β₁ → β₁ < β₀ →
      ∀ (X : Type u) [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
        [CompactSpace X] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
        (hmetric : ∀ a b, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)),
        ManifoldOrientation (𝓡 3) X 3 →
      ∀ (ρ : X → ℝ) (hρpos : ∀ p, 0 < ρ p) (j : X) (a : ℝ), 4 * β₁⁻¹ + 4 < a →
        (0 < v ∧ v ≤ (ballVolume (normalizedCenterMetric g (ρ j) (hρpos j)) j 1).toReal ∧
          (∀ y ∈ riemannianBallOf (normalizedCenterMetric g (ρ j) (hρpos j)) j (a / 4),
            SectionalBoundedBelowAt (normalizedCenterMetric g (ρ j) (hρpos j)) y
              (-((a / 4) ^ 2)⁻¹)) ∧
          ∀ R, 0 < R → 2 * R + 2 < a → ∀ k ≤ K,
            ∀ y ∈ riemannianBallOf (normalizedCenterMetric g (ρ j) (hρpos j)) j R,
              curvatureDerivativeNorm (normalizedCenterMetric g (ρ j) (hρpos j)) k y ≤ 𝒜 R) →
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
              @ball X mX.toPseudoMetricSpace j (2000000 * (Δ * ρ j))) →
      ∃ (Z : Type) (mZ : MetricSpace Z) (z : Z), letI := mZ
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
                  (AddCircle (1 : ℝ) × AddCircle (1 : ℝ)))) := by
  obtain ⟨βf, hβf, hfib⟩ := exists_slimPacket_threshold.{u, 0} hΔ1 hσs hσs1 K hK one_pos hv 𝒜
  obtain ⟨βm, hβm, hmod⟩ := slimChart_zeroFibre_smooth_type_threshold.{u, 0} hΔ1 hσs hσs1 K hK
    one_pos hv 𝒜 hεm Rm
  refine ⟨min βf βm, lt_min hβf hβm,
    fun β₁ hβ1 hβ1b X mX _ _ _ g hmetric o ρ hρpos j a hαβ hdata hslim => ?_⟩
  have hβf1 : β₁ < βf := hβ1b.trans_le (min_le_left _ _)
  have hβm1 : β₁ < βm := hβ1b.trans_le (min_le_right _ _)
  obtain ⟨Z, mZ, z, hD, αs, c, hc1, hc2, hc3, hc4⟩ := hslim
  obtain ⟨-, hvol0, hsec0, hder0⟩ := hdata
  have hconn0 : ConnectedSpace X := connectedSpace_of_aligned_metric g hmetric j
  let hMc : CompleteSpace X := complete_of_compact
  let mR : MetricSpace X := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
  let bR := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
  let cR : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
    radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
  let iR : IsRiemannianManifold 𝓘(ℝ, E3) X :=
    radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
  let kR : CompleteSpace X :=
    (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρpos j))).mpr hMc
  let gR : SmoothRiemannianMetric 𝓘(ℝ, E3) X :=
    scaleMetric ((ρ j)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (hρpos j)) 2) g
  have hnR : IsMetricNorm (I := 𝓘(ℝ, E3)) (M := X) gR := isMetricNorm_of_riemannianBundle gR
  have hconn : ConnectedSpace X := hconn0
  have : IsManifold 𝓘(ℝ, E3) 1 X := IsManifold.of_le (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  have hT2 : T2Space (TangentBundle 𝓘(ℝ, E3) X) := inferInstance
  have hmeq : normalizedCenterMetric g (ρ j) (hρpos j) = gR := by
    have key : ∀ (c d : ℝ) (hc : 0 < c) (hd : 0 < d), c = d →
        scaleMetric c hc g = scaleMetric d hd g := by
      rintro c d hc hd rfl
      rfl
    exact key _ _ _ _ (inv_pow (ρ j) 2).symm
  have hball : ∀ r, riemannianBallOf gR j r = ball j r := fun r =>
    DifferentialGeometry.Geometry.Metric.riemannianBallOf_eq_ball_of_isMetricNorm gR hnR j r
  have hβinv : 0 < β₁⁻¹ := inv_pos.mpr hβ1
  have hvol : ENNReal.ofReal v ≤ riemannianVolumeMeasure 𝓘(ℝ, E3) X gR (ball j 1) := by
    rw [hmeq] at hvol0
    rw [← hball 1]
    exact (ENNReal.ofReal_le_ofReal hvol0).trans ENNReal.ofReal_toReal_le
  have hsec : ∀ y ∈ ball j β₁⁻¹, SectionalBoundedBelowAt gR y (-β₁ ^ 2) := by
    intro y hy
    have hq : β₁⁻¹ ≤ a / 4 := by linarith
    have hy' : y ∈ riemannianBallOf (normalizedCenterMetric g (ρ j) (hρpos j)) j (a / 4) := by
      rw [hmeq, hball]
      exact ball_subset_ball hq hy
    have hs := hsec0 y hy'
    rw [hmeq] at hs
    refine hs.mono ?_
    rw [neg_le_neg_iff, ← inv_pow]
    have hα4 : 0 < a / 4 := hβinv.trans_le hq
    have hinv : (a / 4)⁻¹ ≤ β₁ := by
      rw [inv_le_comm₀ hα4 hβ1]
      exact hq
    exact pow_le_pow_left₀ (inv_pos.mpr hα4).le hinv 2
  have hcurv : ∀ R, 0 < R → R < β₁⁻¹ → ∀ k ≤ K, ∀ y ∈ ball j R, curvDerivNorm k gR y ≤ 𝒜 R := by
    intro R hR hRβ k hk y hy
    have hy' : y ∈ riemannianBallOf (normalizedCenterMetric g (ρ j) (hρpos j)) j R := by
      rw [hmeq, hball]
      exact hy
    have hd := hder0 R hR (by linarith) k hk y hy'
    rw [hmeq, curvatureDerivativeNorm_eq_curvDerivNorm] at hd
    exact hd
  obtain ⟨-, hP⟩ := hfib β₁ hβ1 hβf1 X gR hnR o j hvol hcurv hsec Z z αs hD
  exact ⟨Z, mZ, z, hD, αs, c, hc1, hc2, hc3, hc4, hP c,
    hmod β₁ hβ1 hβm1 X gR hnR o j hvol hcurv hsec Z z αs hD c⟩

/-- **The complete slim bracket with LFR20's comparison for the same `j`, the surface factor and
the smooth fibre type at every slim centre, on the reordered tail.** See the module docstring. -/
theorem eventually_simultaneous_slim_packets_with_comparison_reordered
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
              (∃ (Z : Type) (mZ : MetricSpace Z) (z : Z), letI := mZ
                Bornology.IsBounded (univ : Set Z) ∧ diam (univ : Set Z) < 1000 * Δ ∧
                Nonempty (@KleinerLottApprox (X i) (WithLp 2 (ℝ × Z))
                  ((mX i).rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))) _ p
                  (WithLp.toLp 2 ((0 : ℝ), z)) (β 1)))} ∧
          Js.PairwiseDisjoint (fun j => ball j (Δ * ρ j / 3)) ∧
          (∀ p ∈ scaledSplittingStratum.{u, 0} ρ hρpos β 1,
              (∃ (Z : Type) (mZ : MetricSpace Z) (z : Z), letI := mZ
                Bornology.IsBounded (univ : Set Z) ∧ diam (univ : Set Z) < 1000 * Δ ∧
                Nonempty (@KleinerLottApprox (X i) (WithLp 2 (ℝ × Z))
                  ((mX i).rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))) _ p
                  (WithLp.toLp 2 ((0 : ℝ), z)) (β 1))) →
            ∃ j ∈ Js, ball p (Δ * ρ p) ⊆ ball j (2 * (Δ * ρ j))) ∧
          (∀ x : X i, ((Js ∩ {j | x ∈ ball j (2000000 * (Δ * ρ j))}).ncard : ℝ) ≤
            modelVolume (-((1 / 2000000 : ℝ) ^ 2)) 3 (3 * 2000000 + 2 / 3) /
              modelVolume (-((1 / 2000000 : ℝ) ^ 2)) 3 (1 / 3)) ∧
          (∀ j ∈ Js, ∃ (Z : Type) (mZ : MetricSpace Z) (z : Z), letI := mZ
            (∀ y y' : Z, dist y y' ≤ 10 ^ 3 * Δ) ∧
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
            letI := (mX i).rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
            letI := radialScaledBundle (g i) (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
            letI : IsContinuousRiemannianBundle E3 (fun x : X i => TangentSpace 𝓘(ℝ, E3) x) :=
              radialScaledContinuous (g i) (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
            letI : IsRiemannianManifold 𝓘(ℝ, E3) (X i) :=
              radialScaledManifold (m := mX i) (g i) (hmetric i) (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
            letI : CompleteSpace (X i) :=
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
  have hI : 0 < ∫ t in (0 : ℝ)..1, Real.sinh t ^ 2 := by
    refine intervalIntegral.intervalIntegral_pos_of_pos_on
      ((Real.continuous_sinh.pow 2).intervalIntegrable _ _) (fun x hx => ?_) zero_lt_one
    exact pow_pos (Real.sinh_pos_iff.mpr hx.1) 2
  have H := eventually_simultaneous_local_cover_with_regular_edge_slabs_reordered.{0, 0, u}
    (E := E3) (H := E3) (I := 𝓘(ℝ, E3)) hdim hσs hσs1 K A hA
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
    ⟨w₀, H.1, fun w hw hww hwc b hb hbs hbc hbb₁ hsource εm Rm hεm => ?_⟩
  -- LPA01's `v_*` and `𝒜` for this `w` (A:30301–30306), fixed BEFORE `b₀`
  have hden : 1 < 2 * (1 + 2 * Λ⁻¹) ^ 3 := by
    have h := one_le_pow₀ (show 1 ≤ 1 + 2 * Λ⁻¹ by linarith [inv_pos.mpr hΛ]) (n := 3)
    linarith
  have hv : 0 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) / (24 * ∫ t in (0 : ℝ)..1, Real.sinh t ^ 2) :=
    div_pos (div_pos hw (by linarith)) (by positivity)
  refine Exists.elim (slimCentre_comparison_upgrade_threshold hΔ1 hσs hσs1 K hK hv
    (fun R => 2 ^ (K + 2) * A (2 * R + 2) (w / (2 * (1 + 2 * Λ⁻¹) ^ 3))) hεm Rm) fun βm Hm => ?_
  refine Exists.elim (H.2 w hw hww hwc b hb hbs hbc hbb₁ hsource) fun b₀ H =>
    ⟨min b₀ βm, lt_min H.1 Hm.1, fun β hβ2 hβ1 hβ1b hβone hβ3 ζ hβζ hζone => ?_⟩
  refine Exists.elim (H.2 β hβ2 hβ1 (hβ1b.trans_le (min_le_left _ _)) hβone hβ3 ζ hβζ hζone)
    fun εz H => Exists.elim H fun δ' H => Exists.elim H fun Λ' H => ⟨εz, δ', Λ', H.1, H.2.1,
      H.2.2.1, fun T V hT hTΛ hTV X mX _ _ _ g hmetric α hα hstand hder o => ?_⟩
  refine (hα.eventually_gt_atTop (4 * (β 1)⁻¹ + 4)).mp
    ((H.2.2.2 T V hT hTΛ hTV X g hmetric α hα hstand hder).mono fun i hi hαβ => ?_)
  exact Exists.elim hi fun ρ hi => Exists.elim hi fun hρpos hi =>
    ⟨ρ, hρpos, hi.1, hi.2.1, hi.2.2.1, hi.2.2.2.1, Exists.elim hi.2.2.2.2 fun Js hJ =>
      ⟨Js, hJ.1, hJ.2.1, hJ.2.2.1, hJ.2.2.2.1, hJ.2.2.2.2.1, fun j hj =>
        Hm.2 (β 1) hβ1 (hβ1b.trans_le (min_le_right _ _)) (X i) (g i) (hmetric i) (o i) ρ hρpos j
          (α i) hαβ (hi.2.2.2.1 j) (hJ.2.2.2.2.2.1 j hj), hJ.2.2.2.2.2.2⟩⟩

end DifferentialGeometry.Geometry.Collapse
