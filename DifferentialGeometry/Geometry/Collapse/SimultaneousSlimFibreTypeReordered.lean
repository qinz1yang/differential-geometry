import DifferentialGeometry.Geometry.Collapse.SimultaneousEdgeSlabsReordered
import DifferentialGeometry.Geometry.Collapse.FiniteSurface.SlimFibreTypeThresholdApplications
import DifferentialGeometry.Geometry.Collapse.FiniteSurface.SlimModelEmbeddingThreshold
import DifferentialGeometry.Geometry.Curvature.Metric.DerivativeNormCompatibility

/-!
# The complete slim bracket of LPA04/LPA06 on the reordered tail (oriented, three-dimensional)

Blueprint `master207A.tex`, LPA04 step 5 (A:30498–30507: "choose `β₁` smaller than … LFR20's slim
threshold for these same data") and the slim conclusion "LFR20 with `r = 1`, `v = v_*` and
`A = 𝒜`" (A:30531–30532); LPA06's slim packets (A:30586–30616).

`eventually_simultaneous_slim_packets_with_models_reordered`: the statement of
`eventually_simultaneous_local_cover_with_regular_edge_slabs_reordered` for closed ORIENTED
three-manifolds modelled on `ℝ³` (orientation `o i` of every `X i`, standing data with `K ≥ 5`), in
which every slim chart `c` at every slim centre `j ∈ Js` in addition
* extends to an LC85 `SlimPacket` (`P.toSlimChart = c`: the entire zero fibre is connected and
  homeomorphic to `S²` or `T²`; LFR20 item 2), and
* carries an LFR20 item 3 / LC81 product model (`Nonempty (SlimProductModel c K)`).

LFR20's thresholds (`exists_slimPacket_threshold`, `slimChart_model_embedding_threshold`, F7-LFR20b)
are taken at `Δ, σs, K`, `r = 1`, `v = v_* = w'/(24 ∫₀¹ sinh²)`, `A(R) = 2^{K+2} A'(2R + 2, w')`,
`w' = w/(2(1 + 2Λ⁻¹)³)`. This is possible because the chain is in the blueprint order: `w` (hence
`v_*`, `𝒜`) is fixed BEFORE `b₀` and the tolerances `β`. On the tail, the threshold hypotheses at
`j` (volume of `B(j, 1)`, derivative bounds on `B(j, R)` for `R < β₁⁻¹`, `sec ≥ -β₁²` on
`B(j, β₁⁻¹)`, all for the normalized metric `ρ(j)⁻² g`) are LPA01's analytic data at `j`, which
the reordered tail carries at every point.
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
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis
open DifferentialGeometry.Analysis.Calculus

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

universe u

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

/-- `finrank ℝ ℝ³ ≠ 0`, for the chain theorems' `NeZero` argument. -/
local instance nezero_finrank_euclideanThree_F8LPA3 : NeZero (Module.finrank ℝ E3) :=
  ⟨by rw [finrank_euclideanSpace_fin]; decide⟩

/-- **The complete slim bracket (fibre type and product model at every slim centre) on the
reordered tail.** See the module docstring. -/
theorem eventually_simultaneous_slim_packets_with_models_reordered
    {σs : ℝ} (hσs : 0 < σs) (hσs1 : σs ≤ 1 / 100) (K : ℕ) (hK : 5 ≤ K) (A : ℝ → ℝ → ℝ)
    (hA : ∀ C v, 0 < C → 0 < v → v < 4 * Real.pi / 3 → 0 < A C v) :
    ∃ a₂ : ℝ, 0 < a₂ ∧ ∀ γ : ℝ, 0 < γ → γ < 1 / 10 → ∃ β₀ : ℝ, 0 < β₀ ∧ β₀ ≤ a₂ ∧
      ∀ βc γc : ℝ, 0 < βc → βc < γc / 1000 → 0 < γc → γc < 1 / 100 →
      ∃ σ₀ : ℝ, 0 < σ₀ ∧ ∃ Δ₀ : ℝ, 0 < Δ₀ ∧
      ∀ β₂ Δ : ℝ, 0 < β₂ → β₂ ≤ β₀ → β₂ < 1 / 100 → 100 / β₂ < Δ → Δ₀ ≤ Δ →
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
              Nonempty (SlimProductModel c K)) ∧
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
  obtain ⟨a₂, ha₂, h⟩ :=
    eventually_simultaneous_local_cover_with_regular_edge_slabs_reordered.{0, 0, u}
      (E := E3) (H := E3) (I := 𝓘(ℝ, E3)) hdim hσs hσs1 K A hA
  refine ⟨a₂, ha₂, fun γ hγ hγ1 => ?_⟩
  obtain ⟨β₀, hβ₀, hβ₀a, h⟩ := h γ hγ hγ1
  refine ⟨β₀, hβ₀, hβ₀a, fun βc γc hβc hβγ hγc hγc1 => ?_⟩
  obtain ⟨σ₀, hσ₀, Δ₀, hΔ₀, h⟩ := h βc γc hβc hβγ hγc hγc1
  refine ⟨σ₀, hσ₀, Δ₀, hΔ₀, fun β₂ Δ hβ₂ hβ₂β₀ hβ₂small hΔ hΔ₀Δ => ?_⟩
  have hΔ1 : 1 ≤ Δ := by
    have h100 : 100 < 100 / β₂ := (lt_div_iff₀ hβ₂).mpr (by linarith)
    linarith
  obtain ⟨τ₀, hτ₀, bc₀, hbc₀, h⟩ := h β₂ Δ hβ₂ hβ₂β₀ hβ₂small hΔ hΔ₀Δ
  refine ⟨τ₀, hτ₀, bc₀, hbc₀, fun σc ε μ τ hσc hσcσ₀ hσc1 hε hε1 hμ hμ1 hτ hττ₀ hθ s b' s' hs
    hssmall hsb' hss' hb'd hs'd hb'e hs'e => ?_⟩
  obtain ⟨a₀, b₁, ha₀, hb₁, h⟩ := h σc ε μ τ hσc hσcσ₀ hσc1 hε hε1 hμ hμ1 hτ hττ₀ hθ s b' s' hs
    hssmall hsb' hss' hb'd hs'd hb'e hs'e
  refine ⟨a₀, b₁, ha₀, hb₁, fun σ hσ hσa hση hσa₀ Λ hΛ hΛΔ hΛ44 hlam hbudget hend => ?_⟩
  obtain ⟨w₀, hw₀, h⟩ := h σ hσ hσa hση hσa₀ Λ hΛ hΛΔ hΛ44 hlam hbudget hend
  refine ⟨w₀, hw₀, fun w hw hww hwc b hb hbs hbc hbb₁ hsource => ?_⟩
  -- LPA01's `v_*` and `𝒜` for this `w` (A:30301–30306), fixed BEFORE `b₀`
  have hden : 1 < 2 * (1 + 2 * Λ⁻¹) ^ 3 := by
    have h := one_le_pow₀ (show 1 ≤ 1 + 2 * Λ⁻¹ by linarith [inv_pos.mpr hΛ]) (n := 3)
    linarith
  have hv : 0 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) / (24 * ∫ t in (0 : ℝ)..1, Real.sinh t ^ 2) :=
    div_pos (div_pos hw (by linarith)) (by positivity)
  obtain ⟨βf, hβf, hfib⟩ := exists_slimPacket_threshold.{u, 0} hΔ1 hσs hσs1 K hK one_pos hv
    (fun R => 2 ^ (K + 2) * A (2 * R + 2) (w / (2 * (1 + 2 * Λ⁻¹) ^ 3)))
  obtain ⟨βm, hβm, hmod⟩ := slimChart_model_embedding_threshold.{u, 0} hΔ1 hσs hσs1 K hK one_pos
    hv (fun R => 2 ^ (K + 2) * A (2 * R + 2) (w / (2 * (1 + 2 * Λ⁻¹) ^ 3)))
  obtain ⟨b₀, hb₀, h⟩ := h w hw hww hwc b hb hbs hbc hbb₁ hsource
  refine ⟨min b₀ (min βf βm), lt_min hb₀ (lt_min hβf hβm),
    fun β hβ2 hβ1 hβ1b hβone hβ3 ζ hβζ hζone => ?_⟩
  have hβf1 : β 1 < βf := hβ1b.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hβm1 : β 1 < βm := hβ1b.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨εz, δ', Λ', hεz, hδ', hΛ', h⟩ :=
    h β hβ2 hβ1 (hβ1b.trans_le (min_le_left _ _)) hβone hβ3 ζ hβζ hζone
  refine ⟨εz, δ', Λ', hεz, hδ', hΛ',
    fun T V hT hTΛ hTV X mX _ _ _ g hmetric α hα hstand hder o => ?_⟩
  filter_upwards [h T V hT hTΛ hTV X g hmetric α hα hstand hder,
    hα.eventually_gt_atTop (4 * (β 1)⁻¹ + 4)] with i hi hαβ
  obtain ⟨ρ, hρpos, hρsm, hρlip, hρb, hdata, Js, hJsfin, hJsS, hJsdisj, hJscov, hJsmult, hslim, Je,
    hJefin, hJeE, hJecovE, F, hF0, hFL, hedge⟩ := hi
  refine ⟨ρ, hρpos, hρsm, hρlip, hρb, hdata, Js, hJsfin, hJsS, hJsdisj, hJscov, hJsmult,
    fun j hj => ?_, Je, hJefin, hJeE, hJecovE, F, hF0, hFL, hedge⟩
  obtain ⟨Z, mZ, z, hD, αs, c, hc1, hc2, hc3, hc4⟩ := hslim j hj
  obtain ⟨-, hvol0, hsec0, hder0⟩ := hdata j
  have hconn0 : ConnectedSpace (X i) := connectedSpace_of_aligned_metric (g i) (hmetric i) j
  let hMc : CompleteSpace (X i) := complete_of_compact
  let mR : MetricSpace (X i) := (mX i).rescale (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
  let bR := radialScaledBundle (g i) (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
  let cR : IsContinuousRiemannianBundle E3 (fun x : X i => TangentSpace 𝓘(ℝ, E3) x) :=
    radialScaledContinuous (g i) (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
  let iR : IsRiemannianManifold 𝓘(ℝ, E3) (X i) :=
    radialScaledManifold (m := mX i) (g i) (hmetric i) (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
  let kR : CompleteSpace (X i) :=
    ((mX i).rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρpos j))).mpr hMc
  let gR : SmoothRiemannianMetric 𝓘(ℝ, E3) (X i) :=
    scaleMetric ((ρ j)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (hρpos j)) 2) (g i)
  have hnR : IsMetricNorm (I := 𝓘(ℝ, E3)) (M := X i) gR := isMetricNorm_of_riemannianBundle gR
  have hconn : ConnectedSpace (X i) := hconn0
  have : IsManifold 𝓘(ℝ, E3) 1 (X i) := IsManifold.of_le (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  have hT2 : T2Space (TangentBundle 𝓘(ℝ, E3) (X i)) := inferInstance
  have hmeq : normalizedCenterMetric (g i) (ρ j) (hρpos j) = gR := by
    have key : ∀ (c d : ℝ) (hc : 0 < c) (hd : 0 < d), c = d →
        scaleMetric c hc (g i) = scaleMetric d hd (g i) := by
      rintro c d hc hd rfl
      rfl
    exact key _ _ _ _ (inv_pow (ρ j) 2).symm
  have hball : ∀ r, riemannianBallOf gR j r = ball j r := fun r =>
    DifferentialGeometry.Geometry.Metric.riemannianBallOf_eq_ball_of_isMetricNorm gR hnR j r
  have hβinv : 0 < (β 1)⁻¹ := inv_pos.mpr hβ1
  have hvol : ENNReal.ofReal (w / (2 * (1 + 2 * Λ⁻¹) ^ 3) /
      (24 * ∫ t in (0 : ℝ)..1, Real.sinh t ^ 2)) ≤
      riemannianVolumeMeasure 𝓘(ℝ, E3) (X i) gR (ball j 1) := by
    rw [hmeq] at hvol0
    rw [← hball 1]
    exact (ENNReal.ofReal_le_ofReal hvol0).trans ENNReal.ofReal_toReal_le
  have hsec : ∀ y ∈ ball j (β 1)⁻¹, SectionalBoundedBelowAt gR y (-β 1 ^ 2) := by
    intro y hy
    have hq : (β 1)⁻¹ ≤ α i / 4 := by linarith
    have hy' : y ∈ riemannianBallOf (normalizedCenterMetric (g i) (ρ j) (hρpos j)) j (α i / 4) := by
      rw [hmeq, hball]
      exact ball_subset_ball hq hy
    have hs := hsec0 y hy'
    rw [hmeq] at hs
    refine hs.mono ?_
    rw [neg_le_neg_iff, ← inv_pow]
    have hα4 : 0 < α i / 4 := hβinv.trans_le hq
    have hinv : (α i / 4)⁻¹ ≤ β 1 := by
      rw [inv_le_comm₀ hα4 hβ1]
      exact hq
    exact pow_le_pow_left₀ (inv_pos.mpr hα4).le hinv 2
  have hcurv : ∀ R, 0 < R → R < (β 1)⁻¹ → ∀ k ≤ K, ∀ y ∈ ball j R,
      curvDerivNorm k gR y ≤ 2 ^ (K + 2) * A (2 * R + 2) (w / (2 * (1 + 2 * Λ⁻¹) ^ 3)) := by
    intro R hR hRβ k hk y hy
    have hy' : y ∈ riemannianBallOf (normalizedCenterMetric (g i) (ρ j) (hρpos j)) j R := by
      rw [hmeq, hball]
      exact hy
    have hd := hder0 R hR (by linarith) k hk y hy'
    rw [hmeq, curvatureDerivativeNorm_eq_curvDerivNorm] at hd
    exact hd
  obtain ⟨-, hP⟩ := hfib (β 1) hβ1 hβf1 (X i) gR hnR (o i) j hvol hcurv hsec Z z αs hD
  exact ⟨Z, mZ, z, hD, αs, c, hc1, hc2, hc3, hc4, hP c,
    hmod (β 1) hβ1 hβm1 (X i) gR hnR (o i) j hvol hcurv hsec Z z αs hD c⟩

end DifferentialGeometry.Geometry.Collapse
