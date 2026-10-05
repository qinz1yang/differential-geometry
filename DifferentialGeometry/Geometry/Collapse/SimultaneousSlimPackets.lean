import DifferentialGeometry.Geometry.Collapse.SimultaneousEdgeAnalyticData
import DifferentialGeometry.Geometry.Collapse.LocalExport.SlimChartApplications

/-!
# The slim half of LPA04/LPA06: an LC85 slim chart at every slim centre on the edge tail

Blueprint `master207A.tex`, LPA04 (A:30447–30546: "LC85/LFR20 hold at every slim one-stratum
point"; step 5: "choose `β₁` smaller than … LFR20's slim threshold for these same data. An actual
slim factor has diameter `< 1000Δ`, so LFR20 applies with its fixed weak inequality") and LPA06
(A:30586–30616: "on a slim covering ball LFR20's value estimate gives `|η| < 2Δ < 8·10⁵Δ`. Hence
the cutoffs equal one there, and both balls lie inside the respective proper bundle domain"; slim
cutoffs are supported in `B(p_i, 2·10⁶ r_i)`).

* `exists_slimChart_at_centre`: LFR19 + LFR20 (`exists_slimChart`, F7-LFR20b) in the standing
  convention: in the normalization `(ρ⁻¹ d, ρ⁻² g)` of a closed manifold with an aligned metric, a
  normalized `(1, β)`-splitting with slim factor of diameter `≤ 10³Δ` and `sec ≥ -(β/ρ)²` on
  `B(p, β⁻¹ρ)` carries an LC85 `SlimChart`; its proper slab domain and cutoff plateau contain the
  covering ball `B(p, 2Δρ)` (where `|η| < 3Δ`), and the cutoff is supported in the slab and in
  `B(p, 2·10⁶Δρ)`.
* `eventually_simultaneous_local_cover_with_slim_and_edge_packets`: the parameter chain of
  `eventually_edge_coordinates_with_analytic_data` (G5's chain + (LPA.1)) with one slim quality
  `0 < σs ≤ 1/100` fixed first and LFR20's threshold folded into `b₀`. On ONE tail and ONE
  scale `ρ`: LPA01's analytic data at every point; the finite slim family `Js` (slim one-stratum
  centres, `Δρ/3`-disjoint, covering every slim point, multiplicity bound) with a slim chart at
  EVERY `j ∈ Js` for the SAME `ρ`; and the edge family `Je` with ONE smoothing `F` and an actual
  coordinate `f` at every edge centre, as in `eventually_edge_coordinates_with_analytic_data`.

NOT supplied (LFR20 item 2's "connected fiber, smoothly `S²` or `T²`" and item 3's finite product
`ℝ × Z` with its embedding): they are left out, not assumed. The fibre type exists only in SEQUENCE
form (`eventually_nonempty_slimPacket`, `LocalExport/SlimPacketApplications`): it needs, for one
fixed sequence of pointed slim charts, LFR14's limit data `(N, G, oN, j, Φ)` with the splitting
coordinates converging (`hU`), and it is stated for manifolds modelled on `𝓘(ℝ, ℝ³)`. On this tail
the slim centres are many per index and vary with the index, so the uniform THRESHOLD form is needed
(for `β < β₀` every slim chart of a noncollapsed, derivative-bounded, oriented manifold is a
`SlimPacket`); it waits for the LFR16 row and LFR14's compactness at slim points.
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
open DifferentialGeometry.Analysis
open DifferentialGeometry.Analysis.Calculus

namespace DifferentialGeometry.Geometry.Collapse

universe uE uH u v

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

/-- **An LC85 slim chart at a slim centre, in the standing convention.** See the module
docstring. -/
theorem exists_slimChart_at_centre {Δ σs : ℝ} (hΔ : 1 ≤ Δ) (hσs : 0 < σs) (hσs1 : σs ≤ 1 / 100) :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β : ℝ, 0 < β → β < β₀ →
    ∀ (M : Type u) [m : MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [CompactSpace M]
      (g : SmoothRiemannianMetric I M)
      (hmetric : ∀ a b : M, riemannianEDistOf (I := I) g a b = ENNReal.ofReal (dist a b))
      (R : ℝ) (hR : 0 < R) (p : M) (A : Type v) [MetricSpace A] (a : A),
      (∀ y z : A, dist y z ≤ 10 ^ 3 * Δ) →
      ∀ α : @KleinerLottApprox M (WithLp 2 (ℝ × A)) (m.rescale R⁻¹ (inv_pos.mpr hR)) _ p
        (WithLp.toLp 2 ((0 : ℝ), a)) β,
      (∀ z ∈ ball p (β⁻¹ * R), SectionalBoundedBelowAt g z (-(β / R) ^ 2)) →
      let hMc : CompleteSpace M := complete_of_compact
      letI := m.rescale R⁻¹ (inv_pos.mpr hR)
      letI := radialScaledBundle g R⁻¹ (inv_pos.mpr hR)
      letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
        radialScaledContinuous g R⁻¹ (inv_pos.mpr hR)
      letI : IsRiemannianManifold I M :=
        radialScaledManifold (m := m) g hmetric R⁻¹ (inv_pos.mpr hR)
      letI : CompleteSpace M := (m.rescale_completeSpace_iff R⁻¹ (inv_pos.mpr hR)).mpr hMc
      let gR : SmoothRiemannianMetric I M := scaleMetric (R⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2) g
      have hnR : IsMetricNorm (I := I) (M := M) gR := isMetricNorm_of_riemannianBundle gR
      ∃ c : SlimChart gR hnR Δ σs α,
        @ball M m.toPseudoMetricSpace p (2 * (Δ * R)) ⊆
          (realSlabOpens (ball p (10 ^ 6 * Δ)) isOpen_ball c.coord
            c.lipschitz.continuous.continuousOn (905 * 10 ^ 3 * Δ) : Set M) ∩
            {x | c.cutoff x = 1} ∧
        (∀ x ∈ @ball M m.toPseudoMetricSpace p (2 * (Δ * R)), |c.coord x| < 3 * Δ) ∧
        tsupport c.cutoff ⊆ (realSlabOpens (ball p (10 ^ 6 * Δ)) isOpen_ball c.coord
            c.lipschitz.continuous.continuousOn (905 * 10 ^ 3 * Δ) : Set M) ∧
        tsupport c.cutoff ⊆ @ball M m.toPseudoMetricSpace p (2000000 * (Δ * R)) := by
  obtain ⟨β₀, hβ₀, h⟩ := exists_slimChart.{uE, uH, u, v} hΔ hσs hσs1
  refine ⟨β₀, hβ₀, fun β hβ hββ₀ M m _ _ _ g hmetric R hR p A _ a hD α hsec => ?_⟩
  have hsecR := radialScaled_sectional_bound g (r := β⁻¹) hR hsec
  intro hMc
  let mR : MetricSpace M := m.rescale R⁻¹ (inv_pos.mpr hR)
  let bR := radialScaledBundle g R⁻¹ (inv_pos.mpr hR)
  let cR : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    radialScaledContinuous g R⁻¹ (inv_pos.mpr hR)
  let iR : IsRiemannianManifold I M :=
    radialScaledManifold (m := m) g hmetric R⁻¹ (inv_pos.mpr hR)
  let kR : CompleteSpace M := (m.rescale_completeSpace_iff R⁻¹ (inv_pos.mpr hR)).mpr hMc
  intro gR hnR
  have hΔ0 : 0 < Δ := by linarith
  obtain ⟨c⟩ := h β hβ hββ₀ E H I M gR hnR A p a α hD hsecR
  have hRi : 0 < R⁻¹ := inv_pos.mpr hR
  have hK : ((Real.toNNReal (1 + σs) : NNReal) : ℝ) = 1 + σs :=
    Real.coe_toNNReal _ (by linarith)
  -- an original-metric ball of radius `kΔR` is the normalized ball of radius `kΔ`
  have hball : ∀ k : ℝ, ∀ x ∈ @ball M m.toPseudoMetricSpace p (k * (Δ * R)),
      R⁻¹ * @dist M m.toDist x p < k * Δ := by
    intro k x hx
    have hx' : @dist M m.toDist x p < k * (Δ * R) := hx
    rw [inv_mul_lt_iff₀ hR]
    linarith
  have hcoord : ∀ x ∈ @ball M m.toPseudoMetricSpace p (2 * (Δ * R)),
      x ∈ ball p (10 ^ 6 * Δ) ∧ |c.coord x| < 3 * Δ := by
    intro x hx
    have hd := hball 2 x hx
    have hdist : dist x p = R⁻¹ * @dist M m.toDist x p := rfl
    have hlip := c.lipschitz.dist_le_mul x p
    rw [hK, c.coord_center, Real.dist_eq, sub_zero, hdist] at hlip
    refine ⟨?_, ?_⟩
    · change R⁻¹ * @dist M m.toDist x p < 10 ^ 6 * Δ
      nlinarith
    · have h1 : (1 + σs) * (R⁻¹ * @dist M m.toDist x p) ≤ (1 + σs) * (2 * Δ) :=
        mul_le_mul_of_nonneg_left hd.le (by linarith)
      nlinarith
  refine ⟨c, fun x hx => ?_, fun x hx => (hcoord x hx).2, fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨hxL, hxc⟩ := hcoord x hx
    refine ⟨mem_realSlabOpens_iff.mpr ⟨hxL, by nlinarith⟩, ?_⟩
    exact c.cutoff_eq_one x hxL (by nlinarith)
  · obtain ⟨hxd, hxc⟩ := c.tsupport_cutoff hx
    refine mem_realSlabOpens_iff.mpr ⟨?_, by nlinarith⟩
    change dist x p < 10 ^ 6 * Δ
    nlinarith
  · obtain ⟨hxd, -⟩ := c.tsupport_cutoff hx
    have hxd' : R⁻¹ * @dist M m.toDist x p ≤ 91 / 100 * (10 ^ 6 * Δ) := hxd
    change @dist M m.toDist x p < 2000000 * (Δ * R)
    rw [inv_mul_le_iff₀ hR] at hxd'
    nlinarith

/-- **The slim and edge halves of LPA04/LPA06 on ONE tail.** See the module docstring. -/
theorem eventually_simultaneous_local_cover_with_slim_and_edge_packets
    (hdim : Module.finrank ℝ E = 3) {σs : ℝ} (hσs : 0 < σs) (hσs1 : σs ≤ 1 / 100) :
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
      ∀ b : ℝ, 0 < b → b < s / 100000 → b < bc₀ → b < b₁ → 100 * Δ < b⁻¹ → ∃ b₀ : ℝ, 0 < b₀ ∧
      ∀ β : ℕ → ℝ, β 2 = β₂ → 0 < β 1 → β 1 < b₀ → β 1 < 1 →
        β 3 ≤ threeSplittingExclusionThreshold.{u, 0} →
      ∀ ζ : ℝ, β 1 < ζ → ζ < 1 →
      ∃ εz δ' Λ' : ℝ, 0 < εz ∧ 0 < δ' ∧ 0 < Λ' ∧
      ∀ σ : ℝ, 0 < σ → σ ≤ a₂ → σ ≤ threeSplittingExclusionThreshold.{u, 0} → σ ≤ a₀ →
      ∀ Λ : ℝ, 0 < Λ → Δ * Λ * 2000000 ≤ 1 / 100 → Λ < 1 / (1000000 * Δ) →
        100 * Δ * Λ ≤ 1 / 1000000 →
        2 * ε + 300 * Δ * Λ + Real.sqrt (504000 / Δ + 3780 * τ) < γc / 1000 →
        Λ < s' / (100000000 * Δ ^ 2) →
      ∃ w₀ : ℝ, 0 < w₀ ∧ ∀ w : ℝ, 0 < w → w < w₀ → w < 4 * Real.pi / 3 →
      ∀ T V : ℝ, 0 < T → 20 * Λ' ≤ T → T ≤ V →
      ∀ (X : ℕ → Type u) [mX : ∀ i, MetricSpace (X i)] [∀ i, ChartedSpace H (X i)]
        [∀ i, IsManifold I ∞ (X i)] [∀ i, CompactSpace (X i)]
        (g : ∀ i, SmoothRiemannianMetric I (X i))
        (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
        (α : ℕ → ℝ), Tendsto α atTop atTop →
        (∀ i (p : X i), ENNReal.ofReal (α i * firstVolumeScale (g i) p (α i)⁻¹) ≤
          curvatureRadius (g i) p) →
      ∀ (K : ℕ) (A : ℝ → ℝ → ℝ), (∀ C v, 0 < C → 0 < v → v < 4 * Real.pi / 3 → 0 < A C v) →
        (∀ i (p : X i) v, 0 < v → v < 4 * Real.pi / 3 → (α i)⁻¹ ≤ v →
          ∀ C, 0 < C → C < α i → ∀ k ≤ K,
          ∀ y ∈ riemannianBallOf (g i) p (C * firstVolumeScale (g i) p v),
            curvatureDerivativeNorm (g i) k y ≤
              A C v * (firstVolumeScale (g i) p v ^ (k + 2))⁻¹) →
      ∀ᶠ i in atTop, ∃ ρ : X i → ℝ, ∃ hρpos : ∀ p, 0 < ρ p,
        ContMDiff I 𝓘(ℝ, ℝ) ∞ ρ ∧ LipschitzWith (Real.toNNReal Λ) ρ ∧
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
            letI : IsContinuousRiemannianBundle E (fun x : X i => TangentSpace I x) :=
              radialScaledContinuous (g i) (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
            letI : IsRiemannianManifold I (X i) :=
              radialScaledManifold (m := mX i) (g i) (hmetric i) (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
            letI : CompleteSpace (X i) :=
              ((mX i).rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρpos j))).mpr hMc
            let gR : SmoothRiemannianMetric I (X i) :=
              scaleMetric ((ρ j)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (hρpos j)) 2) (g i)
            have hnR : IsMetricNorm (I := I) (M := X i) gR := isMetricNorm_of_riemannianBundle gR
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
                @ball (X i) (mX i).toPseudoMetricSpace j (2000000 * (Δ * ρ j))) ∧
        ∃ Je : Set (X i), Je.Finite ∧
        (∀ j ∈ Je, @isEdgePoint.{u, 0} (X i)
          ((mX i).rescale (ρ j)⁻¹ (inv_pos.mpr (hρpos j))) j Δ b s) ∧
        (∀ a : X i, @isEdgePoint.{u, 0} (X i)
          ((mX i).rescale (ρ a)⁻¹ (inv_pos.mpr (hρpos a))) a Δ b s →
          ∃ j ∈ Je, dist a j < Δ * ρ j) ∧
        ∃ F : X i → ℝ, (∀ x, 0 ≤ F x) ∧ LipschitzWith (Real.toNNReal (1 + ε)) F ∧
          ∀ p ∈ Je, ∃ f : X i → ℝ, f p = 0 ∧
            (letI := (mX i).rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
            ball p (3 * Δ) ⊆ edgeDiskDomain p Δ (fun x => f x.val)
                (fun x => F x / ρ p) (fun x => ρ x / ρ p) ∧
              EqOn ((Subtype.val : ball p (100 * Δ) → X i).extend
                (fun x => edgeCoordinateProfile (f x.val / Δ) *
                  edgeHeightProfile (F x.val / ρ p / (Δ * (ρ x.val / ρ p)))) 0) 1
                (ball p (3 * Δ))) := by
  obtain ⟨a₂, ha₂, h⟩ := eventually_simultaneous_local_cover_with_edge_coordinates.{uE, uH, u, 0}
    (E := E) (H := H) (I := I) hdim
  refine ⟨a₂, ha₂, fun γ hγ hγ1 => ?_⟩
  obtain ⟨β₀, hβ₀, hβ₀a, h⟩ := h γ hγ hγ1
  refine ⟨β₀, hβ₀, hβ₀a, fun βc γc hβc hβγ hγc hγc1 => ?_⟩
  obtain ⟨σ₀, hσ₀, Δ₀, hΔ₀, h⟩ := h βc γc hβc hβγ hγc hγc1
  refine ⟨σ₀, hσ₀, Δ₀, hΔ₀, fun β₂ Δ hβ₂ hβ₂β₀ hβ₂small hΔ hΔ₀Δ => ?_⟩
  have hΔ1 : 1 ≤ Δ := by
    have h100 : 100 < 100 / β₂ := (lt_div_iff₀ hβ₂).mpr (by linarith)
    linarith
  obtain ⟨βs₀, hβs₀, hslimc⟩ :=
    exists_slimChart_at_centre.{uE, uH, u, 0} (E := E) (H := H) (I := I) hΔ1 hσs hσs1
  obtain ⟨τ₀, hτ₀, bc₀, hbc₀, h⟩ := h β₂ Δ hβ₂ hβ₂β₀ hβ₂small hΔ hΔ₀Δ
  refine ⟨τ₀, hτ₀, bc₀, hbc₀, fun σc ε μ τ hσc hσcσ₀ hσc1 hε hε1 hμ hμ1 hτ hττ₀ hθ s b' s' hs
    hssmall hsb' hss' hb'd hs'd hb'e hs'e => ?_⟩
  obtain ⟨a₀, b₁, ha₀, hb₁, h⟩ := h σc ε μ τ hσc hσcσ₀ hσc1 hε hε1 hμ hμ1 hτ hττ₀ hθ s b' s' hs
    hssmall hsb' hss' hb'd hs'd hb'e hs'e
  refine ⟨a₀, b₁, ha₀, hb₁, fun b hb hbs hbc hbb₁ hsource => ?_⟩
  obtain ⟨b₀, hb₀, h⟩ := h b hb hbs hbc hbb₁ hsource
  refine ⟨min b₀ βs₀, lt_min hb₀ hβs₀, fun β hβ2 hβ1 hβ1b hβone hβ3 ζ hβζ hζone => ?_⟩
  have hβ1s : β 1 < βs₀ := hβ1b.trans_le (min_le_right _ _)
  obtain ⟨εz, δ', Λ', hεz, hδ', hΛ', h⟩ :=
    h β hβ2 hβ1 (hβ1b.trans_le (min_le_left _ _)) hβone hβ3 ζ hβζ hζone
  refine ⟨εz, δ', Λ', hεz, hδ', hΛ', fun σ hσ hσa hση hσa₀ Λ hΛ hΛΔ hΛ44 hlam hbudget hend => ?_⟩
  obtain ⟨w₀, hw₀, h⟩ := h σ hσ hσa hση hσa₀ Λ hΛ hΛΔ hΛ44 hlam hbudget hend
  refine ⟨w₀, hw₀, fun w hw hww hwc T V hT hTΛ hTV X mX _ _ _ g hmetric α hα hstand K A hA hder =>
    ?_⟩
  filter_upwards [h w hw hww hwc T V hT hTΛ hTV X g hmetric α hα hstand,
    eventually_simultaneous_analytic_data hdim g hmetric hα hstand K A hA hder hΛ hw hwc,
    hα.eventually_gt_atTop (2 * (β 1)⁻¹)] with i hi han hαβ
  obtain ⟨ρ, hρpos, hρsm, hρlip, hρb, hsecL, -, -, -, -, -, -, -, -, -, -, -, Js, Je, hJsfin, hJsS,
    hJsdisj, hJscov, hJsmult, hJefin, hJeE, -, hJecovE, -, -, hcollar, -⟩ := hi
  obtain ⟨-, -, -, hdata⟩ := han
  obtain ⟨F, hF0, hFL, hF⟩ := hcollar
  refine ⟨ρ, hρpos, hρsm, hρlip, hρb, fun p => hdata p (ρ p) (hρpos p) (hρb p).2.le, Js, hJsfin,
    hJsS, hJsdisj, hJscov, hJsmult, fun j hj => ?_, Je, hJefin, hJeE, hJecovE, F, hF0, hFL,
    fun p hp => ?_⟩
  · obtain ⟨-, Z, mZ, z, hbdd, hdiam, ⟨αs⟩⟩ := hJsS hj
    have hD : ∀ y y' : Z, dist y y' ≤ 10 ^ 3 * Δ := fun y y' =>
      (dist_le_diam_of_mem hbdd (mem_univ y) (mem_univ y')).trans (by linarith)
    have hsecj : ∀ x ∈ ball j ((β 1)⁻¹ * ρ j),
        SectionalBoundedBelowAt (g i) x (-(β 1 / ρ j) ^ 2) := by
      intro x hx
      have hs := hsecL (β 1)⁻¹ (inv_pos.mpr hβ1) hαβ j x hx
      have he : -(((β 1)⁻¹ * ρ j) ^ 2)⁻¹ = -(β 1 / ρ j) ^ 2 := by
        rw [mul_pow, mul_inv, inv_pow, inv_inv, div_pow, div_eq_mul_inv, ← inv_pow]
      rwa [he] at hs
    exact ⟨Z, mZ, z, hD, αs,
      hslimc (β 1) hβ1 hβ1s (X i) (g i) (hmetric i) (ρ j) (hρpos j) j Z z hD αs hsecj⟩
  obtain ⟨-, Y, mY, q, Fp, Qn, -, hall⟩ := hF p hp
  obtain ⟨⟨f, O, -, hCO, hfs, hfp, hfL, hfv, hft⟩, hallf⟩ := hall
  let mR : MetricSpace (X i) := (mX i).rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
  exact ⟨f, hfp, (hallf f (hfs.mono (ball_subset_closedBall.trans hCO)) hfL
    (fun x hx => (hfv x hx).le) hft).1⟩

end DifferentialGeometry.Geometry.Collapse
