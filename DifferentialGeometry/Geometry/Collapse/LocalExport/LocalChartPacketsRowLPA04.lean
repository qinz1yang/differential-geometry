import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsDiskProducer
import DifferentialGeometry.Geometry.Collapse.FiniteZeroCore.LPA05SelectedZeroPackets

/-!
# Row LPA04: one acyclic simultaneous choice for all four local types (on the reordered tail)

Frozen blueprint master207A, LPA04 (`thm:collapse-simultaneous-interior-parameters`, A:30447):
ONE parameter assignment and ONE uniform late tail on which LC83/LFR07 hold on the two-stratum,
LC85/LFR20 on the slim one-stratum, every strong edge point has LFR28's disk packet and LFR38's full
collar, LFR44's strong-edge density applies to the same strata and predicates, and LPA02 holds at
every centre with the buffered radial choices needed by LC80.

`lpa04_simultaneous_interior_choice`: the parameter order of the LC87 G10 producer
`eventually_nonempty_localChartPacketsD` (blueprint order: circle/edge-collar qualities, `Δ`, the
slim/edge tolerances, endpoint qualities, `σ_col, Λ`, `w`, LFR28's threshold, `b`, `β₁`, `ζ`, the
zero constants `εr, δ', Λ'`, `T`, `e`, then `V` LAST), and on ONE tail ONE modified scale `ρ` with
LC02's bounds and ONE `LocalChartPacketsD`:
* circle kind: `CircleFamily` (LC83 charts; their `2ρ`-balls cover the two-stratum) with LFR07's
  adapted-coordinate packets `circleAdapted`;
* slim kind: `SlimFamily` (LC85 `SlimPacket` + LC81 model at every centre; covers the slim stratum);
* edge kind: `EdgeFamily` (LFR38's rank-two collar inside every `EdgeChart`, LFR44's density
  `covers_strong`/`covers_nonslim`, ONE shared smoothing) and an LFR28 `EdgeDiskPacket` over every
  edge chart (`edgeDisk`);
* zero kind: the LC80 family `zero` built from LPA02 witnesses fixed once at every point, TOGETHER
  with LPA05's buffered clauses on the SAME family (this file's addition: the producer drops them):
  the original buffer `sec ≥ -(1/60)² r⁻²` on `B(c, 400 r)`, LC66's shell splitting, X82's original
  radial coordinate, LC73's adapted coordinates of the SAME radial function, and LC31's zero cutoffs
  with pairwise disjoint supports.

Deviation (as in the chain): the circle and slim conclusions are in covering-centre form (every
stratum point lies in a covering ball of a centre carrying the packet).
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
local notation "I3" => 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-- The model metrics of the zero kind, as a local instance. -/
local instance instMetricN_LPA02b {X : Type} [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
    [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}
    (L : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (L.N a) :=
  L.instMetricN a

/-- The model charts of the zero kind, as a local instance. -/
local instance instChartedN_LPA02b {X : Type} [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
    [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}
    (L : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : ChartedSpace E3 (L.N a) :=
  L.instChartedN a

/-- The cone metrics of the zero kind, as a local instance. -/
local instance instMetricC_LPA02b {X : Type} [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
    [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}
    (L : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (L.C a) :=
  L.instMetricC a

/-- **Row LPA04 (one simultaneous choice for all four local types).** See the module docstring. -/
theorem lpa04_simultaneous_interior_choice
    {σs : ℝ} (hσs : 0 < σs) (hσs1 : σs ≤ 1 / 100) (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ → ℝ)
    (hA : ∀ C v, 0 < C → 0 < v → v < 4 * Real.pi / 3 → 0 < A C v) :
    ∃ a₂ : ℝ, 0 < a₂ ∧ ∀ γ : ℝ, 0 < γ → γ < 1 / 10 → ∃ β₀ : ℝ, 0 < β₀ ∧ β₀ ≤ a₂ ∧
      ∀ βc γc : ℝ, 0 < βc → βc < γc / 1000 → 0 < γc → γc < 1 / 100 →
      ∃ σ₀ : ℝ, 0 < σ₀ ∧ ∃ Δ₀ : ℝ, 0 < Δ₀ ∧
      ∀ β₂ Δ : ℝ, 0 < β₂ → β₂ ≤ β₀ → β₂ < 1 / 100 → 100 / β₂ < Δ → Δ₀ ≤ Δ →
      ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∃ bc₀ : ℝ, 0 < bc₀ ∧
      ∀ σc ε μ τ : ℝ, 0 < σc → σc ≤ σ₀ → σc < 1 → 0 < ε → ε < 1 / 100 → 0 < μ → μ ≤ 1 / 1000000 →
        0 < τ → τ ≤ τ₀ → 140 * Real.sqrt τ < ε ^ 2 / 20 → ε ≤ 1 / 10 ^ 8 → μ ≤ 1 / 10 ^ 8 →
      ∀ s b' s' : ℝ, 0 < s → s < 1 / 100 → s < b' / 100000 → s < s' / 100000 →
        b' < 1 / (1000000 * Δ) → s' < 1 / (1000000 * Δ) →
        b' < τ * Δ / 1000000000 → s' < τ * Δ / 1000000000 → ∃ a₀ b₁ : ℝ, 0 < a₀ ∧ 0 < b₁ ∧
      ∀ σ : ℝ, 0 < σ → σ ≤ a₂ → σ ≤ threeSplittingExclusionThreshold.{0, 0} → σ ≤ a₀ →
      ∀ Λ : ℝ, 0 < Λ → Δ * Λ * 2000000 ≤ 1 / 100 → Λ < 1 / (1000000 * Δ) →
        100 * Δ * Λ ≤ 1 / 1000000 →
        2 * ε + 300 * Δ * Λ + Real.sqrt (504000 / Δ + 3780 * τ) < γc / 1000 →
        Λ < s' / (100000000 * Δ ^ 2) → 100 * Δ * Λ ≤ 1 / 10 ^ 8 →
      ∃ w₀ : ℝ, 0 < w₀ ∧ ∀ w : ℝ, 0 < w → w < w₀ → w < 4 * Real.pi / 3 → ∃ bd₀ : ℝ, 0 < bd₀ ∧
      ∀ b : ℝ, 0 < b → b < s / 100000 → b < bc₀ → b < b₁ → 100 * Δ < b⁻¹ → b < bd₀ →
      ∃ b₀ : ℝ, 0 < b₀ ∧
      ∀ β : ℕ → ℝ, β 2 = β₂ → 0 < β 1 → β 1 < b₀ → β 1 < 1 →
        β 3 ≤ threeSplittingExclusionThreshold.{0, 0} →
      ∀ ζ : ℝ, β 1 < ζ → ζ < 1 →
      ∃ εr δ' Λ' : ℝ, 0 < εr ∧ εr < 1 / 4 ∧ 0 < δ' ∧ 0 < Λ' ∧
      ∀ T : ℝ, 0 < T → 20 * Λ' ≤ T → ∀ e : ℝ, 0 < e → e < 1 / 40 →
      ∀ Lmax : ℝ, 0 < Lmax →
      ∀ (X : ℕ → Type) [mX : ∀ i, MetricSpace (X i)] [∀ i, ChartedSpace E3 (X i)]
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
      ∃ V : ℝ, T ≤ V ∧ ∃ δ : ℝ, 0 < δ ∧ δ < δ' ∧ ∀ᶠ i in atTop,
        ∃ ρ : X i → ℝ, ∃ hρpos : ∀ p, 0 < ρ p,
        (∀ p, firstVolumeScale (g i) p w / 2 < ρ p ∧
          ρ p < 2 * firstVolumeScale (g i) p (w / (2 * (1 + 2 * Λ⁻¹) ^ 3))) ∧
        ∃ P : LocalChartPacketsD (X i) (g i) (hmetric i) ρ hρpos Λ β Δ σs K
          σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V,
            (∀ c (hc : c ∈ P.zero.centres), ∀ y ∈ ball c (400 * (P.zero.zero c hc).radius),
              SectionalBoundedBelowAt (g i) y (-((1 / 60) ^ 2 * ((P.zero.zero c hc).radius)⁻¹ ^ 2))) ∧
            (∀ c (hc : c ∈ P.zero.centres), ∀ q, (P.zero.zero c hc).radius / 10 ≤ dist c q →
              dist c q ≤ 10 * (P.zero.zero c hc).radius →
              @HasEuclideanSplitting.{0, 0} (X i) ((mX i).rescale (ρ q)⁻¹ (inv_pos.mpr (hρpos q))) q 1
                (β 1) ∧
              @splittingRank.{0, 0} (X i) ((mX i).rescale (ρ q)⁻¹ (inv_pos.mpr (hρpos q))) q β 3 ≠ 0) ∧
            (∀ c (hc : c ∈ P.zero.centres), ∀ q, (P.zero.zero c hc).radius / 10 ≤ dist c q →
              dist c q ≤ 10 * (P.zero.zero c hc).radius →
              ∃ (Zf : Type) (mZ : MetricSpace Zf), letI := mZ
                ∃ (z : Zf) (F : @KleinerLottApprox (X i)
                  (WithLp 2 (EuclideanSpace ℝ (Fin 1) × Zf))
                  ((mX i).rescale (ρ q)⁻¹ (inv_pos.mpr (hρpos q))) inferInstance
                  q (WithLp.toLp 2 (0, z)) (β 1)),
                  ∀ x : X i, (@KleinerLottApprox.toFun (X i)
                    (WithLp 2 (EuclideanSpace ℝ (Fin 1) × Zf))
                    ((mX i).rescale (ρ q)⁻¹ (inv_pos.mpr (hρpos q))) inferInstance
                    q (WithLp.toLp 2 (0, z)) (β 1) F x).fst = WithLp.toLp 2
                    (Function.const (Fin 1) ((ρ q)⁻¹ * (dist c x - dist c q)))) ∧
            (∀ c (hc : c ∈ P.zero.centres), ∀ q, (P.zero.zero c hc).radius / 10 ≤ dist c q →
              dist c q ≤ 10 * (P.zero.zero c hc).radius →
              ∀ (lam : ℝ) (hlam : 0 < lam), Λ' ≤ lam →
              let R := (P.zero.zero c hc).radius
              let hR : 0 < R := (P.zero.zero c hc).radius_pos
              let η := (P.zero.zero c hc).radial
              let mr := (mX i).rescale R⁻¹ (inv_pos.mpr hR)
              let gr := scaleMetric (R⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2) (g i)
              let hmr := riemannianEDistOf_scaleMetric_inv_sq_eq_rescale (m := mX i) (g i)
                (hmetric i) hR
              let := mr.rescale lam hlam
              letI := (mr.rescale_completeSpace_iff lam hlam).mpr
                (((mX i).rescale_completeSpace_iff R⁻¹ (inv_pos.mpr hR)).mpr
                  (@complete_of_compact (X i) (mX i).toUniformSpace _))
              letI := radialScaledBundle gr lam hlam
              letI := radialScaledContinuous gr lam hlam
              letI := radialScaledManifold (m := mr) gr hmr lam hlam
              let h := scaleMetric (lam ^ 2) (pow_pos hlam 2) gr
              let ψ := fun x => lam * (η x - η q)
              ∃ hEnorm : IsMetricNorm h,
                ∃ (Zf : Type) (mZ : MetricSpace Zf), letI := mZ
                  ∃ (z : Zf) (κ : KleinerLottApprox q (WithLp.toLp 2 ((0 : ℝ), z)) (β 1)),
                  (∀ x, (κ.toFun x).fst = lam *
                    (@dist (X i) mr.toDist c x - @dist (X i) mr.toDist c q)) ∧
                  ContMDiffOn I3 𝓘(ℝ, ℝ) ∞ ψ (ball q 1) ∧ ψ q = 0 ∧
                  (∀ x ∈ ball q 1, ∀ y ∈ ball q 1, |ψ x - ψ y| ≤ (1 + ζ) * dist x y) ∧
                  (∀ x ∈ ball q 1, infDist (ψ x) (Ioo (-1 : ℝ) 1) ≤ ζ) ∧
                  (∀ t ∈ Ioo (-1 : ℝ) 1, infDist t (ψ '' ball q 1) ≤ ζ) ∧
                  ∀ x ∈ ball q 1, ∀ y ∈ ball q ζ⁻¹, 1 < dist x y →
                    ∀ u : TangentSpace I3 x, h.inner x u u = 1 →
                    intrinsicGeodesic h hEnorm x u (dist x y) = y →
                    |mvfderiv (I := I3) ψ x u -
                      ((κ.toFun y).fst - (κ.toFun x).fst) / dist x y| < ζ) ∧
            ∃ L : ℝ, 0 ≤ L ∧
              (∀ c (hc : c ∈ P.zero.centres),
                let φc : X i → ℝ := fun x => annularCutoff cutoffProfile ((P.zero.zero c hc).radial x)
                let gr := scaleMetric (((P.zero.zero c hc).radius)⁻¹ ^ 2)
                  (pow_pos (inv_pos.mpr (P.zero.zero c hc).radius_pos) 2) (g i)
                ContMDiff I3 𝓘(ℝ, ℝ) ∞ φc ∧ (∀ x, φc x ∈ Icc (0 : ℝ) 1) ∧
                (∀ x, (P.zero.zero c hc).radial x ∈ Icc (3 / 10 : ℝ) (4 / 5) → φc x = 1) ∧
                tsupport φc ⊆ {x | (1 / 5 - e) * (P.zero.zero c hc).radius < dist x c ∧
                  dist x c < (9 / 10 + e) * (P.zero.zero c hc).radius} ∧
                tsupport φc ⊆ ball c (P.zero.zero c hc).radius ∧ HasCompactSupport φc ∧
                (∀ q, Real.sqrt (gr.inner q (gradFun gr φc q) (gradFun gr φc q)) ≤ L * (1 + εr)) ∧
                ball c ((P.zero.zero c hc).radius / 10) ⊆ {x | (P.zero.zero c hc).radial x < 1 / 5}) ∧
              ∀ c (hc : c ∈ P.zero.centres) c' (hc' : c' ∈ P.zero.centres), c ≠ c' →
                Disjoint (tsupport fun x => annularCutoff cutoffProfile ((P.zero.zero c hc).radial x))
                  (tsupport fun x => annularCutoff cutoffProfile ((P.zero.zero c' hc').radial x)) := by
  obtain ⟨a₂, ha₂, h⟩ := eventually_nonempty_localChartFamilyEAD hσs hσs1 K (by omega) A hA
  refine ⟨a₂, ha₂, fun γ hγ hγ1 => ?_⟩
  obtain ⟨β₀, hβ₀, hβ₀a, h⟩ := h γ hγ hγ1
  refine ⟨β₀, hβ₀, hβ₀a, fun βc γc hβc hβγ hγc hγc1 => ?_⟩
  obtain ⟨σ₀, hσ₀, Δ₀, hΔ₀, h⟩ := h βc γc hβc hβγ hγc hγc1
  refine ⟨σ₀, hσ₀, Δ₀, hΔ₀, fun β₂ Δ hβ₂ hβ₂β₀ hβ₂small hΔ hΔ₀Δ => ?_⟩
  obtain ⟨τ₀, hτ₀, bc₀, hbc₀, h⟩ := h β₂ Δ hβ₂ hβ₂β₀ hβ₂small hΔ hΔ₀Δ
  refine ⟨τ₀, hτ₀, bc₀, hbc₀, fun σc ε μ τ hσc hσcσ₀ hσc1 hε hε1 hμ hμ1 hτ hττ₀ hθ hε8 hμ8 s b' s'
    hs hssmall hsb' hss' hb'd hs'd hb'e hs'e => ?_⟩
  obtain ⟨a₀, b₁, ha₀, hb₁, h⟩ := h σc ε μ τ hσc hσcσ₀ hσc1 hε hε1 hμ hμ1 hτ hττ₀ hθ hε8 hμ8 s b'
    s' hs hssmall hsb' hss' hb'd hs'd hb'e hs'e
  refine ⟨a₀, b₁, ha₀, hb₁, fun σ hσ hσa hση hσa₀ Λ hΛ hΛΔ hΛ44 hlam hbudget hend hΛ8 => ?_⟩
  obtain ⟨w₀, hw₀, h⟩ := h σ hσ hσa hση hσa₀ Λ hΛ hΛΔ hΛ44 hlam hbudget hend hΛ8
  refine ⟨w₀, hw₀, fun w hw hww hwc => ?_⟩
  obtain ⟨bd₀, hbd₀, h⟩ := h w hw hww hwc
  refine ⟨bd₀, hbd₀, fun b hb hbs hbc hbb₁ hsource hbd => ?_⟩
  obtain ⟨b₀, hb₀, h⟩ := h b hb hbs hbc hbb₁ hsource hbd
  refine ⟨b₀, hb₀, fun β hβ2 hβ1 hβ1b hβone hβ3 ζ hβζ hζone => ?_⟩
  have hEA := h β hβ2 hβ1 hβ1b hβone hβ3
  obtain ⟨εr, δ', Λ5, hεr, hεr4, hδ', hΛ5, h5⟩ :=
    lpa05_selected_zero_packets_with_witnesses hβ1 hβone hβζ hζone
  refine ⟨εr, δ', Λ5, hεr, hεr4, hδ', hΛ5,
    fun T hT hTΛ e he he1 Lmax hLmax X _ _ _ _ g hmetric α hα hstand hder hor => ?_⟩
  obtain ⟨V, hTV, δ, hδ0, hδδ', h5⟩ := h5 T hT hTΛ e he he1 X g hmetric
    α hα hstand K hK A hA hder Λ w hΛ hw hwc
  refine ⟨V, hTV, δ, hδ0, hδδ', ?_⟩
  filter_upwards [hEA Lmax hLmax X g hmetric α hα hstand hder hor, h5] with i hi h5i
  obtain ⟨ρ, hρpos, hρb, L, ⟨hAd⟩, hDisk⟩ := hi
  obtain ⟨N, C, mN, cN, -, mC, o, -, Z, hZ⟩ :=
    h5i ρ hρpos L.contMDiff_scale.continuous (fun p => (hρb p).2.le)
  exact ⟨ρ, hρpos, hρb, { L with
    circleAdapted := hAd
    N := N
    C := C
    instMetricN := mN
    instChartedN := cN
    instMetricC := mC
    o := o
    zero := Z
    edgeDisk := hDisk }, hZ⟩

end DifferentialGeometry.Geometry.Collapse
