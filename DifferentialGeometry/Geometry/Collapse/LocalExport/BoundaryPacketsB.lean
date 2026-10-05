import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryRegionalSlimValue
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsValueProducer

/-!
# The enriched boundary BASE family `LocalPacketsOnB` (lane BCG-2, review 51)

Review 51 (dispositions `docs/geometrization/chapter14/out/dispositions-task51-boundary-family-
enrichment.md`, binding): the local route is accepted — the shared regionalised packets
`LocalPacketsOn … U₁ U₂` enriched by
* LFR19's separate slim value tolerance `vs` at every slim centre (BCG02 value clause, R17), and
* a SECOND, revised strong-edge family `edgeB` on its own regions `(Ue₁, Ue₂)` (boundary instance:
  centres at `D > 20`, nonslim cover of `D ≥ 35`), whose packet domains `B(j, 1000Δρ(j))` lie in
  `U₁`, with its coarse-border composite and the four-family cover of `Ue₂` with `edgeB`.
This is the **enriched boundary base family**, NOT the final boundary family: the same-chart
certificates of review 51 P0-B (`edgeDiskB`, `circle_residual`, `zero_local_comparison`, zero shell
splitting, enlarged zero curvature, `edgeB_section`) and the request timing P0-C are added by the
final family (lanes BCG/BZ/BE, after their kernels). The inherited `edge`, `edge_coarse`,
`exhaustion` are retained only through `extends`; every boundary construction consumes `edgeB`
(P0-A). No equality of the two edge smoothings or coordinates is required or claimed.

* `LocalPacketsOnB` (structure);
* `LocalPacketsOnB.ofClosedRV`: the closed specialization — every closed `LocalChartPacketsRV`
  is an enriched base family with all four regions `univ` (`edgeB = edge`);
* `eventually_nonempty_localPacketsOnB_closed_BCG2`: the closed producer
  `eventually_nonempty_localChartPacketsRV` composed with the specialization — the structure is
  inhabited on a tail of every closed standing sequence (non-vacuous use; the `PEmpty` fixture
  pattern is a projection check only).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-- **The enriched boundary base family** (review 51): `LocalPacketsOn … U₁ U₂` with LFR19's
separate slim value tolerance `vs` and the revised strong-edge family `edgeB` on its own regions
`(Ue₁, Ue₂)` (boundary instance `U₁ = {D > 10}`, `U₂ = {D ≥ 20}`, `Ue₁ = {D > 20}`,
`Ue₂ = {D ≥ 35}`). Not the final boundary family (review 51 P0-B, P0-C are added later). -/
structure LocalPacketsOnB (X : Type) [mX : MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompleteSpace X] [SigmaCompactSpace X]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
    (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
    (ρ : X → ℝ) (hρ : ∀ p, 0 < ρ p) (Λ : ℝ) (β : ℕ → ℝ) (Δ σs : ℝ) (K : ℕ)
    (σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs : ℝ) (U₁ U₂ Ue₁ Ue₂ : Set X)
    extends LocalPacketsOn X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V
      U₁ U₂ where
  /-- LFR19's separate value tolerance at every slim centre (BCG02 value clause; SGP03 (SB)),
  on the physical ball `B(j, 10⁶Δρ(j))` only. -/
  slim_value : ∀ j (hj : j ∈ slim.centres), ∀ x ∈ ball j (10 ^ 6 * Δ * ρ j),
    |(slim.centre j hj).coord_BCG2 x -
      (letI := (slim.centre j hj).instZ
       @KleinerLottApprox.toFun X (WithLp 2 (ℝ × (slim.centre j hj).Z))
        (mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))) _ j _ (β 1) (slim.centre j hj).split x).fst| < vs
  /-- The revised strong-edge family (B:8704): centres in `Ue₁`, strong cover of `Ue₁`, nonslim
  cover of `Ue₂`; its OWN smoothing of the distance to the weak-edge set. -/
  edgeB : EdgeFamilyOn X g hmetric ρ hρ β Δ σc μ b s b' s' ε γc βc Ue₁ Ue₂
  /-- The coarse-border composite at every revised edge centre (the text of `edge_coarse`). -/
  edgeB_coarse : ∀ j (hj : j ∈ edgeB.centres),
    let c := edgeB.chart j hj
    let A : Set X := closure
      {y | @isEdgePoint.{0, 0} X (mX.rescale (ρ y)⁻¹ (inv_pos.mpr (hρ y))) y Δ b' s'}
    let hMc : CompleteSpace X := ‹CompleteSpace X›
    letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    letI := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    letI : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
      radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    letI : IsRiemannianManifold 𝓘(ℝ, E3) X :=
      radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
    letI : CompleteSpace X :=
      (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
    (c.Qn j = 0 ∧
      (∀ x ∈ ball j (200 * Δ), ∀ y ∈ ball j (200 * Δ),
        (|dist (c.Qn x) (c.Qn y) - dist x y| ≤ τ * Δ)) ∧
      (∀ x ∈ ball j (200 * Δ), 0 ≤ (c.Qn x).snd) ∧
      (∀ z : WithLp 2 (ℝ × ℝ), (|z.fst| ≤ 100 * Δ) → z.snd ∈ Icc 0 (100 * Δ) →
        ∃ x ∈ ball j (200 * Δ), dist (c.Qn x) z ≤ τ * Δ) ∧
      (∀ a ∈ A ∩ ball j (190 * Δ), (c.Qn a).snd ≤ τ * Δ) ∧
      (∀ t : ℝ, (|t| ≤ 100 * Δ) → ∃ a ∈ A ∩ ball j (190 * Δ),
        dist (c.Qn a) (WithLp.toLp 2 (t, (0 : ℝ))) ≤ τ * Δ))
  /-- Every revised edge packet's domain lies in `U₁` (B:8752–8754; radius `1000Δρ(j)` ⊇ the
  printed `100Δρ(j)`). Eligibility only: the collar cover still needs the two-stratum fact. -/
  edgeB_domain : ∀ j ∈ edgeB.centres, ball j (1000 * Δ * ρ j) ⊆ U₁
  /-- The four-family cover of `Ue₂` with the revised edges (B:8750–8751). -/
  exhaustionB : ∀ x ∈ Ue₂, x ∈ scaledSplittingStratum.{0, 0} ρ hρ β 0 ∨
    (∃ j ∈ circle.centres, x ∈ ball j (2 * ρ j)) ∨
    (∃ j ∈ slim.centres, x ∈ ball j (2 * (Δ * ρ j))) ∨
    ∃ j ∈ edgeB.centres, dist x j < 2 * Δ * ρ j

section Closed

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs : ℝ}

/-- **The closed specialization of the enriched base family**: every closed `LocalChartPacketsRV`
(LFR19's slim value tolerance `vs` included) is a `LocalPacketsOnB` with all four regions `univ`;
the revised edge family is the closed edge family, its domain clause is trivial. -/
def LocalPacketsOnB.ofClosedRV
    (P : LocalChartPacketsRV X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs) :
    LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
      univ univ univ univ where
  toLocalPacketsOn :=
    LocalPacketsOn.ofClosed P.toLocalChartPacketsR.toLocalChartPacketsD.toLocalChartPackets
  slim_value := fun j hj x hx => P.slim_value j hj x hx
  edgeB := EdgeFamilyOn.ofClosed P.edge
  edgeB_coarse := P.edge_coarse
  edgeB_domain := fun _ _ => subset_univ _
  exhaustionB := fun x _ => P.exhaustion x

end Closed

/-- **Non-vacuous use: the enriched base family on closed standing sequences.** The closed producer
`eventually_nonempty_localChartPacketsRV` composed with `LocalPacketsOnB.ofClosedRV`: on one tail
of every closed standing sequence the enriched base family with regions `univ` exists, on the
same scale `ρ` with LC02's bounds, for every slim value tolerance `vs > 0`. -/
theorem eventually_nonempty_localPacketsOnB_closed_BCG2 (K : ℕ) (hK : 10 ≤ K)
    (A : ℝ → ℝ → ℝ) (hA : ∀ C v, 0 < C → 0 < v → v < 4 * Real.pi / 3 → 0 < A C v) :
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
      ∀ σs vs : ℝ, 0 < σs → σs ≤ 1 / 100 → 0 < vs →
      ∃ b₀ : ℝ, 0 < b₀ ∧
      ∀ β : ℕ → ℝ, β 2 = β₂ → 0 < β 1 → β 1 < b₀ → β 1 < 1 →
        β 3 ≤ threeSplittingExclusionThreshold.{0, 0} →
      ∀ ζ : ℝ, β 1 < ζ → ζ < 1 →
      ∃ εr δ' Λ' : ℝ, 0 < εr ∧ εr < 1 / 4 ∧ 0 < δ' ∧ 0 < Λ' ∧
      ∀ T : ℝ, 0 < T → 20 * Λ' ≤ T → ∀ e : ℝ, 0 < e → e < 1 / 40 →
      ∀ Lmax : ℝ, 0 < Lmax →
      ∀ (X : ℕ → Type) [∀ i, MetricSpace (X i)] [∀ i, ChartedSpace E3 (X i)]
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
        Nonempty (LocalPacketsOnB (X i) (g i) (hmetric i) ρ hρpos Λ β Δ σs K
          σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs univ univ univ univ) := by
  obtain ⟨a₂, ha₂, h⟩ := eventually_nonempty_localChartPacketsRV K hK A hA
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
  refine ⟨bd₀, hbd₀, fun b hb hbs hbc hbb₁ hsource hbd σs vs hσs hσs1 hvs => ?_⟩
  obtain ⟨b₀, hb₀, h⟩ := h b hb hbs hbc hbb₁ hsource hbd σs vs hσs hσs1 hvs
  refine ⟨b₀, hb₀, fun β hβ2 hβ1 hβ1b hβone hβ3 ζ hβζ hζone => ?_⟩
  obtain ⟨εr, δ', Λ5, hεr, hεr4, hδ', hΛ5, h⟩ := h β hβ2 hβ1 hβ1b hβone hβ3 ζ hβζ hζone
  refine ⟨εr, δ', Λ5, hεr, hεr4, hδ', hΛ5,
    fun T hT hTΛ e he he1 Lmax hLmax X _ _ _ _ g hmetric α hα hstand hder hor => ?_⟩
  obtain ⟨V, hTV, δ, hδ0, hδδ', h⟩ :=
    h T hT hTΛ e he he1 Lmax hLmax X g hmetric α hα hstand hder hor
  refine ⟨V, hTV, δ, hδ0, hδδ', ?_⟩
  filter_upwards [h] with i hi
  obtain ⟨ρ, hρpos, hρb, ⟨P⟩⟩ := hi
  exact ⟨ρ, hρpos, hρb, ⟨LocalPacketsOnB.ofClosedRV P⟩⟩

end DifferentialGeometry.Geometry.Collapse
