import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryRegionalFamilyB

/-!
# The enriched regional kernel exporting the rank bound (lane BCG-5)

`exists_regional_chartFamilyEABR_BCG5` is lane BCG-2's enriched regional kernel
`exists_regional_chartFamilyEAB_BCG2` (same prefix, same proof) whose conclusion also exports the
rank bound the kernel proves from the model hypothesis, `∀ x ∈ U₁, scaledSplittingRank ρ hρ β x ≤ 2`
(conjunct placed right before `∃ E`), for the SAME scale: the producer gap found by lane BCG-4
(BCG01's edge-collar cover needs no 3-splitting at the collar points `B(j, 100Δρ_j) ⊆ U₁`).
Every other clause is verbatim. The consumer is the binding twin
`exists_interior_chartFamilyEABR_BCG5` (LE/BoundaryRegionalBindingBR.lean).
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
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-- **The enriched regional kernel with the rank bound** (lane BCG-5): BCG-2's
`exists_regional_chartFamilyEAB_BCG2` whose conclusion also carries
`∀ x ∈ U₁, scaledSplittingRank ρ hρ β x ≤ 2` (right before `∃ E`). Text of BCG-2:
(review 51; twin of `exists_regional_chartFamilyEA_BDRY4`).
Prefix = the kernel's, with `σs, vs` after `b` (immediately before `∃ b₀`). On the carrier, besides
`(U₁, U₂, Kc)` and its margin: revised edge regions `Ue₂ ⊆ Ue₁` with their margin
`p ∈ Ue₂, d(a, p) < Δρ(a) ⇒ a ∈ Ue₁` and the domain clause `B(a, 1000Δρ(a)) ⊆ U₁` for `a ∈ Ue₁`.
Output (ONE existence statement): a `ChartFamilyEOn … U₁ U₂` with circle adapted packets whose
slim centres carry the value clause `|η_j − u_j| < vs` on `B(j, 10⁶Δρ(j))` (ONE choose, inside the
slim producer), and a revised edge family `E` on `(Ue₁, Ue₂)` — the SAME edge threshold chain called
a second time at the carrier level — with its coarse-border composite, its LC84 disk packets and
EGP05 sections (BE-1's edge kernel), the domain clause at its centres and the four-family cover of
`Ue₂` with `E`; the circle family carries LFR07's residual enclosure (BE-1's circle kernel). Extra
requests of BE-1's kernels: `ε, μ ≤ 10⁻⁸`, `100ΔΛ ≤ 10⁻⁸`, and `∃ bd₀` after `v, A` (`b < bd₀`). -/
theorem exists_regional_chartFamilyEABR_BCG5 (K : ℕ) (hK : 5 ≤ K) :
    ∃ a₂ : ℝ, 0 < a₂ ∧ ∀ γ : ℝ, 0 < γ → γ < 1 / 10 → ∃ β₀ : ℝ, 0 < β₀ ∧ β₀ ≤ a₂ ∧
      ∀ βc γc : ℝ, 0 < βc → βc < γc / 1000 → 0 < γc → γc < 1 / 100 →
      ∃ σ₀ : ℝ, 0 < σ₀ ∧ ∃ Δ₀ : ℝ, 0 < Δ₀ ∧
      ∀ β₂ Δ : ℝ, 0 < β₂ → β₂ ≤ β₀ → β₂ < 1 / 100 → 100 / β₂ < Δ → Δ₀ ≤ Δ →
      ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∃ bc₀ : ℝ, 0 < bc₀ ∧
      ∀ σc ε μ τ : ℝ, 0 < σc → σc ≤ σ₀ → 0 < ε → ε < 1 / 100 → 0 < μ → μ ≤ 1 / 1000000 →
        0 < τ → τ ≤ τ₀ → 140 * Real.sqrt τ < ε ^ 2 / 20 → ε ≤ 1 / 10 ^ 8 → μ ≤ 1 / 10 ^ 8 →
      ∀ s b' s' : ℝ, 0 < s → s < 1 / 100 → s < b' / 100000 → s < s' / 100000 →
        b' < 1 / (1000000 * Δ) → s' < 1 / (1000000 * Δ) →
        b' < τ * Δ / 1000000000 → s' < τ * Δ / 1000000000 → ∃ a₀ b₁ : ℝ, 0 < a₀ ∧ 0 < b₁ ∧
      ∀ σ : ℝ, σ ≤ a₂ → σ ≤ threeSplittingExclusionThreshold.{0, 0} → σ ≤ a₀ →
      ∀ Λ : ℝ, 0 < Λ → Δ * Λ * 2000000 ≤ 1 / 100 → Λ < 1 / (1000000 * Δ) →
        100 * Δ * Λ ≤ 1 / 1000000 →
        2 * ε + 300 * Δ * Λ + Real.sqrt (504000 / Δ + 3780 * τ) < γc / 1000 →
        Λ < s' / (100000000 * Δ ^ 2) → 100 * Δ * Λ ≤ 1 / 10 ^ 8 →
      ∀ v : ℝ, 0 < v → ∀ Aprof : ℝ → ℝ, ∃ bd₀ : ℝ, 0 < bd₀ ∧
      ∀ b : ℝ, 0 < b → b < s / 100000 → b < bc₀ → b < b₁ → 100 * Δ < b⁻¹ → b < bd₀ →
      ∀ σs vs : ℝ, 0 < σs → σs ≤ 1 / 100 → 0 < vs → ∃ b₀ : ℝ, 0 < b₀ ∧
      ∀ β : ℕ → ℝ, β 2 = β₂ → 0 < β 1 → β 1 < b₀ →
        β 3 ≤ threeSplittingExclusionThreshold.{0, 0} →
      ∀ Lmax : ℝ, ∃ L₀ : ℝ, 0 < L₀ ∧ ∀ Lbig : ℝ, L₀ ≤ Lbig → Lmax ≤ Lbig →
      ∀ (X : Type) [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
        [CompleteSpace X] [SigmaCompactSpace X] [ProperSpace X] [ConnectedSpace X]
        (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
        (hmetric : ∀ a b, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)),
        ManifoldOrientation (𝓡 3) X 3 →
        ∀ (ρ : X → ℝ) (hρpos : ∀ p, 0 < ρ p), ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ ρ →
        LipschitzWith (Real.toNNReal Λ) ρ →
      ∀ (U₁ U₂ Kc : Set X), IsCompact Kc → U₁ ⊆ Kc → U₂ ⊆ U₁ →
      (∀ p ∈ U₂, ∀ a, dist a p < Δ * ρ a → a ∈ U₁) →
      ∀ (Ue₁ Ue₂ : Set X), Ue₂ ⊆ Ue₁ → (∀ p ∈ Ue₂, ∀ a, dist a p < Δ * ρ a → a ∈ Ue₁) →
      (∀ a ∈ Ue₁, ball a (1000 * Δ * ρ a) ⊆ U₁) →
      (∀ p ∈ U₁, ∃ (C : Type) (mC : MetricSpace C) (c : C), letI := mC
        CompleteSpace C ∧ ProperSpace C ∧ dimH (univ : Set C) ≤ 2 ∧
        fourPointComparison 0 (univ : Set C) ∧
        (∀ a b : C, ∃ f : Icc (0 : ℝ) 1 → C, Continuous f ∧
          f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
          ∀ s t, dist (f s) (f t) = dist a b * dist s t) ∧
        Nonempty (@KleinerLottApprox X C (mX.rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))) mC p c σ)) →
      (∀ p ∈ U₁, ∀ L, 0 < L → L ≤ Lbig → ∀ y ∈ ball p (L * ρ p),
        SectionalBoundedBelowAt g y (-((L * ρ p) ^ 2)⁻¹)) →
      (∀ p ∈ U₁, v ≤ (DifferentialGeometry.Geometry.Collapse.ballVolume
        (normalizedCenterMetric g (ρ p) (hρpos p)) p 1).toReal) →
      (∀ p ∈ U₁, ∀ R, 0 < R → R ≤ Lbig → ∀ k ≤ K,
        ∀ y ∈ riemannianBallOf (normalizedCenterMetric g (ρ p) (hρpos p)) p R,
          curvatureDerivativeNorm (normalizedCenterMetric g (ρ p) (hρpos p)) k y ≤ Aprof R) →
      ∃ L : ChartFamilyEOn X g hmetric ρ hρpos Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ U₁ U₂,
        Nonempty (∀ j (hj : j ∈ L.circle.centres),
          CircleAdaptedCentreOn X g hmetric ρ hρpos β γ U₁ U₂ L.circle j hj) ∧
        (∀ j (hj : j ∈ L.circle.centres),
          let c := L.circle.chart j hj
          letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
          ∀ x ∈ ball j 200, ‖c.coord x‖ ≤ 8 → x ∈ ball j 10) ∧
        (∀ j (hj : j ∈ L.slim.centres), ∀ x ∈ ball j (10 ^ 6 * Δ * ρ j),
          |(L.slim.centre j hj).coord_BCG2 x -
            (letI := (L.slim.centre j hj).instZ
             @KleinerLottApprox.toFun X (WithLp 2 (ℝ × (L.slim.centre j hj).Z))
              (mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρpos j))) _ j _ (β 1) (L.slim.centre j hj).split
                x).fst| < vs) ∧
        (∀ x ∈ U₁, scaledSplittingRank.{0, 0} ρ hρpos β x ≤ 2) ∧
        ∃ E : EdgeFamilyOn X g hmetric ρ hρpos β Δ σc μ b s b' s' ε γc βc Ue₁ Ue₂,
          (∀ j (hj : j ∈ E.centres),
            let c := E.chart j hj
            let A : Set X := closure
              {y | @isEdgePoint.{0, 0} X (mX.rescale (ρ y)⁻¹ (inv_pos.mpr (hρpos y))) y Δ b' s'}
            let hMc : CompleteSpace X := ‹CompleteSpace X›
            letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
            letI := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
            letI : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
              radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
            letI : IsRiemannianManifold 𝓘(ℝ, E3) X :=
              radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
            letI : CompleteSpace X :=
              (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρpos j))).mpr hMc
            (c.Qn j = 0 ∧
              (∀ x ∈ ball j (200 * Δ), ∀ y ∈ ball j (200 * Δ),
                (|dist (c.Qn x) (c.Qn y) - dist x y| ≤ τ * Δ)) ∧
              (∀ x ∈ ball j (200 * Δ), 0 ≤ (c.Qn x).snd) ∧
              (∀ z : WithLp 2 (ℝ × ℝ), (|z.fst| ≤ 100 * Δ) → z.snd ∈ Icc 0 (100 * Δ) →
                ∃ x ∈ ball j (200 * Δ), dist (c.Qn x) z ≤ τ * Δ) ∧
              (∀ a ∈ A ∩ ball j (190 * Δ), (c.Qn a).snd ≤ τ * Δ) ∧
              (∀ t : ℝ, (|t| ≤ 100 * Δ) → ∃ a ∈ A ∩ ball j (190 * Δ),
                dist (c.Qn a) (WithLp.toLp 2 (t, (0 : ℝ))) ≤ τ * Δ))) ∧
          (∀ j (hj : j ∈ E.centres),
            let c := E.chart j hj
            let Fs := E.smoothing
            let A : Set X := closure
              {y | @isEdgePoint.{0, 0} X (mX.rescale (ρ y)⁻¹ (inv_pos.mpr (hρpos y))) y Δ b' s'}
            let hMc : CompleteSpace X := ‹CompleteSpace X›
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
            have hnR : IsMetricNorm (I := 𝓘(ℝ, E3)) (M := X) gR :=
              isMetricNorm_of_riemannianBundle gR
            ∃ P : EdgeDiskPacket gR hnR Δ σc μ b γc βc A (fun x => ρ x / ρ j)
              (fun x => Fs x / ρ j), P.toEdgeChart = c) ∧
          (∀ j (hj : j ∈ E.centres),
            let c := E.chart j hj
            let Fs := E.smoothing
            let hMc : CompleteSpace X := ‹CompleteSpace X›
            letI := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
            letI := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
            letI : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
              radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
            letI : IsRiemannianManifold 𝓘(ℝ, E3) X :=
              radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρpos j))
            letI : CompleteSpace X :=
              (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρpos j))).mpr hMc
            ∃ sec : Ioo (-(17 / 2 * Δ)) (17 / 2 * Δ) → X, Continuous sec ∧
              ∀ a : Ioo (-(17 / 2 * Δ)) (17 / 2 * Δ), c.coord (sec a) = a ∧
                Fs (sec a) / ρ j / (ρ (sec a) / ρ j) < Δ / 100 ∧ dist (sec a) j < 10 * Δ) ∧
          (∀ j ∈ E.centres, ball j (1000 * Δ * ρ j) ⊆ U₁) ∧
          ∀ x ∈ Ue₂, x ∈ scaledSplittingStratum.{0, 0} ρ hρpos β 0 ∨
            (∃ j ∈ L.circle.centres, x ∈ ball j (2 * ρ j)) ∨
            (∃ j ∈ L.slim.centres, x ∈ ball j (2 * (Δ * ρ j))) ∨
            ∃ j ∈ E.centres, dist x j < 2 * Δ * ρ j := by
  classical
  obtain ⟨a₂, ha₂, hC⟩ := exists_regional_circleFamily_residual_BE1
  refine ⟨a₂, ha₂, fun γ hγ hγ1 => ?_⟩
  obtain ⟨β₀, hβ₀, hβ₀a, hC⟩ := hC γ hγ hγ1
  refine ⟨β₀, hβ₀, hβ₀a, fun βc γc hβc hβγ hγc hγc1 => ?_⟩
  obtain ⟨σ₀, hσ₀, Δ₀, hΔ₀, hE⟩ := exists_regional_edgeDiskFamily_BE1 hβc hβγ hγc hγc1 K hK
  refine ⟨σ₀, hσ₀, Δ₀, hΔ₀, fun β₂ Δ hβ₂ hβ₂β₀ hβ₂small hΔ hΔ₀Δ => ?_⟩
  have hΔ1 : 1 ≤ Δ := by
    have h100 : 100 < 100 / β₂ := (lt_div_iff₀ hβ₂).mpr (by linarith)
    linarith
  have hΔpos : 0 < Δ := by linarith
  obtain ⟨τ₀, hτ₀, κ₀, hκ₀, bc₀, hbc₀, hE⟩ := hE β₂ Δ hβ₂ hβ₂small hΔ hΔ₀Δ
  refine ⟨τ₀, hτ₀, bc₀, hbc₀, fun σc ε μ τ hσc hσcσ₀ hε hε1 hμ hμ1 hτ hττ₀ hθ hε8 hμ8 s b' s'
    hs hssmall hsb' hss' hb'd hs'd hb'e hs'e => ?_⟩
  obtain ⟨a₀, b₁, ha₀, hb₁, hE⟩ := hE σc ε μ τ hσc hσcσ₀ hε hε1 hμ hμ1 hτ hττ₀ hθ hε8 hμ8 s b'
    s' hs hssmall hsb' hss' hb'd hs'd hb'e hs'e
  refine ⟨a₀, b₁, ha₀, hb₁, fun σ hσa hση hσa₀ Λ hΛ hΛΔ hΛ44 hlam hbudget hend hΛ8 v hv Aprof
    => ?_⟩
  obtain ⟨bd₀, hbd₀, hE⟩ := hE Λ hΛ hΛΔ hΛ44 hlam hbudget hend hΛ8 v hv Aprof
  refine ⟨bd₀, hbd₀, fun b hb hbs hbc hbb₁ hsource hbd σs vs hσs hσs1 hvs => ?_⟩
  obtain ⟨b₀e, hb₀e, hE⟩ := hE b hb hbs hbc hbb₁ hsource hbd
  obtain ⟨βS, hβS, hS⟩ := exists_regional_slimFamily_vs_BCG2 hΔ1 hσs hσs1 hvs K hK hv Aprof
  refine ⟨min b₀e βS, lt_min hb₀e hβS, fun β hβ2 hβ1 hβ1b hβ3 Lmax => ?_⟩
  have hβ1e : β 1 < b₀e := hβ1b.trans_le (min_le_left _ _)
  have hβ1S : β 1 < βS := hβ1b.trans_le (min_le_right _ _)
  have hβ2pos : 0 < β 2 := by rw [hβ2]; exact hβ₂
  refine ⟨(3 * 2000000 + 2 / 3) + (3 * 2000000 + 2 / 3) * Δ + 4 * (1 + 2 * 2000000 + 1 / 3) * Δ +
      (10000 * Δ + κ₀⁻¹) + b⁻¹ + (β 1)⁻¹ + (β 2)⁻¹, by positivity,
    fun Lbig hL₀ hLmax X mX _ _ _ _ _ _ g hmetric o ρ hρpos hρsm hρlip U₁ U₂ Kc hKc hU₁ hU₂
    hmargin Ue₁ Ue₂ hUe hmarginE hdomE hmodel hsecL hvol hder => ?_⟩
  have hforms := fun p (hp : p ∈ U₁) => regional_sectional_forms_BDRY4 g (hρpos p) hΔ1 hκ₀ hb hβ1
    hβ2pos (fun L hL hLL => hsecL p hp L hL (hLL.trans hL₀))
  have hβ1L : (β 1)⁻¹ ≤ Lbig := by
    refine le_trans ?_ hL₀
    have h1 : 0 < (3 * 2000000 + 2 / 3) * Δ := by positivity
    have h2 : 0 < 4 * (1 + 2 * 2000000 + 1 / 3) * Δ := by positivity
    have h3 : 0 < 10000 * Δ + κ₀⁻¹ := by positivity
    have h4 : 0 < b⁻¹ := inv_pos.mpr hb
    have h5 : 0 < (β 2)⁻¹ := inv_pos.mpr hβ2pos
    linarith only [h1, h2, h3, h4, h5]
  have hbL : b⁻¹ ≤ Lbig := by
    refine le_trans ?_ hL₀
    have h1 : 0 < (3 * 2000000 + 2 / 3) * Δ := by positivity
    have h2 : 0 < 4 * (1 + 2 * 2000000 + 1 / 3) * Δ := by positivity
    have h3 : 0 < 10000 * Δ + κ₀⁻¹ := by positivity
    have h4 : 0 < (β 1)⁻¹ := inv_pos.mpr hβ1
    have h5 : 0 < (β 2)⁻¹ := inv_pos.mpr hβ2pos
    linarith only [h1, h2, h3, h4, h5]
  have hderb : ∀ p ∈ U₁, ∀ R, 0 < R → R < b⁻¹ → ∀ k ≤ K,
      ∀ y ∈ riemannianBallOf (normalizedCenterMetric g (ρ p) (hρpos p)) p R,
        curvatureDerivativeNorm (normalizedCenterMetric g (ρ p) (hρpos p)) k y ≤ Aprof R :=
    fun p hp R hR hRb => hder p hp R hR (hRb.le.trans hbL)
  -- the circle half
  have hΛ2 : Λ * 2000000 ≤ 1 / 100 := by
    have h := mul_le_mul_of_nonneg_right hΔ1 (by positivity : (0 : ℝ) ≤ Λ * 2000000)
    rw [one_mul, ← mul_assoc] at h
    exact h.trans hΛΔ
  have hβ2b : β 2 ≤ β₀ := by rw [hβ2]; exact hβ₂β₀
  obtain ⟨circle, hcut, ⟨hAd⟩, hres⟩ := hC X g hmetric ρ hρpos hΛ.le hρlip hΛ2 β hσa hβ2b U₁ U₂ Kc
    hKc hU₁ hmodel (fun p hp => (hforms p hp).1) (fun p hp => (hforms p hp).2.1)
  -- the slim half
  have hder' : ∀ p ∈ U₁, ∀ R, 0 < R → R < (β 1)⁻¹ → ∀ k ≤ K,
      ∀ y ∈ riemannianBallOf (normalizedCenterMetric g (ρ p) (hρpos p)) p R,
        curvatureDerivativeNorm (normalizedCenterMetric g (ρ p) (hρpos p)) k y ≤ Aprof R :=
    fun p hp R hR hRβ => hder p hp R hR (hRβ.le.trans hβ1L)
  obtain ⟨slim, hslimcv⟩ := hS X g hmetric o ρ hρpos hΛ.le hρlip hΛΔ β hβ1 hβ1S U₁ U₂ Kc hKc hU₁
    (fun p hp => (hforms p hp).2.2.1) hvol hder' (fun p hp => (hforms p hp).2.2.2.1)
  -- the edge half
  obtain ⟨edge, hcoarse, -, -⟩ := hE X g hmetric o ρ hρpos hρsm hρlip β hβ2 hβ1e hσa₀ U₁ U₂ Kc hKc
    hU₁ hU₂ hmargin (fun p hp => hmodel p (hU₂ hp)) (fun p hp => (hforms p hp).2.2.2.2.1)
    (fun p hp => (hforms p hp).2.2.2.2.2.1) (fun p hp => (hforms p hp).2.2.2.2.2.2) hvol hderb
  -- the revised edge half: the SAME threshold chain, called on `(Ue₁, Ue₂)`
  have hUe1 : Ue₁ ⊆ U₁ := fun a ha =>
    hdomE a ha (mem_ball_self (mul_pos (mul_pos (by norm_num) hΔpos) (hρpos a)))
  obtain ⟨edgeB, hcoarseB, hdiskB, hsecB⟩ := hE X g hmetric o ρ hρpos hρsm hρlip β hβ2 hβ1e hσa₀
    Ue₁ Ue₂ Kc hKc (hUe1.trans hU₁) hUe hmarginE (fun p hp => hmodel p (hUe1 (hUe hp)))
    (fun p hp => (hforms p (hUe1 hp)).2.2.2.2.1) (fun p hp => (hforms p (hUe1 hp)).2.2.2.2.2.1)
    (fun p hp => (hforms p (hUe1 hp)).2.2.2.2.2.2) (fun p hp => hvol p (hUe1 hp))
    (fun p hp => hderb p (hUe1 hp))
  -- the rank bound `≤ 2` on `U₁` (from the model)
  have hrank : ∀ x ∈ U₁, scaledSplittingRank.{0, 0} ρ hρpos β x ≤ 2 := by
    intro x hx1
    obtain ⟨C, mC, c, hCc, -, hCdim, hCcomp, hCseg, ⟨f⟩⟩ := hmodel x hx1
    exact @splittingRank_le_two_of_no_three.{0, 0} X
      (mX.rescale (ρ x)⁻¹ (inv_pos.mpr (hρpos x))) x β
      (@threeSplittingExclusionThreshold_excludes.{0, 0} X
        (mX.rescale (ρ x)⁻¹ (inv_pos.mpr (hρpos x))) x C mC hCc c hCseg hCdim hCcomp σ
        (β 3) hση hβ3 f)
  exact ⟨{ contMDiff_scale := hρsm
           lipschitz_scale := hρlip
           circle := circle
           slim := slim
           edge := edge
           exhaustion := fun x hx => four_family_cover_of_rank_le_two_BCG2 circle slim edge hΔpos
             (hU₂ hx) hx (hrank x (hU₂ hx))
           circle_cutoff_eq := hcut
           slim_cutoff_eq := fun j hj => (hslimcv j hj).1
           sectional_buffer := fun L hL hLL p hp y hy => hsecL p hp L hL (hLL.trans hLmax) y hy
           edge_coarse := hcoarse }, ⟨hAd⟩, hres, fun j hj => (hslimcv j hj).2, hrank,
    edgeB, hcoarseB, hdiskB, hsecB, fun j hj => hdomE j (edgeB.centres_subset hj),
    fun x hx => four_family_cover_of_rank_le_two_BCG2 circle slim edgeB hΔpos (hUe1 (hUe hx)) hx
      (hrank x (hUe1 (hUe hx)))⟩

end DifferentialGeometry.Geometry.Collapse
