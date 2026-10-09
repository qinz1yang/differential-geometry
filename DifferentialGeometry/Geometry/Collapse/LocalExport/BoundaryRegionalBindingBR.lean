import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryRegionalFamilyBR
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryLevelMargins

/-!
# Binding of the rank-exporting regional kernel to `(W°, d_ĝ)` (lane BCG-5)

`exists_interior_chartFamilyEABR_BCG5` is lane BCG-2's binding `exists_interior_chartFamilyEAB_BCG2`
(same prefix, same proof) on the rank-exporting kernel `exists_regional_chartFamilyEABR_BCG5`: the
conclusion also carries the rank bound `≤ 2` of the ORIGINAL scale `ρ ∘ val` in `d_ĝ` on
`U₁ = {D > 10}` (right before `∃ E`). Every other clause is verbatim. The consumer is the producer
of the extended final boundary family (LE/BoundaryPacketsBFRProducerV2.lean).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Manifold Bundle Filter
open scoped ContDiff Manifold Topology ENNReal NNReal
open DifferentialGeometry GC.Endpoint GC.MetricGeometry DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Comparison.Toponogov

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

section Binding

/-- **Binding of the rank-exporting regional kernel to `(W°, d_ĝ)`** (lane BCG-5): BCG-2's
binding with the rank bound `≤ 2` on `{D > 10}` (right before `∃ E`). Text of BCG-2:
(review 51; twin of
`exists_interior_chartFamilyEA_BDRY5`). The kernel `exists_regional_chartFamilyEAB_BCG2` on the
interior carrier `W°` with the ORIGINAL scale `ρ ∘ val`, the regions `U₁ = {D > 10}`,
`U₂ = {D ≥ 20}`, the revised edge regions `Ue₁ = {D > 20}`, `Ue₂ = {D ≥ 35}`, the candidate
envelope `{D ≥ 10}`, and BSA06's clauses at ONE `n` with `8 Lbig ≤ n`, `2300 Δ ≤ n`, `16 ≤ n`
(`2300Δ ≤ n` budgets both margins — `13Δ ≤ 10n` for `(U₁, U₂)`, `23Δ ≤ 15n` for `(Ue₁, Ue₂)` — and
the domain `B_ĝ(a, 1000Δρ(a)) ⊆ {D > 10}` for `a ∈ {D > 20}`). Parameter prefix = the binding's,
with `σs, vs` after `b`, and BE-1's requests (`ε, μ ≤ 10⁻⁸`, `100ΔΛ ≤ 10⁻⁸`, `∃ bd₀` after `w`): the
output also carries the circle residual and the revised edge family's disk packets and sections. -/
theorem exists_interior_chartFamilyEABR_BCG5 (K : ℕ) (hK : 5 ≤ K) (A : ℝ → ℝ) :
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
      ∀ σ : ℝ, 0 < σ → σ ≤ a₂ → σ ≤ threeSplittingExclusionThreshold.{0, 0} → σ ≤ a₀ →
      ∀ Λ : ℝ, 0 < Λ → Δ * Λ * 2000000 ≤ 1 / 100 → Λ < 1 / (1000000 * Δ) →
        100 * Δ * Λ ≤ 1 / 1000000 →
        2 * ε + 300 * Δ * Λ + Real.sqrt (504000 / Δ + 3780 * τ) < γc / 1000 →
        Λ < s' / (100000000 * Δ ^ 2) → 100 * Δ * Λ ≤ 1 / 10 ^ 8 →
      ∃ w₀ : ℝ, 0 < w₀ ∧ ∀ w : ℝ, 0 < w → w < w₀ → ∃ bd₀ : ℝ, 0 < bd₀ ∧
      ∀ b : ℝ, 0 < b → b < s / 100000 → b < bc₀ → b < b₁ → 100 * Δ < b⁻¹ → b < bd₀ →
      ∀ σs vs : ℝ, 0 < σs → σs ≤ 1 / 100 → 0 < vs → ∃ b₀ : ℝ, 0 < b₀ ∧
      ∀ β : ℕ → ℝ, β 2 = β₂ → 0 < β 1 → β 1 < b₀ →
        β 3 ≤ threeSplittingExclusionThreshold.{0, 0} →
      ∀ Lmax : ℝ, ∃ L₀ : ℝ, 0 < L₀ ∧ ∀ Lbig : ℝ, L₀ ≤ Lbig → Lmax ≤ Lbig →
      ∀ (W : CompactCarrier.{0}) [ConnectedSpace W.Carrier]
        (g : SmoothRiemannianMetric W.model W.Carrier)
        (ĝ : SmoothRiemannianMetric (𝓡 3) (W.pieceInterior ⊤)),
        RiemannianMetricComplete (I := 𝓡 3) ĝ →
        (∀ x : W.pieceInterior ⊤, ENNReal.ofReal 4 ≤ distanceToBoundary W g x →
          ĝ.inner x = (pieceInteriorMetric W g ⊤).inner x) →
        (∀ (x : W.pieceInterior ⊤) (v : TangentSpace (𝓡 3) x),
          (pieceInteriorMetric W g ⊤).inner x v v ≤ ĝ.inner x v v) →
      ∀ (ρ : W.Carrier → ℝ) (hρ : ∀ p, 0 < ρ p), ContMDiff W.model 𝓘(ℝ, ℝ) ∞ ρ →
        (∀ x y, ENNReal.ofReal |ρ x - ρ y| ≤ ENNReal.ofReal Λ * riemannianEDistOf g x y) →
        (∀ p, firstVolumeScale g p w / 2 < ρ p) →
      ∀ n : ℝ, 8 * Lbig ≤ n → 2300 * Δ ≤ n → 16 ≤ n →
        (∀ p : W.Carrier,
          w / (2 * (1 + 2 / Λ) ^ 3) / (24 * ∫ t in (0 : ℝ)..1, Real.sinh t ^ 2) ≤
              (ballVolume g p (ρ p)).toReal / ρ p ^ 3 ∧
          (∀ y ∈ riemannianBallOf (normalizedCenterMetric g (ρ p) (hρ p)) p (n / 4),
            SectionalBoundedBelowAt (normalizedCenterMetric g (ρ p) (hρ p)) y
              (-((n / 4) ^ 2)⁻¹)) ∧
          (∀ R : ℝ, 0 < R → 2 * R + 2 < n → ∀ k ≤ K,
            ∀ y ∈ riemannianBallOf (normalizedCenterMetric g (ρ p) (hρ p)) p R,
              curvatureDerivativeNorm (normalizedCenterMetric g (ρ p) (hρ p)) k y ≤
                (2 : ℝ) ^ (K + 2) * boundaryDerivativeConstant A K (2 * R + 2)
                  (w / (2 * (1 + 2 / Λ) ^ 3))) ∧
          (0 < distanceToBoundary W g p →
            n * (distanceToBoundary W g p).toReal / ((distanceToBoundary W g p).toReal + 3) <
              (distanceToBoundary W g p).toReal / ρ p)) →
      letI := inducedMetricSpace ĝ
      ∃ _ : CompleteSpace (W.pieceInterior ⊤),
      ∃ L : ChartFamilyEOn (W.pieceInterior ⊤) ĝ (inducedMetricSpace_hmetric ĝ) (fun x => ρ x)
          (fun x => hρ x) Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ
          {x | ENNReal.ofReal 10 < distanceToBoundary W g x}
          {x | ENNReal.ofReal 20 ≤ distanceToBoundary W g x},
        Nonempty (∀ j (hj : j ∈ L.circle.centres),
          CircleAdaptedCentreOn (W.pieceInterior ⊤) ĝ (inducedMetricSpace_hmetric ĝ)
            (fun x => ρ x) (fun x => hρ x) β γ
            {x | ENNReal.ofReal 10 < distanceToBoundary W g x}
            {x | ENNReal.ofReal 20 ≤ distanceToBoundary W g x} L.circle j hj) ∧
        (∀ j (hj : j ∈ L.circle.centres),
          let c := L.circle.chart j hj
          letI := (inducedMetricSpace ĝ).rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
          ∀ x ∈ ball j 200, ‖c.coord x‖ ≤ 8 → x ∈ ball j 10) ∧
        (∀ j (hj : j ∈ L.slim.centres), ∀ x ∈ ball j (10 ^ 6 * Δ * ρ j),
          |(L.slim.centre j hj).coord_BCG2 x -
            (letI := (L.slim.centre j hj).instZ
             @KleinerLottApprox.toFun (W.pieceInterior ⊤) (WithLp 2 (ℝ × (L.slim.centre j hj).Z))
              ((inducedMetricSpace ĝ).rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))) _ j _ (β 1)
                (L.slim.centre j hj).split x).fst| < vs) ∧
        (∀ x ∈ {x : W.pieceInterior ⊤ | ENNReal.ofReal 10 < distanceToBoundary W g x},
          scaledSplittingRank.{0, 0} (fun y : W.pieceInterior ⊤ => ρ y) (fun y => hρ y) β x
            ≤ 2) ∧
        ∃ E : EdgeFamilyOn (W.pieceInterior ⊤) ĝ (inducedMetricSpace_hmetric ĝ) (fun x => ρ x)
            (fun x => hρ x) β Δ σc μ b s b' s' ε γc βc
            {x | ENNReal.ofReal 20 < distanceToBoundary W g x}
            {x | ENNReal.ofReal 35 ≤ distanceToBoundary W g x},
          (∀ j (hj : j ∈ E.centres),
            let c := E.chart j hj
            let A : Set (W.pieceInterior ⊤) := closure
              {y | @isEdgePoint.{0, 0} (W.pieceInterior ⊤)
                ((inducedMetricSpace ĝ).rescale (ρ y)⁻¹ (inv_pos.mpr (hρ y))) y Δ b' s'}
            let hMc : CompleteSpace (W.pieceInterior ⊤) := ‹CompleteSpace (W.pieceInterior ⊤)›
            letI := (inducedMetricSpace ĝ).rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
            letI := radialScaledBundle ĝ (ρ j)⁻¹ (inv_pos.mpr (hρ j))
            letI : IsContinuousRiemannianBundle E3
                (fun x : W.pieceInterior ⊤ => TangentSpace 𝓘(ℝ, E3) x) :=
              radialScaledContinuous ĝ (ρ j)⁻¹ (inv_pos.mpr (hρ j))
            letI : IsRiemannianManifold 𝓘(ℝ, E3) (W.pieceInterior ⊤) :=
              radialScaledManifold (m := inducedMetricSpace ĝ) ĝ (inducedMetricSpace_hmetric ĝ)
                (ρ j)⁻¹ (inv_pos.mpr (hρ j))
            letI : CompleteSpace (W.pieceInterior ⊤) :=
              ((inducedMetricSpace ĝ).rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr
                hMc
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
            let A : Set (W.pieceInterior ⊤) := closure
              {y | @isEdgePoint.{0, 0} (W.pieceInterior ⊤)
                ((inducedMetricSpace ĝ).rescale (ρ y)⁻¹ (inv_pos.mpr (hρ y))) y Δ b' s'}
            let hMc : CompleteSpace (W.pieceInterior ⊤) := ‹CompleteSpace (W.pieceInterior ⊤)›
            letI := (inducedMetricSpace ĝ).rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
            letI := radialScaledBundle ĝ (ρ j)⁻¹ (inv_pos.mpr (hρ j))
            letI : IsContinuousRiemannianBundle E3
                (fun x : W.pieceInterior ⊤ => TangentSpace 𝓘(ℝ, E3) x) :=
              radialScaledContinuous ĝ (ρ j)⁻¹ (inv_pos.mpr (hρ j))
            letI : IsRiemannianManifold 𝓘(ℝ, E3) (W.pieceInterior ⊤) :=
              radialScaledManifold (m := inducedMetricSpace ĝ) ĝ (inducedMetricSpace_hmetric ĝ)
                (ρ j)⁻¹ (inv_pos.mpr (hρ j))
            letI : CompleteSpace (W.pieceInterior ⊤) :=
              ((inducedMetricSpace ĝ).rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr
                hMc
            let gR : SmoothRiemannianMetric 𝓘(ℝ, E3) (W.pieceInterior ⊤) :=
              scaleMetric ((ρ j)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (hρ j)) 2) ĝ
            have hnR : IsMetricNorm (I := 𝓘(ℝ, E3)) (M := W.pieceInterior ⊤) gR :=
              isMetricNorm_of_riemannianBundle gR
            ∃ P : EdgeDiskPacket gR hnR Δ σc μ b γc βc A (fun x => ρ x / ρ j)
              (fun x => Fs x / ρ j), P.toEdgeChart = c) ∧
          (∀ j (hj : j ∈ E.centres),
            let c := E.chart j hj
            let Fs := E.smoothing
            let hMc : CompleteSpace (W.pieceInterior ⊤) := ‹CompleteSpace (W.pieceInterior ⊤)›
            letI := (inducedMetricSpace ĝ).rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
            letI := radialScaledBundle ĝ (ρ j)⁻¹ (inv_pos.mpr (hρ j))
            letI : IsContinuousRiemannianBundle E3
                (fun x : W.pieceInterior ⊤ => TangentSpace 𝓘(ℝ, E3) x) :=
              radialScaledContinuous ĝ (ρ j)⁻¹ (inv_pos.mpr (hρ j))
            letI : IsRiemannianManifold 𝓘(ℝ, E3) (W.pieceInterior ⊤) :=
              radialScaledManifold (m := inducedMetricSpace ĝ) ĝ (inducedMetricSpace_hmetric ĝ)
                (ρ j)⁻¹ (inv_pos.mpr (hρ j))
            letI : CompleteSpace (W.pieceInterior ⊤) :=
              ((inducedMetricSpace ĝ).rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr
                hMc
            ∃ sec : Ioo (-(17 / 2 * Δ)) (17 / 2 * Δ) → W.pieceInterior ⊤, Continuous sec ∧
              ∀ a : Ioo (-(17 / 2 * Δ)) (17 / 2 * Δ), c.coord (sec a) = a ∧
                Fs (sec a) / ρ j / (ρ (sec a) / ρ j) < Δ / 100 ∧ dist (sec a) j < 10 * Δ) ∧
          (∀ j ∈ E.centres, ball j (1000 * Δ * ρ j) ⊆
            {x | ENNReal.ofReal 10 < distanceToBoundary W g x}) ∧
          ∀ x ∈ {x : W.pieceInterior ⊤ | ENNReal.ofReal 35 ≤ distanceToBoundary W g x},
            x ∈ scaledSplittingStratum.{0, 0} (fun y : W.pieceInterior ⊤ => ρ y) (fun y => hρ y)
              β 0 ∨
            (∃ j ∈ L.circle.centres, x ∈ ball j (2 * ρ j)) ∨
            (∃ j ∈ L.slim.centres, x ∈ ball j (2 * (Δ * ρ j))) ∨
            ∃ j ∈ E.centres, dist x j < 2 * Δ * ρ j := by
  obtain ⟨a₂, ha₂, h⟩ := exists_regional_chartFamilyEABR_BCG5 K hK
  refine ⟨a₂, ha₂, fun γ hγ hγ1 => ?_⟩
  obtain ⟨β₀, hβ₀, hβ₀a, h⟩ := h γ hγ hγ1
  refine ⟨β₀, hβ₀, hβ₀a, fun βc γc hβc hβγ hγc hγc1 => ?_⟩
  obtain ⟨σ₀, hσ₀, Δ₀, hΔ₀, h⟩ := h βc γc hβc hβγ hγc hγc1
  refine ⟨σ₀, hσ₀, Δ₀, hΔ₀, fun β₂ Δ hβ₂ hβ₂β₀ hβ₂small hΔ hΔ₀Δ => ?_⟩
  have hΔpos : 0 < Δ := lt_trans (div_pos (by norm_num) hβ₂) hΔ
  obtain ⟨τ₀, hτ₀, bc₀, hbc₀, h⟩ := h β₂ Δ hβ₂ hβ₂β₀ hβ₂small hΔ hΔ₀Δ
  refine ⟨τ₀, hτ₀, bc₀, hbc₀, fun σc ε μ τ hσc hσcσ₀ hε hε1 hμ hμ1 hτ hττ₀ hθ hε8 hμ8 s b' s'
    hs hssmall hsb' hss' hb'd hs'd hb'e hs'e => ?_⟩
  obtain ⟨a₀, b₁, ha₀, hb₁, h⟩ := h σc ε μ τ hσc hσcσ₀ hε hε1 hμ hμ1 hτ hττ₀ hθ hε8 hμ8 s b'
    s' hs hssmall hsb' hss' hb'd hs'd hb'e hs'e
  refine ⟨a₀, b₁, ha₀, hb₁, fun σ hσ hσa hση hσa₀ Λ hΛ hΛΔ hΛ44 hlam hbudget hend hΛ8 => ?_⟩
  have hσ1 : σ < 1 := hση.trans_lt (threeSplittingExclusionThreshold_lt.trans (by norm_num))
  obtain ⟨w₀, hw₀, -, Lm, hLm, hmodel⟩ := model_completion_BDRY5.{0} hσ hσ1
  refine ⟨w₀, hw₀, fun w hw hww => ?_⟩
  have hw' : 0 < w / (2 * (1 + 2 / Λ) ^ 3) := by positivity
  have hv : 0 < w / (2 * (1 + 2 / Λ) ^ 3) / (24 * ∫ t in (0 : ℝ)..1, Real.sinh t ^ 2) :=
    div_pos hw' (lt_of_lt_of_le (by norm_num) eight_le_twentyFour_mul_integral_sinh_sq)
  obtain ⟨bd₀, hbd₀, h⟩ := h σ hσa hση hσa₀ Λ hΛ hΛΔ hΛ44 hlam hbudget hend hΛ8 _ hv
    (fun R => (2 : ℝ) ^ (K + 2) * boundaryDerivativeConstant A K (2 * R + 2)
      (w / (2 * (1 + 2 / Λ) ^ 3)))
  refine ⟨bd₀, hbd₀, fun b hb hbs hbc hbb₁ hsource hbd σs vs hσs hσs1 hvs => ?_⟩
  obtain ⟨b₀, hb₀, h⟩ := h b hb hbs hbc hbb₁ hsource hbd σs vs hσs hσs1 hvs
  refine ⟨b₀, hb₀, fun β hβ2 hβ1 hβ1b hβ3 Lmax => ?_⟩
  obtain ⟨L₀, hL₀, h⟩ := h β hβ2 hβ1 hβ1b hβ3 Lmax
  refine ⟨max L₀ Lm, lt_max_of_lt_left hL₀, fun Lbig hLbig hLmax W _ g ĝ hcomp heq hle ρ hρ hρsm
    hlip hfirst n hn8 hn2300 hn16 hdata => ?_⟩
  let mX : MetricSpace (W.pieceInterior ⊤) := inducedMetricSpace ĝ
  have hcN : CompleteSpace (W.pieceInterior ⊤) := completeSpace_completion_BDRY2 W ĝ hcomp
  have hpN : ProperSpace (W.pieceInterior ⊤) :=
    inducedMetricSpace_properSpace_of_riemannianMetricComplete hcomp
  obtain ⟨o⟩ := nonempty_interiorOrientation_BDRY5 W
  have hL₀b : L₀ ≤ Lbig := (le_max_left _ _).trans hLbig
  have hLmb : Lm ≤ Lbig := (le_max_right _ _).trans hLbig
  have hLbig0 : 0 ≤ Lbig := hL₀.le.trans hL₀b
  have hnLm : 8 * Lm ≤ n := by linarith only [hLmb, hn8]
  have hn8' : (8 : ℝ) ≤ n := by linarith only [hn16]
  have hbcp : ∀ p, 0 < distanceToBoundary W g p →
      n * (distanceToBoundary W g p).toReal / ((distanceToBoundary W g p).toReal + 3) <
        (distanceToBoundary W g p).toReal / ρ p := fun p => (hdata p).2.2.2
  have hpos5 : ∀ q : W.pieceInterior ⊤, ENNReal.ofReal 10 < distanceToBoundary W g q →
      ENNReal.ofReal 5 < distanceToBoundary W g q := fun q hq =>
    lt_trans ((ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 10)).mpr
      (by norm_num : (5 : ℝ) < 10)) hq
  have hpt := fun (q : W.pieceInterior ⊤) (hq : ENNReal.ofReal 10 < distanceToBoundary W g q) =>
    regional_point_data_BDRY5 W g ĝ heq q (hpos5 q hq) (hρ q)
      (Aprof := fun R => (2 : ℝ) ^ (K + 2) * boundaryDerivativeConstant A K (2 * R + 2)
        (w / (2 * (1 + 2 / Λ) ^ 3)))
      (hbcp q ((zero_le).trans_lt (hpos5 q hq))) (hdata q).1 (hdata q).2.1 (hdata q).2.2.1 hn8 hn8'
  have hΔn : 13 * Δ ≤ 10 * n := by linarith only [hn2300, hΔpos]
  have hΔn' : 23 * Δ ≤ 15 * n := by linarith only [hn2300, hΔpos]
  obtain ⟨L, hL⟩ := h Lbig hL₀b hLmax (W.pieceInterior ⊤) ĝ (inducedMetricSpace_hmetric ĝ) o
    (fun x => ρ x) (fun x => hρ x) (contMDiff_comp_val_BDRY5 W hρsm)
    (lipschitzWith_comp_val_completion_BDRY5 W g ĝ hle hlip)
    {x | ENNReal.ofReal 10 < distanceToBoundary W g x}
    {x | ENNReal.ofReal 20 ≤ distanceToBoundary W g x}
    {x | ENNReal.ofReal 10 ≤ distanceToBoundary W g x}
    (isCompact_le_distanceToBoundary_BDRY1 W g (by norm_num))
    (fun x (hx : ENNReal.ofReal 10 < distanceToBoundary W g x) => show
      ENNReal.ofReal 10 ≤ distanceToBoundary W g x from le_of_lt hx)
    (fun x (hx : ENNReal.ofReal 20 ≤ distanceToBoundary W g x) => show
      ENNReal.ofReal 10 < distanceToBoundary W g x from lt_of_lt_of_le
        ((ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 20)).mpr
          (by norm_num : (10 : ℝ) < 20)) hx)
    (margin_completion_BDRY5 W g ĝ hle ρ hρ hΔpos.le hΔn hbcp)
    {x | ENNReal.ofReal 20 < distanceToBoundary W g x}
    {x | ENNReal.ofReal 35 ≤ distanceToBoundary W g x}
    (fun x (hx : ENNReal.ofReal 35 ≤ distanceToBoundary W g x) => show
      ENNReal.ofReal 20 < distanceToBoundary W g x from lt_of_lt_of_le
        ((ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 35)).mpr
          (by norm_num : (20 : ℝ) < 35)) hx)
    (margin_level_completion_BCG2 W g ĝ hle ρ hρ hΔn' hbcp)
    (ball_subset_level_completion_BCG2 W g ĝ hle ρ hρ hn2300 hbcp)
    (fun p hp => hmodel W g ĝ hcomp heq ρ hρ hbcp hnLm hn16 hw hww hfirst
      (fun q => (hdata q).2.1) p (hpos5 p hp))
    (fun p hp => (hpt p hp).1) (fun p hp => (hpt p hp).2.1) (fun p hp => (hpt p hp).2.2)
  exact ⟨hcN, L, hL⟩

end Binding

end DifferentialGeometry.Geometry.Collapse
