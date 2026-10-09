import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryRegionalEdge

/-!
# LC88 / BCP04, packets P4–P5: the shared regionalised kernel (`ChartFamilyEOn` + circle packets)

Review 45 §3.3 (binding route): ONE shared regionalised kernel — `ControlledLocalData` +
`CompactCandidateRegion` ⟹ `LocalPacketsOn`, the closed case being `U₁ = U₂ = univ`. This module
assembles the circle, slim and strong-edge halves (BDRY-4 G17 modules) into the full
`ChartFamilyEOn` with circle adapted-coordinate packets on ONE complete, proper, σ-compact,
connected, oriented carrier. The controlled local data are explicit hypotheses:

* a smooth positive `Λ`-Lipschitz scale `ρ`;
* regions `U₂ ⊆ U₁ ⊆ Kc` with `Kc` compact (the candidate envelope), and the margin
  "`p ∈ U₂`, `d(a, p) < Δρ(a)` ⇒ `a ∈ U₁`" (for LFR44's witnesses);
* at every `p ∈ U₁`: the collapsed model of quality `σ`, the curvature buffer
  `sec ≥ -(Lρ(p))⁻²` on `B(p, Lρ(p))` for every `0 < L ≤ Lbig`, and LPA01's volume lower bound and
  derivative bounds of `ρ(p)⁻² g` on balls of radius `≤ Lbig` (any profile `A`).

`exists_regional_chartFamilyEA_BDRY4` (parameter prefix = the closed producer's, then `v, A` after
`Λ`, the buffer radius `Lmax` after `β`, and `∃ L₀, ∀ Lbig ≥ max L₀ Lmax`): a
`ChartFamilyEOn … U₁ U₂` (centres in `U₁`, eligible covers of `U₁`, nonslim cover and exhaustion on
`U₂`, the buffer at `p ∈ U₁`) with a `CircleAdaptedCentreOn` at every circle centre. The stratum
exhaustion uses the rank bound `≤ 2` at points of `U₂` obtained from the model (LC18/LC20 with
`σ, β₃` below the three-splitting threshold).

* `sectional_ball_of_buffer_BDRY4`: a buffer on `B(p, r)` with bound `-r⁻²` gives every smaller ball
  and every weaker bound.
* consumer `exists_regional_chartFamilyEA_centres_BDRY4`: all circle, slim and edge centres lie
  in `U₁`.
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

/-- A curvature buffer `sec ≥ -r⁻²` on `B(p, r)` gives every smaller ball and every weaker bound. -/
theorem sectional_ball_of_buffer_BDRY4 {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X) {p : X} {r R κ : ℝ}
    (h : ∀ y ∈ ball p r, SectionalBoundedBelowAt g y (-(r ^ 2)⁻¹)) (hR : R ≤ r)
    (hκ : κ ≤ -(r ^ 2)⁻¹) : ∀ y ∈ ball p R, SectionalBoundedBelowAt g y κ :=
  fun y hy => (h y (ball_subset_ball hR hy)).mono hκ

/-- **The sectional forms used by the three halves**, from ONE buffer `sec ≥ -(Lρ)⁻²` on
`B(p, Lρ)` for all `0 < L ≤ L₀`, `L₀ = c₁ + c₁Δ + c₂Δ + (10⁴Δ + κ⁻¹) + b⁻¹ + β₁⁻¹ + β₂⁻¹`
(`c₁ = 3·2·10⁶ + 2/3`, `c₂ = 4(1 + 2·2·10⁶ + 1/3)`). -/
theorem regional_sectional_forms_BDRY4 {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X) {p : X} {r Δ κ b β₁ β₂ : ℝ}
    (hr : 0 < r) (hΔ : 1 ≤ Δ) (hκ : 0 < κ) (hb : 0 < b) (hβ₁ : 0 < β₁) (hβ₂ : 0 < β₂)
    (hbuf : ∀ L, 0 < L → L ≤ (3 * 2000000 + 2 / 3) + (3 * 2000000 + 2 / 3) * Δ +
        4 * (1 + 2 * 2000000 + 1 / 3) * Δ + (10000 * Δ + κ⁻¹) + b⁻¹ + β₁⁻¹ + β₂⁻¹ →
      ∀ y ∈ ball p (L * r), SectionalBoundedBelowAt g y (-((L * r) ^ 2)⁻¹)) :
    (∀ y ∈ ball p (β₂⁻¹ * r), SectionalBoundedBelowAt g y (-(β₂ ^ 2 * r⁻¹ ^ 2))) ∧
    (∀ y ∈ ball p ((3 * 2000000 + 2 / 3) * r),
      SectionalBoundedBelowAt g y (-((2000000 * r) ^ 2)⁻¹)) ∧
    (∀ y ∈ ball p (β₁⁻¹ * r), SectionalBoundedBelowAt g y (-(β₁ / r) ^ 2)) ∧
    (∀ y ∈ ball p ((3 * 2000000 + 2 / 3) * (Δ * r)),
      SectionalBoundedBelowAt g y (-((2000000 * (Δ * r)) ^ 2)⁻¹)) ∧
    (∀ z ∈ ball p (10000 * (Δ * r)), SectionalBoundedBelowAt g z (-(κ / r) ^ 2)) ∧
    (∀ z ∈ ball p (b⁻¹ * r), SectionalBoundedBelowAt g z (-(b / r) ^ 2)) ∧
    (∀ y ∈ ball p (4 * (1 + 2 * 2000000 + 1 / 3) * Δ * r),
      SectionalBoundedBelowAt g y (-((4 * (1 + 2 * 2000000 + 1 / 3) * Δ * r) ^ 2)⁻¹)) := by
  have hΔpos : 0 < Δ := by linarith
  have hκi : 0 < κ⁻¹ := inv_pos.mpr hκ
  have hbi : 0 < b⁻¹ := inv_pos.mpr hb
  have hβ1i : 0 < β₁⁻¹ := inv_pos.mpr hβ₁
  have hβ2i : 0 < β₂⁻¹ := inv_pos.mpr hβ₂
  have hc1Δ : 0 < (3 * 2000000 + 2 / 3) * Δ := by positivity
  have hc2Δ : 0 < 4 * (1 + 2 * 2000000 + 1 / 3) * Δ := by positivity
  have h4Δ : 0 < 10000 * Δ := by positivity
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine sectional_ball_of_buffer_BDRY4 g (hbuf β₂⁻¹ hβ2i (by linarith)) le_rfl (le_of_eq ?_)
    field_simp
  · refine sectional_ball_of_buffer_BDRY4 g (hbuf (3 * 2000000 + 2 / 3) (by norm_num)
      (by linarith)) le_rfl ?_
    rw [neg_le_neg_iff]
    apply inv_anti₀ (by positivity)
    apply pow_le_pow_left₀ (by positivity)
    nlinarith
  · refine sectional_ball_of_buffer_BDRY4 g (hbuf β₁⁻¹ hβ1i (by linarith)) le_rfl (le_of_eq ?_)
    field_simp
  · have h := hbuf ((3 * 2000000 + 2 / 3) * Δ) hc1Δ (by linarith)
    rw [mul_assoc] at h
    refine sectional_ball_of_buffer_BDRY4 g h le_rfl ?_
    rw [neg_le_neg_iff]
    apply inv_anti₀ (by positivity)
    apply pow_le_pow_left₀ (by positivity)
    have hΔρ := mul_pos hΔpos hr
    nlinarith
  · refine sectional_ball_of_buffer_BDRY4 g (hbuf (10000 * Δ + κ⁻¹) (by positivity)
      (by linarith)) ?_ ?_
    · rw [add_mul, mul_assoc]
      linarith [mul_pos hκi hr]
    · rw [neg_le_neg_iff]
      have hκρ : (κ / r) ^ 2 = ((r / κ) ^ 2)⁻¹ := by rw [← inv_pow, inv_div]
      rw [hκρ]
      apply inv_anti₀ (by positivity)
      apply pow_le_pow_left₀ (by positivity)
      rw [div_eq_inv_mul]
      exact mul_le_mul_of_nonneg_right (by linarith) hr.le
  · refine sectional_ball_of_buffer_BDRY4 g (hbuf b⁻¹ hbi (by linarith)) le_rfl (le_of_eq ?_)
    field_simp
  · exact hbuf _ hc2Δ (by linarith)

/-- **The shared regionalised kernel: `ChartFamilyEOn` with circle adapted packets on a complete
carrier.** See the module docstring. -/
theorem exists_regional_chartFamilyEA_BDRY4
    {σs : ℝ} (hσs : 0 < σs) (hσs1 : σs ≤ 1 / 100) (K : ℕ) (hK : 5 ≤ K) :
    ∃ a₂ : ℝ, 0 < a₂ ∧ ∀ γ : ℝ, 0 < γ → γ < 1 / 10 → ∃ β₀ : ℝ, 0 < β₀ ∧ β₀ ≤ a₂ ∧
      ∀ βc γc : ℝ, 0 < βc → βc < γc / 1000 → 0 < γc → γc < 1 / 100 →
      ∃ σ₀ : ℝ, 0 < σ₀ ∧ ∃ Δ₀ : ℝ, 0 < Δ₀ ∧
      ∀ β₂ Δ : ℝ, 0 < β₂ → β₂ ≤ β₀ → β₂ < 1 / 100 → 100 / β₂ < Δ → Δ₀ ≤ Δ →
      ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∃ bc₀ : ℝ, 0 < bc₀ ∧
      ∀ σc ε μ τ : ℝ, 0 < σc → σc ≤ σ₀ → 0 < ε → ε < 1 / 100 → 0 < μ → μ ≤ 1 / 1000000 →
        0 < τ → τ ≤ τ₀ → 140 * Real.sqrt τ < ε ^ 2 / 20 →
      ∀ s b' s' : ℝ, 0 < s → s < 1 / 100 → s < b' / 100000 → s < s' / 100000 →
        b' < 1 / (1000000 * Δ) → s' < 1 / (1000000 * Δ) →
        b' < τ * Δ / 1000000000 → s' < τ * Δ / 1000000000 → ∃ a₀ b₁ : ℝ, 0 < a₀ ∧ 0 < b₁ ∧
      ∀ σ : ℝ, σ ≤ a₂ → σ ≤ threeSplittingExclusionThreshold.{0, 0} → σ ≤ a₀ →
      ∀ Λ : ℝ, 0 < Λ → Δ * Λ * 2000000 ≤ 1 / 100 → Λ < 1 / (1000000 * Δ) →
        100 * Δ * Λ ≤ 1 / 1000000 →
        2 * ε + 300 * Δ * Λ + Real.sqrt (504000 / Δ + 3780 * τ) < γc / 1000 →
        Λ < s' / (100000000 * Δ ^ 2) →
      ∀ v : ℝ, 0 < v → ∀ Aprof : ℝ → ℝ,
      ∀ b : ℝ, 0 < b → b < s / 100000 → b < bc₀ → b < b₁ → 100 * Δ < b⁻¹ → ∃ b₀ : ℝ, 0 < b₀ ∧
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
          CircleAdaptedCentreOn X g hmetric ρ hρpos β γ U₁ U₂ L.circle j hj) := by
  classical
  obtain ⟨a₂, ha₂, hC⟩ := exists_regional_circleFamily_BDRY4
  refine ⟨a₂, ha₂, fun γ hγ hγ1 => ?_⟩
  obtain ⟨β₀, hβ₀, hβ₀a, hC⟩ := hC γ hγ hγ1
  refine ⟨β₀, hβ₀, hβ₀a, fun βc γc hβc hβγ hγc hγc1 => ?_⟩
  obtain ⟨σ₀, hσ₀, Δ₀, hΔ₀, hE⟩ := exists_regional_edgeFamily_BDRY4 hβc hβγ hγc hγc1
  refine ⟨σ₀, hσ₀, Δ₀, hΔ₀, fun β₂ Δ hβ₂ hβ₂β₀ hβ₂small hΔ hΔ₀Δ => ?_⟩
  have hΔ1 : 1 ≤ Δ := by
    have h100 : 100 < 100 / β₂ := (lt_div_iff₀ hβ₂).mpr (by linarith)
    linarith
  have hΔpos : 0 < Δ := by linarith
  obtain ⟨τ₀, hτ₀, κ₀, hκ₀, bc₀, hbc₀, hE⟩ := hE β₂ Δ hβ₂ hβ₂small hΔ hΔ₀Δ
  refine ⟨τ₀, hτ₀, bc₀, hbc₀, fun σc ε μ τ hσc hσcσ₀ hε hε1 hμ hμ1 hτ hττ₀ hθ s b' s' hs
    hssmall hsb' hss' hb'd hs'd hb'e hs'e => ?_⟩
  obtain ⟨a₀, b₁, ha₀, hb₁, hE⟩ := hE σc ε μ τ hσc hσcσ₀ hε hε1 hμ hμ1 hτ hττ₀ hθ s b' s' hs
    hssmall hsb' hss' hb'd hs'd hb'e hs'e
  refine ⟨a₀, b₁, ha₀, hb₁, fun σ hσa hση hσa₀ Λ hΛ hΛΔ hΛ44 hlam hbudget hend v hv Aprof b hb
    hbs hbc hbb₁ hsource => ?_⟩
  obtain ⟨b₀e, hb₀e, hE⟩ := hE Λ hΛ hΛΔ hΛ44 hlam hbudget hend b hb hbs hbc hbb₁ hsource
  obtain ⟨βS, hβS, hS⟩ := exists_regional_slimFamily_BDRY4 hΔ1 hσs hσs1 K hK hv Aprof
  refine ⟨min b₀e βS, lt_min hb₀e hβS, fun β hβ2 hβ1 hβ1b hβ3 Lmax => ?_⟩
  have hβ1e : β 1 < b₀e := hβ1b.trans_le (min_le_left _ _)
  have hβ1S : β 1 < βS := hβ1b.trans_le (min_le_right _ _)
  have hβ2pos : 0 < β 2 := by rw [hβ2]; exact hβ₂
  refine ⟨(3 * 2000000 + 2 / 3) + (3 * 2000000 + 2 / 3) * Δ + 4 * (1 + 2 * 2000000 + 1 / 3) * Δ +
      (10000 * Δ + κ₀⁻¹) + b⁻¹ + (β 1)⁻¹ + (β 2)⁻¹, by positivity,
    fun Lbig hL₀ hLmax X mX _ _ _ _ _ _ g hmetric o ρ hρpos hρsm hρlip U₁ U₂ Kc hKc hU₁ hU₂
    hmargin hmodel hsecL hvol hder => ?_⟩
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
  -- the circle half
  have hΛ2 : Λ * 2000000 ≤ 1 / 100 := by
    have h := mul_le_mul_of_nonneg_right hΔ1 (by positivity : (0 : ℝ) ≤ Λ * 2000000)
    rw [one_mul, ← mul_assoc] at h
    exact h.trans hΛΔ
  have hβ2b : β 2 ≤ β₀ := by rw [hβ2]; exact hβ₂β₀
  obtain ⟨circle, hcut, ⟨hAd⟩⟩ := hC X g hmetric ρ hρpos hΛ.le hρlip hΛ2 β hσa hβ2b U₁ U₂ Kc
    hKc hU₁ hmodel (fun p hp => (hforms p hp).1) (fun p hp => (hforms p hp).2.1)
  -- the slim half
  have hder' : ∀ p ∈ U₁, ∀ R, 0 < R → R < (β 1)⁻¹ → ∀ k ≤ K,
      ∀ y ∈ riemannianBallOf (normalizedCenterMetric g (ρ p) (hρpos p)) p R,
        curvatureDerivativeNorm (normalizedCenterMetric g (ρ p) (hρpos p)) k y ≤ Aprof R :=
    fun p hp R hR hRβ => hder p hp R hR (hRβ.le.trans hβ1L)
  obtain ⟨slim, hslimcut⟩ := hS X g hmetric o ρ hρpos hΛ.le hρlip hΛΔ β hβ1 hβ1S U₁ U₂ Kc hKc hU₁
    (fun p hp => (hforms p hp).2.2.1) hvol hder' (fun p hp => (hforms p hp).2.2.2.1)
  -- the edge half
  obtain ⟨edge, hcoarse⟩ := hE X g hmetric ρ hρpos hρsm hρlip β hβ2 hβ1e hσa₀ U₁ U₂ Kc hKc hU₁ hU₂
    hmargin (fun p hp => hmodel p (hU₂ hp)) (fun p hp => (hforms p hp).2.2.2.2.1)
    (fun p hp => (hforms p hp).2.2.2.2.2.1) (fun p hp => (hforms p hp).2.2.2.2.2.2)
  -- the stratum exhaustion on `U₂` (rank `≤ 2` from the model)
  have hexh : ∀ x ∈ U₂, x ∈ scaledSplittingStratum.{0, 0} ρ hρpos β 0 ∨
      (∃ j ∈ circle.centres, x ∈ ball j (2 * ρ j)) ∨
      (∃ j ∈ slim.centres, x ∈ ball j (2 * (Δ * ρ j))) ∨
      ∃ j ∈ edge.centres, dist x j < 2 * Δ * ρ j := by
    intro x hx
    have hx1 : x ∈ U₁ := hU₂ hx
    obtain ⟨C, mC, c, hCc, -, hCdim, hCcomp, hCseg, ⟨f⟩⟩ := hmodel x hx1
    have hrank : scaledSplittingRank.{0, 0} ρ hρpos β x ≤ 2 :=
      @splittingRank_le_two_of_no_three.{0, 0} X
        (mX.rescale (ρ x)⁻¹ (inv_pos.mpr (hρpos x))) x β
        (@threeSplittingExclusionThreshold_excludes.{0, 0} X
          (mX.rescale (ρ x)⁻¹ (inv_pos.mpr (hρpos x))) x C mC hCc c hCseg hCdim hCcomp σ
          (β 3) hση hβ3 f)
    rcases Nat.lt_or_ge (scaledSplittingRank.{0, 0} ρ hρpos β x) 1 with h0 | h1
    · left
      change scaledSplittingRank.{0, 0} ρ hρpos β x = 0
      omega
    rcases Nat.lt_or_ge (scaledSplittingRank.{0, 0} ρ hρpos β x) 2 with h1' | h2
    · have hZ1 : x ∈ scaledSplittingStratum.{0, 0} ρ hρpos β 1 := by
        change scaledSplittingRank.{0, 0} ρ hρpos β x = 1
        omega
      by_cases hsl : (∃ (Z : Type) (mZ : MetricSpace Z) (z : Z), letI := mZ
          Bornology.IsBounded (univ : Set Z) ∧ diam (univ : Set Z) < 1000 * Δ ∧
          Nonempty (@KleinerLottApprox X (WithLp 2 (ℝ × Z))
            (mX.rescale (ρ x)⁻¹ (inv_pos.mpr (hρpos x))) _ x (WithLp.toLp 2 ((0 : ℝ), z)) (β 1)))
      · obtain ⟨j, hj, hsub⟩ := slim.covers x ⟨hx1, hZ1⟩ hsl
        exact Or.inr (Or.inr (Or.inl ⟨j, hj, hsub (mem_ball_self (mul_pos hΔpos (hρpos x)))⟩))
      · exact Or.inr (Or.inr (Or.inr (edge.covers_nonslim x ⟨hx, hZ1⟩ hsl)))
    · have hZ2 : x ∈ scaledSplittingStratum.{0, 0} ρ hρpos β 2 := by
        change scaledSplittingRank.{0, 0} ρ hρpos β x = 2
        omega
      obtain ⟨j, hj, hsub⟩ := circle.covers x ⟨hx1, hZ2⟩
      exact Or.inr (Or.inl ⟨j, hj, hsub (mem_ball_self (hρpos x))⟩)
  exact ⟨{ contMDiff_scale := hρsm
           lipschitz_scale := hρlip
           circle := circle
           slim := slim
           edge := edge
           exhaustion := hexh
           circle_cutoff_eq := hcut
           slim_cutoff_eq := hslimcut
           sectional_buffer := fun L hL hLL p hp y hy => hsecL p hp L hL (hLL.trans hLmax) y hy
           edge_coarse := hcoarse }, ⟨hAd⟩⟩

/-- **Consumer: the regional centres lie in `U₁`.** The circle, slim and strong-edge centres of
the shared regionalised kernel lie in `U₁` (the closed case being `U₁ = univ`). -/
theorem exists_regional_chartFamilyEA_centres_BDRY4
    {σs : ℝ} (hσs : 0 < σs) (hσs1 : σs ≤ 1 / 100) (K : ℕ) (hK : 5 ≤ K) :
    ∃ a₂ : ℝ, 0 < a₂ ∧ ∀ γ : ℝ, 0 < γ → γ < 1 / 10 → ∃ β₀ : ℝ, 0 < β₀ ∧ β₀ ≤ a₂ ∧
      ∀ βc γc : ℝ, 0 < βc → βc < γc / 1000 → 0 < γc → γc < 1 / 100 →
      ∃ σ₀ : ℝ, 0 < σ₀ ∧ ∃ Δ₀ : ℝ, 0 < Δ₀ ∧
      ∀ β₂ Δ : ℝ, 0 < β₂ → β₂ ≤ β₀ → β₂ < 1 / 100 → 100 / β₂ < Δ → Δ₀ ≤ Δ →
      ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∃ bc₀ : ℝ, 0 < bc₀ ∧
      ∀ σc ε μ τ : ℝ, 0 < σc → σc ≤ σ₀ → 0 < ε → ε < 1 / 100 → 0 < μ → μ ≤ 1 / 1000000 →
        0 < τ → τ ≤ τ₀ → 140 * Real.sqrt τ < ε ^ 2 / 20 →
      ∀ s b' s' : ℝ, 0 < s → s < 1 / 100 → s < b' / 100000 → s < s' / 100000 →
        b' < 1 / (1000000 * Δ) → s' < 1 / (1000000 * Δ) →
        b' < τ * Δ / 1000000000 → s' < τ * Δ / 1000000000 → ∃ a₀ b₁ : ℝ, 0 < a₀ ∧ 0 < b₁ ∧
      ∀ σ : ℝ, σ ≤ a₂ → σ ≤ threeSplittingExclusionThreshold.{0, 0} → σ ≤ a₀ →
      ∀ Λ : ℝ, 0 < Λ → Δ * Λ * 2000000 ≤ 1 / 100 → Λ < 1 / (1000000 * Δ) →
        100 * Δ * Λ ≤ 1 / 1000000 →
        2 * ε + 300 * Δ * Λ + Real.sqrt (504000 / Δ + 3780 * τ) < γc / 1000 →
        Λ < s' / (100000000 * Δ ^ 2) →
      ∀ v : ℝ, 0 < v → ∀ Aprof : ℝ → ℝ,
      ∀ b : ℝ, 0 < b → b < s / 100000 → b < bc₀ → b < b₁ → 100 * Δ < b⁻¹ → ∃ b₀ : ℝ, 0 < b₀ ∧
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
        L.circle.centres ∪ L.slim.centres ∪ L.edge.centres ⊆ U₁
      := by
  obtain ⟨a₂, ha₂, h⟩ := exists_regional_chartFamilyEA_BDRY4 hσs hσs1 K hK
  refine ⟨a₂, ha₂, fun γ hγ hγ1 => ?_⟩
  obtain ⟨β₀, hβ₀, hβ₀a, h⟩ := h γ hγ hγ1
  refine ⟨β₀, hβ₀, hβ₀a, fun βc γc hβc hβγ hγc hγc1 => ?_⟩
  obtain ⟨σ₀, hσ₀, Δ₀, hΔ₀, h⟩ := h βc γc hβc hβγ hγc hγc1
  refine ⟨σ₀, hσ₀, Δ₀, hΔ₀, fun β₂ Δ hβ₂ hβ₂β₀ hβ₂small hΔ hΔ₀Δ => ?_⟩
  obtain ⟨τ₀, hτ₀, bc₀, hbc₀, h⟩ := h β₂ Δ hβ₂ hβ₂β₀ hβ₂small hΔ hΔ₀Δ
  refine ⟨τ₀, hτ₀, bc₀, hbc₀, fun σc ε μ τ hσc hσcσ₀ hε hε1 hμ hμ1 hτ hττ₀ hθ s b' s' hs
    hssmall hsb' hss' hb'd hs'd hb'e hs'e => ?_⟩
  obtain ⟨a₀, b₁, ha₀, hb₁, h⟩ := h σc ε μ τ hσc hσcσ₀ hε hε1 hμ hμ1 hτ hττ₀ hθ s b' s' hs
    hssmall hsb' hss' hb'd hs'd hb'e hs'e
  refine ⟨a₀, b₁, ha₀, hb₁, fun σ hσa hση hσa₀ Λ hΛ hΛΔ hΛ44 hlam hbudget hend v hv Aprof b hb
    hbs hbc hbb₁ hsource => ?_⟩
  obtain ⟨b₀, hb₀, h⟩ := h σ hσa hση hσa₀ Λ hΛ hΛΔ hΛ44 hlam hbudget hend v hv Aprof b hb hbs hbc
    hbb₁ hsource
  refine ⟨b₀, hb₀, fun β hβ2 hβ1 hβ1b hβ3 Lmax => ?_⟩
  obtain ⟨L₀, hL₀, h⟩ := h β hβ2 hβ1 hβ1b hβ3 Lmax
  refine ⟨L₀, hL₀, fun Lbig hL₀b hLmax X mX _ _ _ _ _ _ g hmetric o ρ hρpos hρsm hρlip U₁ U₂ Kc
    hKc hU₁ hU₂ hmargin hmodel hsecL hvol hder => ?_⟩
  obtain ⟨L, -⟩ := h Lbig hL₀b hLmax X g hmetric o ρ hρpos hρsm hρlip U₁ U₂ Kc hKc hU₁ hU₂
    hmargin hmodel hsecL hvol hder
  refine ⟨L, fun x hx => ?_⟩
  rcases hx with (hx | hx) | hx
  · exact (L.circle.centres_subset hx).1
  · exact (L.slim.centres_subset hx).1
  · exact L.edge.centres_subset hx

end DifferentialGeometry.Geometry.Collapse
