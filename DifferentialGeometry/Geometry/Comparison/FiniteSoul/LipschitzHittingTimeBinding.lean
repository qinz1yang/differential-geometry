import DifferentialGeometry.Geometry.Comparison.FiniteSoul.LipschitzHittingTime
import DifferentialGeometry.Geometry.Comparison.FiniteSoul.QuantitativePatch
import DifferentialGeometry.Geometry.Collapse.DistanceSmoothing.Finite.LocalApproximation

/-!
# Locally Lipschitz hitting times of `d_S` along a `C¹` flow (S-HIT binding, D4)

Package CM-S (finite soul), lane CMS-T.

* `locallyLipschitz_of_contMDiff_prod_finite`: a `C¹` map `ℝ × M → M` is locally Lipschitz for the
  distance of a complete metric of finite order (chart comparison in both directions:
  `exists_ball_finiteSeminormAt_chart_sub_le`, `exists_ball_dist_chart_symm_le_finite`).
* `locallyLipschitzOn_infDist_hittingTime`: for the flow of a `C¹` field along which `d_S` grows at a
  positive rate on an open neighbourhood of the band, the hitting time `(x, s) ↦ τ(x, s)` is locally
  Lipschitz on `{a ≤ d_S ≤ b} × [a, b]`.
* `exists_endpoint_band_field_lipschitz` (consumer, LFR23): for the SAME field and flow of
  `exists_endpoint_band_field`, the hitting time is locally Lipschitz, and so is the graph of the
  level `{d_S = s}` over every locally Lipschitz transversal.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter Metric
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.Geometry.FiniteSoul

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {r : ℕ∞}

/-- **A `C¹` map `ℝ × M → M` is locally Lipschitz** for the distance of a complete finite-order
metric. -/
theorem locallyLipschitz_of_contMDiff_prod_finite [NeZero (Module.finrank ℝ E)] [CompleteSpace M]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {F : ℝ × M → M} (hF : ContMDiff (𝓘(ℝ, ℝ).prod I) I 1 F) : LocallyLipschitz F := by
  rintro ⟨t₀, x₀⟩
  set y₀ := F (t₀, x₀) with hy₀
  set φ := extChartAt I x₀ with hφ
  set ψ := extChartAt I y₀ with hψ
  set χ := extChartAt (𝓘(ℝ, ℝ).prod I) ((t₀, x₀) : ℝ × M) with hχ
  have hχapp : ∀ q : ℝ × M, χ q = (q.1, φ q.2) := by
    intro q
    rw [hχ, extChartAt_prod]
    simp [hφ]
  have hχsrc : ∀ q : ℝ × M, q.2 ∈ φ.source → q ∈ χ.source := by
    intro q hq
    rw [hχ, extChartAt_prod]
    exact ⟨by simp, hq⟩
  -- the chart reading `G = ψ ∘ F ∘ χ⁻¹` is `C¹`, hence locally Lipschitz
  have hFat := hF (t₀, x₀)
  rw [contMDiffAt_iff] at hFat
  have hG : ContDiffAt ℝ 1 (ψ ∘ F ∘ χ.symm) (χ (t₀, x₀)) := by
    have h2 := hFat.2
    rwa [ModelWithCorners.Boundaryless.range_eq_univ, contDiffWithinAt_univ] at h2
  obtain ⟨K₁, T, hT, hlip⟩ := hG.exists_lipschitzOnWith
  -- chart comparisons
  obtain ⟨c₀, hc₀, hc₀N⟩ :=
    DifferentialGeometry.Geometry.Collapse.exists_mul_norm_le_finiteMetricSeminormAt g x₀
  obtain ⟨r₀, hr₀, hr₀src, hchart⟩ :=
    g.exists_ball_finiteSeminormAt_chart_sub_le hr hnorm x₀
      (κ := 2) one_lt_two
  obtain ⟨ρ, hρ, hρtgt, hsymm⟩ :=
    DifferentialGeometry.Geometry.Collapse.exists_ball_dist_chart_symm_le_finite g hnorm y₀
      (κ := 2) one_lt_two
  set C₂ := Real.sqrt ‖DifferentialGeometry.Geometry.Collapse.finiteMetricFormAt g y₀‖ with hC₂
  -- the neighbourhood
  have hFc : ContinuousAt F (t₀, x₀) := hFat.1
  have hψc : ContinuousAt (fun q => ψ (F q)) (t₀, x₀) :=
    (continuousAt_extChartAt y₀).comp hFc
  have hN1 : χ ⁻¹' T ∈ 𝓝 ((t₀, x₀) : ℝ × M) := (continuousAt_extChartAt _).preimage_mem_nhds hT
  have hN2 : (fun q => ψ (F q)) ⁻¹' ball (ψ y₀) ρ ∈ 𝓝 ((t₀, x₀) : ℝ × M) :=
    hψc.preimage_mem_nhds (ball_mem_nhds _ hρ)
  have hN3 : F ⁻¹' ψ.source ∈ 𝓝 ((t₀, x₀) : ℝ × M) :=
    hFc.preimage_mem_nhds (extChartAt_source_mem_nhds y₀)
  have hN4 : Prod.snd ⁻¹' ball x₀ r₀ ∈ 𝓝 ((t₀, x₀) : ℝ × M) :=
    continuous_snd.continuousAt.preimage_mem_nhds (ball_mem_nhds _ hr₀)
  set K : ℝ≥0 := ⟨2 * C₂ * K₁ * max 1 (2 / c₀), by positivity⟩ with hK
  refine ⟨K, _, inter_mem (inter_mem hN1 hN2) (inter_mem hN3 hN4),
    LipschitzOnWith.of_dist_le_mul fun q hq q' hq' => ?_⟩
  obtain ⟨⟨hq1, hq2⟩, hq3, hq4⟩ := hq
  obtain ⟨⟨hq1', hq2'⟩, hq3', hq4'⟩ := hq'
  have hqs : q.2 ∈ φ.source := by rw [hφ, extChartAt_source]; exact hr₀src hq4
  have hqs' : q'.2 ∈ φ.source := by rw [hφ, extChartAt_source]; exact hr₀src hq4'
  have hGq : (ψ ∘ F ∘ χ.symm) (χ q) = ψ (F q) := by
    simp only [Function.comp_apply, χ.left_inv (hχsrc q hqs)]
  have hGq' : (ψ ∘ F ∘ χ.symm) (χ q') = ψ (F q') := by
    simp only [Function.comp_apply, χ.left_inv (hχsrc q' hqs')]
  -- the three estimates
  have e1 : dist (F q) (F q') ≤ 2 * C₂ * ‖ψ (F q) - ψ (F q')‖ := by
    have h := hsymm _ hq2 _ hq2'
    rw [ψ.left_inv hq3, ψ.left_inv hq3'] at h
    refine h.trans ?_
    have := DifferentialGeometry.Geometry.Collapse.finiteMetricSeminormAt_le_mul_norm g y₀
      (ψ (F q) - ψ (F q'))
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left this (by norm_num)
  have e2 : ‖ψ (F q) - ψ (F q')‖ ≤ K₁ * ‖χ q - χ q'‖ := by
    have h := hlip.dist_le_mul _ hq1 _ hq1'
    rw [hGq, hGq', dist_eq_norm, dist_eq_norm] at h
    exact h
  have e3 : ‖χ q - χ q'‖ ≤ max 1 (2 / c₀) * dist q q' := by
    rw [hχapp, hχapp, Prod.norm_def, Prod.dist_eq]
    simp only [Prod.fst_sub, Prod.snd_sub, Real.norm_eq_abs]
    have hφd : ‖φ q.2 - φ q'.2‖ ≤ 2 / c₀ * dist q.2 q'.2 := by
      have h := hchart q'.2 hq4' q.2 hq4
      have h' := (hc₀N (φ q.2 - φ q'.2)).trans h
      rw [dist_comm] at h'
      rw [div_mul_eq_mul_div, le_div_iff₀ hc₀]
      linarith
    have hm1 : |q.1 - q'.1| ≤ max 1 (2 / c₀) * max (dist q.1 q'.1) (dist q.2 q'.2) := by
      rw [← Real.dist_eq]
      calc dist q.1 q'.1 ≤ max (dist q.1 q'.1) (dist q.2 q'.2) := le_max_left _ _
        _ = 1 * max (dist q.1 q'.1) (dist q.2 q'.2) := (one_mul _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    have hm2 : ‖φ q.2 - φ q'.2‖ ≤ max 1 (2 / c₀) * max (dist q.1 q'.1) (dist q.2 q'.2) :=
      hφd.trans (mul_le_mul (le_max_right _ _) (le_max_right _ _) dist_nonneg (by positivity))
    exact max_le hm1 hm2
  calc dist (F q) (F q') ≤ 2 * C₂ * ‖ψ (F q) - ψ (F q')‖ := e1
    _ ≤ 2 * C₂ * (K₁ * ‖χ q - χ q'‖) := mul_le_mul_of_nonneg_left e2 (by positivity)
    _ ≤ 2 * C₂ * (K₁ * (max 1 (2 / c₀) * dist q q')) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left e3 K₁.coe_nonneg) (by positivity)
    _ = K * dist q q' := by
        rw [hK]; change _ = (2 * C₂ * K₁ * max 1 (2 / c₀)) * dist q q'; ring

/-- **S-HIT binding with Lipschitz control**: for the flow of a `C¹` field along which `d_S` grows
at rate `κ > 0` on orbit segments in an open `U ⊇ {a ≤ d_S ≤ b}`, the hitting time is locally
Lipschitz on `{a ≤ d_S ≤ b} × [a, b]`. -/
theorem locallyLipschitzOn_infDist_hittingTime [NeZero (Module.finrank ℝ E)] [CompleteSpace M]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (S : Set M) {Φ : ℝ → M → M} (hΦ : ContMDiff (𝓘(ℝ, ℝ).prod I) I 1 (fun q : ℝ × M => Φ q.1 q.2))
    (hΦ0 : ∀ x, Φ 0 x = x) (hΦadd : ∀ s t x, Φ (s + t) x = Φ s (Φ t x)) {U : Set M}
    (hU : IsOpen U) {a b κ : ℝ} (hκ : 0 < κ) (hbandU : (fun x => infDist x S) ⁻¹' Icc a b ⊆ U)
    (hrate : ∀ x t, 0 ≤ t → (∀ s ∈ Icc 0 t, Φ s x ∈ U) →
      infDist x S + κ * t ≤ infDist (Φ t x) S) :
    LocallyLipschitzOn (((fun x => infDist x S) ⁻¹' Icc a b) ×ˢ Icc a b)
      (fun p : M × ℝ => hittingTime Φ (fun x => infDist x S) p.1 p.2) :=
  locallyLipschitzOn_hittingTime hΦ.continuous hΦ0 hΦadd (continuous_infDist_pt S) hU hκ hbandU
    hrate (lipschitz_infDist_pt S).locallyLipschitz
    (locallyLipschitz_of_contMDiff_prod_finite g hr hnorm hΦ)

/-- **Consumer (LFR23)**: for the SAME field and flow as `exists_endpoint_band_field`, the hitting
time of the band is locally Lipschitz, and over every locally Lipschitz transversal into the band
the level `{d_S = s}` is the graph of a locally Lipschitz function in flow coordinates. -/
theorem exists_endpoint_band_field_lipschitz [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M]
    [CompleteSpace M]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {S A : Set M} (hS : IsClosed S) (hSne : S.Nonempty) (hA : IsClosed A) {a b c : ℝ}
    (ha : 0 < a) (hc : c ∈ Icc a b) (hbandA : (fun x => infDist x S) ⁻¹' Icc a b ⊆ A)
    (w : (x : M) → TangentSpace I x) (hwunit : ∀ x ∈ A, g.inner x (w x) (w x) = 1)
    (hwout : ∀ x ∈ A, ∀ u ∈ g.finiteMinimizingDirectionsTo S x, g.inner x (w x) u < -(7 / 8)) :
    ∃ V : (x : M) → TangentSpace I x,
      ContMDiff I I.tangent ∞ (fun x => (⟨x, V x⟩ : TangentBundle I M)) ∧
      (∀ x, g.inner x (V x) (V x) < 2 ^ 2) ∧
      ∃ Φ : ℝ → M → M,
        (∀ t x, HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s => Φ s x) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight (V (Φ t x)))) ∧
        LocallyLipschitzOn (((fun x => infDist x S) ⁻¹' Icc a b) ×ˢ Icc a b)
          (fun p : M × ℝ => hittingTime Φ (fun x => infDist x S) p.1 p.2) ∧
        (∀ {W : Type*} [MetricSpace W] {σ : W → M}, LocallyLipschitz σ →
          (∀ w, infDist (σ w) S ∈ Icc a b) → ∀ s ∈ Icc a b,
            LocallyLipschitz (fun w => hittingTime Φ (fun x => infDist x S) (σ w) s)) ∧
        ∃ e : ({x : M // infDist x S = c} × Icc a b) ≃ₜ {x : M // infDist x S ∈ Icc a b},
          ∀ p, (e p : M) = Φ (hittingTime Φ (fun x => infDist x S) p.1 p.2) p.1 := by
  obtain ⟨V, hV, hVR, O, hO, hAO, -, Φ, hΦ, hΦ0, hΦadd, hder, hrate, -, -, e, he1, -⟩ :=
    exists_endpoint_band_field g hr hnorm hS hSne hA ha hc hbandA w hwunit hwout
  have hbandU : (fun x => infDist x S) ⁻¹' Icc a b ⊆ O ∩ Sᶜ := fun x hx =>
    ⟨hAO (hbandA hx), fun hxS => by
      have h0 : infDist x S = 0 := infDist_zero_of_mem hxS
      have : a ≤ infDist x S := hx.1
      linarith⟩
  have hΦ1 : ContMDiff (𝓘(ℝ, ℝ).prod I) I 1 (fun q : ℝ × M => Φ q.1 q.2) :=
    hΦ.of_le (by exact_mod_cast le_top)
  have hUo : IsOpen (O ∩ Sᶜ) := hO.inter hS.isOpen_compl
  refine ⟨V, hV, hVR, Φ, hder,
    locallyLipschitzOn_infDist_hittingTime g hr hnorm S hΦ1 hΦ0 hΦadd hUo (by norm_num) hbandU hrate,
    fun hσ hσband s hs => locallyLipschitz_hittingTime_comp hΦ.continuous hΦ0 hΦadd
      (continuous_infDist_pt S) hUo (by norm_num) hbandU hrate
      (lipschitz_infDist_pt S).locallyLipschitz
      (locallyLipschitz_of_contMDiff_prod_finite g hr hnorm hΦ1) hσ hσband hs,
    e, he1⟩

end DifferentialGeometry.Geometry.FiniteSoul
