import DifferentialGeometry.Geometry.Collapse.EdgeModelDirectionTransfer

/-!
# (LFR28.4): the source edge coordinate pulled back is close to the model smoothing (kernel)

Blueprint LFR28 step 2, second half (master207A:27351–27363), modulo LFR14 data, a metric product
structure `Φ`, and the two gradient estimates that LFR27 and LFR02 supply as theorems:

* source: `|dF_i(w) + g_i(v_i, w)| ≤ ε_S |w|_{g_i}` for EVERY nearest-set direction `v_i` of `A_i`
  (LFR27.1, with the quotient error `150ΔΛ` of `η = F/ρ` absorbed in `ε_S`);
* model: `|dG_N(X) + G(v, X)| ≤ ε_N |X|_G` for EVERY radial inward direction `v` (LFR02 on `N`,
  `exists_localized_distance_smoothing_lfr02`).

Results:

* `exists_mem_finiteMinimizingDirectionsTo_of_riemannianEDistOf`: nearest-set directions exist on the
  approximants (closed nonempty sets, T0's convention);
* `eventually_abs_pullback_inner_sub_le_of_isCompact`: the two-sided bilinear comparison
  `|g_i(d j a, d j b) - G(a, b)| ≤ ρ |a|_G |b|_G` eventually, uniformly on compact sets;
* `eventually_abs_mvfderiv_comp_sub_model_le` (**LFR28.4 kernel**): on LFR26's collar, for every
  `c > 40 √(h + τ)` and `ε > 0`, eventually `‖d(F_i ∘ j_i) - dG_N‖_G ≤ ε_S + ε_N + c + ε`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Riemannian.Geodesic

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.MetricSmoothing

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

section Source

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M' : Type*} [MetricSpace M'] [ChartedSpace H M'] [IsManifold I ∞ M'] [CompleteSpace M']

/-- A complete smooth metric carrying the distance of `M'` (T0's convention) has a nearest-set
direction at every point, for every closed nonempty set. -/
theorem exists_mem_finiteMinimizingDirectionsTo_of_riemannianEDistOf
    (g : SmoothRiemannianMetric I M')
    (hmetric : ∀ a b : M', riemannianEDistOf g a b = ENNReal.ofReal (dist a b)) {S : Set M'}
    (hS : IsClosed S) (hSne : S.Nonempty) (x : M') :
    ∃ w : TangentSpace I x, w ∈ ContMDiffRiemannianMetric.finiteMinimizingDirectionsTo g S x := by
  let hRB : RiemannianBundle (fun z : M' => TangentSpace I z) := ⟨g.toRiemannianMetric⟩
  have hRM : IsRiemannianManifold I M' := ⟨fun a b => by
    change edist a b = riemannianEDistOf g a b
    rw [edist_dist, hmetric]⟩
  exact (@ContMDiffRiemannianMetric.finiteMinimizingDirectionsTo_nonempty_isCompact _ _ _ _ _ _ _ _
    _ _ _ _ _ hRB hRM ⊤ _ g le_top (isMetricNorm_of_riemannianBundle g) _ hS hSne x).1

end Source

section Comparison

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {N : Type*} [MetricSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  {M : ℕ → Type*} [∀ i, MetricSpace (M i)] [∀ i, ChartedSpace H (M i)]
  [∀ i, IsManifold I ∞ (M i)]

/-- **Two-sided bilinear comparison on compact sets.** For LFR14-shaped data (exhaustion and `C⁰`
convergence of the pulled-back chart coefficients), eventually
`|g_i(d j_i a, d j_i b) - G(a, b)| ≤ ρ |a|_G |b|_G` for all `x ∈ C` and `a, b ∈ T_x N`. -/
theorem eventually_abs_pullback_inner_sub_le_of_isCompact {r : ℕ∞} (hr : 1 ≤ r)
    (G : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : N → Type _))
    (g : ∀ i, SmoothRiemannianMetric I (M i)) {K : ℕ} (hK : 1 ≤ K)
    (j : ∀ i, PartialDiffeomorph I I N (M i) K)
    (hexh : ∀ C : Set N, IsCompact C → ∀ᶠ i in atTop, C ⊆ (j i).source)
    (hconv : ∀ (x : N) (L : Set E), IsCompact L → L ⊆ (extChartAt I x).target →
      MapCPConvergenceOn L 1
        (fun i => pullbackMetricCoefficients (g i) ((j i : N → M i) ∘ (extChartAt I x).symm))
        (chartCoeff G x))
    {C : Set N} (hC : IsCompact C) {ρ : ℝ} (hρ : 0 < ρ) :
    ∀ᶠ i in atTop, ∀ x ∈ C, ∀ a b : TangentSpace I x,
      |(g i).inner (j i x) (mfderiv I I (j i : N → M i) x a) (mfderiv I I (j i : N → M i) x b) -
        G.inner x a b| ≤ ρ * Real.sqrt (G.inner x a a) * Real.sqrt (G.inner x b b) := by
  by_contra hbad
  rw [Filter.not_eventually] at hbad
  obtain ⟨ψ, hψ, hψbad⟩ := Filter.extraction_of_frequently_atTop hbad
  simp only [not_forall, not_le, exists_prop] at hψbad
  choose x hxC a b hab using hψbad
  have hpos : ∀ k (z : TangentSpace I (x k)), 0 ≤ G.inner (x k) z z := fun k z =>
    DifferentialGeometry.Geometry.Collapse.finite_inner_self_nonneg G (x k) z
  have hnz : ∀ k (z : TangentSpace I (x k)), G.inner (x k) z z = 0 → z = 0 := fun k z hz => by
    by_contra hne
    exact (G.pos (x k) z hne).ne' hz
  have hapos : ∀ k, 0 < G.inner (x k) (a k) (a k) := fun k => by
    rcases (hpos k (a k)).lt_or_eq with h | h
    · exact h
    · exfalso
      have h0 := hnz k (a k) h.symm
      have h1 := hab k
      simp [h0] at h1
  have hbpos : ∀ k, 0 < G.inner (x k) (b k) (b k) := fun k => by
    rcases (hpos k (b k)).lt_or_eq with h | h
    · exact h
    · exfalso
      have h0 := hnz k (b k) h.symm
      have h1 := hab k
      simp [h0] at h1
  set ca : ℕ → ℝ := fun k => (Real.sqrt (G.inner (x k) (a k) (a k)))⁻¹ with hca
  set cb : ℕ → ℝ := fun k => (Real.sqrt (G.inner (x k) (b k) (b k)))⁻¹ with hcb
  have hca0 : ∀ k, 0 < ca k := fun k => inv_pos.mpr (Real.sqrt_pos.mpr (hapos k))
  have hcb0 : ∀ k, 0 < cb k := fun k => inv_pos.mpr (Real.sqrt_pos.mpr (hbpos k))
  have hcaG : ∀ k, ca k * Real.sqrt (G.inner (x k) (a k) (a k)) = 1 := fun k =>
    inv_mul_cancel₀ (Real.sqrt_pos.mpr (hapos k)).ne'
  have hcbG : ∀ k, cb k * Real.sqrt (G.inner (x k) (b k) (b k)) = 1 := fun k =>
    inv_mul_cancel₀ (Real.sqrt_pos.mpr (hbpos k)).ne'
  set a' : ∀ k, TangentSpace I (x k) := fun k => ca k • a k with ha'
  set b' : ∀ k, TangentSpace I (x k) := fun k => cb k • b k with hb'
  have hsqa : ∀ k, Real.sqrt (G.inner (x k) (a k) (a k)) ^ 2 = G.inner (x k) (a k) (a k) :=
    fun k => Real.sq_sqrt (hpos k _)
  have hsqb : ∀ k, Real.sqrt (G.inner (x k) (b k) (b k)) ^ 2 = G.inner (x k) (b k) (b k) :=
    fun k => Real.sq_sqrt (hpos k _)
  have ha'unit : ∀ k, G.inner (x k) (a' k) (a' k) = 1 := fun k => by
    simp only [ha', map_smul, smul_apply, smul_eq_mul]
    rw [← hsqa k]
    have := hcaG k
    nlinarith
  have hb'unit : ∀ k, G.inner (x k) (b' k) (b' k) = 1 := fun k => by
    simp only [hb', map_smul, smul_apply, smul_eq_mul]
    rw [← hsqb k]
    have := hcbG k
    nlinarith
  have hbad' : ∀ k, ρ < |(g (ψ k)).inner (j (ψ k) (x k))
      (mfderiv I I (j (ψ k) : N → M (ψ k)) (x k) (a' k))
      (mfderiv I I (j (ψ k) : N → M (ψ k)) (x k) (b' k)) - G.inner (x k) (a' k) (b' k)| :=
    fun k => by
    simp only [ha', hb', map_smul, smul_apply, smul_eq_mul]
    have h1 := hab k
    have hc := mul_pos (hca0 k) (hcb0 k)
    have he : cb k * (ca k * (g (ψ k)).inner (j (ψ k) (x k))
        (mfderiv I I (j (ψ k) : N → M (ψ k)) (x k) (a k))
        (mfderiv I I (j (ψ k) : N → M (ψ k)) (x k) (b k))) -
        cb k * (ca k * G.inner (x k) (a k) (b k)) =
        (ca k * cb k) * ((g (ψ k)).inner (j (ψ k) (x k))
          (mfderiv I I (j (ψ k) : N → M (ψ k)) (x k) (a k))
          (mfderiv I I (j (ψ k) : N → M (ψ k)) (x k) (b k)) - G.inner (x k) (a k) (b k)) := by
      ring
    rw [he, abs_mul, abs_of_pos hc]
    calc ρ = (ca k * cb k) * (ρ * Real.sqrt (G.inner (x k) (a k) (a k)) *
          Real.sqrt (G.inner (x k) (b k) (b k))) := by
          have h2 := hcaG k
          have h3 := hcbG k
          calc ρ = ρ * (ca k * Real.sqrt (G.inner (x k) (a k) (a k))) *
                (cb k * Real.sqrt (G.inner (x k) (b k) (b k))) := by rw [h2, h3]; ring
            _ = _ := by ring
      _ < (ca k * cb k) * _ := mul_lt_mul_of_pos_left h1 hc
  obtain ⟨xI, -, φ₁, hφ₁, hx₁⟩ := hC.tendsto_subseq hxC
  obtain ⟨α, φ₂, hφ₂, hαlim⟩ := exists_subseq_tendsto_tangentBundle_of_inner_le hr G hx₁
    (fun k => a' (φ₁ k)) (B := 1) (fun k => (ha'unit _).le)
  have hx₂ : Tendsto (fun k => x (φ₁ (φ₂ k))) atTop (𝓝 xI) := hx₁.comp hφ₂.tendsto_atTop
  obtain ⟨β, φ₃, hφ₃, hβlim⟩ := exists_subseq_tendsto_tangentBundle_of_inner_le hr G hx₂
    (fun k => b' (φ₁ (φ₂ k))) (B := 1) (fun k => (hb'unit _).le)
  have hαlim' := hαlim.comp hφ₃.tendsto_atTop
  have hσ : Tendsto (fun k => ψ (φ₁ (φ₂ (φ₃ k)))) atTop atTop :=
    (hψ.comp (hφ₁.comp (hφ₂.comp hφ₃))).tendsto_atTop
  have hT3 := tendsto_pullback_inner_of_tendsto hr G g hK j hexh hconv hσ hαlim' hβlim
  have hT2 := tendsto_inner_of_tendsto_tangentBundle hr G hαlim' hβlim
  have hdiff := (hT3.sub hT2).abs
  rw [sub_self, abs_zero] at hdiff
  obtain ⟨k, hk⟩ := (hdiff.eventually (gt_mem_nhds hρ)).exists
  exact absurd (hbad' (φ₁ (φ₂ (φ₃ k)))) (not_lt.mpr hk.le)

end Comparison

section Numerics

/-- If `|1 - a| ≤ ρ (√a)²` with `0 ≤ a` and `ρ ≤ 1/2`, then `√a ≤ 2`. -/
theorem sqrt_le_two_of_abs_one_sub_le {a ρ : ℝ} (ha : 0 ≤ a) (hρ : ρ ≤ 1 / 2)
    (h : |1 - a| ≤ ρ * Real.sqrt a * Real.sqrt a) : Real.sqrt a ≤ 2 := by
  have hsa : Real.sqrt a * Real.sqrt a = a := Real.mul_self_sqrt ha
  have h1 := (abs_le.mp h).1
  rw [Real.sqrt_le_iff]
  refine ⟨by norm_num, ?_⟩
  nlinarith

/-- If `|b - a| ≤ ρ (√a)²` with `0 ≤ a` and `0 ≤ ρ`, then `√b ≤ (1 + ρ) √a`. -/
theorem sqrt_le_one_add_mul_of_abs_sub_le {a b ρ : ℝ} (ha : 0 ≤ a) (hρ : 0 ≤ ρ)
    (h : |b - a| ≤ ρ * Real.sqrt a * Real.sqrt a) : Real.sqrt b ≤ (1 + ρ) * Real.sqrt a := by
  have hsa : Real.sqrt a * Real.sqrt a = a := Real.mul_self_sqrt ha
  have h1 := (abs_le.mp h).2
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  nlinarith [Real.sqrt_nonneg a]

/-- Numerical assembly of (LFR28.4). -/
theorem abs_sub_le_of_gradient_bounds {dF gv Gu Gv dG s J U εS εN c ρ ε : ℝ}
    (h1 : |dF + gv| ≤ εS * J) (h2 : |gv - Gu| ≤ ρ * U * s) (h3 : |dG + Gv| ≤ εN * s)
    (h4 : |Gu - Gv| ≤ c * s) (hJ : J ≤ (1 + ρ) * s) (hU : U ≤ 2) (hs : 0 ≤ s) (hρ : 0 ≤ ρ)
    (hεS : 0 ≤ εS) (hρε : ρ * (2 + εS) ≤ ε / 2) (hε : 0 < ε) :
    |dF - dG| ≤ (εS + εN + c + ε) * s := by
  have hb1 : εS * J ≤ εS * ((1 + ρ) * s) := mul_le_mul_of_nonneg_left hJ hεS
  have hb2 : ρ * U * s ≤ ρ * 2 * s :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hU hρ) hs
  have hb3 : ρ * (2 + εS) * s ≤ ε / 2 * s := mul_le_mul_of_nonneg_right hρε hs
  have he : dF - dG = (dF + gv) - (gv - Gu) - (Gu - Gv) - (dG + Gv) := by ring
  rw [he]
  have h1' := abs_le.mp h1
  have h2' := abs_le.mp h2
  have h3' := abs_le.mp h3
  have h4' := abs_le.mp h4
  have hεs : 0 ≤ ε / 2 * s := by positivity
  rw [abs_le]
  constructor <;> nlinarith

end Numerics

section Row

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {N : Type*} [MetricSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  {M : ℕ → Type*} [∀ i, MetricSpace (M i)] [∀ i, ChartedSpace H (M i)]
  [∀ i, IsManifold I ∞ (M i)]
  [ProperSpace N] [RiemannianBundle (fun x : N => TangentSpace I x)] [IsRiemannianManifold I N]

/-- **(LFR28.4) kernel.** Under LFR26's hypotheses (with the sets `A i` closed), source functions
`F i` differentiable along `j i` of the collar with LFR27's gradient estimate
`|dF_i(w) + g_i(v_i, w)| ≤ ε_S |w|` for every nearest-set direction `v_i`, and a model function `G_N`
with LFR02's gradient estimate `|dG_N(X) + G(v, X)| ≤ ε_N |X|` for every radial inward direction `v`:
for every `c > 40 √(h + τ)` and `ε > 0`, eventually on the collar
`|d(F_i ∘ j_i)(X) - dG_N(X)| ≤ (ε_S + ε_N + c + ε) |X|_G`. -/
theorem eventually_abs_mvfderiv_comp_sub_model_le [∀ i, CompleteSpace (M i)]
    [CompleteSpace N] {r : ℕ∞} (hr : 2 ≤ r)
    (G : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : N → Type _))
    (hGnorm : ∀ (x : N) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (G.inner x w w)))
    (hGsec : ∀ (y : N) (w₁ w₂ : TangentSpace I y), 0 ≤ G.sectionalCurvature y w₁ w₂)
    (g : ∀ i, SmoothRiemannianMetric I (M i))
    (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
    {K : ℕ} (hK : 2 ≤ K) (q : N) (j : ∀ i, PartialDiffeomorph I I N (M i) K)
    (hexh : ∀ C : Set N, IsCompact C → ∀ᶠ i in atTop, C ⊆ (j i).source)
    (hconv : ∀ (x : N) (L : Set E), IsCompact L → L ⊆ (extChartAt I x).target →
      MapCPConvergenceOn L 1
        (fun i => pullbackMetricCoefficients (g i) ((j i : N → M i) ∘ (extChartAt I x).symm))
        (chartCoeff G x))
    (hdist : ∀ R ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ x ∈ ball q R, ∀ y ∈ ball q R,
      |dist (j i x) (j i y) - dist x y| < ε)
    (hcover : ∀ a b : ℝ, 0 < a → a < b → ∀ᶠ i in atTop,
      ball (j i q) a ⊆ (j i : N → M i) '' ball q b)
    {W : Type*} [MetricSpace W] (Φ : N ≃ᵢ WithLp 2 (ℝ × W)) {z₀ : W}
    (hΦq : Φ q = WithLp.toLp 2 ((0 : ℝ), z₀))
    {Δ τ k h : ℝ} (hΔ : 0 < Δ) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) (hk : 0 < k) (hkΔ : k * Δ ≤ 1 / 100)
    (hh : 0 < h) (hh1 : h < 1 / 100)
    (Q : ∀ i, M i → WithLp 2 (ℝ × ℝ)) (A : ∀ i, Set (M i))
    (hQp : ∀ i, Q i (j i q) = 0)
    (hQdist : ∀ i, ∀ x ∈ ball (j i q) (200 * Δ), ∀ y ∈ ball (j i q) (200 * Δ),
      |dist (Q i x) (Q i y) - dist x y| ≤ τ * Δ)
    (hheight : ∀ i, ∀ x ∈ ball (j i q) (200 * Δ), 0 ≤ (Q i x).snd)
    (hQcover : ∀ i, ∀ z : WithLp 2 (ℝ × ℝ), |z.fst| ≤ 100 * Δ → z.snd ∈ Icc 0 (100 * Δ) →
      ∃ x ∈ ball (j i q) (200 * Δ), dist (Q i x) z ≤ τ * Δ)
    (hpA : ∀ i, j i q ∈ A i)
    (hborder : ∀ i, ∀ a ∈ A i ∩ ball (j i q) (190 * Δ), (Q i a).snd ≤ τ * Δ)
    (hbordercover : ∀ i, ∀ t : ℝ, |t| ≤ 100 * Δ →
      ∃ a ∈ A i ∩ ball (j i q) (190 * Δ), dist (Q i a) (WithLp.toLp 2 (t, (0 : ℝ))) ≤ τ * Δ)
    (hsec : ∀ i, letI : RiemannianBundle (fun x : M i => TangentSpace I x) :=
        ⟨(g i).toRiemannianMetric⟩
      ∀ z ∈ ball (j i q) (1000 * Δ), DifferentialGeometry.Geometry.Riemannian.SectionalBoundedBelowAt
        (g i) z (-k ^ 2))
    (hhgt : ∀ h' : ℝ, h < h' → ∀ᶠ i in atTop, ∀ x ∈ ball q (100 * Δ),
      |(Q i (j i x)).snd - dist (Φ x).snd z₀| ≤ h' * Δ)
    (hAc : ∀ i, IsClosed (A i)) (F : ∀ i, M i → ℝ) {εS εN : ℝ} (hεS : 0 ≤ εS)
    (hFd : ∀ᶠ i in atTop, ∀ x : N, |(Φ x).fst| ≤ 10 * Δ → 5 / 2 * Δ ≤ dist (Φ x).snd z₀ →
      dist (Φ x).snd z₀ ≤ 13 / 2 * Δ → MDifferentiableAt I 𝓘(ℝ, ℝ) (F i) (j i x))
    (hFgrad : ∀ᶠ i in atTop, ∀ x : N, |(Φ x).fst| ≤ 10 * Δ → 5 / 2 * Δ ≤ dist (Φ x).snd z₀ →
      dist (Φ x).snd z₀ ≤ 13 / 2 * Δ →
      ∀ v ∈ ContMDiffRiemannianMetric.finiteMinimizingDirectionsTo (g i) (A i) (j i x),
      ∀ w : TangentSpace I (j i x),
        |mvfderiv I (F i) (j i x) w + (g i).inner (j i x) v w| ≤
          εS * Real.sqrt ((g i).inner (j i x) w w))
    (GN : N → ℝ)
    (hGgrad : ∀ x : N, |(Φ x).fst| ≤ 10 * Δ → 5 / 2 * Δ ≤ dist (Φ x).snd z₀ →
      dist (Φ x).snd z₀ ≤ 13 / 2 * Δ →
      ∀ v ∈ G.finiteMinimizingDirectionsTo (Φ ⁻¹' {z | z.snd = z₀}) x, ∀ X : TangentSpace I x,
        |mvfderiv I GN x X + G.inner x v X| ≤ εN * Real.sqrt (G.inner x X X)) :
    ∀ c : ℝ, 40 * Real.sqrt (h + τ) < c → ∀ ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ x : N,
      |(Φ x).fst| ≤ 10 * Δ → 5 / 2 * Δ ≤ dist (Φ x).snd z₀ → dist (Φ x).snd z₀ ≤ 13 / 2 * Δ →
      ∀ X : TangentSpace I x,
        |mvfderiv I (fun y => F i (j i y)) x X - mvfderiv I GN x X| ≤
          (εS + εN + c + ε) * Real.sqrt (G.inner x X X) := by
  intro c hc ε hε
  have hr1 : 1 ≤ r := one_le_two.trans hr
  have hK1 : 1 ≤ K := by omega
  set ρ : ℝ := min (1 / 2) (ε / (2 * (2 + εS))) with hρdef
  have hρ0 : 0 < ρ := lt_min (by norm_num) (by positivity)
  have hρ1 : ρ ≤ 1 / 2 := min_le_left _ _
  have hρε : ρ * (2 + εS) ≤ ε / 2 := by
    have h1 : ρ ≤ ε / (2 * (2 + εS)) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at h1
    linarith
  have hC17 : IsCompact (closedBall q (17 * Δ)) := isCompact_closedBall q _
  have h26 := eventually_inverse_nearest_directions_close_radial hr G hGnorm hGsec g hmetric hK q j
    hexh hconv hdist hcover Φ hΦq hΔ hτ hτ1 hk hkΔ hh hh1 Q A hQp hQdist hheight hQcover hpA
    hborder hbordercover hsec hhgt c hc
  have hcmp := eventually_abs_pullback_inner_sub_le_of_isCompact hr1 G g hK1 j hexh hconv hC17 hρ0
  filter_upwards [h26, hcmp, hFd, hFgrad, hexh _ hC17] with i h26i hcmpi hFdi hFgi hsrci
  intro x ht hr1x hr2x X
  have hxC : x ∈ closedBall q (17 * Δ) := by
    rw [mem_closedBall]
    have := dist_le_abs_fst_add_axisDist Φ hΦq x
    linarith
  obtain ⟨vi, hvi⟩ := exists_mem_finiteMinimizingDirectionsTo_of_riemannianEDistOf (g i) (hmetric i)
    (hAc i) ⟨j i q, hpA i⟩ (j i x)
  have hSne : (Φ ⁻¹' {z | z.snd = z₀}).Nonempty := ⟨q, by
    simp only [mem_preimage, mem_ofPred_eq, hΦq, WithLp.toLp_snd]⟩
  obtain ⟨v, hv⟩ := (ContMDiffRiemannianMetric.finiteMinimizingDirectionsTo_nonempty_isCompact G hr
    hGnorm (isClosed_axis Φ z₀) hSne x).1
  set u : TangentSpace I x := mfderiv I I ((j i).symm : M i → N) (j i x) vi with hu
  have hdu : mfderiv I I (j i : N → M i) x u = vi :=
    mfderiv_apply_mfderiv_symm_of_mem_source hK1 (j i) (hsrci hxC) vi
  have h26x : G.inner x (u - v) (u - v) ≤ c ^ 2 := h26i x ht hr1x hr2x vi hvi v hv
  have hK0 : ((K : ℕ) : ℕ∞ω) ≠ 0 := by exact_mod_cast (show K ≠ 0 by omega)
  have hjd : MDifferentiableAt I I (j i : N → M i) x := (j i).mdifferentiableAt hK0 (hsrci hxC)
  have hchain : mvfderiv I (fun y => F i (j i y)) x X =
      mvfderiv I (F i) (j i x) (mfderiv I I (j i : N → M i) x X) :=
    mvfderiv_comp_apply x (hFdi x ht hr1x hr2x) hjd X
  have e1 := hFgi x ht hr1x hr2x vi hvi (mfderiv I I (j i : N → M i) x X)
  rw [← hdu] at e1
  have e2 := hcmpi x hxC u X
  have e2X := hcmpi x hxC X X
  have e2u := hcmpi x hxC u u
  rw [hdu, hvi.1] at e2u
  have e3 := hGgrad x ht hr1x hr2x v hv X
  have hcs := DifferentialGeometry.Geometry.Collapse.abs_finite_inner_le G x (u - v) X
  have hGX := DifferentialGeometry.Geometry.Collapse.finite_inner_self_nonneg G x X
  have hGu := DifferentialGeometry.Geometry.Collapse.finite_inner_self_nonneg G x u
  set s := Real.sqrt (G.inner x X X) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hu2 : Real.sqrt (G.inner x u u) ≤ 2 := sqrt_le_two_of_abs_one_sub_le hGu hρ1 e2u
  have hjX := sqrt_le_one_add_mul_of_abs_sub_le hGX hρ0.le e2X
  -- `|G(u - v, X)| ≤ c |X|_G`
  have hcuv : |G.inner x (u - v) X| ≤ c * s := by
    have hc0 : 0 ≤ c := le_trans (by positivity) hc.le
    have h1 : Real.sqrt (G.inner x (u - v) (u - v)) ≤ c := Real.sqrt_le_iff.mpr ⟨hc0, h26x⟩
    exact hcs.trans (mul_le_mul_of_nonneg_right h1 hs0)
  have hsplit : G.inner x (u - v) X = G.inner x u X - G.inner x v X := by
    simp only [map_sub, sub_apply]
  rw [hsplit] at hcuv
  rw [hchain]
  exact abs_sub_le_of_gradient_bounds e1 e2 e3 hcuv hjX hu2 hs0 hρ0.le hεS hρε hε

end Row

end DifferentialGeometry.Geometry.Riemannian.Geodesic
