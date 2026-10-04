import DifferentialGeometry.Geometry.Collapse.DistanceSmoothing.RadialFunctionAtScale
import DifferentialGeometry.Geometry.Collapse.RadialAnnularCutoff
import DifferentialGeometry.Geometry.Comparison.SectionalLowerBound

/-!
# LC57, items (1)–(2): one scale, one tail, the cone map and the selected radial function

Master207A, A:23106 (LC57), first two items, for either model branch. The data are LC56's items
(1), (3), (4) (unbundled): pointed Gromov–Hausdorff convergence `(M_i, p_i) → (N, n)` of the
Riemannian sources, a supplied LC21 cone package `(C, o)` of `(N, n)` (radial cone data and actual
Kleiner–Lott maps of `(N, R⁻¹ d, n)` at every large scale), and the separate curvature bounds
`sec_{g_i} ≥ -H_i⁻²` on `B(p_i, H_i)` with `H_i → ∞`.

The conclusion is the blueprint's quantifier order with the scale chosen ONCE: there is `R₀` such
that for EVERY fixed `R ≥ R₀` one tail carries, at the metric scale `R⁻² g_i`,
1. an actual pointed Kleiner–Lott `δ`-map to the SAME `(C, o)` (LC22), and
2. a selected LC30 function `η_i` (value error `e`, Lipschitz-difference error `ε`, all of LC30's
   clauses) together with LC31's smooth compactly supported cutoff `Φ ∘ η_i` and its bounds.
Any further lower threshold on `R` demanded by a model branch (LC43's diameter condition for a
compact model, LC55's threshold for a noncompact one) is met by choosing `R` above it.

* `exists_radial_cutoff_of_band`: LC31's cutoff from LC30's band clauses (no Riemannian-bundle
  instance needed, so it applies verbatim at the rescaled metric).
* `exists_scale_eventually_cone_radial_witnesses`: LC57 (1)–(2).
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Real Filter
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Analysis.Calculus
open GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

/-- **LC31 from LC30's band clauses.** A continuous `F` with `|F - d_p| < e`, smooth on an open set
containing `F⁻¹[1/5, 2]`, whose band lies in the shell `1/10 ≤ d_p ≤ 10` where `‖∇F‖ ≤ 1 + ε`, has
the LC31 cutoff `Φ ∘ F` (standard profile): smooth, `[0, 1]`-valued, one on `F⁻¹[3/10, 4/5]`,
topologically supported in `{1/5 - e < d_p < 9/10 + e}`, `‖∇(Φ ∘ F)‖ ≤ L (1 + ε)`. -/
theorem exists_radial_cutoff_of_band {M : Type*} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] (g : SmoothRiemannianMetric I M) (p : M) {F : M → ℝ} {ε e : ℝ}
    (hε : 0 ≤ ε) (hFc : Continuous F) (hclose : ∀ x, |F x - Metric.infDist x {p}| < e)
    (hgrad : ∀ q ∈ {x : M | 1 / 10 ≤ dist x p ∧ dist x p ≤ 10},
      Real.sqrt (g.inner q (gradFun g F q) (gradFun g F q)) ≤ 1 + ε)
    (hsub : F ⁻¹' Icc (1 / 5 : ℝ) 2 ⊆ {x : M | 1 / 10 ≤ dist x p ∧ dist x p ≤ 10})
    {O' : Set M} (hO' : IsOpen O') (hband : F ⁻¹' Icc (1 / 5 : ℝ) 2 ⊆ O')
    (hFO' : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ F O') :
    ∃ L : ℝ, 0 ≤ L ∧ (∀ t, |deriv (annularCutoff cutoffProfile) t| ≤ L) ∧
      ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x => annularCutoff cutoffProfile (F x)) ∧
      (∀ x, annularCutoff cutoffProfile (F x) ∈ Icc (0 : ℝ) 1) ∧
      (∀ x, F x ∈ Icc (3 / 10 : ℝ) (4 / 5) → annularCutoff cutoffProfile (F x) = 1) ∧
      tsupport (fun x => annularCutoff cutoffProfile (F x)) ⊆
        {x : M | 1 / 5 - e < dist x p ∧ dist x p < 9 / 10 + e} ∧
      ∀ q, Real.sqrt (g.inner q (gradFun g (fun x => annularCutoff cutoffProfile (F x)) q)
        (gradFun g (fun x => annularCutoff cutoffProfile (F x)) q)) ≤ L * (1 + ε) := by
  obtain ⟨L, hL0, hL⟩ := exists_abs_deriv_annularCutoff_le cutoffProfile_contDiff
    fun _ ht => cutoffProfile_eq_zero ht
  have hclose' : ∀ x, |F x - dist x p| < e := fun x => by
    simpa only [Metric.infDist_singleton] using hclose x
  have hsmall : F ⁻¹' Icc (1 / 5 : ℝ) (9 / 10) ⊆ F ⁻¹' Icc (1 / 5 : ℝ) 2 :=
    fun x hx => ⟨hx.1, hx.2.trans (by norm_num)⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := annularCutoff_comp_radial cutoffProfile_contDiff
    cutoffProfile_mem_Icc (fun _ ht => cutoffProfile_eq_one ht)
    (fun _ ht => cutoffProfile_eq_zero ht) g p hε hFc hO' hFO' (hsmall.trans hband) hclose'
    (fun q hq => hgrad q (hsub (hsmall hq))) hL
  exact ⟨L, hL0, hL, h1, h2, h3, h4, h5⟩

variable [NeZero (Module.finrank ℝ E)] [I.Boundaryless]

/-- **LC57, items (1)–(2)** (master207A, A:23106), either model branch. From LC56's items (1),
(3), (4): there is `R₀ > 0` such that for EVERY `R ≥ R₀` one tail has, at the metric scale
`R⁻² g_i` (the metric rescaling `R⁻¹ d_i`, which realizes it), an actual pointed Kleiner–Lott
`δ`-map to the same `(C, o)`, and a selected LC30 function `η_i` with all of LC30's clauses (value
error `e`, Lipschitz-difference error `ε`) and LC31's cutoff `Φ ∘ η_i` with its bounds. -/
theorem exists_scale_eventually_cone_radial_witnesses
    {M : ℕ → Type*} [mM : ∀ i, MetricSpace (M i)] [∀ i, ChartedSpace H (M i)]
    [∀ i, IsManifold I ∞ (M i)] [∀ i, SigmaCompactSpace (M i)] [∀ i, CompleteSpace (M i)]
    (g : ∀ i, SmoothRiemannianMetric I (M i))
    (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
    {N : Type*} [mN : MetricSpace N] {p : ∀ i, M i} {n : N} (hGH : PointedGHConverges p n)
    {C : Type*} [MetricSpace C] {o : C} (Hc : RadialConeData o)
    (hcone : ∀ τ : ℝ, 0 < τ → τ < 1 → ∃ R₀ : ℝ, ∀ R : ℝ, ∀ hR : 0 < R, R₀ ≤ R →
      Nonempty (@KleinerLottApprox N C (mN.rescale R⁻¹ (inv_pos.mpr hR)) _ n o τ))
    (Hb : ℕ → ℝ) (hHb : Tendsto Hb atTop atTop)
    (hsec : ∀ i, ∀ y ∈ Metric.ball (p i) (Hb i),
      SectionalBoundedBelowAt (g i) y (-((Hb i)⁻¹ ^ 2)))
    {δ ε e : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (hε : 0 < ε) (hε1 : ε < 1) (he : 0 < e)
    (he1 : e < 1 / 40) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, ∀ hR : 0 < R, R₀ ≤ R → ∀ᶠ i in atTop,
      Nonempty (@KleinerLottApprox (M i) C ((mM i).rescale R⁻¹ (inv_pos.mpr hR)) _ (p i) o δ) ∧
      (letI := (mM i).rescale R⁻¹ (inv_pos.mpr hR)
      let gR := scaleMetric (R⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2) (g i)
      ∃ F : M i → ℝ, LipschitzWith (Real.toNNReal (1 + ε)) F ∧
        (∃ O : Set (M i), IsOpen O ∧ {x : M i | 1 / 10 ≤ dist x (p i) ∧ dist x (p i) ≤ 10} ⊆ O ∧
          ContMDiffOn I 𝓘(ℝ, ℝ) ∞ F O) ∧
        (∀ x, |F x - Metric.infDist x {p i}| < e) ∧
        (∀ x, x ∉ {x : M i | 1 / 20 < dist x (p i) ∧ dist x (p i) < 20} →
          F x = Metric.infDist x {p i}) ∧
        (∀ x y, |(F x - Metric.infDist x {p i}) - (F y - Metric.infDist y {p i})| ≤
          ε * dist x y) ∧
        (∀ x, 0 ≤ F x) ∧ F (p i) = 0 ∧
        (∀ q ∈ {x : M i | 1 / 10 ≤ dist x (p i) ∧ dist x (p i) ≤ 10},
          1 - ε ≤ Real.sqrt (gR.inner q (gradFun gR F q) (gradFun gR F q)) ∧
            Real.sqrt (gR.inner q (gradFun gR F q) (gradFun gR F q)) ≤ 1 + ε) ∧
        (∀ x, F x ∈ Icc (1 / 5 : ℝ) 2 → 1 / 5 - e < dist x (p i) ∧ dist x (p i) < 2 + e) ∧
        F ⁻¹' Icc (1 / 5 : ℝ) 2 ⊆ {x : M i | 1 / 10 ≤ dist x (p i) ∧ dist x (p i) ≤ 10} ∧
        (∃ O' : Set (M i), IsOpen O' ∧ F ⁻¹' Icc (1 / 5 : ℝ) 2 ⊆ O' ∧
          ContMDiffOn I 𝓘(ℝ, ℝ) ∞ F O' ∧ ∀ q ∈ O', gradFun gR F q ≠ 0) ∧
        ∃ L : ℝ, 0 ≤ L ∧ (∀ t, |deriv (annularCutoff cutoffProfile) t| ≤ L) ∧
          ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x => annularCutoff cutoffProfile (F x)) ∧
          (∀ x, annularCutoff cutoffProfile (F x) ∈ Icc (0 : ℝ) 1) ∧
          (∀ x, F x ∈ Icc (3 / 10 : ℝ) (4 / 5) → annularCutoff cutoffProfile (F x) = 1) ∧
          tsupport (fun x => annularCutoff cutoffProfile (F x)) ⊆
            {x : M i | 1 / 5 - e < dist x (p i) ∧ dist x (p i) < 9 / 10 + e} ∧
          ∀ q, Real.sqrt (gR.inner q (gradFun gR (fun x => annularCutoff cutoffProfile (F x)) q)
            (gradFun gR (fun x => annularCutoff cutoffProfile (F x)) q)) ≤ L * (1 + ε)) := by
  -- the LC30 cone threshold, halved
  set δ₂ : ℝ := radialSmoothingConeError (ε / 4) / 2 with hδ₂def
  have hrs : 0 < radialSmoothingConeError (ε / 4) := radialSmoothingConeError_pos (by positivity)
  have hrs1 : radialSmoothingConeError (ε / 4) ≤ 1 / 600 := min_le_left _ _
  have hδ₂0 : 0 < δ₂ := by positivity
  have hδ₂1 : δ₂ < 1 := by linarith
  have hδ₂r : δ₂ < radialSmoothingConeError (ε / 4) := by linarith
  -- the LC22 tolerance attached to a target error `d`
  have hτ (d : ℝ) (hd : 0 < d) (hd1 : d < 1) :
      0 < min (d / 100) (1 / (2 * (2 * (d⁻¹ + d) + 4))) ∧
        min (d / 100) (1 / (2 * (2 * (d⁻¹ + d) + 4))) < 1 :=
    ⟨lt_min (by positivity) (by positivity),
      lt_of_le_of_lt (min_le_left _ _) (by linarith)⟩
  obtain ⟨R₁, hR₁⟩ := hcone _ (hτ δ hδ hδ1).1 (hτ δ hδ hδ1).2
  obtain ⟨R₂, hR₂⟩ := hcone _ (hτ δ₂ hδ₂0 hδ₂1).1 (hτ δ₂ hδ₂0 hδ₂1).2
  refine ⟨max (max R₁ R₂) 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun R hR hRR => ?_⟩
  have hR₁R : R₁ ≤ R := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hRR)
  have hR₂R : R₂ ≤ R := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hRR)
  have h1 := eventually_riemannian_rescaled_approx_fixed_target g hmetric hGH R hR hδ hδ1
    (hR₁ R hR hR₁R).some
  have h2 := eventually_riemannian_rescaled_approx_fixed_target g hmetric hGH R hR hδ₂0 hδ₂1
    (hR₂ R hR hR₂R).some
  filter_upwards [h1, h2, hHb.eventually_ge_atTop (400 * R)] with i hi1 hi2 hiH
  refine ⟨hi1.2, ?_⟩
  obtain ⟨φ⟩ := hi2.2
  -- the curvature buffer at scale `R`: `H_i ≥ 400 R`
  have hsecR : ∀ y ∈ Metric.ball (p i) (400 * R),
      SectionalBoundedBelowAt (g i) y (-((1 / 60) ^ 2 * R⁻¹ ^ 2)) := by
    intro y hy
    have h60 : 60 * R ≤ Hb i := by linarith
    have h60R : 0 < 60 * R := by positivity
    have hinv : (Hb i)⁻¹ ≤ (60 * R)⁻¹ := inv_anti₀ h60R h60
    have hsq : (Hb i)⁻¹ ^ 2 ≤ (60 * R)⁻¹ ^ 2 :=
      pow_le_pow_left₀ (inv_nonneg.mpr (h60R.le.trans h60)) hinv 2
    refine (hsec i y (Metric.ball_subset_ball (by linarith) hy)).mono ?_
    have hid : (60 * R)⁻¹ ^ 2 = (1 / 60) ^ 2 * R⁻¹ ^ 2 := by
      rw [mul_inv, ← mul_pow, one_div]
    linarith
  obtain ⟨F, hFlip, hFO, hclose, hout, hdiff, hnn, hp0, hgrad, hrng, hsub, O', hO', hband, hFO',
      hne⟩ :=
    exists_radialFunction_of_kleinerLottApprox_at_scale (g i) (hmetric i) hR φ Hc hsecR hε hε1
      hδ₂r he he1
  let := (mM i).rescale R⁻¹ (inv_pos.mpr hR)
  obtain ⟨L, hL0, hL, hc1, hc2, hc3, hc4, hc5⟩ :=
    exists_radial_cutoff_of_band (scaleMetric (R⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2) (g i))
      (p i) hε.le hFlip.continuous hclose (fun q hq => (hgrad q hq).2) hsub hO' hband hFO'
  exact ⟨F, hFlip, hFO, hclose, hout, hdiff, hnn, hp0, hgrad, hrng, hsub,
    ⟨O', hO', hband, hFO', hne⟩, L, hL0, hL, hc1, hc2, hc3, hc4, hc5⟩

end DifferentialGeometry.Geometry.Collapse
