import DifferentialGeometry.Geometry.Collapse.SublevelCore.JointWitnessConeRadial
import DifferentialGeometry.Geometry.Collapse.SublevelCore.UniformJointScale
import DifferentialGeometry.Geometry.Metric.Scaling.RescaleComposition
import DifferentialGeometry.Geometry.Collapse.CurvatureScaleBalls

/-!
# LC58 binding, items (1)–(2): a uniformly bounded scale for the cone map and the radial function

Master207A, A:23194 (LC58), for LC57's first two conclusions. The manifolds `M^α` carry prescribed
scales `ρ_α(p) > 0`; LC58's hypothesis "every normalized pointed sequence
`(M^{α_i}, ρ_{α_i}(p_i)^{-2} g^{α_i}, p_i)` has a subsequence carrying ONE LC56 package" enters
UNBUNDLED with the items LC57 (1)–(2) consume: the models are indexed by `ι`, each with its supplied
LC21 cone package (radial cone data and Kleiner–Lott maps at every large scale), and along every
sequence `α_i → ∞`, `p_i ∈ M^{α_i}` some subsequence has a model `b`, pointed Gromov–Hausdorff
convergence of the normalized sources to `(N_b, n_b)` (LC56 (1)), and numbers `H_j → ∞` with the
normalized curvature bounds `sec ≥ -H_j⁻²` on the normalized ball of radius `H_j` (LC56 (4)).

The conclusion is LC58's for these witnesses: fixed `δ, ε, e, T`, there are `V ≥ T` and `α₀` such
that for every `α > α₀` and every `p ∈ M^α` some `s ∈ [T, V]` gives, at the metric scale
`(s ρ_α(p))⁻² g^α`, a Kleiner–Lott `δ`-map to the cone of one model, and an LC30 function with all
its clauses together with LC31's cutoff (the SAME scale for both). The proof is the LC58 kernel
`exists_uniform_scale_interval_of_eventual_witnesses` fed by LC57 (1)–(2),
`exists_scale_eventually_normalized_cone_radial_witnesses` (LC57 (1)–(2) for normalized sources,
stated at the scale `(R r_i)⁻² g_i` directly), on the normalized subsequence.
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

variable [NeZero (Module.finrank ℝ E)] [I.Boundaryless]

/-- **LC57 (1)–(2) for normalized sources.** The sources are normalized by scales `r_i > 0`:
LC56's items (1) and (4) hold for `(M_i, r_i⁻² g_i, p_i)` (pointed convergence of the metric
rescalings `r_i⁻¹ d_i`, curvature `sec ≥ -H_i⁻²` of `r_i⁻² g_i` on the normalized `H_i`-ball). Then
there is `R₀ > 0` such that for every `R ≥ R₀` one tail has, at the metric scale `(R r_i)⁻² g_i`
(stated directly, not as a nested rescaling), a Kleiner–Lott `δ`-map to `(C, o)`, an LC30 function
with all its clauses, and LC31's cutoff with its bounds. -/
theorem exists_scale_eventually_normalized_cone_radial_witnesses
    {M : ℕ → Type*} [mM : ∀ i, MetricSpace (M i)] [∀ i, ChartedSpace H (M i)]
    [∀ i, IsManifold I ∞ (M i)] [∀ i, SigmaCompactSpace (M i)] [∀ i, CompleteSpace (M i)]
    (g : ∀ i, SmoothRiemannianMetric I (M i))
    (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
    (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) {N : Type*} [mN : MetricSpace N] {p : ∀ i, M i} {n : N}
    (hGH : @PointedGHConverges M (fun i => (mM i).rescale (r i)⁻¹ (inv_pos.mpr (hr i))) N mN p n)
    {C : Type*} [MetricSpace C] {o : C} (Hc : RadialConeData o)
    (hcone : ∀ τ : ℝ, 0 < τ → τ < 1 → ∃ R₀ : ℝ, ∀ R : ℝ, ∀ hR : 0 < R, R₀ ≤ R →
      Nonempty (@KleinerLottApprox N C (mN.rescale R⁻¹ (inv_pos.mpr hR)) _ n o τ))
    (Hb : ℕ → ℝ) (hHb : Tendsto Hb atTop atTop)
    (hsec : ∀ i, ∀ y ∈ @Metric.ball (M i)
        ((mM i).rescale (r i)⁻¹ (inv_pos.mpr (hr i))).toPseudoMetricSpace (p i) (Hb i),
      SectionalBoundedBelowAt (scaleMetric ((r i)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (hr i)) 2) (g i))
        y (-((Hb i)⁻¹ ^ 2)))
    {δ ε e : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (hε : 0 < ε) (hε1 : ε < 1) (he : 0 < e)
    (he1 : e < 1 / 40) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, ∀ hR : 0 < R, R₀ ≤ R → ∀ᶠ i in atTop,
      Nonempty (@KleinerLottApprox (M i) C
        ((mM i).rescale (R * r i)⁻¹ (inv_pos.mpr (mul_pos hR (hr i)))) _ (p i) o δ) ∧
      (letI := (mM i).rescale (R * r i)⁻¹ (inv_pos.mpr (mul_pos hR (hr i)))
      let gR := scaleMetric ((R * r i)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (mul_pos hR (hr i))) 2) (g i)
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
  set δ₂ : ℝ := radialSmoothingConeError (ε / 4) / 2 with hδ₂def
  have hrs : 0 < radialSmoothingConeError (ε / 4) := radialSmoothingConeError_pos (by positivity)
  have hrs1 : radialSmoothingConeError (ε / 4) ≤ 1 / 600 := min_le_left _ _
  have hδ₂0 : 0 < δ₂ := by positivity
  have hδ₂1 : δ₂ < 1 := by linarith
  have hδ₂r : δ₂ < radialSmoothingConeError (ε / 4) := by linarith
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
  have hmetricN : ∀ i a b, riemannianEDistOf (scaleMetric ((r i)⁻¹ ^ 2)
      (pow_pos (inv_pos.mpr (hr i)) 2) (g i)) a b =
        ENNReal.ofReal (@dist (M i) ((mM i).rescale (r i)⁻¹ (inv_pos.mpr (hr i))).toDist a b) :=
    fun i => riemannianEDistOf_scaleMetric_inv_sq_eq_rescale (g i) (hmetric i) (hr i)
  have h1 := eventually_riemannian_rescaled_approx_fixed_target
    (mX := fun i => (mM i).rescale (r i)⁻¹ (inv_pos.mpr (hr i))) _ hmetricN hGH R hR hδ hδ1
    (hR₁ R hR hR₁R).some
  have h2 := eventually_riemannian_rescaled_approx_fixed_target
    (mX := fun i => (mM i).rescale (r i)⁻¹ (inv_pos.mpr (hr i))) _ hmetricN hGH R hR hδ₂0 hδ₂1
    (hR₂ R hR hR₂R).some
  filter_upwards [h1, h2, hHb.eventually_ge_atTop (400 * R)] with i hi1 hi2 hiH
  have heq : ((mM i).rescale (r i)⁻¹ (inv_pos.mpr (hr i))).rescale R⁻¹ (inv_pos.mpr hR) =
      (mM i).rescale (R * r i)⁻¹ (inv_pos.mpr (mul_pos hR (hr i))) := by
    rw [MetricSpace.rescale_mul]
    exact MetricSpace.rescale_congr _ (mul_inv R (r i)).symm _ _
  have hKL1 := hi1.2
  have hKL2 := hi2.2
  rw [heq] at hKL1 hKL2
  refine ⟨hKL1, ?_⟩
  obtain ⟨φ⟩ := hKL2
  have hRr : 0 < R * r i := mul_pos hR (hr i)
  -- the curvature buffer at the scale `R r_i`
  have hsecR : ∀ y ∈ Metric.ball (p i) (400 * (R * r i)),
      SectionalBoundedBelowAt (g i) y (-((1 / 60) ^ 2 * (R * r i)⁻¹ ^ 2)) := by
    intro y hy
    have hy' : y ∈ @Metric.ball (M i)
        ((mM i).rescale (r i)⁻¹ (inv_pos.mpr (hr i))).toPseudoMetricSpace (p i) (Hb i) := by
      change (r i)⁻¹ * dist y (p i) < Hb i
      have h0 : dist y (p i) < 400 * (R * r i) := hy
      have h3 : (r i)⁻¹ * dist y (p i) < (r i)⁻¹ * (400 * (R * r i)) :=
        mul_lt_mul_of_pos_left h0 (inv_pos.mpr (hr i))
      have h4 : (r i)⁻¹ * (400 * (R * r i)) = 400 * R := by
        field_simp [(hr i).ne']
      linarith
    have hb := (sectionalBoundedBelowAt_scaleMetric_iff (pow_pos (inv_pos.mpr (hr i)) 2)).mp (hsec i y hy')
    refine hb.mono ?_
    have h60 : 60 * R ≤ Hb i := by linarith
    have h60R : 0 < 60 * R := by positivity
    have hinv : (Hb i)⁻¹ ≤ (60 * R)⁻¹ := inv_anti₀ h60R h60
    have hsq : (Hb i)⁻¹ ^ 2 ≤ (60 * R)⁻¹ ^ 2 :=
      pow_le_pow_left₀ (inv_nonneg.mpr (h60R.le.trans h60)) hinv 2
    have hid : (1 / 60) ^ 2 * (R * r i)⁻¹ ^ 2 = (60 * R)⁻¹ ^ 2 * (r i)⁻¹ ^ 2 := by
      rw [mul_inv, mul_inv, mul_pow, mul_pow, one_div]
      ring
    have hr2 : 0 ≤ (r i)⁻¹ ^ 2 := sq_nonneg _
    rw [hid]
    nlinarith
  obtain ⟨F, hFlip, hFO, hclose, hout, hdiff, hnn, hp0, hgrad, hrng, hsub, O', hO', hband, hFO',
      hne⟩ :=
    exists_radialFunction_of_kleinerLottApprox_at_scale (g i) (hmetric i) hRr φ Hc hsecR hε hε1
      hδ₂r he he1
  let := (mM i).rescale (R * r i)⁻¹ (inv_pos.mpr hRr)
  obtain ⟨L, hL0, hL, hc1, hc2, hc3, hc4, hc5⟩ :=
    exists_radial_cutoff_of_band (scaleMetric ((R * r i)⁻¹ ^ 2) (pow_pos (inv_pos.mpr hRr) 2) (g i))
      (p i) hε.le hFlip.continuous hclose (fun q hq => (hgrad q hq).2) hsub hO' hband hFO'
  exact ⟨F, hFlip, hFO, hclose, hout, hdiff, hnn, hp0, hgrad, hrng, hsub,
    ⟨O', hO', hband, hFO', hne⟩, L, hL0, hL, hc1, hc2, hc3, hc4, hc5⟩

/-- **LC58 binding, items (1)–(2)** (master207A, A:23194). Under LC58's sequential hypothesis
(unbundled: an LC56 model with its cone package, pointed convergence of the normalized sources,
and the normalized curvature bounds along a subsequence of every sequence), every `0 < δ < 1`,
`0 < ε < 1`, `0 < e < 1/40`, `T` admit `V ≥ T` and `α₀` such that for `α > α₀` and every
`p ∈ M^α` one `s ∈ [T, V]` and one model `b` give, at the metric scale `(s ρ_α(p))⁻² g^α`, an
actual Kleiner–Lott `δ`-map to `(C_b, o_b)` and an LC30 function with all LC30 clauses and LC31's
cutoff with its bounds. -/
theorem exists_uniform_scale_interval_cone_radial_witnesses
    {M : ℕ → Type*} [mM : ∀ α, MetricSpace (M α)] [∀ α, ChartedSpace H (M α)]
    [∀ α, IsManifold I ∞ (M α)] [∀ α, SigmaCompactSpace (M α)] [∀ α, CompleteSpace (M α)]
    (g : ∀ α, SmoothRiemannianMetric I (M α))
    (hmetric : ∀ α a b, riemannianEDistOf (g α) a b = ENNReal.ofReal (dist a b))
    (ρ : ∀ α, M α → ℝ) (hρ : ∀ α x, 0 < ρ α x)
    {ι : Type*} {N C : ι → Type*} [mN : ∀ b, MetricSpace (N b)] [mC : ∀ b, MetricSpace (C b)]
    (n : ∀ b, N b) (o : ∀ b, C b) (Hc : ∀ b, RadialConeData (o b))
    (hcone : ∀ b : ι, ∀ τ : ℝ, 0 < τ → τ < 1 → ∃ R₀ : ℝ, ∀ R : ℝ, ∀ hR : 0 < R, R₀ ≤ R →
      Nonempty (@KleinerLottApprox (N b) (C b) ((mN b).rescale R⁻¹ (inv_pos.mpr hR)) (mC b)
        (n b) (o b) τ))
    (hmodel : ∀ a : ℕ → ℕ, Tendsto a atTop atTop → ∀ z : ∀ j, M (a j),
      ∃ b : ι, ∃ k : ℕ → ℕ, StrictMono k ∧
        @PointedGHConverges (fun j => M (a (k j)))
          (fun j => (mM (a (k j))).rescale (ρ (a (k j)) (z (k j)))⁻¹ (inv_pos.mpr (hρ _ _)))
          (N b) (mN b) (fun j => z (k j)) (n b) ∧
        ∃ Hb : ℕ → ℝ, Tendsto Hb atTop atTop ∧ ∀ j,
          ∀ y ∈ @Metric.ball (M (a (k j)))
            ((mM (a (k j))).rescale (ρ (a (k j)) (z (k j)))⁻¹
              (inv_pos.mpr (hρ _ _))).toPseudoMetricSpace (z (k j)) (Hb j),
            SectionalBoundedBelowAt (scaleMetric ((ρ (a (k j)) (z (k j)))⁻¹ ^ 2)
              (pow_pos (inv_pos.mpr (hρ _ _)) 2) (g (a (k j)))) y (-((Hb j)⁻¹ ^ 2)))
    {δ ε e T : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (hε : 0 < ε) (hε1 : ε < 1) (he : 0 < e)
    (he1 : e < 1 / 40) :
    ∃ V : ℝ, T ≤ V ∧ ∃ α₀ : ℕ, ∀ α : ℕ, α₀ < α → ∀ p : M α, ∃ s ∈ Icc T V,
      ∃ hs : 0 < s, ∃ b : ι,
        Nonempty (@KleinerLottApprox (M α) (C b)
          ((mM α).rescale (s * ρ α p)⁻¹ (inv_pos.mpr (mul_pos hs (hρ α p)))) (mC b)
          p (o b) δ) ∧
        (letI := (mM α).rescale (s * ρ α p)⁻¹ (inv_pos.mpr (mul_pos hs (hρ α p)))
        let gR := scaleMetric ((s * ρ α p)⁻¹ ^ 2)
          (pow_pos (inv_pos.mpr (mul_pos hs (hρ α p))) 2) (g α)
        ∃ F : M α → ℝ, LipschitzWith (Real.toNNReal (1 + ε)) F ∧
          (∃ O : Set (M α), IsOpen O ∧ {x : M α | 1 / 10 ≤ dist x p ∧ dist x p ≤ 10} ⊆ O ∧
            ContMDiffOn I 𝓘(ℝ, ℝ) ∞ F O) ∧
          (∀ x, |F x - Metric.infDist x {p}| < e) ∧
          (∀ x, x ∉ {x : M α | 1 / 20 < dist x p ∧ dist x p < 20} →
            F x = Metric.infDist x {p}) ∧
          (∀ x y, |(F x - Metric.infDist x {p}) - (F y - Metric.infDist y {p})| ≤
            ε * dist x y) ∧
          (∀ x, 0 ≤ F x) ∧ F p = 0 ∧
          (∀ q ∈ {x : M α | 1 / 10 ≤ dist x p ∧ dist x p ≤ 10},
            1 - ε ≤ Real.sqrt (gR.inner q (gradFun gR F q) (gradFun gR F q)) ∧
              Real.sqrt (gR.inner q (gradFun gR F q) (gradFun gR F q)) ≤ 1 + ε) ∧
          (∀ x, F x ∈ Icc (1 / 5 : ℝ) 2 → 1 / 5 - e < dist x p ∧ dist x p < 2 + e) ∧
          F ⁻¹' Icc (1 / 5 : ℝ) 2 ⊆ {x : M α | 1 / 10 ≤ dist x p ∧ dist x p ≤ 10} ∧
          (∃ O' : Set (M α), IsOpen O' ∧ F ⁻¹' Icc (1 / 5 : ℝ) 2 ⊆ O' ∧
            ContMDiffOn I 𝓘(ℝ, ℝ) ∞ F O' ∧ ∀ q ∈ O', gradFun gR F q ≠ 0) ∧
          ∃ L : ℝ, 0 ≤ L ∧ (∀ t, |deriv (annularCutoff cutoffProfile) t| ≤ L) ∧
            ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x => annularCutoff cutoffProfile (F x)) ∧
            (∀ x, annularCutoff cutoffProfile (F x) ∈ Icc (0 : ℝ) 1) ∧
            (∀ x, F x ∈ Icc (3 / 10 : ℝ) (4 / 5) → annularCutoff cutoffProfile (F x) = 1) ∧
            tsupport (fun x => annularCutoff cutoffProfile (F x)) ⊆
              {x : M α | 1 / 5 - e < dist x p ∧ dist x p < 9 / 10 + e} ∧
            ∀ q, Real.sqrt (gR.inner q (gradFun gR (fun x => annularCutoff cutoffProfile (F x)) q)
              (gradFun gR (fun x => annularCutoff cutoffProfile (F x)) q)) ≤ L * (1 + ε)) := by
  refine exists_uniform_scale_interval_of_eventual_witnesses (X := M) _ T ?_
  intro a ha z
  obtain ⟨b, k, hk, hGH, Hb, hHb, hsec⟩ := hmodel a ha z
  obtain ⟨R₀, hR₀, hall⟩ := exists_scale_eventually_normalized_cone_radial_witnesses
    (M := fun j => M (a (k j))) (fun j => g (a (k j))) (fun j => hmetric (a (k j)))
    (fun j => ρ (a (k j)) (z (k j))) (fun j => hρ _ _) hGH (Hc b) (hcone b) Hb hHb hsec
    hδ hδ1 hε hε1 he he1
  have hs : 0 < max R₀ T := lt_of_lt_of_le hR₀ (le_max_left _ _)
  refine ⟨k, hk, max R₀ T, le_max_right _ _, ?_⟩
  filter_upwards [hall (max R₀ T) hs (le_max_left _ _)] with j hj
  exact ⟨hs, b, hj⟩

end DifferentialGeometry.Geometry.Collapse
