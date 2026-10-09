import DifferentialGeometry.Geometry.Collapse.BoundaryScale.TorusAreaRatio
import DifferentialGeometry.Geometry.Comparison.Distance.Continuity

/-!
# The flat half-product volume as a slice integral (route R3, statement M.2)

For a hyperbolic cusp `H` with flat torus `g_T`, put `μ₀ = vol_{g_T} ⊗ Lebesgue` on `T² × ℝ`
(the torus factor with its Borel σ-algebra `borel Torus`, the σ-algebra of
`riemannianVolumeMeasure`; the convention of the boundary-geometry design, §(b.2).1). For a centre
`(x, z₁)` and `r ≥ 0` the half ellipsoid `E_r = {(t, z) : 0 ≤ z, (z - z₁)² + d_T(x, t)² < r²}`
(with `g_T`'s OWN length distance `d_T`) has volume
`μ₀(E_r) = ∫_{max(-r,-z₁)}^r A(√(r² - y²)) dy`, `A(s)` the `g_T`-ball area.
Proof: Fubini over the height (`Measure.prod_apply_symm`); the slice at height `z ≥ 0` is the
`g_T`-ball of radius `√(r² - (z - z₁)²)` (empty, of area `0`, when the radicand is `≤ 0`);
translate `y = z - z₁`; the integrand vanishes outside `[-r, r]`.
No sign condition on `z₁` is needed (the interface's `0 ≤ z₁` and `0 < r` are weakened to `0 ≤ r`;
the verbatim form is kept as an `example`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry.Geometry.Collapse

/-- M.2 (Fubini): the flat half-ellipsoid volume is `∫_{max(-r,-z₁)}^r A(√(r² - y²)) dy`, for
every `z₁` and `r ≥ 0`. -/
theorem torus_halfProduct_volume_eq (Hc : HyperbolicCusp) (x : Torus) {z₁ r : ℝ} (hr : 0 ≤ r) :
    let A : ℝ → ℝ := fun s => (ballVolume Hc.torusMetric x s).toReal
    let μ₀ := @Measure.prod Torus ℝ (borel Torus) _
      (riemannianVolumeMeasure torusModel Torus Hc.torusMetric) volume
    (μ₀ {p : Torus × ℝ | 0 ≤ p.2 ∧
        (p.2 - z₁) ^ 2 + (riemannianEDistOf Hc.torusMetric x p.1).toReal ^ 2 < r ^ 2}).toReal =
      ∫ y in max (-r) (-z₁)..r, A (Real.sqrt (r ^ 2 - y ^ 2)) := by
  intro A μ₀
  let : MeasurableSpace Torus := borel Torus
  have : BorelSpace Torus := ⟨rfl⟩
  let μT := riemannianVolumeMeasure torusModel Torus Hc.torusMetric
  have : IsFiniteMeasure μT :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := torusModel) (M := Torus) Hc.torusMetric
  let D : Torus → ℝ := fun t => (riemannianEDistOf Hc.torusMetric x t).toReal
  have hne (t : Torus) : riemannianEDistOf Hc.torusMetric x t ≠ ⊤ :=
    riemannianEDistOf_ne_top Hc.torusMetric x t
  have hcont : Continuous fun t : Torus => riemannianEDistOf Hc.torusMetric x t :=
    Geometry.Riemannian.continuous_riemannianEDist Hc.torusMetric x
  have hDcont : Continuous D := ENNReal.continuousOn_toReal.comp_continuous hcont hne
  let S : Set (Torus × ℝ) := {p | 0 ≤ p.2 ∧ (p.2 - z₁) ^ 2 + D p.1 ^ 2 < r ^ 2}
  have hS : MeasurableSet S :=
    (measurableSet_le measurable_const measurable_snd).inter
      (measurableSet_lt (((measurable_snd.sub_const z₁).pow_const 2).add
        ((hDcont.measurable.comp measurable_fst).pow_const 2)) measurable_const)
  let B : ℝ → ℝ≥0∞ := fun y => ballVolume Hc.torusMetric x (Real.sqrt (r ^ 2 - y ^ 2))
  have hBtop (y : ℝ) : B y ≠ ⊤ := torus_ballVolume_ne_top Hc x _
  have hB0 (y : ℝ) (hy : r ^ 2 - y ^ 2 ≤ 0) : B y = 0 := by
    refine le_antisymm ?_ zero_le
    have h := torus_ballVolume_le_pi_mul_sq Hc x 0
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
      ENNReal.ofReal_zero, nonpos_iff_eq_zero] at h
    simp only [B, Real.sqrt_eq_zero'.2 hy, h, le_refl]
  -- the slice at height `z`
  have hslice (z : ℝ) : μT ((fun t => (t, z)) ⁻¹' S) = (Ici (0 : ℝ)).indicator (fun z => B (z - z₁)) z := by
    by_cases hz : 0 ≤ z
    · rw [indicator_of_mem (mem_Ici.2 hz)]
      have hset : (fun t => (t, z)) ⁻¹' S = riemannianBallOf Hc.torusMetric x
          (Real.sqrt (r ^ 2 - (z - z₁) ^ 2)) := by
        ext t
        simp only [S, mem_preimage, mem_ofPred_eq, riemannianBallOf]
        rw [ENNReal.lt_ofReal_iff_toReal_lt (hne t), Real.lt_sqrt ENNReal.toReal_nonneg]
        constructor
        · rintro ⟨-, h⟩
          change D t ^ 2 < _
          linarith
        · intro h
          refine ⟨hz, ?_⟩
          change D t ^ 2 < _ at h
          linarith
      rw [hset]
      rfl
    · rw [indicator_of_notMem (fun h => hz (mem_Ici.1 h))]
      have hset : (fun t => (t, z)) ⁻¹' S = ∅ := by
        ext t
        simp only [S, mem_preimage, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
        exact fun h => absurd h hz
      rw [hset, measure_empty]
  have hμ₀ : μ₀ S = ∫⁻ y, (Ici (-z₁)).indicator B y := by
    have hfub : μ₀ S = ∫⁻ z, μT ((fun t => (t, z)) ⁻¹' S) := Measure.prod_apply_symm hS
    rw [hfub, lintegral_congr hslice, ← lintegral_add_right_eq_self _ z₁]
    refine lintegral_congr fun y => ?_
    simp only [indicator_apply, mem_Ici, add_sub_cancel_right, neg_le_iff_add_nonneg]
  have hmeasA : Monotone fun s : ℝ => (ballVolume Hc.torusMetric x s).toReal := by
    intro s t hst
    exact ENNReal.toReal_mono (torus_ballVolume_ne_top Hc x t)
      (measure_lt_ofReal_monotone μT (riemannianEDistOf Hc.torusMetric x) hst)
  change (μ₀ S).toReal = ∫ y in max (-r) (-z₁)..r, (B y).toReal
  rcases le_or_gt (max (-r) (-z₁)) r with hle | hlt
  · -- the main case: the window `[max(-r,-z₁), r]` is nonempty
    have hind : (fun y => (Ici (-z₁)).indicator B y) =
        fun y => (Icc (max (-r) (-z₁)) r).indicator B y := by
      funext y
      by_cases hy : y ∈ Icc (max (-r) (-z₁)) r
      · rw [indicator_of_mem hy, indicator_of_mem (mem_Ici.2 ((le_max_right _ _).trans hy.1))]
      · rw [indicator_of_notMem hy]
        by_cases hy' : -z₁ ≤ y
        · rw [indicator_of_mem (mem_Ici.2 hy')]
          apply hB0
          simp only [mem_Icc, max_le_iff, not_and_or, not_le] at hy
          rcases hy with (h | h) | h
          · nlinarith
          · exact absurd hy' (not_le.2 h)
          · nlinarith
        · exact indicator_of_notMem (fun h => hy' (mem_Ici.1 h)) _
    have hlin : μ₀ S = ∫⁻ y in Ioc (max (-r) (-z₁)) r, B y := by
      rw [hμ₀, hind, lintegral_indicator measurableSet_Icc,
        Measure.restrict_congr_set Ioc_ae_eq_Icc]
    have hmeasB : Measurable fun y : ℝ => (B y).toReal :=
      hmeasA.measurable.comp (Real.continuous_sqrt.comp
        (continuous_const.sub (continuous_pow 2))).measurable
    rw [intervalIntegral.integral_of_le hle,
      integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun _ => ENNReal.toReal_nonneg)
        hmeasB.aestronglyMeasurable, hlin]
    congr 1
    exact lintegral_congr fun y => (ENNReal.ofReal_toReal (hBtop y)).symm
  · -- the degenerate case `r < -z₁`: both sides vanish
    have hz : r < -z₁ := by
      rcases max_choice (-r) (-z₁) with h | h
      · rw [h] at hlt; linarith
      · rwa [h] at hlt
    have hzero : μ₀ S = 0 := by
      rw [hμ₀]
      refine (lintegral_congr fun y => ?_).trans lintegral_zero
      by_cases hy : -z₁ ≤ y
      · rw [indicator_of_mem (mem_Ici.2 hy)]
        exact hB0 y (by nlinarith)
      · exact indicator_of_notMem (fun h => hy (mem_Ici.1 h)) _
    rw [hzero, ENNReal.toReal_zero]
    have hint : ∫ y in max (-r) (-z₁)..r, (B y).toReal = ∫ _y in max (-r) (-z₁)..r, (0 : ℝ) := by
      refine intervalIntegral.integral_congr fun y hy => ?_
      rw [uIcc_of_ge hlt.le] at hy
      rw [hB0 y (by nlinarith [hy.1]), ENNReal.toReal_zero]
    rw [hint, intervalIntegral.integral_zero]

/-- The interface statement `M_half_product_volume` (scratch `BoundaryInterfaces.lean`), verbatim:
the special case `0 ≤ z₁`, `0 < r` of `torus_halfProduct_volume_eq`. -/
example (Hc : HyperbolicCusp) (x : Torus) {z₁ r : ℝ} (hz₁ : 0 ≤ z₁) (hr : 0 < r) :
    let A : ℝ → ℝ := fun s => (ballVolume Hc.torusMetric x s).toReal
    let μ₀ := @Measure.prod Torus ℝ (borel Torus) _
      (riemannianVolumeMeasure torusModel Torus Hc.torusMetric) volume
    (μ₀ {p : Torus × ℝ | 0 ≤ p.2 ∧
        (p.2 - z₁) ^ 2 + (riemannianEDistOf Hc.torusMetric x p.1).toReal ^ 2 < r ^ 2}).toReal =
      ∫ y in max (-r) (-z₁)..r, A (Real.sqrt (r ^ 2 - y ^ 2)) :=
  Function.const _ (torus_halfProduct_volume_eq Hc x hr.le) hz₁

/-- Consumer (M.2 + M, the form read by Q through V.2): the flat half-ellipsoid volume
`F(r) = μ₀(E_r)` has antitone ratio `F(r)/r³` at every height `z₁ ≥ 0`. -/
theorem torus_halfProduct_volume_div_cube_antitone (Hc : HyperbolicCusp) (x : Torus)
    {z₁ s b : ℝ} (hz₁ : 0 ≤ z₁) (hs : 0 < s) (hsb : s ≤ b) :
    let F : ℝ → ℝ := fun r =>
      ((@Measure.prod Torus ℝ (borel Torus) _
        (riemannianVolumeMeasure torusModel Torus Hc.torusMetric) volume)
        {p : Torus × ℝ | 0 ≤ p.2 ∧ (p.2 - z₁) ^ 2 +
          (riemannianEDistOf Hc.torusMetric x p.1).toReal ^ 2 < r ^ 2}).toReal
    F b / b ^ 3 ≤ F s / s ^ 3 := by
  intro F
  have hb : 0 < b := hs.trans_le hsb
  have hFb := torus_halfProduct_volume_eq Hc x (z₁ := z₁) hb.le
  have hFs := torus_halfProduct_volume_eq Hc x (z₁ := z₁) hs.le
  simp only at hFb hFs
  change F b = _ at hFb
  change F s = _ at hFs
  rw [hFb, hFs]
  exact torus_halfBall_div_cube_antitone Hc x hz₁ hs hsb

end DifferentialGeometry.Geometry.Collapse
