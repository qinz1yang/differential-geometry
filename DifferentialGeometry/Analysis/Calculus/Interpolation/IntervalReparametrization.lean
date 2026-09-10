import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import DifferentialGeometry.Analysis.Calculus.Inverse.InjectiveParameterizedInverse
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Topology.Order.Compact

noncomputable section
open Set Filter Topology
open scoped ContDiff Manifold

namespace Poincare.Analysis

private def transitionPrimitive (x : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..x, Real.smoothTransition t

private theorem hasDerivAt_transitionPrimitive (x : ℝ) :
    HasDerivAt transitionPrimitive (Real.smoothTransition x) x :=
  intervalIntegral.integral_hasDerivAt_right
    (Real.smoothTransition.continuous.intervalIntegrable _ _)
    Real.smoothTransition.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter
    Real.smoothTransition.continuousAt

private theorem contDiff_transitionPrimitive : ContDiff ℝ ∞ transitionPrimitive := by
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun x ↦ (hasDerivAt_transitionPrimitive x).differentiableAt, ?_⟩
  have he : deriv transitionPrimitive = Real.smoothTransition :=
    funext fun x ↦ (hasDerivAt_transitionPrimitive x).deriv
  rw [he]
  exact Real.smoothTransition.contDiff

private theorem transitionPrimitive_zero {x : ℝ} (hx : x ≤ 0) :
    transitionPrimitive x = 0 := by
  have he : (∫ t in (0 : ℝ)..x, Real.smoothTransition t) = ∫ _ in (0 : ℝ)..x, (0 : ℝ) :=
    intervalIntegral.integral_congr (fun t ht ↦
      Real.smoothTransition.zero_of_nonpos ((uIcc_of_ge hx ▸ ht).2))
  simpa only [transitionPrimitive, intervalIntegral.integral_zero] using he

private theorem transitionPrimitive_linear {x : ℝ} (hx : 1 ≤ x) :
    transitionPrimitive x = transitionPrimitive 1 + x - 1 := by
  have he : (∫ t in (1 : ℝ)..x, Real.smoothTransition t) = ∫ _ in (1 : ℝ)..x, (1 : ℝ) :=
    intervalIntegral.integral_congr (fun t ht ↦
      Real.smoothTransition.one_of_one_le ((uIcc_of_le hx ▸ ht).1))
  have ha := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (Real.smoothTransition.continuous.intervalIntegrable (0 : ℝ) 1)
    (Real.smoothTransition.continuous.intervalIntegrable (1 : ℝ) x)
  rw [he, intervalIntegral.integral_const] at ha
  dsimp only [transitionPrimitive]
  simpa only [smul_eq_mul, mul_one, add_sub_assoc] using ha.symm

private def windowPrimitive (ε x : ℝ) : ℝ :=
  ε * (transitionPrimitive ((x - ε) / ε) -
    transitionPrimitive ((x - (1 - 2 * ε)) / ε))

private def windowDensity (ε x : ℝ) : ℝ :=
  Real.smoothTransition ((x - ε) / ε) -
    Real.smoothTransition ((x - (1 - 2 * ε)) / ε)

private theorem hasDerivAt_windowPrimitive {ε : ℝ} (hε : ε ≠ 0) (x : ℝ) :
    HasDerivAt (windowPrimitive ε) (windowDensity ε x) x := by
  have h₀ := (hasDerivAt_transitionPrimitive ((x - ε) / ε)).comp x
    (((hasDerivAt_id x).sub_const ε).div_const ε)
  have h₁ := (hasDerivAt_transitionPrimitive ((x - (1 - 2 * ε)) / ε)).comp x
    (((hasDerivAt_id x).sub_const (1 - 2 * ε)).div_const ε)
  convert (h₀.sub h₁).const_mul ε using 1 <;>
    first | rfl | (dsimp only [windowDensity]; field_simp)

private theorem windowDensity_bounds {ε : ℝ} (hε : 0 < ε) (hs : 3 * ε ≤ 1) (x : ℝ) :
    0 ≤ windowDensity ε x ∧ windowDensity ε x ≤ 1 := by
  have he : (x - (1 - 2 * ε)) / ε ≤ (x - ε) / ε := by
    apply (div_le_div_iff_of_pos_right hε).mpr
    linarith
  have hm := Real.smoothTransition.monotone he
  have hl := Real.smoothTransition.nonneg ((x - (1 - 2 * ε)) / ε)
  have hu := Real.smoothTransition.le_one ((x - ε) / ε)
  dsimp only [windowDensity]
  constructor <;> linarith

private theorem windowPrimitive_lower {ε x : ℝ} (hε : 0 < ε) (hs : 3 * ε ≤ 1)
    (hx : x ≤ ε) : windowPrimitive ε x = 0 := by
  have h₀ : (x - ε) / ε ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le
  have h₁ : (x - (1 - 2 * ε)) / ε ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le
  simp only [windowPrimitive, transitionPrimitive_zero h₀, transitionPrimitive_zero h₁,
    sub_self, mul_zero]

private theorem windowPrimitive_upper {ε x : ℝ} (hε : 0 < ε) (hs : 3 * ε ≤ 1)
    (hx : 1 - ε ≤ x) : windowPrimitive ε x = 1 - 3 * ε := by
  have h₀ : 1 ≤ (x - ε) / ε := (le_div_iff₀ hε).mpr (by nlinarith)
  have h₁ : 1 ≤ (x - (1 - 2 * ε)) / ε := (le_div_iff₀ hε).mpr (by linarith)
  rw [windowPrimitive, transitionPrimitive_linear h₀, transitionPrimitive_linear h₁]
  field_simp
  ring

private def intervalWidth (r : ℝ) : ℝ := r / (8 * (1 + r))

private theorem intervalWidth_bounds {r : ℝ} (hr : 0 < r) :
    0 < intervalWidth r ∧ 3 * intervalWidth r < 1 ∧ 3 * intervalWidth r < r := by
  have hd : 0 < 8 * (1 + r) := by positivity
  have hpos : 0 < intervalWidth r := div_pos hr hd
  have hs : intervalWidth r < 1 / 8 := by
    rw [intervalWidth, div_lt_iff₀ hd]
    linarith
  have ht : intervalWidth r < r / 4 := by
    rw [intervalWidth, div_lt_iff₀ hd]
    nlinarith [sq_nonneg r]
  exact ⟨hpos, by linarith, by linarith⟩

private def intervalChange (q : ℝ × ℝ) : ℝ :=
  q.2 + (q.1 - 1) * windowPrimitive (intervalWidth q.1) q.2 / (1 - 3 * intervalWidth q.1)

private theorem contDiffOn_intervalChange :
    ContDiffOn ℝ ∞ intervalChange (Ioi 0 ×ˢ univ) := by
  have hw : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ ↦ intervalWidth q.1) (Ioi 0 ×ˢ univ) := by
    apply contDiffOn_fst.div (contDiffOn_const.mul (contDiffOn_const.add contDiffOn_fst))
    intro q hq
    have : 0 < q.1 := hq.1
    positivity
  have hne (q : ℝ × ℝ) (hq : q ∈ Ioi 0 ×ˢ univ) : intervalWidth q.1 ≠ 0 :=
    (intervalWidth_bounds hq.1).1.ne'
  have h₀ := contDiff_transitionPrimitive.comp_contDiffOn ((contDiffOn_snd.sub hw).div hw hne)
  have h₁ := contDiff_transitionPrimitive.comp_contDiffOn
    ((contDiffOn_snd.sub ((contDiffOn_const (c := (1 : ℝ))).sub
      ((contDiffOn_const (c := (2 : ℝ))).mul hw))).div hw hne)
  apply contDiffOn_snd.add
    (((contDiffOn_fst.sub contDiffOn_const).mul (hw.mul (h₀.sub h₁))).div
      (contDiffOn_const.sub (contDiffOn_const.mul hw)) ?_)
  intro q hq
  exact (sub_pos.mpr (intervalWidth_bounds hq.1).2.1).ne'

private theorem hasDerivAt_intervalChange {r : ℝ} (hr : 0 < r) (x : ℝ) :
    HasDerivAt (fun x ↦ intervalChange (r, x))
      (1 + (r - 1) * windowDensity (intervalWidth r) x / (1 - 3 * intervalWidth r)) x :=
  (hasDerivAt_id x).add
    (((hasDerivAt_windowPrimitive (intervalWidth_bounds hr).1.ne' x).const_mul (r - 1)).div_const
      (1 - 3 * intervalWidth r))

private theorem intervalChange_deriv_pos {r : ℝ} (hr : 0 < r) (x : ℝ) :
    0 < deriv (fun x ↦ intervalChange (r, x)) x := by
  rw [(hasDerivAt_intervalChange hr x).deriv]
  obtain ⟨hε, hs, ht⟩ := intervalWidth_bounds hr
  obtain ⟨hβ₀, hβ₁⟩ := windowDensity_bounds hε hs.le x
  have hm : 0 < 1 - 3 * intervalWidth r := sub_pos.mpr hs
  have he : 1 + (r - 1) * windowDensity (intervalWidth r) x / (1 - 3 * intervalWidth r) =
      (1 - 3 * intervalWidth r + (r - 1) * windowDensity (intervalWidth r) x) /
        (1 - 3 * intervalWidth r) := by field_simp
  rw [he]
  apply div_pos _ hm
  by_cases hr₁ : 1 ≤ r
  · have : 0 ≤ (r - 1) * windowDensity (intervalWidth r) x := mul_nonneg (by linarith) hβ₀
    linarith
  · have : r - 1 ≤ (r - 1) * windowDensity (intervalWidth r) x := by nlinarith
    linarith

private theorem intervalChange_lower {r x : ℝ} (hr : 0 < r) (hx : x ≤ intervalWidth r) :
    intervalChange (r, x) = x := by
  simp only [intervalChange, windowPrimitive_lower (intervalWidth_bounds hr).1
    (intervalWidth_bounds hr).2.1.le hx, mul_zero, zero_div, add_zero]

private theorem intervalChange_upper {r x : ℝ} (hr : 0 < r) (hx : 1 - intervalWidth r ≤ x) :
    intervalChange (r, x) = x + r - 1 := by
  rw [intervalChange, windowPrimitive_upper (intervalWidth_bounds hr).1
    (intervalWidth_bounds hr).2.1.le hx]
  rw [mul_div_cancel_right₀ _ (sub_pos.mpr (intervalWidth_bounds hr).2.1).ne']
  ring

private theorem intervalChange_spec :
    ContDiffOn ℝ ∞ intervalChange (Ioi 0 ×ˢ univ) ∧
      (∀ x, intervalChange (1, x) = x) ∧
      ∀ r : ℝ, 0 < r →
        (∀ x, 0 < deriv (fun x ↦ intervalChange (r, x)) x) ∧
        BijOn (fun x ↦ intervalChange (r, x)) (Icc 0 1) (Icc 0 r) ∧
        ∃ ε : ℝ, 0 < ε ∧ ε < 1 / 2 ∧ ε < r / 2 ∧
          (∀ x, x ≤ ε → intervalChange (r, x) = x) ∧
          ∀ x, 1 - ε ≤ x → intervalChange (r, x) = x + r - 1 := by
  refine ⟨contDiffOn_intervalChange, ?_, fun r hr ↦ ?_⟩
  · intro x
    simp only [intervalChange, sub_self, zero_mul, zero_div, add_zero]
  · have hmono := strictMono_of_deriv_pos (intervalChange_deriv_pos hr)
    have hcont : Continuous (fun x ↦ intervalChange (r, x)) :=
      continuous_iff_continuousAt.mpr (fun x ↦ (hasDerivAt_intervalChange hr x).continuousAt)
    obtain ⟨hε, hs, ht⟩ := intervalWidth_bounds hr
    have hz : intervalChange (r, 0) = 0 := intervalChange_lower hr hε.le
    have ho : intervalChange (r, 1) = r := by
      simpa only [add_sub_cancel_left] using intervalChange_upper hr (x := 1) (by linarith)
    refine ⟨intervalChange_deriv_pos hr, ?_, intervalWidth r, hε,
      by linarith, by linarith, fun _ hx ↦ intervalChange_lower hr hx,
      fun _ hx ↦ intervalChange_upper hr hx⟩
    have himage : (fun x ↦ intervalChange (r, x)) '' Icc 0 1 = Icc 0 r := by
      simpa only [hz, ho] using hcont.continuousOn.image_Icc_of_monotoneOn
        (a := (0 : ℝ)) (b := 1) (by norm_num) (hmono.monotone.monotoneOn _)
    exact ⟨fun x hx ↦ himage ▸ mem_image_of_mem _ hx, hmono.injective.injOn,
      fun y hy ↦ himage ▸ hy⟩

theorem exists_smooth_interval_reparametrization :
    ∃ χ : ℝ × ℝ → ℝ,
      ContDiffOn ℝ ∞ χ (Ioi 0 ×ˢ univ) ∧
      (∀ x, χ (1, x) = x) ∧
      ∀ r : ℝ, 0 < r →
        (∀ x, 0 < deriv (fun x ↦ χ (r, x)) x) ∧
        BijOn (fun x ↦ χ (r, x)) (Icc 0 1) (Icc 0 r) ∧
        ∃ ε : ℝ, 0 < ε ∧ ε < 1 / 2 ∧ ε < r / 2 ∧
          (∀ x, x ≤ ε → χ (r, x) = x) ∧
          ∀ x, 1 - ε ≤ x → χ (r, x) = x + r - 1 :=
  ⟨intervalChange, intervalChange_spec⟩

private theorem exists_interval_diffeomorph_with_formula :
    ∃ D : ℝ → Diffeomorph 𝓘(ℝ) 𝓘(ℝ) ℝ ℝ ∞,
      ContDiffOn ℝ ∞ (fun q : ℝ × ℝ ↦ D q.1 q.2) (Ioi 0 ×ˢ univ) ∧
      ContDiffOn ℝ ∞ (fun q : ℝ × ℝ ↦ (D q.1).symm q.2) (Ioi 0 ×ˢ univ) ∧
      D 1 = Diffeomorph.refl 𝓘(ℝ) ℝ ∞ ∧
      (∀ r : ℝ, 0 < r →
        (∀ x, 0 < deriv (D r) x) ∧
        BijOn (D r) (Icc 0 1) (Icc 0 r) ∧
        ∃ ε : ℝ, 0 < ε ∧ ε < 1 / 2 ∧ ε < r / 2 ∧
          (∀ x, x ≤ ε → D r x = x) ∧
          ∀ x, 1 - ε ≤ x → D r x = x + r - 1) ∧
      ∀ r : ℝ, 0 < r → ∀ x, D r x = intervalChange (r, x) := by
  classical
  let χ := intervalChange
  obtain ⟨hχ, hχone, hprop⟩ := intervalChange_spec
  have hsmooth (r : ℝ) (hr : 0 < r) : ContDiff ℝ ∞ (fun x ↦ χ (r, x)) :=
    contDiffOn_univ.mp (hχ.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun _ _ ↦ ⟨hr, mem_univ _⟩))
  have hbij (r : ℝ) (hr : r ∈ Ioi 0) : Function.Bijective (fun x ↦ χ (r, x)) := by
    refine ⟨(strictMono_of_deriv_pos (hprop r hr).1).injective, ?_⟩
    obtain ⟨ε, _, _, _, hlo, hhi⟩ := (hprop r hr).2.2
    have htop : Tendsto (fun x ↦ χ (r, x)) atTop atTop := by
      apply (tendsto_atTop_add_const_right atTop (r - 1) tendsto_id).congr'
      filter_upwards [eventually_ge_atTop (1 - ε)] with x hx
      simpa only [add_sub_assoc, id_eq] using (hhi x hx).symm
    have hbot : Tendsto (fun x ↦ χ (r, x)) atBot atBot := by
      apply tendsto_id.congr'
      filter_upwards [eventually_le_atBot ε] with x hx
      exact (hlo x hx).symm
    exact (hsmooth r hr).continuous.surjective htop hbot
  have hver (r : ℝ) (hr : r ∈ Ioi 0) (x : ℝ) : fderiv ℝ χ (r, x) (0, 1) ≠ 0 := by
    have hd : HasDerivAt (fun x ↦ χ (r, x)) (fderiv ℝ χ (r, x) (0, 1)) x :=
      ((hχ.contDiffAt ((isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨hr, mem_univ _⟩)).differentiableAt
        (by simp)).hasFDerivAt.comp_hasDerivAt x
          ((hasDerivAt_const x r).prodMk (hasDerivAt_id x))
    rw [← hd.deriv]
    exact ((hprop r hr).1 x).ne'
  obtain ⟨R, hR, hleft, hright⟩ :=
    exists_contDiffOn_inverse_of_bijective isOpen_Ioi hχ hbij hver
  have hRsmooth (r : ℝ) (hr : 0 < r) : ContDiff ℝ ∞ (fun x ↦ R (r, x)) :=
    contDiffOn_univ.mp (hR.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun _ _ ↦ ⟨hr, mem_univ _⟩))
  let D (r : ℝ) : Diffeomorph 𝓘(ℝ) 𝓘(ℝ) ℝ ℝ ∞ := if hr : 0 < r then
    { toEquiv :=
        { toFun := fun x ↦ χ (r, x)
          invFun := fun x ↦ R (r, x)
          left_inv := hleft r hr
          right_inv := hright r hr }
      contMDiff_toFun := (hsmooth r hr).contMDiff
      contMDiff_invFun := (hRsmooth r hr).contMDiff }
    else Diffeomorph.refl 𝓘(ℝ) ℝ ∞
  have hD (r : ℝ) (hr : 0 < r) (x : ℝ) : D r x = χ (r, x) := by simp only [D, dif_pos hr]; rfl
  have hDi (r : ℝ) (hr : 0 < r) (x : ℝ) : (D r).symm x = R (r, x) := by
    simp only [D, dif_pos hr]; rfl
  refine ⟨D, hχ.congr (fun q hq ↦ hD q.1 hq.1 q.2),
    hR.congr (fun q hq ↦ hDi q.1 hq.1 q.2), ?_, (fun r hr ↦ ?_), hD⟩
  · apply Diffeomorph.ext
    intro x
    exact (hD 1 (by norm_num) x).trans (hχone x)
  · have he : (D r : ℝ → ℝ) = fun x ↦ χ (r, x) := funext (hD r hr)
    simpa only [he] using hprop r hr

theorem exists_smooth_interval_reparametrization_diffeomorph :
    ∃ D : ℝ → Diffeomorph 𝓘(ℝ) 𝓘(ℝ) ℝ ℝ ∞,
      ContDiffOn ℝ ∞ (fun q : ℝ × ℝ ↦ D q.1 q.2) (Ioi 0 ×ˢ univ) ∧
      ContDiffOn ℝ ∞ (fun q : ℝ × ℝ ↦ (D q.1).symm q.2) (Ioi 0 ×ˢ univ) ∧
      D 1 = Diffeomorph.refl 𝓘(ℝ) ℝ ∞ ∧
      ∀ r : ℝ, 0 < r →
        (∀ x, 0 < deriv (D r) x) ∧
        BijOn (D r) (Icc 0 1) (Icc 0 r) ∧
        ∃ ε : ℝ, 0 < ε ∧ ε < 1 / 2 ∧ ε < r / 2 ∧
          (∀ x, x ≤ ε → D r x = x) ∧
          ∀ x, 1 - ε ≤ x → D r x = x + r - 1 := by
  obtain ⟨D, hD, hDi, hone, hprop, _⟩ := exists_interval_diffeomorph_with_formula
  exact ⟨D, hD, hDi, hone, hprop⟩

theorem exists_smooth_interval_diffeomorphs_uniform_ends :
    ∃ D : ℝ → Diffeomorph 𝓘(ℝ) 𝓘(ℝ) ℝ ℝ ∞,
      ContDiffOn ℝ ∞ (fun q : ℝ × ℝ ↦ D q.1 q.2) (Ioi 0 ×ˢ univ) ∧
      ContDiffOn ℝ ∞ (fun q : ℝ × ℝ ↦ (D q.1).symm q.2) (Ioi 0 ×ˢ univ) ∧
      D 1 = Diffeomorph.refl 𝓘(ℝ) ℝ ∞ ∧
      (∀ r : ℝ, 0 < r →
        (∀ x, 0 < deriv (D r) x) ∧
        BijOn (D r) (Icc 0 1) (Icc 0 r) ∧
        ∃ ε : ℝ, 0 < ε ∧ ε < 1 / 2 ∧ ε < r / 2 ∧
          (∀ x, x ≤ ε → D r x = x) ∧
          ∀ x, 1 - ε ≤ x → D r x = x + r - 1) ∧
      ∀ K : Set ℝ, IsCompact K → K ⊆ Ioi 0 →
        ∃ ε : ℝ, 0 < ε ∧ ε < 1 / 2 ∧ ∀ r ∈ K, ε < r / 2 ∧
          (∀ x, x ≤ ε → D r x = x) ∧
          ∀ x, 1 - ε ≤ x → D r x = x + r - 1 := by
  obtain ⟨D, hD, hDi, hone, hprop, hformula⟩ := exists_interval_diffeomorph_with_formula
  refine ⟨D, hD, hDi, hone, hprop, fun K hK hpos ↦ ?_⟩
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1 / 4, by norm_num, by norm_num, fun r hr ↦ (notMem_empty r hr).elim⟩
  have hw : ContinuousOn intervalWidth K := by
    apply continuousOn_id.div (continuousOn_const.mul (continuousOn_const.add continuousOn_id))
    intro r hr
    have : 0 < r := hpos hr
    change 8 * (1 + r) ≠ (0 : ℝ)
    positivity
  obtain ⟨r₀, hr₀, hmin⟩ := hK.exists_isMinOn hne hw
  have h₀ := intervalWidth_bounds (hpos hr₀)
  refine ⟨intervalWidth r₀ / 2, half_pos h₀.1, by linarith [h₀.2.1], fun r hr ↦ ?_⟩
  have hbound := intervalWidth_bounds (hpos hr)
  have hminr : intervalWidth r₀ ≤ intervalWidth r := hmin hr
  have hle : intervalWidth r₀ / 2 ≤ intervalWidth r := by linarith [h₀.1]
  refine ⟨by linarith [hbound.2.2], fun x hx ↦ ?_, fun x hx ↦ ?_⟩
  · rw [hformula r (hpos hr)]
    exact intervalChange_lower (hpos hr) (hx.trans hle)
  · rw [hformula r (hpos hr)]
    exact intervalChange_upper (hpos hr) (by linarith)

end Poincare.Analysis
