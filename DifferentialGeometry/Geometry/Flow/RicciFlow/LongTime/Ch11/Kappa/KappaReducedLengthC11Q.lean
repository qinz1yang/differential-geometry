import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Kappa.KappaSeedPatchC11Q
import DifferentialGeometry.Analysis.Calculus.Derivative.Right
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.SmallVol.WindowGlueC11V

/-!
# K4 / K5 骨架（O-CH11-KAPPA G4，后缀 `_C11Q`）

* **K5 体积解释**（`redVolume_ge_of_lowActionPatch_C11Q`）：时钟 `w` 切片上开集 `U`，
  `vol U ≥ κ₀ w³`，且 `U` 每点是非 barely admissible 极小端点、`l ≤ C` ⇒
  `Ṽ_{(t,x)}(w) ≥ κ₀ e^{−C} (4π)^{−3/2}`（照树内 `exists_test_volume_lower_of_regular_endpoint_block`
  的 `hRV` 段；树内 adapter 缺口，digest §1 K5 / §4.5）。
* **K5 装配**（`seedReducedVolumeLower_of_patch_C11Q`）：K0 patch（深度 `3r²/4`、`B(O⋆, r/20)`、
  体积 `(A⁻¹e⁻⁵⁷/512)(r/20)³`）+ K4 点 + K5a（拼接，仍为前提）⇒ `SeedReducedVolumeLower_C11Q`，
  `v_A = κ₀(A) e^{−C₅(A)} (4π)^{−3/2}`。
* **K4 ⇐ K2 + K3（极大值原理骨架）**（`boundedReducedLength_of_maxPrinciple_C11Q`）：带状
  右上支撑比较 `le_of_upper_support_band_C11Q`（树内 `le_of_upper_support` 的带状版）作用于
  `N(v) − η v`；K3 的屏障让 K2 的支撑条件在带内成立；半时钟终点 `v₁ = r/√2` 处 `M(v₁)` 被达到
  （K3 空间逃逸），极小点在 `B(O, r/10)`（`shift = 0`）且是非 barely admissible 极小（K3）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter DifferentialGeometry MeasureTheory
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal Topology

namespace GC.LongTime.Ch11

universe u

private local instance (P : OrientedThreeStage.{u}) : MeasurableSpace P.Carrier :=
  borel P.Carrier

private local instance (P : OrientedThreeStage.{u}) : BorelSpace P.Carrier := ⟨rfl⟩

/-! ## K5 体积解释 -/

private theorem exp_density_mul_clock_volume_eq_C11Q {v C κ₀ : ℝ} (hv : 0 < v) :
    Real.exp (-C - (3 / 2 : ℝ) * Real.log (v ^ 2) -
        (3 / 2 : ℝ) * Real.log (4 * Real.pi)) * (κ₀ * v ^ 3) =
      κ₀ * Real.exp (-C) * (4 * Real.pi) ^ (-(3 / 2 : ℝ)) := by
  rw [Real.exp_sub, Real.exp_sub]
  have h4 : (0 : ℝ) < 4 * Real.pi := by positivity
  have hpow : v ^ 3 = Real.exp ((3 / 2 : ℝ) * Real.log (v ^ 2)) := by
    calc
      v ^ 3 = (Real.exp (Real.log v)) ^ 3 := by rw [Real.exp_log hv]
      _ = Real.exp ((3 : ℝ) * Real.log v) := (Real.exp_nat_mul _ 3).symm
      _ = Real.exp ((3 / 2 : ℝ) * Real.log (v ^ 2)) := by
        rw [Real.log_pow]
        congr 1
        ring
  have hpow4 : (4 * Real.pi) ^ (-(3 / 2 : ℝ)) =
      (Real.exp ((3 / 2 : ℝ) * Real.log (4 * Real.pi)))⁻¹ := by
    rw [Real.rpow_def_of_pos h4, ← Real.exp_neg]
    ring_nf
  rw [hpow, hpow4]
  have he1 := (Real.exp_pos ((3 / 2 : ℝ) * Real.log (v ^ 2))).ne'
  have he2 := (Real.exp_pos ((3 / 2 : ℝ) * Real.log (4 * Real.pi))).ne'
  field_simp

/-- **K5 体积解释**：时钟 `w` 切片上的开集 `U`（`vol U ≥ κ₀ w³`），每点是非 barely admissible 极小
端点且 `𝓛 ≤ 2Cw`（`l ≤ C`）⇒ `Ṽ_{(t,x)}(w) ≥ κ₀ e^{−C} (4π)^{−3/2}`。 -/
theorem redVolume_ge_of_lowActionPatch_C11Q (R : RetainedCoreHistory.{u}) {Bf : ℝ}
    (hBf : ScalarFloor_C11Q R Bf) (t : Icc (0 : ℝ) R.toHistory.horizon)
    (x : (R.toHistory.stageAt t).Carrier) {w κ₀ C : ℝ} (hw : 0 < w)
    (hle : R.toHistory.activeStage (clockSlice_C11Q R t w) ≤ R.toHistory.activeStage t)
    (U : Set (R.stage (R.toHistory.activeStage (clockSlice_C11Q R t w))).Carrier)
    (hU : IsOpen U)
    (hvol : ENNReal.ofReal (κ₀ * w ^ 3) ≤
      riemannianVolumeMeasure ThreeModel
        (R.stage (R.toHistory.activeStage (clockSlice_C11Q R t w))).Carrier
        (R.toHistory.stageMetric (R.toHistory.activeStage (clockSlice_C11Q R t w))
          ((t : ℝ) - w ^ 2)) U)
    (hblock : ∀ q ∈ U,
      q ∈ R.toHistory.regularMinimizerEndpoints (R.toHistory.activeStage (clockSlice_C11Q R t w))
        (R.toHistory.activeStage t) hle t Bf w x ∧
      R.toHistory.regularizedCost (R.toHistory.activeStage (clockSlice_C11Q R t w))
        (R.toHistory.activeStage t) hle t Bf 0 w x q ≤ ((2 * C * w : ℝ) : WithTop ℝ)) :
    ENNReal.ofReal (κ₀ * Real.exp (-C) * (4 * Real.pi) ^ (-(3 / 2 : ℝ))) ≤
      R.reducedVolume (R.toHistory.activeStage t) x t w := by
  rw [RetainedCoreHistory.reducedVolume_eq_of_scalar_lower_bound_le hBf
    (R.toHistory.activeStage t) x t w le_rfl hle]
  set densityLower := ENNReal.ofReal (Real.exp
    (-C - (3 / 2 : ℝ) * Real.log (w ^ 2) -
      (3 / 2 : ℝ) * Real.log (4 * Real.pi))) with hdensityLower
  have hdens : ∀ q ∈ U, densityLower ≤
      R.toHistory.regularizedDensity _ (R.toHistory.activeStage t) hle t Bf w x q := by
    intro q hq
    have hcost := (hblock q hq).2
    have hne : R.toHistory.regularizedCost _ (R.toHistory.activeStage t) hle t Bf 0 w x q ≠ ⊤ :=
      ne_top_of_le_ne_top WithTop.coe_ne_top hcost
    obtain ⟨A, hA⟩ := WithTop.ne_top_iff_exists.mp hne
    rw [R.toHistory.regularizedDensity_eq_exp_of_regularizedCost_eq
      _ _ hle t Bf hw x q hA.symm, hdensityLower]
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have hAle : A ≤ 2 * C * w := by
      rw [← hA] at hcost
      exact WithTop.coe_le_coe.mp hcost
    have hdiv : A / (2 * w) ≤ C := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    have hneg : -A / (2 * w) = -(A / (2 * w)) := neg_div _ _
    linarith
  have hsub :
      U ⊆ R.toHistory.regularMinimizerEndpoints _ (R.toHistory.activeStage t) hle t Bf w x :=
    fun q hq => (hblock q hq).1
  calc
    ENNReal.ofReal (κ₀ * Real.exp (-C) * (4 * Real.pi) ^ (-(3 / 2 : ℝ))) =
        densityLower * ENNReal.ofReal (κ₀ * w ^ 3) := by
      rw [hdensityLower, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
        exp_density_mul_clock_volume_eq_C11Q hw]
    _ ≤ densityLower * riemannianVolumeMeasure ThreeModel
        (R.stage (R.toHistory.activeStage (clockSlice_C11Q R t w))).Carrier
        (R.toHistory.stageMetric (R.toHistory.activeStage (clockSlice_C11Q R t w))
          ((t : ℝ) - w ^ 2)) U := mul_le_mul' le_rfl hvol
    _ = ∫⁻ _ in U, densityLower ∂riemannianVolumeMeasure ThreeModel
        (R.stage (R.toHistory.activeStage (clockSlice_C11Q R t w))).Carrier
        (R.toHistory.stageMetric (R.toHistory.activeStage (clockSlice_C11Q R t w))
          ((t : ℝ) - w ^ 2)) := (setLIntegral_const U densityLower).symm
    _ ≤ ∫⁻ q in U, R.toHistory.regularizedDensity _ (R.toHistory.activeStage t) hle t Bf w x q
        ∂riemannianVolumeMeasure ThreeModel
        (R.stage (R.toHistory.activeStage (clockSlice_C11Q R t w))).Carrier
        (R.toHistory.stageMetric (R.toHistory.activeStage (clockSlice_C11Q R t w))
          ((t : ℝ) - w ^ 2)) :=
      lintegral_mono_ae ((ae_restrict_mem hU.measurableSet).mono fun q hq => hdens q hq)
    _ ≤ _ := lintegral_mono_set hsub

/-- K0 patch 的体积系数换到时钟 `w = √(3/4) r`：`κ₀(A) = (A⁻¹e⁻⁵⁷/512)(1/20)³/(√(3/4))³`。 -/
def seedPatchKappa₀_C11Q (A : ℝ) : ℝ :=
  A⁻¹ * Real.exp (-57) / 512 * (1 / 20) ^ 3 / Real.sqrt (3 / 4) ^ 3

/-- K5 的 `v_A = κ₀(A) e^{−C₅(A)} (4π)^{−3/2}`。 -/
def seedVolumeLowerConst_C11Q (C₅ : ℝ → ℝ) (A : ℝ) : ℝ :=
  seedPatchKappa₀_C11Q A * Real.exp (-C₅ A) * (4 * Real.pi) ^ (-(3 / 2 : ℝ))

/-- **K5 装配**：K0（patch）+ K4（低作用量点）+ K5a（拼接：patch 上处处 `l ≤ C₅`）+ 体积解释
⇒ `SeedReducedVolumeLower_C11Q`（`v_A = κ₀(A) e^{−C₅(A)} (4π)^{−3/2}`，深度 `3r²/4`）。 -/
theorem seedReducedVolumeLower_of_patch_C11Q {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ} {nr C₄ C₅ : ℝ → ℝ}
    (hK0 : SeedPatchTransport_C11Q.{u})
    (hK4 : BoundedReducedLengthNearSeed_C11Q F δ α nr C₄)
    (hK5a : SeedPatchLowAction_C11Q F δ α nr C₄ C₅) :
    SeedReducedVolumeLower_C11Q F δ α nr (seedVolumeLowerConst_C11Q C₅) := by
  intro A hA
  refine ⟨by unfold seedVolumeLowerConst_C11Q seedPatchKappa₀_C11Q; positivity, ?_⟩
  intro n H t p r hr hacc hsmall hvol x hx ϱ₀ hϱ₀ hball₀
  have hr0 : 0 < r := hsmall.1
  obtain ⟨b, hbt, hb, htraces⟩ := hsmall.2
  have hp : p ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p r := by
    change riemannianEDistOf _ p p < ENNReal.ofReal r
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr hr0
  obtain ⟨seedTrace, -⟩ := htraces p hp
  obtain ⟨Bf, -, hfl⟩ := (F.tower.history n).exists_stageMetric_scalar_lower_bound
  have hBf : ScalarFloor_C11Q (F.tower.history n) Bf := hfl
  set w : ℝ := Real.sqrt (3 / 4) * r with hwdef
  have hs34 : 0 < Real.sqrt (3 / 4) := Real.sqrt_pos.2 (by norm_num)
  have hw : 0 < w := mul_pos hs34 hr0
  have hw2 : w ^ 2 = 3 / 4 * r ^ 2 := by
    rw [hwdef, mul_pow, Real.sq_sqrt (by norm_num)]
  have ht0 : (0 : ℝ) ≤ (t : ℝ) - w ^ 2 := by rw [hw2]; nlinarith
  have htH : (t : ℝ) - w ^ 2 ≤ H.horizon := by
    have := t.2.2
    nlinarith [sq_nonneg w]
  set s := clockSlice_C11Q (F.tower.history n) t w with hsdef
  have hsval : (s : ℝ) = (t : ℝ) - w ^ 2 := by
    rw [hsdef, clockSlice_C11Q, Set.projIcc_of_mem _ ⟨ht0, htH⟩]
  have hbs : b ≤ s := by
    change (b : ℝ) ≤ (s : ℝ)
    rw [hsval, hb, hw2]
    nlinarith
  have hst : s ≤ t := by
    change (s : ℝ) ≤ (t : ℝ)
    rw [hsval]
    nlinarith [sq_nonneg w]
  have hs : (s : ℝ) = (t : ℝ) - 3 * r ^ 2 / 4 := by rw [hsval, hw2]; ring
  let s₁ : Icc (0 : ℝ) H.horizon :=
    ⟨(t : ℝ) - r ^ 2 / 2, ⟨by nlinarith, by have := t.2.2; nlinarith [sq_nonneg r]⟩⟩
  have hbs₁ : b ≤ s₁ := by
    change (b : ℝ) ≤ (t : ℝ) - r ^ 2 / 2
    rw [hb]
    nlinarith
  have hs₁t : s₁ ≤ t := by
    change (t : ℝ) - r ^ 2 / 2 ≤ (t : ℝ)
    nlinarith [sq_nonneg r]
  have hpatch := hK0 H t p r A⁻¹ hr hsmall hvol b hbt hb seedTrace s hbs hst hs
  have hq₁ := hK4 A hA n t p r hr hacc hsmall hvol b hbt hb seedTrace x hx ϱ₀ hϱ₀ hball₀ Bf hBf
    s₁ hbs₁ hs₁t rfl
  have hlow := hK5a A hA n t p r hr hacc hsmall hvol b hbt hb seedTrace x hx ϱ₀ hϱ₀ hball₀ Bf
    hBf s₁ hbs₁ hs₁t rfl s hbs hst hs hpatch hq₁
  set O := seedTrace.point (H.activeStage s) (H.activeStage_mono hbs) (H.activeStage_mono hst)
    with hOdef
  have hmet : H.stageMetric (H.activeStage s) (s : ℝ) =
      H.stageMetric (H.activeStage s) ((t : ℝ) - w ^ 2) := by rw [hsval]
  have hsq : Real.sqrt ((t : ℝ) - (s : ℝ)) = w := by
    rw [hsval, show (t : ℝ) - ((t : ℝ) - w ^ 2) = w ^ 2 by ring, Real.sqrt_sq hw.le]
  let U := riemannianBallOf (H.stageMetric (H.activeStage s) ((t : ℝ) - w ^ 2)) O (r / 20)
  have hU : IsOpen U :=
    isOpen_lt (Geometry.Riemannian.continuous_riemannianEDist _ O) continuous_const
  have hpv := hpatch.2.1 (r / 20) (by positivity) (by linarith)
  rw [hmet] at hpv
  have hκ : seedPatchKappa₀_C11Q A * w ^ 3 = A⁻¹ * Real.exp (-57) / 512 * (r / 20) ^ 3 := by
    unfold seedPatchKappa₀_C11Q
    rw [hwdef]
    field_simp
  have hvolU : ENNReal.ofReal (seedPatchKappa₀_C11Q A * w ^ 3) ≤
      riemannianVolumeMeasure ThreeModel (H.stage (H.activeStage s)).Carrier
        (H.stageMetric (H.activeStage s) ((t : ℝ) - w ^ 2)) U := by
    rw [hκ]
    exact hpv
  have hblock : ∀ q ∈ U,
      q ∈ H.regularMinimizerEndpoints (H.activeStage s) (H.activeStage t)
        (H.activeStage_mono hst) t Bf w x ∧
      H.regularizedCost (H.activeStage s) (H.activeStage t) (H.activeStage_mono hst) t Bf 0 w x
        q ≤ ((2 * C₅ A * w : ℝ) : WithTop ℝ) := by
    intro q hq
    have hq' : q ∈ riemannianBallOf (H.stageMetric (H.activeStage s) s) O (r / 20) := by
      rw [hmet]
      exact hq
    obtain ⟨⟨hle', hmem⟩, hcost⟩ := hlow q hq'
    unfold sliceCost_C11Q at hcost
    rw [dite_eq_left (H.activeStage_mono hst)] at hcost
    rw [hsq] at hmem hcost
    exact ⟨hmem, hcost⟩
  have hfinal := redVolume_ge_of_lowActionPatch_C11Q (F.tower.history n) hBf t x hw
    (H.activeStage_mono hst) U hU hvolU hblock
  unfold redVolTau_C11Q
  rw [show 3 / 4 * r ^ 2 = w ^ 2 from hw2.symm, Real.sqrt_sq hw.le]
  exact hfinal

/-! ## K4 ⇐ K2 + K3：极大值原理骨架 -/

/-- **带状右上支撑比较**（树内 `le_of_upper_support` 的带状版，右导数）：`f` 在 `[a, b]` 连续、
`f a ≤ c`，且只在 `c < f t < c + 1` 处有右上支撑、导数 `< 0` ⇒ `f ≤ c`。（证明只在 `f = c + δ`，
`δ < 1` 的首次越界点用支撑。） -/
theorem le_of_upper_support_band_C11Q {f : ℝ → ℝ} {a b c : ℝ}
    (hf : ContinuousOn f (Icc a b)) (ha : f a ≤ c)
    (hsupport : ∀ t ∈ Ico a b, c < f t → f t < c + 1 →
      ∃ φ : ℝ → ℝ, ∃ d : ℝ, φ t = f t ∧ f ≤ᶠ[𝓝[>] t] φ ∧
        HasDerivWithinAt φ d (Ioi t) t ∧ d < 0) :
    ∀ t ∈ Icc a b, f t ≤ c := by
  intro t ht
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  set δ' := min δ (1 / 2) with hδ'
  have hδ'pos : 0 < δ' := lt_min hδ (by norm_num)
  have hδ'1 : δ' < 1 := (min_le_right δ (1 / 2)).trans_lt (by norm_num)
  suffices h : f t ≤ c + δ' from h.trans (by linarith [min_le_left δ (1 / 2)])
  let S : Set ℝ := {r | f r ≤ c + δ'}
  have hs_closed : IsClosed (S ∩ Icc a b) := by
    have hconst : ContinuousOn (fun _ : ℝ => c + δ') (Icc a b) := continuousOn_const
    change IsClosed {x | f x ≤ c + δ' ∧ x ∈ Icc a b}
    simpa only [and_comm] using isClosed_Icc.isClosed_le hf hconst
  have ha_s : a ∈ S := by
    change f a ≤ c + δ'
    linarith
  have hs_all : Icc a b ⊆ S := by
    apply hs_closed.Icc_subset_of_forall_exists_gt ha_s
    rintro x ⟨hx_s, hx⟩ y hxy
    change f x ≤ c + δ' at hx_s
    rcases hx_s.lt_or_eq with hx_lt | hx_eq
    · have hnear : ∀ᶠ z in 𝓝[Icc a b] x, f z < c + δ' :=
        hf x (Ico_subset_Icc_self hx) (Iio_mem_nhds hx_lt)
      have hright : ∀ᶠ z in 𝓝[>] x, f z < c + δ' :=
        nhdsWithin_le_of_mem (Icc_mem_nhdsGT_of_mem hx) hnear
      obtain ⟨z, hz_lt, hz_mem⟩ := (hright.and (Ioc_mem_nhdsGT (show x < y from hxy))).exists
      exact ⟨z, ⟨show z ∈ S from hz_lt.le, hz_mem⟩⟩
    · obtain ⟨φ, d, hφ_eq, hupper, hφ_deriv, hd_neg⟩ :=
        hsupport x hx (by rw [hx_eq]; linarith) (by rw [hx_eq]; linarith)
      have hslope : ∀ᶠ z in 𝓝[>] x, slope φ x z < 0 :=
        ((hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl x)).mp hφ_deriv).eventually_lt_const
          hd_neg
      have hφ_lt : ∀ᶠ z in 𝓝[>] x, φ z < φ x := by
        filter_upwards [hslope, self_mem_nhdsWithin] with z hz_slope hxz
        rw [slope_def_field] at hz_slope
        have hdiff : φ z - φ x < 0 := by
          simpa only [zero_mul] using (div_lt_iff₀ (sub_pos.mpr hxz)).mp hz_slope
        exact sub_lt_zero.mp hdiff
      have hright : ∀ᶠ z in 𝓝[>] x, f z < c + δ' := by
        filter_upwards [hupper, hφ_lt] with z hle hlt
        calc
          f z ≤ φ z := hle
          _ < φ x := hlt
          _ = c + δ' := hφ_eq.trans hx_eq
      obtain ⟨z, hz_lt, hz_mem⟩ := (hright.and (Ioc_mem_nhdsGT (show x < y from hxy))).exists
      exact ⟨z, ⟨show z ∈ S from hz_lt.le, hz_mem⟩⟩
  exact hs_all ht

/-- 时钟切片的取值：`0 ≤ t − v²` ⇒ `clockSlice t v = t − v²`。 -/
theorem clockSlice_val_C11Q (R : RetainedCoreHistory.{u}) (t : Icc (0 : ℝ) R.toHistory.horizon)
    {v : ℝ} (h : 0 ≤ (t : ℝ) - v ^ 2) : (clockSlice_C11Q R t v : ℝ) = (t : ℝ) - v ^ 2 := by
  have htH : (t : ℝ) - v ^ 2 ≤ R.horizon := by
    have := t.2.2
    change (t : ℝ) ≤ R.horizon at this
    nlinarith [sq_nonneg v]
  rw [clockSlice_C11Q, Set.projIcc_of_mem _ ⟨h, htH⟩]

/-- cutoff 值有限时的拆解：`q` 在截断区内，且 `𝓛(q) = L` 满足 `2vL + 2rv ≤ max m 0`（`φ ≥ 1`）。 -/
theorem cutoffValue_spec_C11Q (R : RetainedCoreHistory.{u}) {Bf r A : ℝ}
    {t b : Icc (0 : ℝ) R.toHistory.horizon} (hbt : b ≤ t) {p : (R.toHistory.stageAt t).Carrier}
    (seedTrace : BackwardPointTrace R.toHistory (R.toHistory.activeStage b)
      (R.toHistory.activeStage t) (R.toHistory.activeStage_mono hbt) p)
    (x : (R.toHistory.stageAt t).Carrier) {v m : ℝ} (hr : 0 < r)
    (h : b ≤ clockSlice_C11Q R t v ∧ clockSlice_C11Q R t v ≤ t)
    (q : (R.toHistory.stageAt (clockSlice_C11Q R t v)).Carrier)
    (hq : cutoffValue_C11Q R Bf r A hbt seedTrace x v q = (m : WithTop ℝ)) :
    riemannianEDistOf (R.toHistory.stageMetric (R.toHistory.activeStage (clockSlice_C11Q R t v))
        ((t : ℝ) - v ^ 2))
      (seedTrace.point (R.toHistory.activeStage (clockSlice_C11Q R t v))
        (R.toHistory.activeStage_mono h.1) (R.toHistory.activeStage_mono h.2)) q <
      ENNReal.ofReal (r * (A * (1 - 2 * v ^ 2 / r ^ 2) + 1 / 10)) ∧
    ∃ L : ℝ, R.toHistory.regularizedCost (R.toHistory.activeStage (clockSlice_C11Q R t v))
        (R.toHistory.activeStage t) (R.toHistory.activeStage_mono h.2) t Bf 0 v x q = L ∧
      2 * v * L + 2 * r * v ≤ max m 0 := by
  unfold cutoffValue_C11Q at hq
  rw [dite_eq_left h] at hq
  unfold ObservedHistory.physicalWeightedCost at hq
  dsimp only at hq
  split_ifs at hq with hreg
  · refine ⟨hreg, ?_⟩
    by_cases hne : R.toHistory.regularizedCost (R.toHistory.activeStage (clockSlice_C11Q R t v))
        (R.toHistory.activeStage t) (R.toHistory.activeStage_mono h.2) t Bf 0 v x q = ⊤
    · rw [hne, WithTop.map_top] at hq
      exact absurd hq WithTop.top_ne_coe
    · obtain ⟨L, hL⟩ := WithTop.ne_top_iff_exists.mp hne
      refine ⟨L, hL.symm, ?_⟩
      rw [← hL, WithTop.map_coe, WithTop.coe_inj] at hq
      set arg := (riemannianEDistOf (R.toHistory.stageMetric
          (R.toHistory.activeStage (clockSlice_C11Q R t v)) ((t : ℝ) - v ^ 2))
          (seedTrace.point (R.toHistory.activeStage (clockSlice_C11Q R t v))
            (R.toHistory.activeStage_mono h.1) (R.toHistory.activeStage_mono h.2)) q).toReal / r -
          A * (1 - 2 * v ^ 2 / r ^ 2) with harg
      have harg_lt : arg < 1 / 10 := by
        have htr := ENNReal.toReal_lt_of_lt_ofReal hreg
        rw [harg, sub_lt_iff_lt_add, div_lt_iff₀ hr]
        nlinarith
      have hφ := DifferentialGeometry.Analysis.SingularBarrier.one_le harg_lt
      rcases le_or_gt 0 (2 * v * L + 2 * r * v) with hX | hX
      · calc 2 * v * L + 2 * r * v
            ≤ DifferentialGeometry.Analysis.SingularBarrier.value arg *
              (2 * v * L + 2 * r * v) := le_mul_of_one_le_left hX hφ
          _ = m := hq
          _ ≤ max m 0 := le_max_left _ _
      · exact hX.le.trans (le_max_right _ _)
  · exact absurd hq WithTop.top_ne_coe

/-- `M(v) = ↑m` ⇒ `m = N(v) · 2rv · e^{Cv²/r² + 32v/r}`。 -/
theorem cutoffMin_eq_normalized_C11Q (R : RetainedCoreHistory.{u}) {Bf r A C : ℝ}
    {t b : Icc (0 : ℝ) R.toHistory.horizon} (hbt : b ≤ t) {p : (R.toHistory.stageAt t).Carrier}
    (seedTrace : BackwardPointTrace R.toHistory (R.toHistory.activeStage b)
      (R.toHistory.activeStage t) (R.toHistory.activeStage_mono hbt) p)
    (x : (R.toHistory.stageAt t).Carrier) {v m : ℝ} (hr : 0 < r) (hv : 0 < v)
    (hM : cutoffMin_C11Q R Bf r A hbt seedTrace x v = (m : WithTop ℝ)) :
    m = cutoffMinNormalized_C11Q R Bf r A C hbt seedTrace x v * (2 * r * v) *
      Real.exp (C * v ^ 2 / r ^ 2 + 32 * v / r) := by
  unfold cutoffMinNormalized_C11Q
  rw [hM, WithTop.untopD_coe]
  have h2 : 0 < 2 * r * v := by positivity
  rw [Real.exp_neg]
  field_simp

/-- K4 常数：`C₄(A) = (4 e^{C₂(A)/2 + 32/√2} − 1)/√2`。 -/
def boundedLengthConst_C11Q (C₂ : ℝ → ℝ) (A : ℝ) : ℝ :=
  (4 * Real.exp (C₂ A / 2 + 32 / Real.sqrt 2) - 1) / Real.sqrt 2

/-- **K4 ⇐ K2 + K3（极大值原理）**：屏障 `Λ_A ≥ 4 e^{C₂/2 + 32/√2}`（K3 的参数小性要压过 K2 的增长；
`C₂ ≥ 0`）。对 `f(v) = N(v) − η(v − v₀)`（`η = 1/(2v₁)`，`v₁ = r/√2`，`N(v₀) ≤ 2` 由 K2 初值）用
带状右上支撑比较：带内 `N < 4` ⇒ `M(v) < Λ·2rv` ⇒ K3 给可达极小且 regular ⇒ K2 的支撑导数
`≤ η/2` ⇒ `f` 的支撑导数 `< 0`。故 `N(v₁) ≤ 3`，`M(v₁) < (7/2)e^{…}·2rv₁`，再由 K3 取极小点：
截断区（`shift = 0`）⇒ `q ∈ B(O₁, r/10)`；`φ ≥ 1` ⇒ `𝓛(q) ≤ (4e^{…} − 1) r`，即 `l ≤ C₄(A)`。 -/
theorem boundedReducedLength_of_maxPrinciple_C11Q {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ} {nr C₂ Λ : ℝ → ℝ}
    (hC₂ : ∀ A, 0 < A → 0 ≤ C₂ A)
    (hΛ : ∀ A, 0 < A → 4 * Real.exp (C₂ A / 2 + 32 / Real.sqrt 2) ≤ Λ A)
    (hK2 : LocalizedLCutoffInequality_C11Q F nr C₂)
    (hK3 : SurgeryActionBarrier_C11Q F δ α nr Λ) :
    BoundedReducedLengthNearSeed_C11Q F δ α nr (boundedLengthConst_C11Q C₂) := by
  intro A hA n R H t p r hr hacc hsmall hvol b hbt hb seedTrace x hx ϱ₀ hϱ₀ hball₀ Bf hBf s₁ hbs₁
    hs₁t hs₁
  have hr0 : 0 < r := hsmall.1
  have hs2 : 0 < Real.sqrt 2 := by positivity
  have hss : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  set v₁ : ℝ := r / Real.sqrt 2 with hv₁
  have hv₁pos : 0 < v₁ := div_pos hr0 hs2
  have hv₁sq : v₁ ^ 2 = r ^ 2 / 2 := by
    rw [hv₁, div_pow, Real.sq_sqrt (by norm_num)]
  obtain ⟨hfin, hcont, hinit, hdiff⟩ :=
    hK2 A hA n t p r hr hsmall hvol b hbt hb seedTrace x hx ϱ₀ hϱ₀ hball₀ Bf hBf
  have hK3' := hK3 A hA n t p r hr hacc hsmall hvol b hbt hb seedTrace x hx ϱ₀ hϱ₀ hball₀ Bf hBf
  set E₁ : ℝ := C₂ A / 2 + 32 / Real.sqrt 2 with hE₁
  have hΛA := hΛ A hA
  have hΛpos : 0 < Λ A := lt_of_lt_of_le (by positivity) hΛA
  set N := cutoffMinNormalized_C11Q R Bf r A (C₂ A) hbt seedTrace x with hN
  -- 时钟事实
  have hclock : ∀ v, 0 < v → v ≤ v₁ →
      (clockSlice_C11Q R t v : ℝ) = (t : ℝ) - v ^ 2 ∧
      b ≤ clockSlice_C11Q R t v ∧ clockSlice_C11Q R t v ≤ t := by
    intro v hv hvle
    have hv2 : v ^ 2 ≤ r ^ 2 / 2 := by
      rw [← hv₁sq]
      exact pow_le_pow_left₀ hv.le hvle 2
    have hval := clockSlice_val_C11Q R t (v := v) (by nlinarith)
    refine ⟨hval, ?_, ?_⟩
    · change (b : ℝ) ≤ (clockSlice_C11Q R t v : ℝ)
      rw [hval, hb]
      nlinarith
    · change (clockSlice_C11Q R t v : ℝ) ≤ (t : ℝ)
      rw [hval]
      nlinarith [sq_nonneg v]
  have hsqrt : ∀ v, 0 < v → v ≤ v₁ →
      Real.sqrt ((t : ℝ) - (clockSlice_C11Q R t v : ℝ)) = v := by
    intro v hv hvle
    rw [(hclock v hv hvle).1, show (t : ℝ) - ((t : ℝ) - v ^ 2) = v ^ 2 by ring,
      Real.sqrt_sq hv.le]
  have hE : ∀ v, 0 < v → v ≤ v₁ → C₂ A * v ^ 2 / r ^ 2 + 32 * v / r ≤ E₁ := by
    intro v hv hvle
    have hv2 : v ^ 2 / r ^ 2 ≤ 1 / 2 := by
      rw [div_le_iff₀ (by positivity)]
      have := pow_le_pow_left₀ hv.le hvle 2
      rw [hv₁sq] at this
      linarith
    have hvr : v / r ≤ 1 / Real.sqrt 2 := by
      rw [div_le_iff₀ hr0]
      calc v ≤ v₁ := hvle
        _ = 1 / Real.sqrt 2 * r := by rw [hv₁]; ring
    have h1 : C₂ A * v ^ 2 / r ^ 2 ≤ C₂ A / 2 := by
      rw [mul_div_assoc]
      nlinarith [hC₂ A hA]
    have h2 : 32 * v / r ≤ 32 / Real.sqrt 2 := by
      rw [mul_div_assoc, div_eq_mul_one_div 32 (Real.sqrt 2)]
      nlinarith
    rw [hE₁]
    linarith
  -- `N < K` ⇒ `M = ↑m`，`m < K e^{E₁} · 2rv`
  have hbelow : ∀ v, 0 < v → v ≤ v₁ → ∀ K : ℝ, 0 < K → N v < K →
      ∃ m : ℝ, cutoffMin_C11Q R Bf r A hbt seedTrace x v = (m : WithTop ℝ) ∧
        m < K * Real.exp E₁ * (2 * r * v) := by
    intro v hv hvle K hK hNv
    have hfin' := hfin v ⟨hv, hvle⟩
    obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hfin'.ne
    refine ⟨m, hm.symm, ?_⟩
    have heq := cutoffMin_eq_normalized_C11Q R (C := C₂ A) hbt seedTrace x hr0 hv hm.symm
    rw [heq]
    have hpos : 0 < 2 * r * v * Real.exp (C₂ A * v ^ 2 / r ^ 2 + 32 * v / r) := by positivity
    have hexp : Real.exp (C₂ A * v ^ 2 / r ^ 2 + 32 * v / r) ≤ Real.exp E₁ :=
      Real.exp_le_exp.mpr (hE v hv hvle)
    calc N v * (2 * r * v) * Real.exp (C₂ A * v ^ 2 / r ^ 2 + 32 * v / r)
        = N v * (2 * r * v * Real.exp (C₂ A * v ^ 2 / r ^ 2 + 32 * v / r)) := by ring
      _ < K * (2 * r * v * Real.exp (C₂ A * v ^ 2 / r ^ 2 + 32 * v / r)) :=
        mul_lt_mul_of_pos_right hNv hpos
      _ ≤ K * (2 * r * v * Real.exp E₁) := by gcongr
      _ = K * Real.exp E₁ * (2 * r * v) := by ring
  -- 屏障下：可达极小、regular、截断区、作用量界
  have hattain : ∀ v, 0 < v → v ≤ v₁ → ∀ m : ℝ,
      cutoffMin_C11Q R Bf r A hbt seedTrace x v = (m : WithTop ℝ) →
      m < Λ A * (2 * r * v) →
      ∃ (h : b ≤ clockSlice_C11Q R t v ∧ clockSlice_C11Q R t v ≤ t)
        (q : (H.stageAt (clockSlice_C11Q R t v)).Carrier),
        cutoffValue_C11Q R Bf r A hbt seedTrace x v q =
          cutoffMin_C11Q R Bf r A hbt seedTrace x v ∧
        IsRegularMinimizerEndpoint_C11Q R Bf t (clockSlice_C11Q R t v) x q ∧
        riemannianEDistOf (H.stageMetric (H.activeStage (clockSlice_C11Q R t v))
            ((t : ℝ) - v ^ 2))
          (seedTrace.point (H.activeStage (clockSlice_C11Q R t v))
            (H.activeStage_mono h.1) (H.activeStage_mono h.2)) q <
          ENNReal.ofReal (r * (A * (1 - 2 * v ^ 2 / r ^ 2) + 1 / 10)) ∧
        ∃ L : ℝ, sliceCost_C11Q R Bf t (clockSlice_C11Q R t v) x q = L ∧
          2 * v * L + 2 * r * v ≤ max m 0 := by
    intro v hv hvle m hM hm
    obtain ⟨-, hmem1, hmem2⟩ := hclock v hv hvle
    obtain ⟨q, hq⟩ := (hK3' v ⟨hv, hvle⟩).2 (by rw [hM]; exact WithTop.coe_lt_coe.mpr hm)
    obtain ⟨hreg, L, hL, hX⟩ :=
      cutoffValue_spec_C11Q R hbt seedTrace x hr0 ⟨hmem1, hmem2⟩ q (hq.trans hM)
    have hcostL : sliceCost_C11Q R Bf t (clockSlice_C11Q R t v) x q = L := by
      unfold sliceCost_C11Q
      rw [dite_eq_left (H.activeStage_mono hmem2), hsqrt v hv hvle]
      exact hL
    have hLbound : L ≤ (Λ A - 1) * r := by
      have hmax : max m 0 < Λ A * (2 * r * v) := max_lt hm (by positivity)
      have h2v : 0 < 2 * v := by positivity
      nlinarith
    have hregq : IsRegularMinimizerEndpoint_C11Q R Bf t (clockSlice_C11Q R t v) x q :=
      (hK3' v ⟨hv, hvle⟩).1 q (by rw [hcostL]; exact WithTop.coe_le_coe.mpr hLbound)
    exact ⟨⟨hmem1, hmem2⟩, q, hq, hregq, hreg, L, hcostL, hX⟩
  -- 初值
  obtain ⟨v₀, ⟨hv₀pos, hv₀lt⟩, hNv₀⟩ := hinit 1 one_pos
  have hv₀lt' : v₀ < v₁ := hv₀lt
  set η : ℝ := 1 / (2 * v₁) with hη
  have hηpos : 0 < η := by positivity
  have hηv : η * v₁ = 1 / 2 := by rw [hη]; field_simp
  -- 带状比较
  have hband := le_of_upper_support_band_C11Q (f := fun v => N v - η * (v - v₀))
    (a := v₀) (b := v₁) (c := N v₀)
    ((hcont.mono fun z hz => ⟨hv₀pos.trans_le hz.1, hz.2⟩).sub
      (continuousOn_const.mul (continuousOn_id.sub continuousOn_const)))
    (by simp)
    (by
      intro t' ht' _ hhi
      have ht'pos : 0 < t' := hv₀pos.trans_le ht'.1
      have ht'le : t' ≤ v₁ := ht'.2.le
      have hNt' : N t' < 4 := by
        have h1 : η * (t' - v₀) ≤ 1 / 2 := by
          rw [← hηv]
          exact mul_le_mul_of_nonneg_left (by linarith) hηpos.le
        change N t' - η * (t' - v₀) < N v₀ + 1 at hhi
        linarith
      obtain ⟨m, hM, hm⟩ := hbelow t' ht'pos ht'le 4 (by norm_num) hNt'
      have hmΛ : m < Λ A * (2 * r * t') :=
        hm.trans_le (mul_le_mul_of_nonneg_right hΛA (by positivity))
      obtain ⟨_, q, hq, hqreg, -⟩ := hattain t' ht'pos ht'le m hM hmΛ
      obtain ⟨ψ, d, hψ, hNψ, hψd, hdε⟩ :=
        hdiff t' ⟨ht'pos, ht'.2⟩ ⟨q, hq, hqreg⟩ (η / 2) (by positivity)
      refine ⟨fun z => ψ z - η * (z - v₀), d - η * 1, by simp only [hψ], ?_, ?_, by linarith⟩
      · filter_upwards [hNψ] with z hz
        linarith
      · exact hψd.sub (((hasDerivWithinAt_id t' (Ioi t')).sub_const v₀).const_mul η))
  have hNv₁ : N v₁ < 7 / 2 := by
    have h := hband v₁ ⟨hv₀lt'.le, le_rfl⟩
    change N v₁ - η * (v₁ - v₀) ≤ N v₀ at h
    have h1 : η * (v₁ - v₀) ≤ 1 / 2 := by
      rw [← hηv]
      exact mul_le_mul_of_nonneg_left (by linarith) hηpos.le
    linarith
  obtain ⟨m₁, hM₁, hm₁⟩ := hbelow v₁ hv₁pos le_rfl (7 / 2) (by norm_num) hNv₁
  have hm₁Λ : m₁ < Λ A * (2 * r * v₁) := by
    refine hm₁.trans_le (mul_le_mul_of_nonneg_right ?_ (by positivity))
    have := Real.exp_pos E₁
    linarith
  obtain ⟨hmem, q, -, hqreg, hreg, L, hL, hX⟩ := hattain v₁ hv₁pos le_rfl m₁ hM₁ hm₁Λ
  -- 搬到 `s₁`
  have hval₁ := (hclock v₁ hv₁pos le_rfl).1
  have hs₁eq : clockSlice_C11Q R t v₁ = s₁ := Subtype.ext (by rw [hval₁, hs₁, hv₁sq])
  subst hs₁eq
  refine ⟨q, ?_, hqreg, ?_⟩
  · change riemannianEDistOf _ _ q < ENNReal.ofReal (r / 10)
    have hrad : r * (A * (1 - 2 * v₁ ^ 2 / r ^ 2) + 1 / 10) = r / 10 := by
      rw [hv₁sq]
      field_simp
      ring
    rw [hrad, ← hval₁] at hreg
    exact hreg
  · rw [hL, hsqrt v₁ hv₁pos le_rfl]
    refine WithTop.coe_le_coe.mpr ?_
    have hmax : max m₁ 0 ≤ 7 / 2 * Real.exp E₁ * (2 * r * v₁) :=
      max_le hm₁.le (by positivity)
    have hL' : L ≤ (4 * Real.exp E₁ - 1) * r := by
      have h2v : 0 < 2 * v₁ := by positivity
      have her : 0 < Real.exp E₁ * r := mul_pos (Real.exp_pos E₁) hr0
      have h1 : 2 * v₁ * L ≤ 2 * v₁ * ((7 / 2 * Real.exp E₁ - 1) * r) := by linarith
      have h2 := le_of_mul_le_mul_left h1 h2v
      linarith
    have hconst : 2 * boundedLengthConst_C11Q C₂ A * v₁ = (4 * Real.exp E₁ - 1) * r := by
      rw [boundedLengthConst_C11Q, hv₁, ← hE₁]
      field_simp
      rw [Real.sq_sqrt (by norm_num)]
      ring
    rw [hconst]
    exact hL'

/-! ## 强链：K0、K4、K5（体积解释）、K6 都已证 -/

/-- **强链**：K0（G2）、K6（G3）、K4 ⇐ K2 + K3（极大值原理，本组）、K5 ⇐ K0 + K4 + K5a + 体积解释
（本组）都已证。剩余前提 = K1、K1 → K2、K3、K1 → K5a（拼接）与常数相容
（`C₂ ≥ 0`，`Λ_A ≥ 4 e^{C₂/2 + 32/√2}`）；全部在同一 `nr`。 -/
theorem localKappa_of_K1_K2_K3_K5a_C11Q {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ} {nr C₂ Λ C₅ : ℝ → ℝ}
    (hK1 : ∀ n, AdmissibleLCalculus_C11Q (F.tower.history n))
    (hK2 : (∀ n, AdmissibleLCalculus_C11Q (F.tower.history n)) →
      LocalizedLCutoffInequality_C11Q F nr C₂)
    (hK3 : SurgeryActionBarrier_C11Q F δ α nr Λ)
    (hC₂ : ∀ A, 0 < A → 0 ≤ C₂ A)
    (hΛ : ∀ A, 0 < A → 4 * Real.exp (C₂ A / 2 + 32 / Real.sqrt 2) ≤ Λ A)
    (hK5a : (∀ n, AdmissibleLCalculus_C11Q (F.tower.history n)) →
      SeedPatchLowAction_C11Q F δ α nr (boundedLengthConst_C11Q C₂) C₅) :
    LocalKappaWideSupply_C11Q F δ α nr :=
  localKappaWide_of_seedReducedVolume_C11Q
    (seedReducedVolumeLower_of_patch_C11Q seedPatchTransport_C11Q
      (boundedReducedLength_of_maxPrinciple_C11Q hC₂ hΛ (hK2 hK1) hK3) (hK5a hK1))

/-- 型对齐：G1 链 `localKappa_of_K0_to_K6_C11Q` 的 K0 / K4 / K5 / K6 前提全部由已证定理填入。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ} {nr C₂ Λ C₅ : ℝ → ℝ}
    (hK1 : ∀ n, AdmissibleLCalculus_C11Q (F.tower.history n))
    (hK2 : (∀ n, AdmissibleLCalculus_C11Q (F.tower.history n)) →
      LocalizedLCutoffInequality_C11Q F nr C₂)
    (hK3 : SurgeryActionBarrier_C11Q F δ α nr Λ)
    (hC₂ : ∀ A, 0 < A → 0 ≤ C₂ A)
    (hΛ : ∀ A, 0 < A → 4 * Real.exp (C₂ A / 2 + 32 / Real.sqrt 2) ≤ Λ A)
    (hK5a : (∀ n, AdmissibleLCalculus_C11Q (F.tower.history n)) →
      SeedPatchLowAction_C11Q F δ α nr (boundedLengthConst_C11Q C₂) C₅) :
    LocalKappaSupply_P6B F δ α nr :=
  (localKappa_of_K0_to_K6_C11Q seedPatchTransport_C11Q hK1 hK2 hK3
    (fun h2 h3 => boundedReducedLength_of_maxPrinciple_C11Q hC₂ hΛ h2 h3)
    (fun h0 _ h4 => seedReducedVolumeLower_of_patch_C11Q h0 h4 (hK5a hK1))
    controlledBallVolumeFromReducedVolume_holds_C11Q).toP6B

/-- **consumer（G4，简报要求）**：K 链（同一 `nr`）+ S7 ⇒ P6B window（真实 `nr`）；再加 Q3 的小尺度
`hsmall`（SMALLVOL 的显式形）⇒ `nr := 0` window（`localKappaWindow_zero_of_window_and_small_C11V`）
⇒ `Pre841Data_C11K`（`pre841Data_of_window_C11K`）⇒ 其 `volume_ge` 的基点块。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ} {nr C₂ Λ C₅ : ℝ → ℝ}
    (hK1 : ∀ n, AdmissibleLCalculus_C11Q (F.tower.history n))
    (hK2 : (∀ n, AdmissibleLCalculus_C11Q (F.tower.history n)) →
      LocalizedLCutoffInequality_C11Q F nr C₂)
    (hK3 : SurgeryActionBarrier_C11Q F δ α nr Λ)
    (hC₂ : ∀ A, 0 < A → 0 ≤ C₂ A)
    (hΛ : ∀ A, 0 < A → 4 * Real.exp (C₂ A / 2 + 32 / Real.sqrt 2) ≤ Λ A)
    (hK5a : (∀ n, AdmissibleLCalculus_C11Q (F.tower.history n)) →
      SeedPatchLowAction_C11Q F δ α nr (boundedLengthConst_C11Q C₂) C₅)
    (hacc : LargerBallAccuracySupply_C11S δ α) {A κ' : ℝ} (hA : 0 < A) (hκ' : 0 < κ')
    (hsmallScale : ∃ T : ℝ, 0 < T ∧
      ∀ n, let H := (F.tower.history n).toHistory;
      ∀ (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (r : ℝ),
        T ≤ (t : ℝ) →
        2 * r ^ 2 < (t : ℝ) →
        hasSmallParabolicCurvature H t p r →
        ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage t) t) p r →
        ∀ (aSeed : Icc (0 : ℝ) H.horizon) (haT : aSeed ≤ t),
          (aSeed : ℝ) = (t : ℝ) - r ^ 2 →
        ∀ seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage t)
          (H.activeStage_mono haT) p,
        ∀ (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvt : v ≤ t),
          (t : ℝ) - r ^ 2 / 2 ≤ (v : ℝ) →
        ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage v) v)
          (seedTrace.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))
          (A * r),
        ∀ ρ' : ℝ, 0 < ρ' → ρ' < nr v / 100 → ρ' < r / 100 →
          H.isParabolicallyRmControlledBall v x ρ' →
          ENNReal.ofReal (κ' * ρ' ^ 3) ≤ ballVolume (H.stageMetric (H.activeStage v) v) x ρ')
    (ind : ℕ → ℕ)
    (N : Pre841NativeData_C11K (fun n => (F.tower.history (ind n)).toHistory))
    (t : ∀ n, Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon)
    (p : ∀ n, ((F.tower.history (ind n)).toHistory.stageAt (t n)).Carrier) (r : ℕ → ℝ)
    (hlate : Tendsto (fun n => (t n : ℝ)) atTop atTop)
    (htime : ∀ n, 2 * r n ^ 2 < (t n : ℝ))
    (hsmall : ∀ n, hasSmallParabolicCurvature (F.tower.history (ind n)).toHistory (t n) (p n)
      (r n))
    (hvol : ∀ n, ENNReal.ofReal (A⁻¹ * r n ^ 3) ≤
      ballVolume ((F.tower.history (ind n)).toHistory.stageMetric
        ((F.tower.history (ind n)).toHistory.activeStage (t n)) (t n)) (p n) (r n))
    (aSeed : ∀ n, Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon)
    (haT : ∀ n, aSeed n ≤ t n) (hclock : ∀ n, (aSeed n : ℝ) = (t n : ℝ) - r n ^ 2)
    (seedTrace : ∀ n, BackwardPointTrace (F.tower.history (ind n)).toHistory
      ((F.tower.history (ind n)).toHistory.activeStage (aSeed n))
      ((F.tower.history (ind n)).toHistory.activeStage (t n))
      ((F.tower.history (ind n)).toHistory.activeStage_mono (haT n)) (p n))
    (s : ∀ n, Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon)
    (hst : ∀ n, s n ≤ t n)
    (y : ∀ n, ((F.tower.history (ind n)).toHistory.stageAt (s n)).Carrier) (R : ℕ → ℝ)
    (hR : ∀ n, 0 < R n)
    (hradii : Tendsto (fun n => r n / 200 * Real.sqrt (R n)) atTop atTop)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (t n : ℝ) - r n ^ 2 / 2 ≤ (s n : ℝ) - T / R n)
    (hdist : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((F.tower.history (ind n)).toHistory.stageMetric
          ((F.tower.history (ind n)).toHistory.activeStage (s n)) (s n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (w : Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon) (hws : w ≤ s n),
        (s n : ℝ) - T / R n ≤ w →
      ∀ tr : BackwardPointTrace (F.tower.history (ind n)).toHistory
        ((F.tower.history (ind n)).toHistory.activeStage w)
        ((F.tower.history (ind n)).toHistory.activeStage (s n))
        ((F.tower.history (ind n)).toHistory.activeStage_mono hws) x,
      ∀ haw : aSeed n ≤ w,
        riemannianEDistOf ((F.tower.history (ind n)).toHistory.stageMetric
            ((F.tower.history (ind n)).toHistory.activeStage w) w)
          ((seedTrace n).point ((F.tower.history (ind n)).toHistory.activeStage w)
            ((F.tower.history (ind n)).toHistory.activeStage_mono haw)
            ((F.tower.history (ind n)).toHistory.activeStage_mono (hws.trans (hst n))))
          (tr.point ((F.tower.history (ind n)).toHistory.activeStage w) le_rfl
            ((F.tower.history (ind n)).toHistory.activeStage_mono hws)) <
          ENNReal.ofReal (A * r n)) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((F.tower.history (ind n)).toHistory.stageMetric
          ((F.tower.history (ind n)).toHistory.activeStage (s n)) (s n)) (y n)
          (A / Real.sqrt (R n)),
      ∀ ρ' : ℝ, 0 < ρ' → ρ' ≤ 1 / Real.sqrt (R n) →
        (F.tower.history (ind n)).toHistory.isParabolicallyRmControlledBall (s n) x ρ' →
        ENNReal.ofReal (κ * ρ' ^ 3) ≤
          ballVolume ((F.tower.history (ind n)).toHistory.stageMetric
            ((F.tower.history (ind n)).toHistory.activeStage (s n)) (s n)) x ρ' := by
  have hloc : LocalKappaSupply_P6B F δ α nr :=
    (localKappa_of_K1_K2_K3_K5a_C11Q hK1 hK2 hK3 hC₂ hΛ hK5a).toP6B
  obtain ⟨κ, hκ, hW⟩ :=
    localKappaWindow_of_late_P6B (localKappaLateSupply_of_envelope_P6B hacc hloc) A hA
  have hW0 := localKappaWindow_zero_of_window_and_small_C11V hW hsmallScale
  let d := pre841Data_of_window_C11K (lt_min hκ hκ') hW0 ind N t p r hlate htime hsmall hvol
    aSeed haT hclock seedTrace s hst y R hR hradii hwin hdist
  exact ⟨d.kappa, d.kappa_pos, d.eventually_localKappa_base A⟩

end GC.LongTime.Ch11
