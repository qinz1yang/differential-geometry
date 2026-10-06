import DifferentialGeometry.Geometry.Metric.CurveSpeedCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Route W, IMS06′ 的路径长度下界（S-W-NECK G3，后缀 `_NK`，第 1 部分：单条 `C¹` 曲线）

一般的 Riemannian 流形 `(M, g)`（模型 `𝓘(ℝ, E)`）里，`Z : M → ℝ` 在开集 `N` 上光滑、band
`B = {p ∈ N | |Z p| < 20}` 上 `|dZ|² ≤ 4 g`，`closure B ⊆ N`：

* `ofReal_abs_sub_le_two_mul_curveELength_NK`：`Z` 沿 `C¹` 曲线的变化 `≤ 2 ×` `g`-长度
  （FTC：`f = Z ∘ γ` 在 `[a,b]` 上 `C¹`，`|f'| ≤ 2 · speed`）；
* `stay_or_exit_NK`：起点在 `B` 的 `C¹` 曲线 `γ : [0,1] → M` 要么整条留在 `B`（于是 `Z` 变化
  `≤ 2 ×` 长度），要么离开 `B`，此时 `20 - |Z (γ 0)| ≤ 2 ×` 长度（first-exit 时刻 `τ = sInf`
  的坏集；`γ τ ∈ closure B ⊆ N` 且 `∉ B` ⇒ `|Z (γ τ)| ≥ 20`）。
长度用树里的 `riemannianCurveELength`（`∫⁻ ofReal (speed)`，`Metric/CurveSpeedCalculus`）。
-/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Filter Manifold
open DifferentialGeometry DifferentialGeometry.Geometry
open scoped Manifold ContDiff ENNReal Topology

namespace GC.LongTime

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- 曲线 `γ` 在 `Z ∘ γ` 的导数等于 `mfderiv Z` 作用在 `γ'` 上。 -/
theorem deriv_comp_curve_NK {Z : M → ℝ} {γ : ℝ → M} {t : ℝ}
    (hZ : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) Z (γ t))
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t) :
    deriv (Z ∘ γ) t =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) Z (γ t) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t (1 : ℝ)) := by
  have hD := mfderiv_comp t hZ hγ
  have hf : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (Z ∘ γ) t := hZ.comp t hγ
  have h1 : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (Z ∘ γ) t (1 : ℝ) = deriv (Z ∘ γ) t := by
    rw [mfderiv_eq_fderiv]
    exact fderiv_apply_one_eq_deriv (𝕜 := ℝ) (f := Z ∘ γ) (x := t)
  rw [← h1, hD]
  rfl

/-- **FTC 型长度下界**：`Z` 沿 `C¹` 曲线 `γ` 的变化 `≤ 2 ×` 曲线的 `g`-长度，只要沿曲线内部
`|dZ|² ≤ 4 g`。 -/
theorem ofReal_abs_sub_le_two_mul_curveELength_NK
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {Z : M → ℝ} {γ : ℝ → M} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ (Icc a b))
    (hZ : ∀ t ∈ Icc a b, ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 1 Z (γ t))
    (hdz : ∀ t ∈ Ioo a b, ∀ w : TangentSpace 𝓘(ℝ, E) (γ t),
      (show ℝ from mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) Z (γ t) w) ^ 2 ≤ 4 * g.inner (γ t) w w) :
    ENNReal.ofReal |Z (γ b) - Z (γ a)| ≤ 2 * riemannianCurveELength g γ a b := by
  rcases hab.eq_or_lt with rfl | hlt
  · simp
  set f : ℝ → ℝ := Z ∘ γ with hfdef
  have hfc : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) 1 f (Icc a b) := fun t ht =>
    (hZ t ht).comp_contMDiffWithinAt t (hγ t ht)
  have hfd : ContDiffOn ℝ 1 f (Icc a b) := contMDiffOn_iff_contDiffOn.mp hfc
  have hcont : ContinuousOn f (Icc a b) := hfd.continuousOn
  have hfdA : ∀ t ∈ Ioo a b, DifferentiableAt ℝ f t := fun t ht =>
    ((hfd.differentiableOn one_ne_zero) t (Ioo_subset_Icc_self ht)).differentiableAt
      (Icc_mem_nhds ht.1 ht.2)
  have hder : ∀ t ∈ Ioo a b, HasDerivWithinAt f (derivWithin f (Icc a b) t) (Ioi t) t := by
    intro t ht
    have := (hfdA t ht).hasDerivAt
    rw [derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]
    exact this.hasDerivWithinAt
  have hint : IntervalIntegrable (derivWithin f (Icc a b)) volume a b :=
    (hfd.continuousOn_derivWithin (uniqueDiffOn_Icc hlt) le_rfl).intervalIntegrable_of_Icc hlt.le
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hlt.le hcont hder hint
  have h1 : ENNReal.ofReal |f b - f a| ≤ ∫⁻ y in Ioc a b, ‖derivWithin f (Icc a b) y‖ₑ := by
    rw [← hFTC, intervalIntegral.integral_of_le hlt.le, ← Real.enorm_eq_ofReal_abs]
    exact enorm_integral_le_lintegral_enorm _
  refine h1.trans ?_
  have h2 : ∀ᵐ y ∂(volume.restrict (Ioc a b)),
      ‖derivWithin f (Icc a b) y‖ₑ ≤ 2 * ENNReal.ofReal (riemannianCurveSpeed g γ y) := by
    rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc.symm]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
    have hyI : y ∈ Icc a b := Ioo_subset_Icc_self hy
    have hZd : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) Z (γ y) :=
      (hZ y hyI).mdifferentiableAt one_ne_zero
    have hγd : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ y :=
      ((hγ y hyI).mdifferentiableWithinAt one_ne_zero).mdifferentiableAt (Icc_mem_nhds hy.1 hy.2)
    have hD : derivWithin f (Icc a b) y =
        mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) Z (γ y) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ y (1 : ℝ)) := by
      rw [derivWithin_of_mem_nhds (Icc_mem_nhds hy.1 hy.2)]
      exact deriv_comp_curve_NK hZd hγd
    have hsq := hdz y hy (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ y (1 : ℝ))
    have h0 := metric_inner_self_nonneg g (γ y) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ y (1 : ℝ))
    have hle : |derivWithin f (Icc a b) y| ≤ 2 * riemannianCurveSpeed g γ y := by
      rw [← sq_le_sq₀ (abs_nonneg _) (by unfold riemannianCurveSpeed; positivity), sq_abs,
        mul_pow, riemannianCurveSpeed, Real.sq_sqrt h0, hD, show (2 : ℝ) ^ 2 = 4 by norm_num]
      exact hsq
    rw [Real.enorm_eq_ofReal_abs, show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp,
      ← ENNReal.ofReal_mul (by norm_num)]
    exact ENNReal.ofReal_le_ofReal hle
  calc ∫⁻ y in Ioc a b, ‖derivWithin f (Icc a b) y‖ₑ
      ≤ ∫⁻ y in Ioc a b, 2 * ENNReal.ofReal (riemannianCurveSpeed g γ y) :=
        lintegral_mono_ae h2
    _ ≤ ∫⁻ y in Icc a b, 2 * ENNReal.ofReal (riemannianCurveSpeed g γ y) :=
        lintegral_mono_set Ioc_subset_Icc_self
    _ = 2 * riemannianCurveELength g γ a b := by
        rw [lintegral_const_mul' _ _ (by simp)]
        rfl

/-- **first-exit**：`C¹` 曲线 `γ : [0,1] → M` 起点在 band `B = {p ∈ N | |Z p| < 20}` 内，则要么整条
曲线留在 `B` 内（此时 `Z` 的变化 `≤ 2 ×` 长度），要么离开 `B`，此时 `20 - |Z (γ 0)| ≤ 2 ×` 长度。
（离开点落在 `closure B ⊆ N` 的 `|Z| ≥ 20` 处。） -/
theorem stay_or_exit_NK
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {Nset : Set M} (hN : IsOpen Nset) {Z : M → ℝ}
    (hZ : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 1 Z Nset)
    (hcl : closure {p : M | p ∈ Nset ∧ |Z p| < 20} ⊆ Nset)
    (hdz : ∀ p ∈ Nset, |Z p| < 20 → ∀ w : TangentSpace 𝓘(ℝ, E) p,
      (show ℝ from mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) Z p w) ^ 2 ≤ 4 * g.inner p w w)
    {γ : ℝ → M} (hγ : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ (Icc 0 1))
    (h0 : γ 0 ∈ Nset) (h0' : |Z (γ 0)| < 20) :
    ((∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ Nset ∧ |Z (γ t)| < 20) ∧
        ENNReal.ofReal |Z (γ 1) - Z (γ 0)| ≤ 2 * riemannianCurveELength g γ 0 1) ∨
      ENNReal.ofReal (20 - |Z (γ 0)|) ≤ 2 * riemannianCurveELength g γ 0 1 := by
  set B : Set M := {p : M | p ∈ Nset ∧ |Z p| < 20} with hB
  have hBopen : IsOpen B :=
    hZ.continuousOn.isOpen_inter_preimage hN (isOpen_lt continuous_abs continuous_const)
  have hγc : ContinuousOn γ (Icc 0 1) := hγ.continuousOn
  by_cases hall : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ B
  · left
    refine ⟨hall, ofReal_abs_sub_le_two_mul_curveELength_NK g zero_le_one hγ
      (fun t ht => hZ.contMDiffAt (hN.mem_nhds (hall t ht).1))
      (fun t ht w => hdz _ (hall t (Ioo_subset_Icc_self ht)).1
        (hall t (Ioo_subset_Icc_self ht)).2 w)⟩
  · right
    have hall' : ∃ t ∈ Icc (0 : ℝ) 1, γ t ∉ B := by
      by_contra hc
      exact hall fun t ht => by
        by_contra hn
        exact hc ⟨t, ht, hn⟩
    set Bad : Set ℝ := {t | t ∈ Icc (0 : ℝ) 1 ∧ γ t ∈ Bᶜ} with hBad
    have hBadc : IsClosed Bad :=
      hγc.preimage_isClosed_of_isClosed isClosed_Icc hBopen.isClosed_compl
    have hBadne : Bad.Nonempty := by
      obtain ⟨t, ht, hnt⟩ := hall'
      exact ⟨t, ht, hnt⟩
    have hBadbdd : BddBelow Bad := ⟨0, fun t ht => ht.1.1⟩
    set τ := sInf Bad with hτ
    have hτmem : τ ∈ Bad := hBadc.csInf_mem hBadne hBadbdd
    have hτ1 : τ ≤ 1 := hτmem.1.2
    have hτ0 : 0 ≤ τ := hτmem.1.1
    have hτpos : 0 < τ := by
      rcases hτ0.eq_or_lt with h | h
      · exfalso
        have : γ 0 ∉ B := by
          have := hτmem.2
          rw [← h] at this
          exact this
        exact this ⟨h0, h0'⟩
      · exact h
    have hbefore : ∀ t ∈ Ico (0 : ℝ) τ, γ t ∈ B := by
      intro t ht
      by_contra hnot
      have : t ∈ Bad := ⟨⟨ht.1, ht.2.le.trans hτ1⟩, hnot⟩
      exact absurd (csInf_le hBadbdd this) (not_le.mpr ht.2)
    have hτB : γ τ ∉ B := hτmem.2
    have hτcl : γ τ ∈ closure B := by
      have hmono : ContinuousWithinAt γ (Ico 0 τ) τ :=
        (hγc τ ⟨hτ0, hτ1⟩).mono (Ico_subset_Icc_self.trans (Icc_subset_Icc le_rfl hτ1))
      have : (𝓝[Ico 0 τ] τ).NeBot := by
        rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ico hτpos.ne]
        exact ⟨hτ0, le_rfl⟩
      exact mem_closure_of_tendsto hmono (eventually_nhdsWithin_of_forall hbefore)
    have hτN : γ τ ∈ Nset := hcl hτcl
    have hτZ : 20 ≤ |Z (γ τ)| := by
      by_contra hlt
      exact hτB ⟨hτN, not_le.mp hlt⟩
    have hsub : Icc (0 : ℝ) τ ⊆ Icc 0 1 := Icc_subset_Icc le_rfl hτ1
    have hFTC := ofReal_abs_sub_le_two_mul_curveELength_NK g hτ0 (hγ.mono hsub)
      (fun t ht => by
        rcases ht.2.eq_or_lt with h | h
        · rw [h]; exact hZ.contMDiffAt (hN.mem_nhds hτN)
        · exact hZ.contMDiffAt (hN.mem_nhds (hbefore t ⟨ht.1, h⟩).1))
      (fun t ht w => hdz _ (hbefore t ⟨ht.1.le, ht.2⟩).1 (hbefore t ⟨ht.1.le, ht.2⟩).2 w)
    have hmono : riemannianCurveELength g γ 0 τ ≤ riemannianCurveELength g γ 0 1 :=
      lintegral_mono_set (Icc_subset_Icc le_rfl hτ1)
    have hreal : 20 - |Z (γ 0)| ≤ |Z (γ τ) - Z (γ 0)| := by
      have := abs_sub_abs_le_abs_sub (Z (γ τ)) (Z (γ 0))
      linarith
    calc ENNReal.ofReal (20 - |Z (γ 0)|) ≤ ENNReal.ofReal |Z (γ τ) - Z (γ 0)| :=
          ENNReal.ofReal_le_ofReal hreal
      _ ≤ 2 * riemannianCurveELength g γ 0 τ := hFTC
      _ ≤ 2 * riemannianCurveELength g γ 0 1 := by gcongr

end GC.LongTime
