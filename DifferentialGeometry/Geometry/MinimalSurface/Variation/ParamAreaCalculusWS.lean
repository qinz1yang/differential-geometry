import DifferentialGeometry.Analysis.Integration.Measure.Parametric.FiniteIntegral
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# S-W-STAB G1：局部极小 + 光滑积分的一阶 / 二阶导数检验

`a(t) = C + ∫_K f(t, z) dz`（`K` 紧、`f` 在含 `T × K` 的开集 `Ω` 上 `C^∞`）在 `0` 取局部极小 ⇒
`∫_K ∂_t f(0, z) = 0` 且 `0 ≤ ∫_K ∂_t² f(0, z)`。两次对参数积分求导沿用
`SecondIntegralDerivative` 的紧源积分论证（该处引理 `private`，此处重写并同时给出一阶导数）。
-/

set_option autoImplicit false
noncomputable section

open Set Filter MeasureTheory
open DifferentialGeometry.Integral.Measure
open scoped Topology ContDiff

namespace DifferentialGeometry.Geometry

private theorem hasDerivAt_integral_compactOn_scalar_WS
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] [T2Space X] [SecondCountableTopology X]
    (μ : Measure X) [IsFiniteMeasure μ] {T : Set ℝ} (hT : IsOpen T)
    (f d : ℝ → X → ℝ)
    (hf : ContinuousOn (fun p : ℝ × X => f p.1 p.2) (T ×ˢ univ))
    (hd : ContinuousOn (fun p : ℝ × X => d p.1 p.2) (T ×ˢ univ))
    (hderiv : ∀ t ∈ T, ∀ x, HasDerivAt (fun s => f s x) (d t x) t)
    {t : ℝ} (ht : t ∈ T) :
    HasDerivAt (fun s => ∫ x, f s x ∂μ) (∫ x, d t x ∂μ) t := by
  let L : ℝ → X → ℝ →L[ℝ] ℝ := fun s x =>
    ContinuousLinearMap.toSpanSingleton ℝ (d s x)
  have hL : ContinuousOn (fun p : ℝ × X => L p.1 p.2) (T ×ˢ univ) :=
    (ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℝ) (E := ℝ)).continuous.comp_continuousOn hd
  have hI : Integrable (L t) μ := by
    have hc : Continuous (L t) := by
      rw [← continuousOn_univ]
      exact hL.comp (continuousOn_const.prodMk continuousOn_id)
        (fun x _ => ⟨ht, mem_univ x⟩)
    exact integrableOn_univ.mp (hc.continuousOn.integrableOn_compact isCompact_univ)
  have hh := (hasFDerivAt_integral_compactOn μ hT f L hf hL
    (fun s hs x => (hderiv s hs x).hasFDerivAt) t ht).hasDerivAt
  rw [ContinuousLinearMap.integral_apply hI] at hh
  simpa only [L, ContinuousLinearMap.toSpanSingleton_apply, one_smul] using hh

private theorem hasDerivAt_slice_WS {Ω : Set (ℝ × ℂ)} (hΩ : IsOpen Ω) {f : ℝ × ℂ → ℝ}
    (hf : ContDiffOn ℝ ∞ f Ω) {t : ℝ} {z : ℂ} (hp : (t, z) ∈ Ω) :
    HasDerivAt (fun s => f (s, z)) (fderiv ℝ f (t, z) (1, 0)) t := by
  have h := ((hf.contDiffAt (hΩ.mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt
  have h2 : HasDerivAt (fun s : ℝ => (s, z)) ((1 : ℝ), (0 : ℂ)) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t z)
  exact h.comp_hasDerivAt t h2

/-- 光滑密度在紧集 `K` 上的积分关于参数两次可导，且一阶导数是被积函数一阶导数的积分。 -/
theorem hasDerivAt_deriv_setIntegral_of_smooth_WS
    {K : Set ℂ} (hK : IsCompact K) {T : Set ℝ} {Ω : Set (ℝ × ℂ)}
    (hT : IsOpen T) (hΩ : IsOpen Ω) (hsub : T ×ˢ K ⊆ Ω)
    {f : ℝ × ℂ → ℝ} (hf : ContDiffOn ℝ ∞ f Ω)
    {t₀ : ℝ} (ht₀ : t₀ ∈ T) :
    IntegrableOn (fun z => deriv (deriv (fun t => f (t, z))) t₀) K ∧
    IntegrableOn (fun z => deriv (fun t => f (t, z)) t₀) K ∧
    (∀ t ∈ T, HasDerivAt (fun s => ∫ z in K, f (s, z))
      (∫ z in K, deriv (fun s => f (s, z)) t) t) ∧
      HasDerivAt (deriv (fun t => ∫ z in K, f (t, z)))
        (∫ z in K, deriv (deriv (fun t => f (t, z))) t₀) t₀ := by
  let D1 : ℝ × ℂ → ℝ := fun p => fderiv ℝ f p (1, 0)
  let D2 : ℝ × ℂ → ℝ := fun p => fderiv ℝ D1 p (1, 0)
  have hD1 : ContDiffOn ℝ ∞ D1 Ω :=
    (hf.fderiv_of_isOpen hΩ (by simp)).clm_apply contDiffOn_const
  have hD2 : ContDiffOn ℝ ∞ D2 Ω :=
    (hD1.fderiv_of_isOpen hΩ (by simp)).clm_apply contDiffOn_const
  have hd (t : ℝ) (ht : t ∈ T) (z : ℂ) (hz : z ∈ K) :
      HasDerivAt (fun s => f (s, z)) (D1 (t, z)) t :=
    hasDerivAt_slice_WS hΩ hf (hsub ⟨ht, hz⟩)
  have hd1 (t : ℝ) (ht : t ∈ T) (z : ℂ) (hz : z ∈ K) :
      HasDerivAt (fun s => D1 (s, z)) (D2 (t, z)) t :=
    hasDerivAt_slice_WS hΩ hD1 (hsub ⟨ht, hz⟩)
  have hD1eq (t : ℝ) (ht : t ∈ T) (z : ℂ) (hz : z ∈ K) :
      deriv (fun s => f (s, z)) t = D1 (t, z) := (hd t ht z hz).deriv
  have hD2eq (z : ℂ) (hz : z ∈ K) :
      deriv (deriv (fun t => f (t, z))) t₀ = D2 (t₀, z) := by
    have heq : deriv (fun t => f (t, z)) =ᶠ[𝓝 t₀] fun t => D1 (t, z) := by
      filter_upwards [hT.mem_nhds ht₀] with t ht
      exact hD1eq t ht z hz
    exact ((hd1 t₀ ht₀ z hz).congr_of_eventuallyEq heq).deriv
  have hint2 : IntegrableOn (fun z => deriv (deriv (fun t => f (t, z))) t₀) K := by
    have hc : ContinuousOn (fun z => D2 (t₀, z)) K :=
      hD2.continuousOn.comp (continuousOn_const.prodMk continuousOn_id)
        (fun z hz => hsub ⟨ht₀, hz⟩)
    exact (hc.congr hD2eq).integrableOn_compact hK
  have hint1 : IntegrableOn (fun z => deriv (fun t => f (t, z)) t₀) K := by
    have hc : ContinuousOn (fun z => D1 (t₀, z)) K :=
      hD1.continuousOn.comp (continuousOn_const.prodMk continuousOn_id)
        (fun z hz => hsub ⟨ht₀, hz⟩)
    exact (hc.congr (fun z hz => hD1eq t₀ ht₀ z hz)).integrableOn_compact hK
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let : MeasureSpace K := MeasureTheory.Measure.Subtype.measureSpace
  let : IsFiniteMeasure (volume : Measure K) := {
    measure_univ_lt_top := by
      rw [MeasureTheory.Measure.Subtype.volume_univ hK.measurableSet.nullMeasurableSet]
      exact hK.measure_lt_top }
  have hc : ContinuousOn (fun p : ℝ × K => f (p.1, p.2)) (T ×ˢ univ) :=
    hf.continuousOn.comp (by fun_prop) (fun p hp => hsub ⟨hp.1, p.2.property⟩)
  have hc1 : ContinuousOn (fun p : ℝ × K => D1 (p.1, p.2)) (T ×ˢ univ) :=
    hD1.continuousOn.comp (by fun_prop) (fun p hp => hsub ⟨hp.1, p.2.property⟩)
  have hc2 : ContinuousOn (fun p : ℝ × K => D2 (p.1, p.2)) (T ×ˢ univ) :=
    hD2.continuousOn.comp (by fun_prop) (fun p hp => hsub ⟨hp.1, p.2.property⟩)
  have hfirst (t : ℝ) (ht : t ∈ T) :
      HasDerivAt (fun s => ∫ z : K, f (s, z)) (∫ z : K, D1 (t, z)) t :=
    hasDerivAt_integral_compactOn_scalar_WS volume hT
      (fun s (z : K) => f (s, z)) (fun s (z : K) => D1 (s, z)) hc hc1
      (fun s hs z => hd s hs z z.property) ht
  have hsecond : HasDerivAt (fun t => ∫ z : K, D1 (t, z))
      (∫ z : K, D2 (t₀, z)) t₀ :=
    hasDerivAt_integral_compactOn_scalar_WS volume hT
      (fun s (z : K) => D1 (s, z)) (fun s (z : K) => D2 (s, z)) hc1 hc2
      (fun s hs z => hd1 s hs z z.property) ht₀
  have heq : deriv (fun t => ∫ z : K, f (t, z)) =ᶠ[𝓝 t₀]
      fun t => ∫ z : K, D1 (t, z) := by
    filter_upwards [hT.mem_nhds ht₀] with t ht
    exact (hfirst t ht).deriv
  have hsecond' := hsecond.congr_of_eventuallyEq heq
  have harea : (fun t => ∫ z : K, f (t, z)) = (fun t => ∫ z in K, f (t, z)) :=
    funext (fun t => integral_subtype hK.measurableSet (fun z => f (t, z)))
  have hcoeff (t : ℝ) (ht : t ∈ T) : (∫ z : K, D1 (t, z)) =
      ∫ z in K, deriv (fun s => f (s, z)) t := by
    calc
      (∫ z : K, D1 (t, z)) = ∫ z in K, D1 (t, z) :=
        integral_subtype hK.measurableSet (fun z : ℂ => D1 (t, z))
      _ = _ := setIntegral_congr_fun hK.measurableSet (fun z hz => (hD1eq t ht z hz).symm)
  have hcoeff2 : (∫ z : K, D2 (t₀, z)) =
      ∫ z in K, deriv (deriv (fun t => f (t, z))) t₀ := by
    calc
      (∫ z : K, D2 (t₀, z)) = ∫ z in K, D2 (t₀, z) :=
        integral_subtype hK.measurableSet (fun z : ℂ => D2 (t₀, z))
      _ = _ := setIntegral_congr_fun hK.measurableSet (fun z hz => (hD2eq z hz).symm)
  refine ⟨hint2, hint1, ?_, ?_⟩
  · intro t ht
    have h := hfirst t ht
    rw [harea, hcoeff t ht] at h
    exact h
  · rw [harea, hcoeff2] at hsecond'
    exact hsecond'

/-- 二阶导数检验：`a` 在 `0` 局部极小，`a'` 在 `0` 处可导 ⇒ `a'(0) = 0`、`a''(0) ≥ 0`。 -/
theorem second_deriv_nonneg_of_isLocalMin_WS {a : ℝ → ℝ} {a₁ a₂ : ℝ}
    (hmin : IsLocalMin a 0) (h1 : HasDerivAt a a₁ 0) (h2 : HasDerivAt (deriv a) a₂ 0) :
    a₁ = 0 ∧ 0 ≤ a₂ := by
  have hz : deriv a 0 = 0 := hmin.deriv_eq_zero
  refine ⟨by rw [← h1.deriv, hz], ?_⟩
  by_contra hneg
  replace hneg := not_le.mp hneg
  have hdd : deriv (deriv a) 0 < 0 := by rw [h2.deriv]; exact hneg
  have hmax : IsLocalMax a 0 := isLocalMax_of_deriv_deriv_neg hdd hz h1.continuousAt
  have hconst : a =ᶠ[𝓝 0] fun _ => a 0 := by
    filter_upwards [hmin, hmax] with t ht1 ht2
    exact le_antisymm ht2 ht1
  have hd1 : deriv a =ᶠ[𝓝 0] fun _ => (0 : ℝ) := by
    have := hconst.deriv
    simpa only [deriv_const'] using this
  have : deriv (deriv a) 0 = 0 := by
    rw [hd1.deriv_eq]
    simp
  linarith

/-- `a(t) = C + ∫_K f(t, z)` 在 `0` 局部极小 ⇒ `∫_K ∂_t f(0, ·) = 0`、`0 ≤ ∫_K ∂_t² f(0, ·)`。 -/
theorem integral_second_nonneg_of_isLocalMin_WS
    {K : Set ℂ} (hK : IsCompact K) {T : Set ℝ} {Ω : Set (ℝ × ℂ)}
    (hT : IsOpen T) (hΩ : IsOpen Ω) (hsub : T ×ˢ K ⊆ Ω)
    {f : ℝ × ℂ → ℝ} (hf : ContDiffOn ℝ ∞ f Ω) (h0 : (0 : ℝ) ∈ T) (C : ℝ)
    (hmin : IsLocalMin (fun t => C + ∫ z in K, f (t, z)) 0) :
    IntegrableOn (fun z => deriv (deriv (fun t => f (t, z))) 0) K ∧
    IntegrableOn (fun z => deriv (fun t => f (t, z)) 0) K ∧
    (∫ z in K, deriv (fun t => f (t, z)) 0 = 0) ∧
      0 ≤ ∫ z in K, deriv (deriv (fun t => f (t, z))) 0 := by
  obtain ⟨hi2, hi1, hfirst, hsecond⟩ :=
    hasDerivAt_deriv_setIntegral_of_smooth_WS hK hT hΩ hsub hf h0
  have h1 := (hfirst 0 h0).const_add C
  have h2 : HasDerivAt (deriv (fun t => C + ∫ z in K, f (t, z)))
      (∫ z in K, deriv (deriv (fun t => f (t, z))) 0) 0 := by
    have : deriv (fun t => C + ∫ z in K, f (t, z)) = deriv (fun t => ∫ z in K, f (t, z)) :=
      funext (fun t => deriv_const_add C)
    rw [this]
    exact hsecond
  obtain ⟨e1, e2⟩ := second_deriv_nonneg_of_isLocalMin_WS hmin h1 h2
  exact ⟨hi2, hi1, e1, e2⟩

end DifferentialGeometry.Geometry
