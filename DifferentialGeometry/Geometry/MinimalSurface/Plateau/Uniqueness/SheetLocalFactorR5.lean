import DifferentialGeometry.Geometry.MinimalSurface.Plateau.DiskDifferential
import DifferentialGeometry.Analysis.Calculus.Inverse.SmoothLocalInverse
import Mathlib.Analysis.Complex.Conformal
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

/-!
# O-MY-R5：R5-B(i) 的局部 sheet 因子（inverse germ 的单步延拓）

两张盘 `U V : ℂ → M`（R5 中 `U = diskExtension u`、`V = diskExtension q`）。若在 `(z, W)` 处
`U z = V W`、image germ `map U (𝓝 z) ≤ map V (𝓝 W)`、`V` 在 `W` 处 rank 2，则存在光滑局部因子
`Φ`（`Φ z = W`，`U = V ∘ Φ` 于 `z` 的开邻域）——这就是 D-3 的 "germ continuation" 的局部一步：
始终用 `V` 在 `W` 附近的**同一个** inverse germ（光滑左逆 `r`，`exists_smooth_local_leftInverse`）。
* `exists_local_factor_R5`：局部因子；
* `map_nhds_eq_of_local_factor_R5`：`dΦ` 可逆处 image germ 相等（germ 沿因子传播）；
* `conformalAt_of_local_factor_R5`：`U`、`V` 都 conformal 且 rank 2 ⇒ `Φ` 是 `ConformalAt`
  （`G(Bv, Bw) = λ⟨v, w⟩` 的双线性展开 + `ℂ` 上"正交等长 ⇒ 复线性 ∨ 共轭线性"）。
-/

set_option autoImplicit false
noncomputable section

open Set Filter Function Manifold DifferentialGeometry DifferentialGeometry.Analysis
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.Geometry

/-! ## `ℂ` 上的共形线性代数 -/

/-- 正交等长：`⟨a, b⟩ = 0`、`|a| = |b|` ⇒ `b = I a` 或 `b = −I a`。 -/
theorem eq_I_mul_or_eq_neg_I_mul_of_orth_R5 {a b : ℂ}
    (horth : a.re * b.re + a.im * b.im = 0)
    (hnorm : a.re ^ 2 + a.im ^ 2 = b.re ^ 2 + b.im ^ 2) :
    b = Complex.I * a ∨ b = -(Complex.I * a) := by
  have hid : ((b.re + a.im) ^ 2 + (b.im - a.re) ^ 2) * ((b.re - a.im) ^ 2 + (b.im + a.re) ^ 2) =
      (b.re ^ 2 + b.im ^ 2 - (a.re ^ 2 + a.im ^ 2)) ^ 2 +
        4 * (a.re * b.re + a.im * b.im) ^ 2 := by ring
  rw [horth, hnorm, sub_self] at hid
  norm_num at hid
  rcases hid with h | h
  · left
    have h1 : b.re + a.im = 0 := by nlinarith [sq_nonneg (b.re + a.im), sq_nonneg (b.im - a.re)]
    have h2 : b.im - a.re = 0 := by nlinarith [sq_nonneg (b.re + a.im), sq_nonneg (b.im - a.re)]
    apply Complex.ext <;> simp <;> linarith
  · right
    have h1 : b.re - a.im = 0 := by nlinarith [sq_nonneg (b.re - a.im), sq_nonneg (b.im + a.re)]
    have h2 : b.im + a.re = 0 := by nlinarith [sq_nonneg (b.re - a.im), sq_nonneg (b.im + a.re)]
    apply Complex.ext <;> simp <;> linarith

/-- 实线性 `A : ℂ → ℂ`：`A v = v.re • A 1 + v.im • A I`。 -/
theorem clm_apply_eq_re_im_R5 (A : ℂ →L[ℝ] ℂ) (v : ℂ) :
    A v = v.re • A 1 + v.im • A Complex.I := by
  conv_lhs => rw [← Complex.re_add_im v]
  rw [show (v.re : ℂ) + v.im * Complex.I = v.re • (1 : ℂ) + v.im • Complex.I by
    simp [Complex.real_smul]]
  rw [map_add, map_smul, map_smul]

/-- 正交等长且非零 ⇒ `IsConformalMap A`。 -/
theorem isConformalMap_of_orth_R5 (A : ℂ →L[ℝ] ℂ) (h1 : A 1 ≠ 0)
    (horth : (A 1).re * (A Complex.I).re + (A 1).im * (A Complex.I).im = 0)
    (hnorm : (A 1).re ^ 2 + (A 1).im ^ 2 = (A Complex.I).re ^ 2 + (A Complex.I).im ^ 2) :
    IsConformalMap A := by
  set a := A 1 with ha
  let map : ℂ →L[ℂ] ℂ := (ContinuousLinearMap.id ℂ ℂ).smulRight a
  have hmap : map ≠ 0 := by
    intro h
    apply h1
    have := congrArg (fun L : ℂ →L[ℂ] ℂ => L 1) h
    simpa [map] using this
  rcases eq_I_mul_or_eq_neg_I_mul_of_orth_R5 horth hnorm with hb | hb
  · have hA : A = map.restrictScalars ℝ := by
      ext1 v
      rw [clm_apply_eq_re_im_R5 A v, hb]
      simp only [ContinuousLinearMap.coe_restrictScalars', map,
        ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
      conv_rhs => rw [← Complex.re_add_im v]
      simp only [Complex.real_smul]
      ring
    rw [hA]
    exact isConformalMap_complex_linear hmap
  · have hA : A = (map.restrictScalars ℝ).comp (Complex.conjCLE : ℂ →L[ℝ] ℂ) := by
      ext1 v
      rw [clm_apply_eq_re_im_R5 A v, hb]
      simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
        ContinuousLinearMap.coe_restrictScalars', map, ContinuousLinearMap.smulRight_apply,
        ContinuousLinearMap.id_apply, smul_eq_mul, ContinuousLinearEquiv.coe_coe,
        Complex.conjCLE_apply]
      conv_rhs => rw [← Complex.re_add_im v]
      simp only [Complex.real_smul, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
      ring
    rw [hA]
    exact isConformalMap_complex_linear_conj hmap

/-- 双线性展开：`G p q = G q p = 0`、`G p p = G q q` ⇒
`G (x p + y q) (x' p + y' q) = G p p · (x x' + y y')`。 -/
theorem bilin_expand_R5 {F : Type*} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
    (G : F →L[ℝ] F →L[ℝ] ℝ) {p q : F} (hpq : G p q = 0) (hqp : G q p = 0)
    (hpp : G p p = G q q) (x y x' y' : ℝ) :
    G (x • p + y • q) (x' • p + y' • q) = G p p * (x * x' + y * y') := by
  simp only [map_add, map_smul, add_apply, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, hpq,
    hqp]
  rw [← hpp]
  ring

/-- 共形的抽象版本：`B` 单射且对 `G` 共形，`B ∘ A` 对 `G` 共形，`A` 单射 ⇒ `IsConformalMap A`。 -/
theorem isConformalMap_of_comp_bilin_R5 {F : Type*} [AddCommGroup F] [Module ℝ F]
    [TopologicalSpace F] (G : F →L[ℝ] F →L[ℝ] ℝ) (hsymm : ∀ v w, G v w = G w v)
    (hpos : ∀ v, v ≠ 0 → 0 < G v v) (B : ℂ →L[ℝ] F) (A : ℂ →L[ℝ] ℂ)
    (hBi : Injective B) (hAi : Injective A)
    (hB1 : G (B 1) (B Complex.I) = 0) (hB2 : G (B 1) (B 1) = G (B Complex.I) (B Complex.I))
    (hBA1 : G (B (A 1)) (B (A Complex.I)) = 0)
    (hBA2 : G (B (A 1)) (B (A 1)) = G (B (A Complex.I)) (B (A Complex.I))) :
    IsConformalMap A := by
  have hB1' : G (B Complex.I) (B 1) = 0 := by rw [hsymm]; exact hB1
  have hlam : 0 < G (B 1) (B 1) := hpos _ (fun h => one_ne_zero (hBi (h.trans (map_zero B).symm)))
  have hexp : ∀ v w : ℂ, G (B v) (B w) = G (B 1) (B 1) * (v.re * w.re + v.im * w.im) := by
    intro v w
    have hv : B v = v.re • B 1 + v.im • B Complex.I := by
      rw [← map_smul, ← map_smul, ← map_add]
      congr 1
      conv_lhs => rw [← Complex.re_add_im v]
      simp [Complex.real_smul]
    have hw : B w = w.re • B 1 + w.im • B Complex.I := by
      rw [← map_smul, ← map_smul, ← map_add]
      congr 1
      conv_lhs => rw [← Complex.re_add_im w]
      simp [Complex.real_smul]
    rw [hv, hw]
    exact bilin_expand_R5 G hB1 hB1' hB2 _ _ _ _
  have h1 : A 1 ≠ 0 := fun h => one_ne_zero (hAi (h.trans (map_zero A).symm))
  rw [hexp (A 1) (A Complex.I)] at hBA1
  rw [hexp (A 1) (A 1), hexp (A Complex.I) (A Complex.I)] at hBA2
  refine isConformalMap_of_orth_R5 A h1 ?_ ?_
  · rcases mul_eq_zero.mp hBA1 with h | h
    · exact absurd h hlam.ne'
    · exact h
  · have := mul_left_cancel₀ hlam.ne' hBA2
    nlinarith [this]

/-! ## 局部因子 -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

omit [FiniteDimensional ℝ E] in
/-- 光滑映射在 chart 中的坐标表示是 `C^∞` 的。 -/
theorem contDiffOn_extChartAt_comp_R5 {U : ℂ → M} {s : Set ℂ} (hs : IsOpen s)
    (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s) (p : M) :
    IsOpen (s ∩ U ⁻¹' (chartAt E p).source) ∧
      ContDiffOn ℝ ∞ (fun w => extChartAt 𝓘(ℝ, E) p (U w))
        (s ∩ U ⁻¹' (chartAt E p).source) := by
  refine ⟨hU.continuousOn.isOpen_inter_preimage hs (chartAt E p).open_source, ?_⟩
  intro z hz
  have hzU : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U z := hU.contMDiffAt (hs.mem_nhds hz.1)
  exact (((contMDiffAt_extChartAt' (I := 𝓘(ℝ, E)) (n := ∞) hz.2).comp z
    hzU).contDiffAt).contDiffWithinAt

omit [FiniteDimensional ℝ E] in
/-- rank 在 chart 中保持。 -/
theorem injective_fderiv_extChartAt_comp_R5 {U : ℂ → M} {z : ℂ} {p : M}
    (hz : U z ∈ (chartAt E p).source) (hU : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U z)
    (hi : Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z)) :
    Injective (fderiv ℝ (fun w => extChartAt 𝓘(ℝ, E) p (U w)) z) := by
  have hc := contMDiffAt_extChartAt' (I := 𝓘(ℝ, E)) (n := ∞) hz
  have hDX : fderiv ℝ (fun w => extChartAt 𝓘(ℝ, E) p (U w)) z =
      (show E →L[ℝ] E from mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E)
        (extChartAt 𝓘(ℝ, E) p) (U z)).comp
      (show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z) :=
    mfderiv_eq_fderiv.symm.trans
      (mfderiv_comp z (hc.mdifferentiableAt (by simp)) (hU.mdifferentiableAt (by simp)))
  rw [hDX]
  exact (isInvertible_mfderiv_extChartAt (I := 𝓘(ℝ, E))
    (show U z ∈ (extChartAt 𝓘(ℝ, E) p).source by
      simpa only [extChartAt_source] using hz)).injective.comp hi

/-- **局部因子（germ continuation 的一步）**：`U` 在开集 `s ∋ z` 上光滑，`V` 在开集 `t ∋ W` 上光滑且
`W` 处 rank 2，`U z = V W`，`map U (𝓝 z) ≤ map V (𝓝 W)` ⇒ 对任意 `O ∈ 𝓝 W`，存在开 `N ∋ z` 与
`C^∞` 的 `Φ`，`Φ z = W`、`Φ(N) ⊆ O ∩ t`、`U = V ∘ Φ` on `N`。 -/
theorem exists_local_factor_R5 {U V : ℂ → M} {s t : Set ℂ} (hs : IsOpen s) (ht : IsOpen t)
    (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s) (hV : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ V t)
    {z W : ℂ} (hz : z ∈ s) (hW : W ∈ t)
    (hVi : Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) V W))
    (hval : U z = V W) (hgerm : Filter.map U (𝓝 z) ≤ Filter.map V (𝓝 W))
    {O : Set ℂ} (hO : O ∈ 𝓝 W) :
    ∃ (N : Set ℂ) (Φ : ℂ → ℂ), IsOpen N ∧ z ∈ N ∧ N ⊆ s ∧ ContDiffOn ℝ ∞ Φ N ∧ Φ z = W ∧
      MapsTo Φ N (O ∩ t) ∧ ∀ z' ∈ N, U z' = V (Φ z') := by
  set p : M := V W with hp
  obtain ⟨htV, hXV⟩ := contDiffOn_extChartAt_comp_R5 ht hV p
  obtain ⟨hsU, hXU⟩ := contDiffOn_extChartAt_comp_R5 hs hU p
  have hWt' : W ∈ t ∩ V ⁻¹' (chartAt E p).source := ⟨hW, mem_chart_source E p⟩
  have hzs' : z ∈ s ∩ U ⁻¹' (chartAt E p).source := ⟨hz, by
    change U z ∈ (chartAt E p).source
    rw [hval]
    exact mem_chart_source E p⟩
  have hXVi : Injective (fderiv ℝ (fun w => extChartAt 𝓘(ℝ, E) p (V w)) W) :=
    injective_fderiv_extChartAt_comp_R5 (mem_chart_source E p)
      (hV.contMDiffAt (ht.mem_nhds hW)) hVi
  obtain ⟨r, Ur, Vr, hUr, hXWUr, hVr, hWVr, hVrsub, hr, hleft, hrW⟩ :=
    exists_smooth_local_leftInverse htV hXV hWt' hXVi
  -- 目标 sheet：`O'' := Vr ∩ interior O`
  set O'' : Set ℂ := Vr ∩ interior O with hO''
  have hO''o : IsOpen O'' := hVr.inter isOpen_interior
  have hWO'' : W ∈ O'' := ⟨hWVr, mem_interior_iff_mem_nhds.mpr hO⟩
  have himg : V '' O'' ∈ Filter.map V (𝓝 W) :=
    Filter.mem_map.mpr (Filter.mem_of_superset (hO''o.mem_nhds hWO'') (subset_preimage_image V _))
  have hpre : U ⁻¹' (V '' O'') ∈ 𝓝 z := hgerm himg
  -- chart 坐标里 `X_U` 连续 ⇒ 落在 `Ur`
  have hXUz : extChartAt 𝓘(ℝ, E) p (U z) ∈ Ur := by rw [hval]; exact hXWUr
  have hXUcont : ContinuousAt (fun w => extChartAt 𝓘(ℝ, E) p (U w)) z :=
    (hXU.continuousOn.continuousAt (hsU.mem_nhds hzs'))
  have hpre2 : (fun w => extChartAt 𝓘(ℝ, E) p (U w)) ⁻¹' Ur ∈ 𝓝 z :=
    hXUcont (hUr.mem_nhds hXUz)
  have hNnhds : (s ∩ U ⁻¹' (chartAt E p).source) ∩ (U ⁻¹' (V '' O'') ∩
      (fun w => extChartAt 𝓘(ℝ, E) p (U w)) ⁻¹' Ur) ∈ 𝓝 z :=
    Filter.inter_mem (hsU.mem_nhds hzs') (Filter.inter_mem hpre hpre2)
  obtain ⟨N, hNsub, hNo, hzN⟩ := mem_nhds_iff.mp hNnhds
  let Φ : ℂ → ℂ := fun w => r (extChartAt 𝓘(ℝ, E) p (U w))
  have hfac : ∀ z' ∈ N, ∃ w ∈ O'', V w = U z' ∧ Φ z' = w := by
    intro z' hz'
    obtain ⟨w, hwO, hwU⟩ := (hNsub hz').2.1
    refine ⟨w, hwO, hwU, ?_⟩
    change r (extChartAt 𝓘(ℝ, E) p (U z')) = w
    rw [← hwU]
    exact hleft w hwO.1
  refine ⟨N, Φ, hNo, hzN, fun z' hz' => (hNsub hz').1.1, ?_, ?_, ?_, ?_⟩
  · exact hr.comp (hXU.mono fun w hw => (hNsub hw).1) (fun w hw => (hNsub hw).2.2)
  · change r (extChartAt 𝓘(ℝ, E) p (U z)) = W
    rw [hval]
    exact hrW
  · intro z' hz'
    obtain ⟨w, hwO, -, hΦ⟩ := hfac z' hz'
    rw [hΦ]
    exact ⟨interior_subset hwO.2, hVrsub hwO.1 |>.1⟩
  · intro z' hz'
    obtain ⟨w, -, hwU, hΦ⟩ := hfac z' hz'
    rw [hΦ, hwU]

omit [TopologicalSpace M] in
/-- **germ 沿因子传播**：`U = V ∘ Φ` 于开 `N ∋ z`、`Φ` 在 `z` 处 `C¹` 且 `dΦ(z)` 单射 ⇒
`map U (𝓝 z) = map V (𝓝 (Φ z))`。 -/
theorem map_nhds_eq_of_local_factor_R5 {U V : ℂ → M} {Φ : ℂ → ℂ} {N : Set ℂ} (hN : IsOpen N)
    {z : ℂ} (hz : z ∈ N) (hΦ : ContDiffOn ℝ ∞ Φ N) (hfac : ∀ z' ∈ N, U z' = V (Φ z'))
    (hinj : Injective (fderiv ℝ Φ z)) :
    Filter.map U (𝓝 z) = Filter.map V (𝓝 (Φ z)) := by
  have hΦz : ContDiffAt ℝ ∞ Φ z := (hΦ z hz).contDiffAt (hN.mem_nhds hz)
  have hbij : Bijective (fderiv ℝ Φ z) :=
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp hinj⟩
  let D : ℂ ≃L[ℝ] ℂ :=
    (LinearEquiv.ofBijective (fderiv ℝ Φ z).toLinearMap hbij).toContinuousLinearEquiv
  have hstrict : HasStrictFDerivAt Φ (D : ℂ →L[ℝ] ℂ) z := by
    have h := hΦz.hasStrictFDerivAt (by simp)
    convert h using 1
    exact ContinuousLinearMap.ext fun v => rfl
  have hmap : Filter.map Φ (𝓝 z) = 𝓝 (Φ z) := hstrict.map_nhds_eq_of_equiv
  have heq : U =ᶠ[𝓝 z] V ∘ Φ := by
    filter_upwards [hN.mem_nhds hz] with z' hz'
    exact hfac z' hz'
  rw [Filter.map_congr heq, ← Filter.map_map, hmap]

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- 因子的链式法则：`mfderiv U z = mfderiv V (Φ z) ∘ dΦ(z)`。 -/
theorem mfderiv_eq_comp_of_local_factor_R5 {U V : ℂ → M} {Φ : ℂ → ℂ} {N : Set ℂ}
    (hN : IsOpen N) {z : ℂ} (hz : z ∈ N) (hΦ : ContDiffOn ℝ ∞ Φ N)
    (hfac : ∀ z' ∈ N, U z' = V (Φ z'))
    (hV : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) V (Φ z)) :
    (show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z) =
      (show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) V (Φ z)).comp (fderiv ℝ Φ z) := by
  have heq : U =ᶠ[𝓝 z] V ∘ Φ := by
    filter_upwards [hN.mem_nhds hz] with z' hz'
    exact hfac z' hz'
  have hΦd : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) Φ z :=
    (((hΦ z hz).contDiffAt (hN.mem_nhds hz)).differentiableAt (by simp)).mdifferentiableAt
  change mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z = _
  rw [heq.mfderiv_eq, mfderiv_comp z hV hΦd, mfderiv_eq_fderiv]
  rfl

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- 因子的 rank：`U` 在 `z` 处 rank 2 ⇒ `dΦ(z)` 单射。 -/
theorem injective_fderiv_of_local_factor_R5 {U V : ℂ → M} {Φ : ℂ → ℂ} {N : Set ℂ}
    (hN : IsOpen N) {z : ℂ} (hz : z ∈ N) (hΦ : ContDiffOn ℝ ∞ Φ N)
    (hfac : ∀ z' ∈ N, U z' = V (Φ z'))
    (hV : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) V (Φ z))
    (hUi : Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z)) :
    Injective (fderiv ℝ Φ z) := by
  have hcomp := mfderiv_eq_comp_of_local_factor_R5 hN hz hΦ hfac hV
  set B : ℂ →L[ℝ] E := mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) V (Φ z) with hBdef
  set A : ℂ →L[ℝ] ℂ := fderiv ℝ Φ z with hAdef
  set D : ℂ →L[ℝ] E := mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z with hDdef
  have hDA : ∀ v : ℂ, D v = B (A v) := fun v => congrArg (fun L : ℂ →L[ℝ] E => L v) hcomp
  intro v w hvw
  apply hUi
  change D v = D w
  rw [hDA, hDA, hvw]

omit [FiniteDimensional ℝ E] in
/-- **因子共形**：`U`、`V` 在对应点 conformal 且 rank 2 ⇒ `Φ` 在 `z` 处 `ConformalAt`。 -/
theorem conformalAt_of_local_factor_R5 (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {U V : ℂ → M} {Φ : ℂ → ℂ} {N : Set ℂ} (hN : IsOpen N) {z : ℂ} (hz : z ∈ N)
    (hΦ : ContDiffOn ℝ ∞ Φ N) (hfac : ∀ z' ∈ N, U z' = V (Φ z'))
    (hV : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) V (Φ z))
    (hUi : Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z))
    (hVi : Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) V (Φ z)))
    (hUc : DiskMapConformalAt g U z) (hVc : DiskMapConformalAt g V (Φ z)) :
    ConformalAt Φ z := by
  have hcomp := mfderiv_eq_comp_of_local_factor_R5 hN hz hΦ hfac hV
  have hΦd : DifferentiableAt ℝ Φ z :=
    ((hΦ z hz).contDiffAt (hN.mem_nhds hz)).differentiableAt (by simp)
  have hx : U z = V (Φ z) := hfac z hz
  set B : ℂ →L[ℝ] E := mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) V (Φ z) with hBdef
  set A : ℂ →L[ℝ] ℂ := fderiv ℝ Φ z with hAdef
  set D : ℂ →L[ℝ] E := mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z with hDdef
  have hDA : ∀ v : ℂ, D v = B (A v) := fun v => congrArg (fun L : ℂ →L[ℝ] E => L v) hcomp
  have hAi : Injective A := by
    intro v w hvw
    apply hUi
    change D v = D w
    rw [hDA, hDA, hvw]
  set G₂ : E →L[ℝ] E →L[ℝ] ℝ := g.inner (V (Φ z)) with hG₂
  have hG : (g.inner (U z) : E →L[ℝ] E →L[ℝ] ℝ) = G₂ := by rw [hG₂, hx]
  obtain ⟨hU1, hU2⟩ := hUc
  obtain ⟨hV1, hV2⟩ := hVc
  have hU1' : G₂ (B (A 1)) (B (A Complex.I)) = 0 := by
    rw [← hDA, ← hDA, ← hG]
    exact hU1
  have hU2' : G₂ (B (A 1)) (B (A 1)) = G₂ (B (A Complex.I)) (B (A Complex.I)) := by
    rw [← hDA, ← hDA, ← hG]
    exact hU2
  have hV1' : G₂ (B 1) (B Complex.I) = 0 := hV1
  have hV2' : G₂ (B 1) (B 1) = G₂ (B Complex.I) (B Complex.I) := hV2
  exact ⟨A, hΦd.hasFDerivAt, isConformalMap_of_comp_bilin_R5 G₂ (g.symm _) (g.pos _) B A hVi
    hAi hV1' hV2' hU1' hU2'⟩

end DifferentialGeometry.Geometry
