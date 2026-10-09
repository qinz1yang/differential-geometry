import DifferentialGeometry.Geometry.MinimalSurface.Plateau.NoTransverseTransportR15T
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.BoundaryRegularity

/-!
# S-MY-R8：二次 trim（外审 R8 / R8-C1），从**显式** `C⁰` + `C^∞_loc` 收敛数据出发

不经 R7（R7 的两条收敛作为显式前提 `hC0` / `hCk`，形状取 `MYD2/R06to08.lean` 合同；
`hCk` 是 chart 意义的 `C^∞_loc`）。设 `q` 是极限盘（内部 smooth + 闭盘 rank 在 `D°` 上 +
R1 collar `ρ₁`），`uₙ` 是 Morrey 盘列，`s ∈ (ρ₁, 1)`，`vₙ z := diskExtension uₙ (s • z)`，
`v₀ z := diskExtension q (s • z)`。`s • D̄ ⋐ D°`，所以 `D̄` 上只需要 `D°` 的紧子集收敛。

* **G1** `second_trim_c1_R8`：`vₙ → v₀` 于 `D̄` 的每个紧子集上 chartwise `C¹`（值 + `fderiv`
  在 chart 内一致收敛）。`iteratedFDeriv ℝ 0/1` 经线性等距化成值 / `fderiv`，`fderiv_comp_smul` 搬 `s`。
* **G2** `second_trim_rank_R8`：`n` 充分大时 `dvₙ` 在整个 `D̄` 上单射（紧 `C¹` 扰动保持 rank：
  局部引理 `exists_local_inj_rank_R8` + 有限子覆盖 `exists_uniform_inj_rank_R8`）。
* **G3** `second_trim_collar_R8`：`∃ μ < 1`，`n` 充分大时 `‖z‖ > μ` 的点 fiber 是 singleton。
  近处：统一局部单射（Lebesgue number）；远处：极限盘 `{‖z‖ ≥ μ, |z − w| ≥ δ}` 紧，`riemannianEDistOf G`
  有正下界 `η`（`exists_pos_lower_bound_edist_R8`），`hC0` 取 `ε = min η 1 / 2`。"eventually" 统一丢弃
  有限前缀，不为小 `n` 补盘。
* **G4** `second_trim_own_trace_minimal_R8`：`vₙ` 对**自身** trace 是 `Gn n`-Morrey disk 且 trace
  smooth embedded（`isSmoothEmbeddedLoop_trim_R8` + `isMorreyDisk_trim_R8`；R2 机制
  `IsMorreyDisk.affineSubdisk`，Lipschitz 由 `IsMorreyDisk.exists_smooth_extension` 给）。
* **G5** `second_trim_c1_data_R8`：R15 / MY-13 要的 `hv / hval / hchart / hder`，极限是
  `diskExtension (affineSubdisk q 0 s)`，对齐 `noTransverse_of_c1_limit_trimmed_R15T` 与 ADP 的
  `noTransverse_of_c1_limit_open_trimmed_ADP`。`vₙ` 单射性（R9–R14 的输出）**不**在这里。
* `second_trim_regular_collar_R8`：G2 + G3 + G4 合成（`second_trim_regular_collar_MYD2` 的显式数据版）。

不要 `uₙ` 在原 `S¹` 的 `C¹` 收敛，不要 `uₙ` 整盘满秩（D-R-MY1-11）。不含新 Prop / structure。
-/

set_option autoImplicit false
noncomputable section

open Set Filter Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Topology
open scoped Topology ContDiff Manifold NNReal ENNReal

namespace DifferentialGeometry.Geometry

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_lower_bound_of_injective_R8 (L : ℂ →L[ℝ] E) (hL : Function.Injective L) :
    ∃ c : ℝ, 0 < c ∧ ∀ h : ℂ, c * ‖h‖ ≤ ‖L h‖ := by
  obtain ⟨K, hK0, hK⟩ :=
    (L : ℂ →ₗ[ℝ] E).exists_antilipschitzWith (LinearMap.ker_eq_bot.mpr hL)
  have hK0' : (0 : ℝ) < K := by exact_mod_cast hK0
  refine ⟨(K : ℝ)⁻¹, inv_pos.mpr hK0', fun h => ?_⟩
  have h1 := hK.le_mul_dist h 0
  simp only [ContinuousLinearMap.coe_coe, map_zero, dist_zero_right] at h1
  rw [inv_mul_le_iff₀ hK0']
  linarith

theorem injOn_and_injective_fderiv_of_close_R8 {F : ℂ → E} {L : ℂ →L[ℝ] E} {c : ℝ}
    (hc : 0 < c) (hL : ∀ h : ℂ, c * ‖h‖ ≤ ‖L h‖) {K : Set ℂ} (hK : Convex ℝ K)
    (hd : ∀ ξ ∈ K, DifferentiableAt ℝ F ξ)
    (hclose : ∀ ξ ∈ K, ‖fderiv ℝ F ξ - L‖ ≤ c / 2) :
    InjOn F K ∧ ∀ ξ ∈ K, Function.Injective (fderiv ℝ F ξ) := by
  constructor
  · intro x hx y hy hxy
    have hG : ∀ ξ ∈ K, HasFDerivWithinAt (fun z => F z - L z) (fderiv ℝ F ξ - L) K ξ :=
      fun ξ hξ => ((hd ξ hξ).hasFDerivAt.sub L.hasFDerivAt).hasFDerivWithinAt
    have hmv := hK.norm_image_sub_le_of_norm_hasFDerivWithin_le hG hclose hx hy
    have hLxy : ‖L (y - x)‖ ≤ c / 2 * ‖y - x‖ := by
      have h2 : (F y - L y) - (F x - L x) = -(L (y - x)) := by
        rw [map_sub, ← hxy]
        abel
      rw [h2, norm_neg] at hmv
      exact hmv
    have h3 := hL (y - x)
    have hn : ‖y - x‖ ≤ 0 := by nlinarith [norm_nonneg (y - x)]
    have h4 : y - x = 0 := norm_le_zero_iff.mp hn
    exact (sub_eq_zero.mp h4).symm
  · intro ξ hξ a b hab
    have hD : fderiv ℝ F ξ (a - b) = 0 := by rw [map_sub, hab, sub_self]
    have h1 : ‖L (a - b)‖ ≤ c / 2 * ‖a - b‖ := by
      have h2 : L (a - b) = (L - fderiv ℝ F ξ) (a - b) := by
        rw [sub_apply, hD, sub_zero]
      rw [h2]
      calc ‖(L - fderiv ℝ F ξ) (a - b)‖ ≤ ‖L - fderiv ℝ F ξ‖ * ‖a - b‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ c / 2 * ‖a - b‖ := by
            apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
            rw [norm_sub_rev]
            exact hclose ξ hξ
    have h3 := hL (a - b)
    have hn : ‖a - b‖ ≤ 0 := by nlinarith [norm_nonneg (a - b)]
    exact (sub_eq_zero.mp (norm_le_zero_iff.mp hn))

end Abstract

section Transfer

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem iteratedFDeriv_one_eq_R8 (f : ℂ → E) (x : ℂ) :
    iteratedFDeriv ℝ 1 f x = (continuousMultilinearCurryFin1 ℝ ℂ E).symm (fderiv ℝ f x) := by
  ext m
  simp

theorem tendstoUniformlyOn_comp_of_mapsTo_R8 {β : Type*} [UniformSpace β] {F : ℕ → ℂ → β}
    {f : ℂ → β} {S K : Set ℂ} {φ : ℂ → ℂ} (h : TendstoUniformlyOn F f atTop S)
    (hφ : MapsTo φ K S) :
    TendstoUniformlyOn (fun n x => F n (φ x)) (fun x => f (φ x)) atTop K :=
  fun u hu => (h u hu).mono fun _ hn x hx => hn (φ x) (hφ hx)

theorem tendstoUniformlyOn_fderiv_of_iteratedFDeriv_one_R8 {g : ℕ → ℂ → E} {g₀ : ℂ → E}
    {S : Set ℂ}
    (h : TendstoUniformlyOn (fun n => iteratedFDeriv ℝ 1 (g n)) (iteratedFDeriv ℝ 1 g₀)
      atTop S) :
    TendstoUniformlyOn (fun n x => fderiv ℝ (g n) x) (fun x => fderiv ℝ g₀ x) atTop S := by
  have h1 := (continuousMultilinearCurryFin1 ℝ ℂ E).isometry.uniformContinuous
    |>.comp_tendstoUniformlyOn h
  simpa only [iteratedFDeriv_one_eq_R8, Function.comp_def,
    LinearIsometryEquiv.apply_symm_apply] using h1

theorem tendstoUniformlyOn_of_iteratedFDeriv_zero_R8 {g : ℕ → ℂ → E} {g₀ : ℂ → E}
    {S : Set ℂ}
    (h : TendstoUniformlyOn (fun n => iteratedFDeriv ℝ 0 (g n)) (iteratedFDeriv ℝ 0 g₀)
      atTop S) :
    TendstoUniformlyOn (fun n x => g n x) (fun x => g₀ x) atTop S := by
  have h1 := (continuousMultilinearCurryFin0 ℝ ℂ E).isometry.uniformContinuous
    |>.comp_tendstoUniformlyOn h
  simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_def,
    LinearIsometryEquiv.apply_symm_apply] using h1

end Transfer


section Chart

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- **G1**（R8）：二次 trim `vₙ := uₙ(s·)` 的 chartwise `C¹` 收敛于 `closedBall 0 1`（`D̄`）的紧子集上：
chart 内 value / `fderiv` 一致收敛。输入只有 R7 的 chart `C^∞_loc` 数据（`iteratedFDeriv` k = 0, 1），
`s < 1` 使 `s • D̄ ⋐ D°`。 -/
theorem second_trim_c1_R8 {q : C(closedDisk, M)} {u : ℕ → C(closedDisk, M)} {s : ℝ}
    (hs0 : 0 < s) (hs : s < 1)
    (hCk : ∀ (p : M) (Kc : Set ℂ), IsCompact Kc →
      Kc ⊆ Metric.ball (0 : ℂ) 1 ∩ diskExtension q ⁻¹' (extChartAt 𝓘(ℝ, E) p).source →
      (∀ᶠ n in atTop, MapsTo (diskExtension (u n)) Kc (extChartAt 𝓘(ℝ, E) p).source) ∧
      ∀ k : ℕ, TendstoUniformlyOn
        (fun n => iteratedFDeriv ℝ k (fun z => extChartAt 𝓘(ℝ, E) p (diskExtension (u n) z)))
        (iteratedFDeriv ℝ k (fun z => extChartAt 𝓘(ℝ, E) p (diskExtension q z))) atTop Kc)
    (p : M) {K : Set ℂ} (hK : IsCompact K)
    (hKs : K ⊆ Metric.closedBall (0 : ℂ) 1 ∩
      (fun z => diskExtension q (s • z)) ⁻¹' (extChartAt 𝓘(ℝ, E) p).source) :
    (∀ᶠ n in atTop, MapsTo (fun z => diskExtension (u n) (s • z)) K
      (extChartAt 𝓘(ℝ, E) p).source) ∧
    TendstoUniformlyOn (fun n z => extChartAt 𝓘(ℝ, E) p (diskExtension (u n) (s • z)))
      (fun z => extChartAt 𝓘(ℝ, E) p (diskExtension q (s • z))) atTop K ∧
    TendstoUniformlyOn
      (fun n z => fderiv ℝ (fun w => extChartAt 𝓘(ℝ, E) p (diskExtension (u n) (s • w))) z)
      (fun z => fderiv ℝ (fun w => extChartAt 𝓘(ℝ, E) p (diskExtension q (s • w))) z)
      atTop K := by
  have hsK : IsCompact ((fun z : ℂ => s • z) '' K) := hK.image (continuous_const_smul s)
  have hmaps0 : MapsTo (fun z : ℂ => s • z) K ((fun z : ℂ => s • z) '' K) := mapsTo_image _ _
  have hsub : (fun z : ℂ => s • z) '' K ⊆
      Metric.ball (0 : ℂ) 1 ∩ diskExtension q ⁻¹' (extChartAt 𝓘(ℝ, E) p).source := by
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨?_, (hKs hz).2⟩
    have hz' : ‖z‖ ≤ 1 := by simpa using (hKs hz).1
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hs0]
    nlinarith [norm_nonneg z]
  obtain ⟨hmaps, hk⟩ := hCk p _ hsK hsub
  refine ⟨hmaps.mono fun n hn z hz => hn (hmaps0 hz), ?_, ?_⟩
  · exact tendstoUniformlyOn_comp_of_mapsTo_R8
      (tendstoUniformlyOn_of_iteratedFDeriv_zero_R8 (hk 0)) hmaps0
  · have h1 := tendstoUniformlyOn_comp_of_mapsTo_R8
      (tendstoUniformlyOn_fderiv_of_iteratedFDeriv_one_R8 (hk 1)) hmaps0
    have h2 := (uniformContinuous_const_smul s).comp_tendstoUniformlyOn h1
    convert h2 using 1
    · funext n z
      exact fderiv_comp_smul (f := fun z => extChartAt 𝓘(ℝ, E) p (diskExtension (u n) z))
        (x := z) s
    · funext z
      exact fderiv_comp_smul (f := fun z => extChartAt 𝓘(ℝ, E) p (diskExtension q z))
        (x := z) s

end Chart

section Local

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

omit [FiniteDimensional ℝ E] in
/-- chart 的 `mfderiv` 在 source 内可逆 ⇒ 单射。 -/
theorem injective_mfderiv_extChartAt_R8 {p y : M} (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).source) :
    Function.Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) p) y) := by
  obtain ⟨e, he⟩ := isInvertible_mfderiv_extChartAt (I := 𝓘(ℝ, E)) hy
  rw [← he]
  exact e.injective

omit [FiniteDimensional ℝ E] in
theorem mdifferentiableAt_extChartAt_R8 {p y : M} (hy : y ∈ (extChartAt 𝓘(ℝ, E) p).source) :
    MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) p) y :=
  ((contMDiffOn_extChartAt (I := 𝓘(ℝ, E)) (x := p) (n := ∞)).mdifferentiableOn
    (by simp)).mdifferentiableAt (by
      rw [← extChartAt_source 𝓘(ℝ, E) p]
      exact (isOpen_extChartAt_source p).mem_nhds hy)

omit [FiniteDimensional ℝ E] in
/-- chart 复合的链式法则：`fderiv (φ ∘ f) z = mfderiv φ (f z) ∘ mfderiv f z`。 -/
theorem fderiv_chart_comp_R8 {p : M} {f : ℂ → M} {z : ℂ}
    (hf : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) f z)
    (hz : f z ∈ (extChartAt 𝓘(ℝ, E) p).source) :
    fderiv ℝ (fun w => extChartAt 𝓘(ℝ, E) p (f w)) z =
      (show E →L[ℝ] E from mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) p) (f z)).comp
        (show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) f z) := by
  have h := mfderiv_comp z (mdifferentiableAt_extChartAt_R8 hz) hf
  have h2 : mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) p ∘ f) z =
      fderiv ℝ (fun w => extChartAt 𝓘(ℝ, E) p (f w)) z := mfderiv_eq_fderiv
  exact h2.symm.trans h

omit [FiniteDimensional ℝ E] in
/-- **局部引理**（R8，Step B）：若极限 `f₀` 在 `B` 上 `C¹` 且 `df₀` 单射、`fₙ` 在 `B` 上 mdifferentiable，
且 chart 内 `fderiv` 在 `B` 的紧子集上一致收敛（G1 的形），则 `B` 的每点有邻域，使 `fₙ`（`n` 充分大）
在其上单射且 `dfₙ` 单射。（`ε` 与 `n` 无关；`n` 的阈值依赖点。） -/
theorem exists_local_inj_rank_R8 {f₀ : ℂ → M} {f : ℕ → ℂ → M} {B : Set ℂ}
    (hBc : IsCompact B) (hBv : Convex ℝ B)
    (hf₀ : ∀ z ∈ B, ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 f₀ z)
    (hfn : ∀ n, ∀ z ∈ B, MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (f n) z)
    (hrank : ∀ z ∈ B, Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) f₀ z))
    (hC1 : ∀ (p : M) (K : Set ℂ), IsCompact K →
      K ⊆ B ∩ f₀ ⁻¹' (extChartAt 𝓘(ℝ, E) p).source →
      (∀ᶠ n in atTop, MapsTo (f n) K (extChartAt 𝓘(ℝ, E) p).source) ∧
      TendstoUniformlyOn (fun n z => fderiv ℝ (fun w => extChartAt 𝓘(ℝ, E) p (f n w)) z)
        (fun z => fderiv ℝ (fun w => extChartAt 𝓘(ℝ, E) p (f₀ w)) z) atTop K)
    {z₀ : ℂ} (hz₀ : z₀ ∈ B) :
    ∃ ε > 0, ∀ᶠ n in atTop, InjOn (f n) (Metric.ball z₀ ε ∩ B) ∧
      ∀ ξ ∈ Metric.ball z₀ ε ∩ B, Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (f n) ξ) := by
  set p : M := f₀ z₀ with hp
  set φ := extChartAt 𝓘(ℝ, E) p with hφ
  have hsrc : IsOpen φ.source := isOpen_extChartAt_source p
  have hz₀src : f₀ z₀ ∈ φ.source := mem_extChartAt_source p
  have hf₀z : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 f₀ z₀ := hf₀ z₀ hz₀
  -- `F := φ ∘ f₀` 在 `z₀` 处 `C¹`
  have hφsm : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) 1 φ (f₀ z₀) := by
    refine ((contMDiffOn_extChartAt (I := 𝓘(ℝ, E)) (x := p) (n := 1)).contMDiffAt ?_)
    rw [← extChartAt_source 𝓘(ℝ, E) p]
    exact hsrc.mem_nhds hz₀src
  have hFd : ContDiffAt ℝ 1 (fun w => φ (f₀ w)) z₀ :=
    contMDiffAt_iff_contDiffAt.mp (hφsm.comp z₀ hf₀z)
  have hFcont : ContinuousAt (fderiv ℝ (fun w => φ (f₀ w))) z₀ :=
    (hFd.fderiv_right (m := 0) (by norm_num)).continuousAt
  -- `L := fderiv F z₀` 单射
  set L : ℂ →L[ℝ] E := fderiv ℝ (fun w => φ (f₀ w)) z₀ with hL
  have hLinj : Function.Injective L := by
    rw [hL, fderiv_chart_comp_R8 (hf₀z.mdifferentiableAt (by norm_num)) hz₀src]
    exact (injective_mfderiv_extChartAt_R8 hz₀src).comp (hrank z₀ hz₀)
  obtain ⟨c, hc, hcL⟩ := exists_lower_bound_of_injective_R8 L hLinj
  -- 选 `ε`
  obtain ⟨δ₁, hδ₁, hsrcball⟩ : ∃ δ₁ > 0, ∀ ξ ∈ Metric.ball z₀ δ₁, f₀ ξ ∈ φ.source :=
    Metric.eventually_nhds_iff_ball.mp
      (hf₀z.continuousAt.eventually_mem (hsrc.mem_nhds hz₀src))
  obtain ⟨δ₂, hδ₂, hderball⟩ := Metric.continuousAt_iff.mp hFcont (c / 4) (by positivity)
  set ε : ℝ := min δ₁ δ₂ / 2 with hε
  have hεpos : 0 < ε := by positivity
  have hεδ₁ : ε < δ₁ := by have := min_le_left δ₁ δ₂; linarith [lt_min hδ₁ hδ₂]
  have hεδ₂ : ε < δ₂ := by have := min_le_right δ₁ δ₂; linarith [lt_min hδ₁ hδ₂]
  set K : Set ℂ := Metric.closedBall z₀ ε ∩ B with hK
  have hKc : IsCompact K := (isCompact_closedBall z₀ ε).inter_right hBc.isClosed
  have hKv : Convex ℝ K := (convex_closedBall z₀ ε).inter hBv
  have hKb : ∀ ξ ∈ K, ξ ∈ B ∧ dist ξ z₀ < δ₁ ∧ dist ξ z₀ < δ₂ := by
    intro ξ hξ
    have h1 : dist ξ z₀ ≤ ε := Metric.mem_closedBall.mp hξ.1
    exact ⟨hξ.2, h1.trans_lt hεδ₁, h1.trans_lt hεδ₂⟩
  have hKsub : K ⊆ B ∩ f₀ ⁻¹' φ.source := fun ξ hξ =>
    ⟨(hKb ξ hξ).1, hsrcball ξ (Metric.mem_ball.mpr (hKb ξ hξ).2.1)⟩
  obtain ⟨hmaps, hunif⟩ := hC1 p K hKc hKsub
  have hclose := Metric.tendstoUniformlyOn_iff.mp hunif (c / 4) (by positivity)
  refine ⟨ε, hεpos, ?_⟩
  filter_upwards [hmaps, hclose] with n hn1 hn2
  have hdiff : ∀ ξ ∈ K, DifferentiableAt ℝ (fun w => φ (f n w)) ξ := by
    intro ξ hξ
    have := (mdifferentiableAt_extChartAt_R8 (hn1 hξ)).comp ξ (hfn n ξ (hKb ξ hξ).1)
    exact mdifferentiableAt_iff_differentiableAt.mp this
  have hcl : ∀ ξ ∈ K, ‖fderiv ℝ (fun w => φ (f n w)) ξ - L‖ ≤ c / 2 := by
    intro ξ hξ
    have h1 := hn2 ξ hξ
    have h2 : dist (fderiv ℝ (fun w => φ (f₀ w)) ξ) L < c / 4 :=
      hderball (Metric.mem_ball.mpr (hKb ξ hξ).2.2)
    rw [dist_eq_norm] at h1 h2
    have h3 : fderiv ℝ (fun w => φ (f n w)) ξ - L =
        -(fderiv ℝ (fun w => φ (f₀ w)) ξ - fderiv ℝ (fun w => φ (f n w)) ξ) +
          (fderiv ℝ (fun w => φ (f₀ w)) ξ - L) := by abel
    rw [h3]
    calc _ ≤ ‖-(fderiv ℝ (fun w => φ (f₀ w)) ξ - fderiv ℝ (fun w => φ (f n w)) ξ)‖ +
          ‖fderiv ℝ (fun w => φ (f₀ w)) ξ - L‖ := norm_add_le _ _
      _ ≤ c / 2 := by rw [norm_neg]; linarith
  obtain ⟨hinjOn, hinjD⟩ := injOn_and_injective_fderiv_of_close_R8 hc hcL hKv hdiff hcl
  have hball : Metric.ball z₀ ε ∩ B ⊆ K := fun ξ hξ => ⟨Metric.ball_subset_closedBall hξ.1, hξ.2⟩
  refine ⟨fun a ha b hb hab => hinjOn (hball ha) (hball hb) (by simp only [hab]), ?_⟩
  intro ξ hξ
  have hξK := hball hξ
  have hchain := fderiv_chart_comp_R8 (hfn n ξ (hKb ξ hξK).1) (hn1 hξK)
  have hD := hinjD ξ hξK
  rw [hchain, ContinuousLinearMap.coe_comp] at hD
  exact hD.of_comp

omit [FiniteDimensional ℝ E] in
/-- **一致局部单射 + 统一 rank**（R8，Step C）：`B` 紧凸，局部引理的前提 ⇒ 存在 Lebesgue 常数 `δ`，使
`n` 充分大时 `B` 里距离 `< δ` 的两点不碰撞，且 `dfₙ` 在整个 `B` 上单射。有限子覆盖 +
`eventually_all_finset` + Lebesgue number。 -/
theorem exists_uniform_inj_rank_R8 {f₀ : ℂ → M} {f : ℕ → ℂ → M} {B : Set ℂ}
    (hBc : IsCompact B) (hBv : Convex ℝ B)
    (hf₀ : ∀ z ∈ B, ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 f₀ z)
    (hfn : ∀ n, ∀ z ∈ B, MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (f n) z)
    (hrank : ∀ z ∈ B, Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) f₀ z))
    (hC1 : ∀ (p : M) (K : Set ℂ), IsCompact K →
      K ⊆ B ∩ f₀ ⁻¹' (extChartAt 𝓘(ℝ, E) p).source →
      (∀ᶠ n in atTop, MapsTo (f n) K (extChartAt 𝓘(ℝ, E) p).source) ∧
      TendstoUniformlyOn (fun n z => fderiv ℝ (fun w => extChartAt 𝓘(ℝ, E) p (f n w)) z)
        (fun z => fderiv ℝ (fun w => extChartAt 𝓘(ℝ, E) p (f₀ w)) z) atTop K) :
    ∃ δ > 0, ∀ᶠ n in atTop,
      (∀ z ∈ B, ∀ w ∈ B, dist z w < δ → f n z = f n w → z = w) ∧
      ∀ ξ ∈ B, Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (f n) ξ) := by
  choose! ε hε hev using fun z₀ (hz₀ : z₀ ∈ B) =>
    exists_local_inj_rank_R8 hBc hBv hf₀ hfn hrank hC1 hz₀
  obtain ⟨t, htB, hcover⟩ := hBc.elim_nhds_subcover (fun z => Metric.ball z (ε z))
    (fun z hz => Metric.ball_mem_nhds z (hε z hz))
  have hevt : ∀ᶠ n in atTop, ∀ z ∈ t, InjOn (f n) (Metric.ball z (ε z) ∩ B) ∧
      ∀ ξ ∈ Metric.ball z (ε z) ∩ B, Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (f n) ξ) :=
    (Filter.eventually_all_finset t).mpr fun z hz => hev z (htB z hz)
  obtain ⟨δ, hδ, hleb⟩ := lebesgue_number_lemma_of_metric (s := B) (ι := t)
    (c := fun i : t => Metric.ball (i : ℂ) (ε i)) hBc (fun _ => Metric.isOpen_ball) (by
      intro x hx
      obtain ⟨i, hi, hxi⟩ : ∃ i ∈ t, x ∈ Metric.ball i (ε i) := by simpa using hcover hx
      exact Set.mem_iUnion.mpr ⟨⟨i, hi⟩, hxi⟩)
  refine ⟨δ, hδ, hevt.mono fun n hn => ⟨?_, ?_⟩⟩
  · intro z hz w hw hzw hfe
    obtain ⟨i, hi⟩ := hleb z hz
    have hzi : z ∈ Metric.ball (i : ℂ) (ε i) := hi (Metric.mem_ball_self hδ)
    have hwi : w ∈ Metric.ball (i : ℂ) (ε i) := hi (by
      rw [Metric.mem_ball, dist_comm]
      exact hzw)
    exact (hn i i.2).1 ⟨hzi, hz⟩ ⟨hwi, hw⟩ hfe
  · intro ξ hξ
    obtain ⟨i, hi, hξi⟩ : ∃ i ∈ t, ξ ∈ Metric.ball i (ε i) := by simpa using hcover hξ
    exact (hn i hi).2 ξ ⟨hξi, hξ⟩

end Local


section Dist

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- `riemannianEDistOf G` 在流形拓扑下联合连续（`PseudoEMetricSpace.ofRiemannianMetric`）。 -/
theorem continuous_riemannianEDistOf_prod_R8 (G : SmoothRiemannianMetric 𝓘(ℝ, E) M) :
    Continuous (fun p : M × M => riemannianEDistOf G p.1 p.2) := by
  let : RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E) x) := ⟨G.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : M => TangentSpace 𝓘(ℝ, E) x) :=
    ⟨⟨G.inner, G.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  have : LocallyCompactSpace M :=
    Manifold.locallyCompact_of_finiteDimensional (M := M) 𝓘(ℝ, E)
  have : RegularSpace M := inferInstance
  let : PseudoEMetricSpace M := PseudoEMetricSpace.ofRiemannianMetric 𝓘(ℝ, E) M
  exact continuous_fst.edist continuous_snd

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- `riemannianEDistOf G x y = 0 ⇒ x = y`（`T2` 流形）。 -/
theorem eq_of_riemannianEDistOf_eq_zero_R8 (G : SmoothRiemannianMetric 𝓘(ℝ, E) M) {x y : M}
    (h : riemannianEDistOf G x y = 0) : x = y := by
  let : RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E) x) := ⟨G.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : M => TangentSpace 𝓘(ℝ, E) x) :=
    ⟨⟨G.inner, G.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  have : LocallyCompactSpace M :=
    Manifold.locallyCompact_of_finiteDimensional (M := M) 𝓘(ℝ, E)
  have : RegularSpace M := inferInstance
  have : T3Space M := inferInstance
  let em : EMetricSpace M := EMetricSpace.ofRiemannianMetric 𝓘(ℝ, E) M
  have hedist : @edist M em.toEDist x y = 0 := h
  exact em.eq_of_edist_eq_zero hedist

/-- 紧集上两点像两两不同 ⇒ 像的 Riemannian 距离有统一正下界（极限盘的 compact positive separation）。 -/
theorem exists_pos_lower_bound_edist_R8 (G : SmoothRiemannianMetric 𝓘(ℝ, E) M) {B : Set ℂ}
    {f : ℂ → M} (hf : ContinuousOn f B) {S : Set (ℂ × ℂ)} (hS : IsCompact S)
    (hSB : S ⊆ B ×ˢ B) (hne : ∀ p ∈ S, f p.1 ≠ f p.2) :
    ∃ η : ℝ≥0∞, 0 < η ∧ ∀ p ∈ S, η ≤ riemannianEDistOf G (f p.1) (f p.2) := by
  rcases S.eq_empty_or_nonempty with rfl | hSne
  · exact ⟨1, one_pos, by simp⟩
  have hcont : ContinuousOn (fun p : ℂ × ℂ => riemannianEDistOf G (f p.1) (f p.2)) S :=
    (continuous_riemannianEDistOf_prod_R8 G).comp_continuousOn
      ((hf.comp continuousOn_fst fun p hp => (hSB hp).1).prodMk
        (hf.comp continuousOn_snd fun p hp => (hSB hp).2))
  obtain ⟨p₀, hp₀, hmin⟩ := hS.exists_isMinOn hSne hcont
  refine ⟨riemannianEDistOf G (f p₀.1) (f p₀.2), ?_, fun p hp => isMinOn_iff.mp hmin p hp⟩
  rw [pos_iff_ne_zero]
  intro h0
  exact hne p₀ hp₀ (eq_of_riemannianEDistOf_eq_zero_R8 G h0)

end Dist


section Disk

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem smul_mem_ball_R8 {s : ℝ} (hs0 : 0 < s) (hs : s < 1) {z : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) 1) : s • z ∈ Metric.ball (0 : ℂ) 1 := by
  have hz' : ‖z‖ ≤ 1 := by simpa using hz
  rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hs0]
  nlinarith [norm_nonneg z]

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem contMDiffAt_scaled_R8 {q : C(closedDisk, M)}
    (hq : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (diskExtension q) (Metric.ball (0 : ℂ) 1))
    {s : ℝ} (hs0 : 0 < s) (hs : s < 1) {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) 1) :
    ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (fun w : ℂ => diskExtension q (s • w)) z := by
  have h1 : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (diskExtension q) (s • z) :=
    hq.contMDiffAt (Metric.isOpen_ball.mem_nhds (smul_mem_ball_R8 hs0 hs hz))
  have h2 : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (fun w : ℂ => s • w) z :=
    (contDiff_const_smul s).contMDiff.contMDiffAt
  exact h1.comp z h2

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- source 缩放的链式法则：`D(f(r·))_x = Df_{r x} ∘ (r • id)`。 -/
theorem mfderiv_comp_smul_R8 {f : ℂ → M} {r : ℝ} {x : ℂ}
    (hf : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) f (r • x)) :
    (show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun w : ℂ => f (r • w)) x) =
      (show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) f (r • x)).comp
        (r • ContinuousLinearMap.id ℝ ℂ) := by
  have hS : HasMFDerivAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun z : ℂ => r • z) x
      (r • ContinuousLinearMap.id ℝ ℂ) :=
    ((hasFDerivAt_id x).const_smul r).hasMFDerivAt
  exact (hf.hasMFDerivAt.comp x hS).mfderiv

omit [FiniteDimensional ℝ E] in
theorem injective_comp_smul_R8 {r : ℝ} (hr : r ≠ 0) {A : ℂ →L[ℝ] E} (hA : Function.Injective A) :
    Function.Injective (A.comp (r • ContinuousLinearMap.id ℝ ℂ)) := by
  intro a b hab
  have hab' : A (r • a) = A (r • b) := by
    simp only [ContinuousLinearMap.comp_apply, smul_apply,
      ContinuousLinearMap.id_apply] at hab
    exact hab
  exact smul_right_injective ℂ hr (hA hab')

omit [FiniteDimensional ℝ E] in
/-- **G2 + 近处统一局部单射**（R8）：`vₙ := uₙ(s·)`（`0 < s < 1`）。由 G1 的 `C¹` 数据与极限盘在
`s • D̄ ⊂ D°` 的 rank：存在 `δ > 0`，`n` 充分大时 `D̄` 上距离 `< δ` 的两点不碰撞（统一局部单射），
且 `dvₙ` 在整个 `D̄` 上单射。只用 R7 的 chart `C^∞_loc` 数据，不用 `un` 在原边界的任何信息。 -/
theorem second_trim_near_rank_R8
    {q : C(closedDisk, M)} {u : ℕ → C(closedDisk, M)} {s : ℝ} (hs0 : 0 < s) (hs : s < 1)
    (hqs : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (diskExtension q) (Metric.ball (0 : ℂ) 1))
    (hus : ∀ n, ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (diskExtension (u n)) (Metric.ball (0 : ℂ) 1))
    (hqrank : ∀ z ∈ Metric.ball (0 : ℂ) 1,
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension q) z))
    (hCk : ∀ (p : M) (Kc : Set ℂ), IsCompact Kc →
      Kc ⊆ Metric.ball (0 : ℂ) 1 ∩ diskExtension q ⁻¹' (extChartAt 𝓘(ℝ, E) p).source →
      (∀ᶠ n in atTop, MapsTo (diskExtension (u n)) Kc (extChartAt 𝓘(ℝ, E) p).source) ∧
      ∀ k : ℕ, TendstoUniformlyOn
        (fun n => iteratedFDeriv ℝ k (fun z => extChartAt 𝓘(ℝ, E) p (diskExtension (u n) z)))
        (iteratedFDeriv ℝ k (fun z => extChartAt 𝓘(ℝ, E) p (diskExtension q z))) atTop Kc) :
    ∃ δ > 0, ∀ᶠ n in atTop,
      (∀ z ∈ Metric.closedBall (0 : ℂ) 1, ∀ w ∈ Metric.closedBall (0 : ℂ) 1, dist z w < δ →
        diskExtension (u n) (s • z) = diskExtension (u n) (s • w) → z = w) ∧
      ∀ z ∈ Metric.closedBall (0 : ℂ) 1, Function.Injective
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun w : ℂ => diskExtension (u n) (s • w)) z) := by
  have hBc : IsCompact (Metric.closedBall (0 : ℂ) 1) := isCompact_closedBall 0 1
  have hBv : Convex ℝ (Metric.closedBall (0 : ℂ) 1) := convex_closedBall 0 1
  have hf₀ : ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 (fun w : ℂ => diskExtension q (s • w)) z :=
    fun z hz => (contMDiffAt_scaled_R8 hqs hs0 hs hz).of_le (by simp)
  have hfn : ∀ n, ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun w : ℂ => diskExtension (u n) (s • w)) z :=
    fun n z hz => (contMDiffAt_scaled_R8 (hus n) hs0 hs hz).mdifferentiableAt (by simp)
  have hrank : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun w : ℂ => diskExtension q (s • w)) z) := by
    intro z hz
    have hqd : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension q) (s • z) :=
      (hqs.contMDiffAt (Metric.isOpen_ball.mem_nhds (smul_mem_ball_R8 hs0 hs hz))
        ).mdifferentiableAt (by simp)
    have h1 := mfderiv_comp_smul_R8 hqd
    have h2 := injective_comp_smul_R8 hs0.ne'
      (hqrank (s • z) (smul_mem_ball_R8 hs0 hs hz))
    intro a b hab
    apply h2
    have h3 := congrArg (fun L : ℂ →L[ℝ] E => L a) h1
    have h4 := congrArg (fun L : ℂ →L[ℝ] E => L b) h1
    exact (h3.symm.trans (hab.trans h4))
  have hC1 : ∀ (p : M) (K : Set ℂ), IsCompact K →
      K ⊆ Metric.closedBall (0 : ℂ) 1 ∩
        (fun w : ℂ => diskExtension q (s • w)) ⁻¹' (extChartAt 𝓘(ℝ, E) p).source →
      (∀ᶠ n in atTop, MapsTo (fun w : ℂ => diskExtension (u n) (s • w)) K
        (extChartAt 𝓘(ℝ, E) p).source) ∧
      TendstoUniformlyOn
        (fun n z => fderiv ℝ (fun w => extChartAt 𝓘(ℝ, E) p (diskExtension (u n) (s • w))) z)
        (fun z => fderiv ℝ (fun w => extChartAt 𝓘(ℝ, E) p (diskExtension q (s • w))) z)
        atTop K :=
    fun p K hK hKs => let h := second_trim_c1_R8 hs0 hs hCk p hK hKs; ⟨h.1, h.2.2⟩
  exact exists_uniform_inj_rank_R8 hBc hBv hf₀ hfn hrank hC1

/-- **G2 + G3 的核心**（R8）：`vₙ := uₙ(s·)` 在 `D̄` 上满秩，且存在 `μ < 1` 使 `‖z‖ > μ` 的点
不与任何点碰撞。近：`exists_uniform_inj_rank_R8`（G1 的 `C¹` 数据 + 极限盘闭盘 rank）；远：极限盘
`s·` 的 collar（`ρ₁ < ‖z‖ → q z = q w → z = w`）+ compact positive separation + `hC0`（C⁰ 一致小）。 -/
theorem second_trim_rank_collar_core_R8 [T2Space M]
    {G : SmoothRiemannianMetric 𝓘(ℝ, E) M} {q : C(closedDisk, M)} {u : ℕ → C(closedDisk, M)}
    {ρ₁ s : ℝ} (hρ₁ : 0 < ρ₁) (hρ₁s : ρ₁ < s) (hs : s < 1)
    (hqs : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (diskExtension q) (Metric.ball (0 : ℂ) 1))
    (hus : ∀ n, ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (diskExtension (u n)) (Metric.ball (0 : ℂ) 1))
    (hqrank : ∀ z ∈ Metric.ball (0 : ℂ) 1,
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension q) z))
    (hqcol : ∀ z w : closedDisk, ρ₁ < ‖(z : ℂ)‖ → q z = q w → z = w)
    (hC0 : ∀ ε : ℝ≥0∞, 0 < ε → ∀ᶠ n in atTop, ∀ z, riemannianEDistOf G (u n z) (q z) < ε)
    (hCk : ∀ (p : M) (Kc : Set ℂ), IsCompact Kc →
      Kc ⊆ Metric.ball (0 : ℂ) 1 ∩ diskExtension q ⁻¹' (extChartAt 𝓘(ℝ, E) p).source →
      (∀ᶠ n in atTop, MapsTo (diskExtension (u n)) Kc (extChartAt 𝓘(ℝ, E) p).source) ∧
      ∀ k : ℕ, TendstoUniformlyOn
        (fun n => iteratedFDeriv ℝ k (fun z => extChartAt 𝓘(ℝ, E) p (diskExtension (u n) z)))
        (iteratedFDeriv ℝ k (fun z => extChartAt 𝓘(ℝ, E) p (diskExtension q z))) atTop Kc) :
    ∃ μ : ℝ, μ < 1 ∧ ∀ᶠ n in atTop,
      (∀ z ∈ Metric.closedBall (0 : ℂ) 1, Function.Injective
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun w : ℂ => diskExtension (u n) (s • w)) z)) ∧
      ∀ z ∈ Metric.closedBall (0 : ℂ) 1, ∀ w ∈ Metric.closedBall (0 : ℂ) 1, μ < ‖z‖ →
        diskExtension (u n) (s • z) = diskExtension (u n) (s • w) → z = w := by
  have hs0 : 0 < s := hρ₁.trans hρ₁s
  have hs0 : 0 < s := hρ₁.trans hρ₁s
  obtain ⟨δ, hδ, hnear⟩ := second_trim_near_rank_R8 hs0 hs hqs hus hqrank hCk
  have hBc : IsCompact (Metric.closedBall (0 : ℂ) 1) := isCompact_closedBall 0 1
  have hf₀ : ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 (fun w : ℂ => diskExtension q (s • w)) z :=
    fun z hz => (contMDiffAt_scaled_R8 hqs hs0 hs hz).of_le (by simp)
  -- 远处：μ ∈ (ρ₁ / s, 1)
  have hρs : ρ₁ / s < 1 := (div_lt_one hs0).mpr hρ₁s
  set μ : ℝ := (ρ₁ / s + 1) / 2 with hμ
  have hμ1 : μ < 1 := by rw [hμ]; linarith
  have hμρ : ρ₁ < s * μ := by
    have h1 : ρ₁ / s < μ := by rw [hμ]; linarith
    have h2 := (div_lt_iff₀ hs0).mp h1
    linarith
  -- 极限盘在 `B` 上：`f₀ z = f₀ w`、`μ ≤ ‖z‖` ⇒ `z = w`
  have hlimcol : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, ∀ w ∈ Metric.closedBall (0 : ℂ) 1,
      μ ≤ ‖z‖ → diskExtension q (s • z) = diskExtension q (s • w) → z = w := by
    intro z hz w hw hμz hzw
    have hzs := Metric.ball_subset_closedBall (smul_mem_ball_R8 hs0 hs hz)
    have hws := Metric.ball_subset_closedBall (smul_mem_ball_R8 hs0 hs hw)
    have hcol := hqcol ⟨s • z, hzs⟩ ⟨s • w, hws⟩ (by
      change ρ₁ < ‖s • z‖
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs0]
      nlinarith) (by
      rw [← diskExtension_coe q ⟨s • z, hzs⟩, ← diskExtension_coe q ⟨s • w, hws⟩]
      exact hzw)
    exact smul_right_injective ℂ hs0.ne' (congrArg Subtype.val hcol)
  let S : Set (ℂ × ℂ) := (Metric.closedBall (0 : ℂ) 1 ×ˢ Metric.closedBall (0 : ℂ) 1) ∩
    ({p | μ ≤ ‖p.1‖} ∩ {p | δ ≤ ‖p.1 - p.2‖})
  have hSc : IsCompact S := (hBc.prod hBc).inter_right
    ((isClosed_le continuous_const (continuous_norm.comp continuous_fst)).inter
      (isClosed_le continuous_const (continuous_norm.comp (continuous_fst.sub continuous_snd))))
  have hf₀cont : ContinuousOn (fun w : ℂ => diskExtension q (s • w))
      (Metric.closedBall (0 : ℂ) 1) := fun z hz => (hf₀ z hz).continuousAt.continuousWithinAt
  have hne : ∀ p ∈ S, diskExtension q (s • p.1) ≠ diskExtension q (s • p.2) := by
    rintro ⟨z, w⟩ ⟨⟨hz, hw⟩, hμz, hδzw⟩ hfeq
    have hzw := hlimcol z hz w hw hμz hfeq
    have : δ ≤ ‖z - w‖ := hδzw
    rw [hzw, sub_self, norm_zero] at this
    exact absurd hδ (not_lt.mpr this)
  obtain ⟨η, hη, hηlow⟩ := exists_pos_lower_bound_edist_R8 G hf₀cont hSc
    Set.inter_subset_left hne
  have hεpos : 0 < min η 1 / 2 :=
    ENNReal.div_pos (ne_of_gt (lt_min hη one_pos)) ENNReal.ofNat_ne_top
  refine ⟨μ, hμ1, ?_⟩
  filter_upwards [hnear, hC0 _ hεpos] with n hn1 hn2
  refine ⟨hn1.2, ?_⟩
  intro z hz w hw hμz hfeq
  by_cases hdist : dist z w < δ
  · exact hn1.1 z hz w hw hdist hfeq
  · by_contra hzw
    have hmem : (z, w) ∈ S :=
      ⟨⟨hz, hw⟩, hμz.le, by simpa [dist_eq_norm] using not_lt.mp hdist⟩
    have hlow := hηlow (z, w) hmem
    have hzs := Metric.ball_subset_closedBall (smul_mem_ball_R8 hs0 hs hz)
    have hws := Metric.ball_subset_closedBall (smul_mem_ball_R8 hs0 hs hw)
    have hc1 : riemannianEDistOf G (diskExtension q (s • z)) (diskExtension (u n) (s • z)) <
        min η 1 / 2 := by
      rw [riemannianEDistOf_comm, diskExtension_coe (u n) ⟨s • z, hzs⟩,
        diskExtension_coe q ⟨s • z, hzs⟩]
      exact hn2 _
    have hc2 : riemannianEDistOf G (diskExtension (u n) (s • w)) (diskExtension q (s • w)) <
        min η 1 / 2 := by
      rw [diskExtension_coe (u n) ⟨s • w, hws⟩, diskExtension_coe q ⟨s • w, hws⟩]
      exact hn2 _
    have hmid : riemannianEDistOf G (diskExtension (u n) (s • z))
        (diskExtension (u n) (s • w)) = 0 := by
      rw [hfeq]
      exact riemannianEDistOf_self G _
    have htri := (riemannianEDistOf_triangle G (diskExtension q (s • z))
      (diskExtension (u n) (s • z)) (diskExtension q (s • w))).trans
      (add_le_add_right (riemannianEDistOf_triangle G (diskExtension (u n) (s • z))
        (diskExtension (u n) (s • w)) (diskExtension q (s • w))) _)
    rw [hmid, zero_add] at htri
    have hlt : riemannianEDistOf G (diskExtension q (s • z)) (diskExtension q (s • w)) <
        min η 1 := by
      calc _ ≤ _ := htri
        _ < min η 1 / 2 + min η 1 / 2 := ENNReal.add_lt_add hc1 hc2
        _ = min η 1 := ENNReal.add_halves _
    exact absurd (lt_of_le_of_lt hlow hlt) (not_lt.mpr (min_le_left _ _))

omit [FiniteDimensional ℝ E] in
/-- **G2**（R8）：`dvₙ` 在整个 `D̄` 上单射（`n` 充分大）。紧 `C¹` 扰动保持 rank：G1 的 chart `C¹` 数据
+ 极限盘在 `s • D̄ ⊂ D°` 上 rank。 -/
theorem second_trim_rank_R8
    {q : C(closedDisk, M)} {u : ℕ → C(closedDisk, M)} {s : ℝ} (hs0 : 0 < s) (hs : s < 1)
    (hqs : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (diskExtension q) (Metric.ball (0 : ℂ) 1))
    (hus : ∀ n, ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (diskExtension (u n)) (Metric.ball (0 : ℂ) 1))
    (hqrank : ∀ z ∈ Metric.ball (0 : ℂ) 1,
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension q) z))
    (hCk : ∀ (p : M) (Kc : Set ℂ), IsCompact Kc →
      Kc ⊆ Metric.ball (0 : ℂ) 1 ∩ diskExtension q ⁻¹' (extChartAt 𝓘(ℝ, E) p).source →
      (∀ᶠ n in atTop, MapsTo (diskExtension (u n)) Kc (extChartAt 𝓘(ℝ, E) p).source) ∧
      ∀ k : ℕ, TendstoUniformlyOn
        (fun n => iteratedFDeriv ℝ k (fun z => extChartAt 𝓘(ℝ, E) p (diskExtension (u n) z)))
        (iteratedFDeriv ℝ k (fun z => extChartAt 𝓘(ℝ, E) p (diskExtension q z))) atTop Kc) :
    ∀ᶠ n in atTop, ∀ z ∈ Metric.closedBall (0 : ℂ) 1, Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun w : ℂ => diskExtension (u n) (s • w)) z) := by
  obtain ⟨_, _, h⟩ := second_trim_near_rank_R8 hs0 hs hqs hus hqrank hCk
  exact h.mono fun _ hn => hn.2

/-- **G3**（R8）：二次 trim 的统一 singleton collar：存在 `μ < 1`，`n` 充分大时 `‖z‖ > μ` 的
`z : closedDisk` 在 `vₙ = affineSubdisk (uₙ) 0 s` 下 fiber 是 singleton。近：统一局部单射（G1/G2 的
`C¹` 数据）；远：极限盘的 compact positive separation + `C⁰` 一致小。"eventually" 统一丢弃有限前缀。 -/
theorem second_trim_collar_R8 [T2Space M]
    {G : SmoothRiemannianMetric 𝓘(ℝ, E) M} {q : C(closedDisk, M)} {u : ℕ → C(closedDisk, M)}
    {ρ₁ s : ℝ} (hρ₁ : 0 < ρ₁) (hρ₁s : ρ₁ < s) (hs : s < 1)
    (hqs : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (diskExtension q) (Metric.ball (0 : ℂ) 1))
    (hus : ∀ n, ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (diskExtension (u n)) (Metric.ball (0 : ℂ) 1))
    (hqrank : ∀ z ∈ Metric.ball (0 : ℂ) 1,
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension q) z))
    (hqcol : ∀ z w : closedDisk, ρ₁ < ‖(z : ℂ)‖ → q z = q w → z = w)
    (hC0 : ∀ ε : ℝ≥0∞, 0 < ε → ∀ᶠ n in atTop, ∀ z, riemannianEDistOf G (u n z) (q z) < ε)
    (hCk : ∀ (p : M) (Kc : Set ℂ), IsCompact Kc →
      Kc ⊆ Metric.ball (0 : ℂ) 1 ∩ diskExtension q ⁻¹' (extChartAt 𝓘(ℝ, E) p).source →
      (∀ᶠ n in atTop, MapsTo (diskExtension (u n)) Kc (extChartAt 𝓘(ℝ, E) p).source) ∧
      ∀ k : ℕ, TendstoUniformlyOn
        (fun n => iteratedFDeriv ℝ k (fun z => extChartAt 𝓘(ℝ, E) p (diskExtension (u n) z)))
        (iteratedFDeriv ℝ k (fun z => extChartAt 𝓘(ℝ, E) p (diskExtension q z))) atTop Kc) :
    ∃ μ : ℝ, μ < 1 ∧ ∀ᶠ n in atTop, ∀ z w : closedDisk, μ < ‖(z : ℂ)‖ →
      affineSubdisk (u n) 0 s z = affineSubdisk (u n) 0 s w → z = w := by
  obtain ⟨μ, hμ, h⟩ := second_trim_rank_collar_core_R8 (G := G) hρ₁ hρ₁s hs hqs hus hqrank
    hqcol hC0 hCk
  refine ⟨μ, hμ, h.mono fun n hn z w hμz hzw => ?_⟩
  apply Subtype.ext
  refine hn.2 z z.property w w.property hμz ?_
  change diskExtension (u n) (0 + s • (z : ℂ)) = diskExtension (u n) (0 + s • (w : ℂ)) at hzw
  simpa only [zero_add] using hzw

end Disk


section Trace

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- 二次 trim 盘 `affineSubdisk u 0 s` 的 trace 是 smooth embedded loop：边界 singleton fiber（G3 collar
给出）⇒ trace 单射 ⇒ 闭嵌入；`s • D̄ ⊂ D°` 上的 rank（G2）⇒ immersed；smooth 来自
`smoothDiskExtension_affineSubdisk`。照 `exists_regular_concentric_restrictions` 的证明改写：这里没有
`SmoothDiskExtension q Q`，只有 `u` 的内部光滑性与 `v = u(s·)` 在单位圆上的 `mfderiv` 单射。 -/
theorem isSmoothEmbeddedLoop_trim_R8 [T2Space M] {g : SmoothRiemannianMetric 𝓘(ℝ, E) M}
    {γ : freeLoop M} {u : C(closedDisk, M)} (hu : IsMorreyDisk g γ u) {s : ℝ}
    (hs0 : 0 < s) (hs : s < 1)
    (hrank : ∀ z : ℂ, ‖z‖ = 1 → Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun w : ℂ => diskExtension u (s • w)) z))
    (hbd : ∀ z w : closedDisk, ‖(z : ℂ)‖ = 1 →
      affineSubdisk u 0 s z = affineSubdisk u 0 s w → z = w) :
    IsSmoothEmbeddedLoop (E := E) (diskTrace (affineSubdisk u 0 s)) := by
  have hinside : ‖(0 : ℂ)‖ + s < 1 := by simpa using hs
  have hExt := hu.smoothDiskExtension_affineSubdisk 0 s hs0.le hinside
  let d : C(closedDisk, M) := affineSubdisk u 0 s
  have hbInj : Function.Injective (diskTrace d) := by
    intro θ η hθη
    have h1 : d (diskBoundary θ) = d (diskBoundary η) := hθη
    have h2 := hbd (diskBoundary θ) (diskBoundary η) (Circle.norm_coe _) h1
    apply AddCircle.injective_toCircle one_ne_zero
    apply Subtype.ext
    change (diskBoundary θ : ℂ) = (diskBoundary η : ℂ)
    exact congrArg Subtype.val h2
  refine ⟨hExt.smoothUpToBoundary.trace,
    ((diskTrace d).continuous.isClosedEmbedding hbInj).isEmbedding, ?_⟩
  intro t
  let β : ℝ → ℂ := fun τ => circleMap 0 1 (2 * Real.pi * τ)
  have hβnorm : ∀ τ : ℝ, ‖β τ‖ = 1 := by
    intro τ
    simp only [β, circleMap, zero_add, norm_mul, Complex.norm_exp_ofReal_mul_I]
    simp
  have hβ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ β :=
    ((contDiff_circleMap 0 1).comp (contDiff_const.mul contDiff_id)).contMDiff
  have hθ : HasDerivAt (fun τ : ℝ => 2 * Real.pi * τ) (2 * Real.pi) t := by
    simpa only [mul_one, id_eq] using! (hasDerivAt_id t).const_mul (2 * Real.pi)
  have hβder : HasDerivAt β
      ((2 * Real.pi) • (circleMap 0 1 (2 * Real.pi * t) * Complex.I)) t := by
    simpa only [Function.comp_def, β] using
      (hasDerivAt_circleMap 0 1 (2 * Real.pi * t)).scomp t hθ
  have hβnonzero : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) β t 1 ≠ 0 := by
    rw [mfderiv_eq_fderiv]
    change fderiv ℝ β t 1 ≠ 0
    rw [fderiv_eq_smul_deriv, one_smul, hβder.deriv]
    apply smul_ne_zero (by positivity : (2 * Real.pi : ℝ) ≠ 0)
    apply mul_ne_zero _ Complex.I_ne_zero
    simp only [circleMap, zero_add]
    exact mul_ne_zero one_ne_zero (Complex.exp_ne_zero _)
  have htrace' : (fun τ : ℝ => diskTrace d (τ : loopCircle)) =
      (fun w : ℂ => diskExtension u (s • w)) ∘ β := by
    funext τ
    change diskExtension u (0 + s • (diskBoundary (τ : loopCircle) : ℂ)) = _
    rw [diskBoundary_coe]
    simp only [Function.comp_apply, β, circleMap, Complex.real_smul, zero_add, Complex.ofReal_one,
      one_mul]
  have hfd : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun w : ℂ => diskExtension u (s • w)) (β t) :=
    (contMDiffAt_scaled_R8 hu.smoothInterior hs0 hs
      (by simpa using (hβnorm t).le)).mdifferentiableAt (by simp)
  have hβdiff : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) β t := hβ.mdifferentiable (by simp) t
  rw [htrace', mfderiv_comp t hfd hβdiff]
  intro hzero
  apply hβnonzero
  apply hrank (β t) (hβnorm t)
  let Df : ℂ →L[ℝ] E := mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun w : ℂ => diskExtension u (s • w)) (β t)
  let Dβ : ℝ →L[ℝ] ℂ := mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) β t
  change Df (Dβ 1) = Df 0
  rw [map_zero]
  have hzeroE := congrArg
    (fun v : TangentSpace 𝓘(ℝ, E) (diskTrace d (t : loopCircle)) => (show E from v)) hzero
  change Df (Dβ 1) = 0 at hzeroE
  exact hzeroE

/-- 二次 trim 盘对**自身** trace 是 Morrey disk：`u` 是 smooth embedded `Γ` 的 Morrey disk（`finrank = 3`）
⇒ `IsMorreyDisk.exists_smooth_extension` 给 `SmoothDiskExtension` 从而全局 Lipschitz；再由
`IsMorreyDisk.affineSubdisk`（R2 机制：原盘 least-area + 源盘 chart 替换）。trimmed trace 的 immersed
是前提（G2 给出）。 -/
theorem isMorreyDisk_trim_R8 [T3Space M] {g : SmoothRiemannianMetric 𝓘(ℝ, E) M}
    {Γ : freeLoop M} (hΓ : IsSmoothEmbeddedLoop (E := E) Γ) (hd : Module.finrank ℝ E = 3)
    {u : C(closedDisk, M)} (hu : IsMorreyDisk g Γ u) {s : ℝ} (hs0 : 0 < s) (hs : s < 1)
    (himm : ∀ t : ℝ, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E)
      (fun τ : ℝ => diskTrace (affineSubdisk u 0 s) (τ : loopCircle)) t 1 ≠ 0) :
    IsMorreyDisk g (diskTrace (affineSubdisk u 0 s)) (affineSubdisk u 0 s) := by
  obtain ⟨U, hU⟩ := IsMorreyDisk.exists_smooth_extension g hd hΓ hu
  obtain ⟨L, hL⟩ := hU.lipschitz g
  exact hu.affineSubdisk hL 0 s hs0 (by simpa using hs) himm

/-- **G4**（R8）：二次 trim 盘对**自身** trace 的 `Kº`-Morrey 极小性。给定 G2（rank）与 G3（collar，
`μ < 1`）的 eventual 输出：`n` 充分大时 `diskTrace (affineSubdisk (uₙ) 0 s)` 是 smooth embedded loop，
且 `affineSubdisk (uₙ) 0 s` 对它是（度量 `Gn n` 的）Morrey disk。只用 `uₙ` 是 smooth embedded `Γ`
的 Morrey disk（`exists_smooth_extension` 给全局 Lipschitz），不用 `uₙ` 在原边界的收敛。 -/
theorem second_trim_own_trace_minimal_R8 [T3Space M]
    {Gn : ℕ → SmoothRiemannianMetric 𝓘(ℝ, E) M} {Γ : freeLoop M}
    (hΓ : IsSmoothEmbeddedLoop (E := E) Γ) (hd : Module.finrank ℝ E = 3)
    {u : ℕ → C(closedDisk, M)} (hu : ∀ n, IsMorreyDisk (Gn n) Γ (u n)) {s : ℝ}
    (hs0 : 0 < s) (hs : s < 1)
    (hrank : ∀ᶠ n in atTop, ∀ z ∈ Metric.closedBall (0 : ℂ) 1, Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun w : ℂ => diskExtension (u n) (s • w)) z))
    {μ : ℝ} (hμ : μ < 1)
    (hcol : ∀ᶠ n in atTop, ∀ z w : closedDisk, μ < ‖(z : ℂ)‖ →
      affineSubdisk (u n) 0 s z = affineSubdisk (u n) 0 s w → z = w) :
    ∀ᶠ n in atTop, IsSmoothEmbeddedLoop (E := E) (diskTrace (affineSubdisk (u n) 0 s)) ∧
      IsMorreyDisk (Gn n) (diskTrace (affineSubdisk (u n) 0 s)) (affineSubdisk (u n) 0 s) := by
  filter_upwards [hrank, hcol] with n h1 h2
  have hloop := isSmoothEmbeddedLoop_trim_R8 (hu n) hs0 hs
    (fun z hz => h1 z (mem_closedBall_zero_iff.mpr hz.le))
    (fun z w hz hzw => h2 z w (by rw [hz]; exact hμ) hzw)
  exact ⟨hloop, isMorreyDisk_trim_R8 hΓ hd (hu n) hs0 hs hloop.immersed⟩

end Trace

section Package

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- **R8 合同形**（`second_trim_regular_collar_MYD2` 的显式数据版）：从显式 `hC0`（C⁰）+ `hCk`
（C^∞_loc）收敛数据，`s ∈ (ρ₁, 1)`（`ρ₁` 是极限盘 `q` 的 R1 collar 半径）。存在 `μ < 1`，`n` 充分大时：
`vₙ = uₙ(s·)` 闭盘满秩（G2）、统一 collar（G3）、trimmed trace smooth embedded、`vₙ` 对自身 trace 是
`Gn n`-Morrey disk（G4）。不经 R7，不要 `uₙ` 在原 `S¹` 的 `C¹` 收敛、不要 `uₙ` 整盘满秩。 -/
theorem second_trim_regular_collar_R8 [T3Space M]
    {G : SmoothRiemannianMetric 𝓘(ℝ, E) M} {Gn : ℕ → SmoothRiemannianMetric 𝓘(ℝ, E) M}
    {Γ : freeLoop M} (hΓ : IsSmoothEmbeddedLoop (E := E) Γ) (hd : Module.finrank ℝ E = 3)
    {q : C(closedDisk, M)} (hq : IsMorreyDisk G Γ q)
    (hqrank : ∀ z ∈ Metric.ball (0 : ℂ) 1,
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension q) z))
    {ρ₁ s : ℝ} (hρ₁ : 0 < ρ₁) (hρ₁s : ρ₁ < s) (hs : s < 1)
    (hqcol : ∀ z w : closedDisk, ρ₁ < ‖(z : ℂ)‖ → q z = q w → z = w)
    {u : ℕ → C(closedDisk, M)} (hu : ∀ n, IsMorreyDisk (Gn n) Γ (u n))
    (hC0 : ∀ ε : ℝ≥0∞, 0 < ε → ∀ᶠ n in atTop, ∀ z, riemannianEDistOf G (u n z) (q z) < ε)
    (hCk : ∀ (p : M) (Kc : Set ℂ), IsCompact Kc →
      Kc ⊆ Metric.ball (0 : ℂ) 1 ∩ diskExtension q ⁻¹' (extChartAt 𝓘(ℝ, E) p).source →
      (∀ᶠ n in atTop, MapsTo (diskExtension (u n)) Kc (extChartAt 𝓘(ℝ, E) p).source) ∧
      ∀ k : ℕ, TendstoUniformlyOn
        (fun n => iteratedFDeriv ℝ k (fun z => extChartAt 𝓘(ℝ, E) p (diskExtension (u n) z)))
        (iteratedFDeriv ℝ k (fun z => extChartAt 𝓘(ℝ, E) p (diskExtension q z))) atTop Kc) :
    ∃ μ : ℝ, μ < 1 ∧ ∀ᶠ n in atTop,
      (∀ z ∈ Metric.closedBall (0 : ℂ) 1, Function.Injective
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun w : ℂ => diskExtension (u n) (s • w)) z)) ∧
      (∀ z w : closedDisk, μ < ‖(z : ℂ)‖ →
        affineSubdisk (u n) 0 s z = affineSubdisk (u n) 0 s w → z = w) ∧
      IsSmoothEmbeddedLoop (E := E) (diskTrace (affineSubdisk (u n) 0 s)) ∧
      IsMorreyDisk (Gn n) (diskTrace (affineSubdisk (u n) 0 s)) (affineSubdisk (u n) 0 s) := by
  have hs0 : 0 < s := hρ₁.trans hρ₁s
  obtain ⟨μ, hμ, hcol⟩ := second_trim_collar_R8 (G := G) hρ₁ hρ₁s hs hq.smoothInterior
    (fun n => (hu n).smoothInterior) hqrank hqcol hC0 hCk
  have hrank := second_trim_rank_R8 hs0 hs hq.smoothInterior (fun n => (hu n).smoothInterior)
    hqrank hCk
  have hown := second_trim_own_trace_minimal_R8 hΓ hd hu hs0 hs hrank hμ hcol
  refine ⟨μ, hμ, ?_⟩
  filter_upwards [hrank, hcol, hown] with n h1 h2 h3
  exact ⟨h1, h2, h3.1, h3.2⟩

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- **G5**（R8-C1）：R15 / MY-13 需要的 chartwise `C¹` 极限数据（`hv / hval / hchart / hder`），
`S = ball 0 1`，`vₙ z = diskExtension (uₙ) (s • z)`，极限是 trimmed 盘
`diskExtension (affineSubdisk q 0 s)`（与 `noTransverse_of_c1_limit_trimmed_R15T` / ADP
`noTransverse_of_c1_limit_open_trimmed_ADP` 的前提逐字对齐；`vₙ` 的单射性是 R9–R14 的输出，这里**不**给）。
另附极限盘在 `ball 0 1` 上 `C¹`（MY-13 的 `hf₀`）。 -/
theorem second_trim_c1_data_R8 {q : C(closedDisk, M)} {u : ℕ → C(closedDisk, M)} {s : ℝ}
    (hs0 : 0 < s) (hs : s < 1)
    (hqs : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (diskExtension q) (Metric.ball (0 : ℂ) 1))
    (hus : ∀ n, ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (diskExtension (u n)) (Metric.ball (0 : ℂ) 1))
    (hCk : ∀ (p : M) (Kc : Set ℂ), IsCompact Kc →
      Kc ⊆ Metric.ball (0 : ℂ) 1 ∩ diskExtension q ⁻¹' (extChartAt 𝓘(ℝ, E) p).source →
      (∀ᶠ n in atTop, MapsTo (diskExtension (u n)) Kc (extChartAt 𝓘(ℝ, E) p).source) ∧
      ∀ k : ℕ, TendstoUniformlyOn
        (fun n => iteratedFDeriv ℝ k (fun z => extChartAt 𝓘(ℝ, E) p (diskExtension (u n) z)))
        (iteratedFDeriv ℝ k (fun z => extChartAt 𝓘(ℝ, E) p (diskExtension q z))) atTop Kc) :
    (∀ n, MDifferentiableOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun z : ℂ => diskExtension (u n) (s • z))
      (Metric.ball (0 : ℂ) 1)) ∧
    ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 (diskExtension (affineSubdisk q 0 s))
      (Metric.ball (0 : ℂ) 1) ∧
    (∀ p : M, ∀ x ∈ Metric.ball (0 : ℂ) 1,
      diskExtension (affineSubdisk q 0 s) x ∈ (extChartAt 𝓘(ℝ, E) p).source →
      Tendsto (fun n => extChartAt 𝓘(ℝ, E) p (diskExtension (u n) (s • x))) atTop
        (𝓝 (extChartAt 𝓘(ℝ, E) p (diskExtension (affineSubdisk q 0 s) x)))) ∧
    (∀ p : M, ∀ K : Set ℂ, IsCompact K →
      K ⊆ Metric.ball (0 : ℂ) 1 ∩
        diskExtension (affineSubdisk q 0 s) ⁻¹' (extChartAt 𝓘(ℝ, E) p).source →
      ∀ᶠ n in atTop, MapsTo (fun z : ℂ => diskExtension (u n) (s • z)) K
        (extChartAt 𝓘(ℝ, E) p).source) ∧
    ∀ p : M, ∀ K : Set ℂ, IsCompact K →
      K ⊆ Metric.ball (0 : ℂ) 1 ∩
        diskExtension (affineSubdisk q 0 s) ⁻¹' (extChartAt 𝓘(ℝ, E) p).source →
      TendstoUniformlyOn
        (fun n x => fderiv ℝ (fun z => extChartAt 𝓘(ℝ, E) p (diskExtension (u n) (s • z))) x)
        (fun x => fderiv ℝ
          (fun z => extChartAt 𝓘(ℝ, E) p (diskExtension (affineSubdisk q 0 s) z)) x)
        atTop K := by
  have hball : ∀ x ∈ Metric.ball (0 : ℂ) 1, x ∈ Metric.closedBall (0 : ℂ) 1 :=
    fun x hx => Metric.ball_subset_closedBall hx
  -- 极限盘在 `ball` 内与 `dE q (s • ·)` 局部相等
  have hval_eq : ∀ x ∈ Metric.ball (0 : ℂ) 1,
      diskExtension (affineSubdisk q 0 s) x = diskExtension q (s • x) :=
    fun x hx => diskExtension_affineSubdisk_zero_apply_R15T q s hx
  -- 把 `K ⊆ ball ∩ dE(q_s)⁻¹' source` 转成 G1 的形
  have hKconv : ∀ (p : M) (K : Set ℂ),
      K ⊆ Metric.ball (0 : ℂ) 1 ∩ diskExtension (affineSubdisk q 0 s) ⁻¹'
        (extChartAt 𝓘(ℝ, E) p).source →
      K ⊆ Metric.closedBall (0 : ℂ) 1 ∩
        (fun z => diskExtension q (s • z)) ⁻¹' (extChartAt 𝓘(ℝ, E) p).source := by
    intro p K hK x hx
    refine ⟨hball x (hK hx).1, ?_⟩
    have := (hK hx).2
    simp only [mem_preimage] at this ⊢
    rwa [hval_eq x (hK hx).1] at this
  refine ⟨fun n x hx => ?_, ?_, fun p x hx hxs => ?_, fun p K hK hKs => ?_,
    fun p K hK hKs => ?_⟩
  · exact ((contMDiffAt_scaled_R8 (hus n) hs0 hs (hball x hx)).mdifferentiableAt
      (by simp)).mdifferentiableWithinAt
  · intro x hx
    have hsm : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 (fun w : ℂ => diskExtension q (s • w)) x :=
      (contMDiffAt_scaled_R8 hqs hs0 hs (hball x hx)).of_le (by simp)
    refine (hsm.congr_of_eventuallyEq ?_).contMDiffWithinAt
    filter_upwards [Metric.isOpen_ball.mem_nhds hx] with w hw using hval_eq w hw
  · have hK1 : IsCompact ({x} : Set ℂ) := isCompact_singleton
    have hsub : ({x} : Set ℂ) ⊆ Metric.closedBall (0 : ℂ) 1 ∩
        (fun z => diskExtension q (s • z)) ⁻¹' (extChartAt 𝓘(ℝ, E) p).source := by
      intro y hy
      rw [Set.mem_singleton_iff.mp hy]
      refine ⟨hball x hx, ?_⟩
      simp only [mem_preimage]
      rwa [hval_eq x hx] at hxs
    have h := (second_trim_c1_R8 hs0 hs hCk p hK1 hsub).2.1
    rw [hval_eq x hx]
    exact h.tendsto_at (Set.mem_singleton x)
  · exact (second_trim_c1_R8 hs0 hs hCk p hK (hKconv p K hKs)).1
  · have h := (second_trim_c1_R8 hs0 hs hCk p hK (hKconv p K hKs)).2.2
    refine h.congr_right fun x hx => ?_
    have hx1 : x ∈ Metric.ball (0 : ℂ) 1 := (hKs hx).1
    have hev : (fun z => extChartAt 𝓘(ℝ, E) p (diskExtension (affineSubdisk q 0 s) z)) =ᶠ[𝓝 x]
        fun z => extChartAt 𝓘(ℝ, E) p (diskExtension q (s • z)) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hx1] with w hw
      rw [hval_eq w hw]
    exact (hev.fderiv_eq).symm

end Package

end DifferentialGeometry.Geometry
