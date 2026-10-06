import DifferentialGeometry.Geometry.Geodesic.ConformalPlane.PositiveExtensionGM
import DifferentialGeometry.Geometry.Geodesic.ConformalPlane.CompleteMinimizerGM
import DifferentialGeometry.Geometry.Geodesic.ConformalPlane.ConformalCompleteGM
import DifferentialGeometry.Geometry.Geodesic.ConformalPlane.SegmentDistanceGM
import DifferentialGeometry.Geometry.Geodesic.ConformalPlane.ArcReparamGM

/-!
# IMS05′ (5)：共形度量 `ĝ = u² g_Σ` 下到内蕴球面的极小路径（O-W-GEO-MIN G1，后缀 `_GM`）

数据（全部显式参数，无新结构 / 新 Prop）：开集 `Ω ⊆ ℂ`，`g_Σ = lam |dz|²`（`lam > 0` 光滑 on `Ω`），
`u > 0` 光滑 on `Ω`，`ĝ = u² g_Σ = ρ² |dz|²`，`ρ = u √lam`。到 `p` 的内蕴距离以函数 `d` 进入：
`ContinuousOn d Ω`、线段 Lipschitz `hseg`（见 `SegmentDistanceGM`）、`d p = 0`；闭内蕴球
`B̄ = {z ∈ Ω | d z ≤ r}` 紧（`r > 0`）。

**主定理 `exists_minimizing_path_to_sphere_GM`**：存在光滑 `c : ℝ → ℂ`、`L`、全局光滑正函数 `ρt`、
开 `V`（`B̄ ⊆ V ⊆ Ω`，`ρt = u √lam` on `V`）：`c 0 = p`、`d (c L) = r`（终点在内蕴球面 `S_r` 上）、
`r ≤ L`、`c [0, L] ⊆ B̄`、`[0, L)` 上 `d ∘ c < r`（首次碰面）、`c′ ≠ 0` 处处、`g_Σ`-弧长参数化
`lam(c) ‖c′‖² = 1`（S-W-GEO 的 `harc`）、`hloc : ρt =ᶠ[𝓝 (c s)] u √lam`，且 `c` 在**所有**同端点
`C¹` 曲线中 `ρt`-加权长度最小（`hmin`）——逐字是 S-W-GEO `weighted_stability_of_minimizing_GE` 的输入。
另给 `V` 内的局部极小性（`u √lam` 形式，`exists_minimizing_path_to_sphere_local_GM`）。

证明（路线 R1′）：cutoff 把 `ρ` 延拓为全平面光滑正函数 `ρt = χρ + (1−χ)`（`= ρ` 在 `V` 上，
有正下界 δ）；`riemannianMetricComplete_conformal_GM` ⇒ `(ℂ, ρt²|dz|²)` complete；`y ∈ S_r` 取
`d_{ĝ}(p, ·)` 在紧 `S_r` 上的最小点；Hopf–Rinow 极小测地线 `γ : p → y`
（`exists_minimizing_geodesic_of_complete_GM`）；`d_{ĝ}(p, γ t) ≤ t < L̂ = d_{ĝ}(p, y)`
⇒ `γ` 在 `[0, L̂)` 上不碰 `S_r` ⇒ 连通性 ⇒ 在开球里（`mem_ball_of_avoid_sphere_GM`）；最后按
`g_Σ`-弧长重参数化（`exists_reparam_GM`，权 `1/ũ(γ)`，`ũ` 为 `u` 的正延拓），极小性经两次换元
（`weightedLength_comp_GM`）传过去，`r ≤ L` 由 `le_add_integral_of_segment_GM`。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Manifold
open scoped Topology ContDiff Manifold ENNReal

namespace DifferentialGeometry.Geometry

/-- 紧闭球 `B̄ ∋ p`（`d p < r`）⇒ 内蕴球面 `S_r = {z ∈ Ω | d z = r}` 非空（`ℂ` 连通且非紧）。 -/
theorem exists_mem_sphere_GM {Ω : Set ℂ} (hΩ : IsOpen Ω) {d : ℂ → ℝ} (hd : ContinuousOn d Ω)
    {p : ℂ} (hp : p ∈ Ω) {r : ℝ} (hpr : d p < r) (hK : IsCompact {z | z ∈ Ω ∧ d z ≤ r}) :
    ∃ y, y ∈ Ω ∧ d y = r := by
  by_contra hne'
  have hne : ∀ z ∈ Ω, d z ≠ r := fun z hz h => hne' ⟨z, hz, h⟩
  have hB : IsOpen (Ω ∩ d ⁻¹' Iio r) := hd.isOpen_inter_preimage hΩ isOpen_Iio
  have hBK : Ω ∩ d ⁻¹' Iio r = {z | z ∈ Ω ∧ d z ≤ r} := by
    ext z
    constructor
    · rintro ⟨hz, hlt⟩
      exact ⟨hz, le_of_lt hlt⟩
    · rintro ⟨hz, hle⟩
      exact ⟨hz, lt_of_le_of_ne hle (hne z hz)⟩
  have hclo : IsClopen (Ω ∩ d ⁻¹' Iio r) := ⟨hBK ▸ hK.isClosed, hB⟩
  rcases isClopen_iff.mp hclo with h | h
  · have : p ∈ Ω ∩ d ⁻¹' Iio r := ⟨hp, hpr⟩
    rw [h] at this
    exact this
  · rw [hBK] at h
    rw [h] at hK
    exact noncompact_univ ℂ hK

/-- 首次碰面：连续 `γ` 起点在开球 `{z ∈ Ω | d z < r}` 内、`[a, b)` 上不碰 `S_r`、`B̄` 紧
⇒ `γ [a, b)` 留在开球内（`ℂ ∖ S_r = B ⊔ (ℂ ∖ B̄)` 两开集不交 + `[a, b)` 连通）。 -/
theorem mem_ball_of_avoid_sphere_GM {Ω : Set ℂ} (hΩ : IsOpen Ω) {d : ℂ → ℝ}
    (hd : ContinuousOn d Ω) {r : ℝ} (hK : IsCompact {z | z ∈ Ω ∧ d z ≤ r}) {γ : ℝ → ℂ}
    (hγ : Continuous γ) {a b : ℝ} (hab : a < b) (hγa : γ a ∈ Ω ∧ d (γ a) < r)
    (havoid : ∀ t ∈ Ico a b, ¬ (γ t ∈ Ω ∧ d (γ t) = r)) :
    ∀ t ∈ Ico a b, γ t ∈ Ω ∧ d (γ t) < r := by
  have hB : IsOpen (Ω ∩ d ⁻¹' Iio r) := hd.isOpen_inter_preimage hΩ isOpen_Iio
  have hKc : IsOpen {z | z ∈ Ω ∧ d z ≤ r}ᶜ := hK.isClosed.isOpen_compl
  have hdisj : Disjoint (Ω ∩ d ⁻¹' Iio r) {z | z ∈ Ω ∧ d z ≤ r}ᶜ :=
    Set.disjoint_left.mpr fun z hz hz' => hz' ⟨hz.1, le_of_lt hz.2⟩
  have hsub : γ '' Ico a b ⊆ (Ω ∩ d ⁻¹' Iio r) ∪ {z | z ∈ Ω ∧ d z ≤ r}ᶜ := by
    rintro _ ⟨t, ht, rfl⟩
    by_cases hk : γ t ∈ {z | z ∈ Ω ∧ d z ≤ r}
    · exact Or.inl ⟨hk.1, lt_of_le_of_ne hk.2 fun heq => havoid t ht ⟨hk.1, heq⟩⟩
    · exact Or.inr hk
  have hne : (γ '' Ico a b ∩ (Ω ∩ d ⁻¹' Iio r)).Nonempty :=
    ⟨γ a, ⟨a, left_mem_Ico.mpr hab, rfl⟩, hγa.1, hγa.2⟩
  have hpre : IsPreconnected (γ '' Ico a b) := isPreconnected_Ico.image γ hγ.continuousOn
  have key := hpre.subset_left_of_subset_union hB hKc hdisj hsub hne
  intro t ht
  exact key ⟨t, ht, rfl⟩

/-- **G1 主定理**（IMS05′ (5) 的几何部分）：共形度量 `ĝ = (u √lam)² |dz|²` 下从 `p` 到内蕴球面
`S_r` 的极小路径：`g_Σ`-弧长参数化、首次碰面、`r ≤ L`；全局光滑正 `ρt`（在 `B̄` 的开邻域 `V` 上
`= u √lam`），`c` 在所有同端点 `C¹` 曲线中 `ρt`-加权长度最小。 -/
theorem exists_minimizing_path_to_sphere_GM {Ω : Set ℂ} (hΩ : IsOpen Ω) {lam u d : ℂ → ℝ}
    (hlam : ContDiffOn ℝ ∞ lam Ω) (hu : ContDiffOn ℝ ∞ u Ω)
    (hlam0 : ∀ z ∈ Ω, 0 < lam z) (hu0 : ∀ z ∈ Ω, 0 < u z) (hd : ContinuousOn d Ω)
    (hseg : ∀ x y : ℂ, segment ℝ x y ⊆ Ω →
      d y ≤ d x + ∫ t in (0 : ℝ)..1, Real.sqrt (lam (x + t • (y - x))) * ‖y - x‖)
    {p : ℂ} (hp : p ∈ Ω) (hdp : d p = 0) {r : ℝ} (hr : 0 < r)
    (hK : IsCompact {z | z ∈ Ω ∧ d z ≤ r}) :
    ∃ (c : ℝ → ℂ) (L : ℝ) (ρt : ℂ → ℝ) (V : Set ℂ),
      IsOpen V ∧ {z | z ∈ Ω ∧ d z ≤ r} ⊆ V ∧ V ⊆ Ω ∧
      ContDiff ℝ ∞ ρt ∧ (∀ z, 0 < ρt z) ∧ (∀ z ∈ V, ρt z = u z * Real.sqrt (lam z)) ∧
      (∀ s ∈ Icc 0 L, ρt =ᶠ[𝓝 (c s)] fun z => u z * Real.sqrt (lam z)) ∧
      ContDiff ℝ ∞ c ∧ (∀ s, deriv c s ≠ 0) ∧ c 0 = p ∧ d (c L) = r ∧ r ≤ L ∧
      (∀ s ∈ Icc 0 L, c s ∈ Ω ∧ d (c s) ≤ r) ∧ (∀ s ∈ Ico 0 L, d (c s) < r) ∧
      (∀ s ∈ Icc 0 L, lam (c s) * ‖deriv c s‖ ^ 2 = 1) ∧
      (∀ η : ℝ → ℂ, ContDiff ℝ 1 η → η 0 = c 0 → η L = c L →
        ∫ s in (0 : ℝ)..L, ρt (c s) * ‖deriv c s‖ ≤ ∫ s in (0 : ℝ)..L, ρt (η s) * ‖deriv η s‖) := by
  have hKΩ : {z | z ∈ Ω ∧ d z ≤ r} ⊆ Ω := fun z hz => hz.1
  -- cutoff 与正延拓
  obtain ⟨χ, V, hχ, hV, hKV, hVΩ, hχ1, hχ01, hχc, hχΩ⟩ := exists_cutoff_GM hΩ hK hKΩ
  set ρ : ℂ → ℝ := fun z => u z * Real.sqrt (lam z) with hρdef
  have hρ : ContDiffOn ℝ ∞ ρ Ω := hu.mul (hlam.sqrt fun z hz => (hlam0 z hz).ne')
  have hρ0 : ∀ z ∈ Ω, 0 < ρ z := fun z hz =>
    mul_pos (hu0 z hz) (Real.sqrt_pos.mpr (hlam0 z hz))
  set ρt : ℂ → ℝ := posExt_GM χ ρ with hρtdef
  have hρt : ContDiff ℝ ∞ ρt := contDiff_posExt_GM hΩ hχ hχΩ hρ
  have hρtpos : ∀ z, 0 < ρt z := posExt_pos_GM hχΩ hχ01 hρ0
  have hρtV : ∀ z ∈ V, ρt z = ρ z := fun z hz => posExt_eq_GM (hχ1 z hz)
  obtain ⟨δ, hδ, hδρ⟩ := exists_le_posExt_GM hχΩ hχc hχ01 hρ.continuousOn hρ0
  have hf : ContDiff ℝ ∞ (fun z => Real.log (ρt z)) := hρt.log fun z => (hρtpos z).ne'
  -- `(ℂ, ρt²|dz|²)` complete
  set g := conformalEuclideanMetric (fun z => Real.log (ρt z)) hf with hgdef
  have hg : RiemannianMetricComplete (I := 𝓘(ℝ, ℂ)) g :=
    riemannianMetricComplete_conformal_GM hρtpos hf hδ hδρ
  have hspeed : ∀ z v : ℂ, Real.sqrt (g.inner z v v) = ρt z * ‖v‖ :=
    sqrt_conformalEuclideanMetric_inner_GM hρtpos hf
  have harcLen : ∀ (η : ℝ → ℂ) (a b : ℝ),
      Riemannian.Variation.arcLength (I := 𝓘(ℝ, ℂ)) g η a b =
        ∫ t in a..b, ρt (η t) * ‖deriv η t‖ := by
    intro η a b
    unfold Riemannian.Variation.arcLength
    refine intervalIntegral.integral_congr fun t _ => ?_
    change Real.sqrt (g.inner (η t) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) η t (1 : ℝ))
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) η t (1 : ℝ))) = ρt (η t) * ‖deriv η t‖
    rw [mfderiv_curve_complex_GM, hspeed]
  -- 终点 y：`d_ĝ(p, ·)` 在紧 `S_r` 上的最小点
  obtain ⟨y₀, hy₀⟩ := exists_mem_sphere_GM hΩ hd hp (by rw [hdp]; exact hr) hK
  have hSclosed : IsClosed ({z | z ∈ Ω ∧ d z ≤ r} ∩ d ⁻¹' {r}) :=
    ContinuousOn.preimage_isClosed_of_isClosed (hd.mono hKΩ) hK.isClosed isClosed_singleton
  have hScpt : IsCompact ({z | z ∈ Ω ∧ d z ≤ r} ∩ d ⁻¹' {r}) :=
    hK.of_isClosed_subset hSclosed inter_subset_left
  obtain ⟨y, hyS, hymin⟩ := hScpt.exists_isMinOn ⟨y₀, ⟨hy₀.1, hy₀.2.le⟩, hy₀.2⟩
    (continuous_riemannianEDistOf_GM g p).continuousOn
  have hyd : d y = r := hyS.2
  have hpy : p ≠ y := by
    intro h
    rw [← h, hdp] at hyd
    exact hr.ne hyd
  -- Hopf–Rinow
  have := t2Space_tangentBundle_complex_GM
  have := neZero_finrank_complex_GM
  obtain ⟨γ, Lh, hLh, hγ0, hγL, hγsm, hunit, hmin, hdist, hdle⟩ :=
    exists_minimizing_geodesic_of_complete_GM g hg p y hpy
  have hγ : ContDiff ℝ ∞ γ := contMDiff_iff_contDiff.mp hγsm
  have hγ1 : ContDiff ℝ 1 γ := hγ.of_le (by simp)
  -- 首次碰面
  have havoid : ∀ t ∈ Ico 0 Lh, ¬ (γ t ∈ Ω ∧ d (γ t) = r) := by
    rintro t ht ⟨h1, h2⟩
    have hmem : γ t ∈ {z | z ∈ Ω ∧ d z ≤ r} ∩ d ⁻¹' {r} := ⟨⟨h1, h2.le⟩, h2⟩
    have h3 : riemannianEDistOf g p y ≤ riemannianEDistOf g p (γ t) :=
      isMinOn_iff.mp hymin _ hmem
    have h4 := hdle t (Ico_subset_Icc_self ht)
    rw [hdist] at h3
    have h5 := (ENNReal.ofReal_le_ofReal_iff ht.1).mp (h3.trans h4)
    exact absurd ht.2 (not_lt.mpr h5)
  have hball := mem_ball_of_avoid_sphere_GM hΩ hd hK hγ.continuous hLh
    ⟨by rw [hγ0]; exact hp, by rw [hγ0, hdp]; exact hr⟩ havoid
  have hγK : ∀ t ∈ Icc 0 Lh, γ t ∈ Ω ∧ d (γ t) ≤ r := by
    intro t ht
    rcases eq_or_lt_of_le ht.2 with h | h
    · rw [h, hγL]
      exact hyS.1
    · exact ⟨(hball t ⟨ht.1, h⟩).1, (hball t ⟨ht.1, h⟩).2.le⟩
  have hγspeed : ∀ t, ρt (γ t) * ‖deriv γ t‖ = 1 := by
    intro t
    have h := hunit t
    rw [mfderiv_curve_complex_GM] at h
    rw [← hspeed, h, Real.sqrt_one]
  have hγreg : ∀ t, deriv γ t ≠ 0 := by
    intro t h0
    have h := hγspeed t
    rw [h0, norm_zero, mul_zero] at h
    exact zero_ne_one h
  -- g_Σ-弧长重参数化
  have hut : ContDiff ℝ ∞ (posExt_GM χ u) := contDiff_posExt_GM hΩ hχ hχΩ hu
  have hutpos : ∀ z, 0 < posExt_GM χ u z := posExt_pos_GM hχΩ hχ01 hu0
  obtain ⟨C, hC⟩ := exists_posExt_le_GM hχΩ hχc hχ01 hu.continuousOn
  have hCpos : 0 < C := (hutpos 0).trans_le (hC 0)
  set w : ℝ → ℝ := fun t => (posExt_GM χ u (γ t))⁻¹ with hwdef
  have hw : ContDiff ℝ ∞ w := (hut.comp hγ).inv fun t => (hutpos _).ne'
  have hwc : ∀ t, C⁻¹ ≤ w t := fun t => inv_anti₀ (hutpos _) (hC _)
  have hwpos : ∀ t, 0 < w t := fun t => inv_pos.mpr (hutpos _)
  obtain ⟨σ, τ, hσsm, hτsm, hστ, hτσ, hσd, hτd, hσmono, hτmono, hσ0⟩ :=
    exists_reparam_GM hw (inv_pos.mpr hCpos) hwc
  have hτ0 : τ 0 = 0 := by
    have h := hτσ 0
    rwa [hσ0] at h
  set L : ℝ := σ Lh with hLdef
  have hτL : τ L = Lh := hτσ Lh
  set c : ℝ → ℂ := fun s => γ (τ s) with hcdef
  have hτIcc : ∀ s ∈ Icc 0 L, τ s ∈ Icc 0 Lh := fun s hs =>
    ⟨hτ0 ▸ hτmono.monotone hs.1, hτL ▸ hτmono.monotone hs.2⟩
  have hτIco : ∀ s ∈ Ico 0 L, τ s ∈ Ico 0 Lh := fun s hs =>
    ⟨hτ0 ▸ hτmono.monotone hs.1, hτL ▸ hτmono hs.2⟩
  have hc : ContDiff ℝ ∞ c := hγ.comp hτsm
  have hc1 : ContDiff ℝ 1 c := hc.of_le (by simp)
  have hc0 : c 0 = p := by simp only [hcdef, hτ0, hγ0]
  have hcL : c L = y := by simp only [hcdef, hτL, hγL]
  have hcσ : c ∘ σ = γ := funext fun t => by simp only [hcdef, Function.comp_apply, hτσ]
  have hcd : ∀ s, deriv c s = (w (τ s))⁻¹ • deriv γ (τ s) := fun s =>
    ((hγ1.differentiable one_ne_zero (τ s)).hasDerivAt.scomp s (hτd s)).deriv
  have hcreg : ∀ s, deriv c s ≠ 0 := fun s => by
    rw [hcd]
    exact smul_ne_zero (inv_ne_zero (hwpos _).ne') (hγreg _)
  have hcIcc : ∀ s ∈ Icc 0 L, c s ∈ Ω ∧ d (c s) ≤ r := fun s hs => hγK _ (hτIcc s hs)
  have harc : ∀ s ∈ Icc 0 L, lam (c s) * ‖deriv c s‖ ^ 2 = 1 := by
    intro s hs
    have ht := hτIcc s hs
    have hΩt := (hγK _ ht).1
    have hVt : γ (τ s) ∈ V := hKV (hγK _ ht)
    have hwt : (w (τ s))⁻¹ = u (γ (τ s)) := by
      rw [hwdef, inv_inv, posExt_eq_GM (hχ1 _ hVt)]
    have h1 := hγspeed (τ s)
    rw [hρtV _ hVt] at h1
    have hsq : Real.sqrt (lam (γ (τ s))) ^ 2 = lam (γ (τ s)) := Real.sq_sqrt (hlam0 _ hΩt).le
    rw [hcd, hwt, norm_smul, Real.norm_eq_abs, abs_of_pos (hu0 _ hΩt)]
    change lam (γ (τ s)) * (u (γ (τ s)) * ‖deriv γ (τ s)‖) ^ 2 = 1
    have h2 : lam (γ (τ s)) * (u (γ (τ s)) * ‖deriv γ (τ s)‖) ^ 2 =
        (u (γ (τ s)) * Real.sqrt (lam (γ (τ s))) * ‖deriv γ (τ s)‖) ^ 2 := by
      rw [mul_pow, mul_pow, mul_pow, hsq]
      ring
    rw [h2]
    change (ρ (γ (τ s)) * ‖deriv γ (τ s)‖) ^ 2 = 1
    rw [h1, one_pow]
  have hL0 : 0 ≤ L := by
    rw [hLdef, ← hσ0]
    exact hσmono.monotone hLh.le
  have hrL : r ≤ L := by
    have h := le_add_integral_of_segment_GM hΩ hlam.continuousOn hd hseg hc1 hL0
      fun s hs => (hcIcc s hs).1
    have hint : ∫ s in (0 : ℝ)..L, Real.sqrt (lam (c s)) * ‖deriv c s‖ = L := by
      have hcongr : ∫ s in (0 : ℝ)..L, Real.sqrt (lam (c s)) * ‖deriv c s‖ =
          ∫ _s in (0 : ℝ)..L, (1 : ℝ) := by
        refine intervalIntegral.integral_congr fun s hs => ?_
        rw [uIcc_of_le hL0] at hs
        have hΩs := (hcIcc s hs).1
        change Real.sqrt (lam (c s)) * ‖deriv c s‖ = 1
        rw [← Real.sqrt_sq (norm_nonneg (deriv c s)), ← Real.sqrt_mul (hlam0 _ hΩs).le,
          harc s hs, Real.sqrt_one]
      rw [hcongr]
      simp
    rw [hcL, hyd, hc0, hdp, hint] at h
    linarith
  have hloc : ∀ s ∈ Icc 0 L, ρt =ᶠ[𝓝 (c s)] fun z => u z * Real.sqrt (lam z) := fun s hs =>
    Filter.eventuallyEq_of_mem (hV.mem_nhds (hKV (hcIcc s hs))) fun z hz => hρtV z hz
  refine ⟨c, L, ρt, V, hV, hKV, hVΩ, hρt, hρtpos, hρtV, hloc, hc, hcreg, hc0,
    by rw [hcL]; exact hyd, hrL, hcIcc, fun s hs => (hball _ (hτIco s hs)).2, harc, ?_⟩
  -- 全局极小性：两次换元
  intro η hη hη0 hηL
  have hηh : ContDiff ℝ 1 (η ∘ σ) := hη.comp (hσsm.of_le (by simp))
  have hηh0 : (η ∘ σ) 0 = γ 0 := by
    simp only [Function.comp_apply, hσ0, hη0, hc0, hγ0]
  have hηhL : (η ∘ σ) Lh = γ Lh := by
    change η L = γ Lh
    rw [hηL, hcL, hγL]
  have h1 := hmin (η ∘ σ) hηh.contMDiff.contMDiffOn hηh0 hηhL
  rw [harcLen γ 0 Lh, harcLen (η ∘ σ) 0 Lh] at h1
  have e1 := weightedLength_comp_GM (Ω := univ) hρt.continuous.continuousOn hσd hw.continuous
    hwpos hη hLh.le (fun _ _ => mem_univ _)
  have e2 := weightedLength_comp_GM (Ω := univ) hρt.continuous.continuousOn hσd hw.continuous
    hwpos hc1 hLh.le (fun _ _ => mem_univ _)
  rw [hcσ] at e2
  rw [hσ0] at e1 e2
  change ∫ t in (0 : ℝ)..Lh, ρt ((η ∘ σ) t) * ‖deriv (η ∘ σ) t‖ =
    ∫ s in (0 : ℝ)..L, ρt (η s) * ‖deriv η s‖ at e1
  change ∫ t in (0 : ℝ)..Lh, ρt (γ t) * ‖deriv γ t‖ =
    ∫ s in (0 : ℝ)..L, ρt (c s) * ‖deriv c s‖ at e2
  rw [← e1, ← e2]
  exact h1

/-- 局部形状（S-W-GEO (B) 入口）：`V` 内同端点 `C¹` 曲线中 `ĝ`-长度 `∫ u √lam (c) ‖c′‖` 最小。 -/
theorem weightedLength_le_local_GM {u lam ρt : ℂ → ℝ} {V : Set ℂ}
    (hρtV : ∀ z ∈ V, ρt z = u z * Real.sqrt (lam z)) {c : ℝ → ℂ} {L : ℝ} (hL : 0 ≤ L)
    (hcV : ∀ s ∈ Icc 0 L, c s ∈ V)
    (hmin : ∀ η : ℝ → ℂ, ContDiff ℝ 1 η → η 0 = c 0 → η L = c L →
      ∫ s in (0 : ℝ)..L, ρt (c s) * ‖deriv c s‖ ≤ ∫ s in (0 : ℝ)..L, ρt (η s) * ‖deriv η s‖)
    (η : ℝ → ℂ) (hη : ContDiff ℝ 1 η) (hηV : ∀ s ∈ Icc 0 L, η s ∈ V) (h0 : η 0 = c 0)
    (h1 : η L = c L) :
    ∫ s in (0 : ℝ)..L, u (c s) * Real.sqrt (lam (c s)) * ‖deriv c s‖ ≤
      ∫ s in (0 : ℝ)..L, u (η s) * Real.sqrt (lam (η s)) * ‖deriv η s‖ := by
  have e : ∀ ζ : ℝ → ℂ, (∀ s ∈ Icc 0 L, ζ s ∈ V) →
      ∫ s in (0 : ℝ)..L, ρt (ζ s) * ‖deriv ζ s‖ =
        ∫ s in (0 : ℝ)..L, u (ζ s) * Real.sqrt (lam (ζ s)) * ‖deriv ζ s‖ := by
    intro ζ hζ
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le hL] at hs
    simp only [hρtV _ (hζ s hs)]
  rw [← e c hcV, ← e η hηV]
  exact hmin η hη h0 h1

/-- G1 的局部形状版本：`U₀ = V`（`B̄ ⊆ V ⊆ Ω` 开），`V` 内同端点 `C¹` 曲线中 `ĝ`-长度
`∫ u √lam (c) ‖c′‖` 最小（S-W-GEO `ConformalGeodesicStabilityLocalGE` 的 (B) 入口形状）。 -/
theorem exists_minimizing_path_to_sphere_local_GM {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {lam u d : ℂ → ℝ} (hlam : ContDiffOn ℝ ∞ lam Ω) (hu : ContDiffOn ℝ ∞ u Ω)
    (hlam0 : ∀ z ∈ Ω, 0 < lam z) (hu0 : ∀ z ∈ Ω, 0 < u z) (hd : ContinuousOn d Ω)
    (hseg : ∀ x y : ℂ, segment ℝ x y ⊆ Ω →
      d y ≤ d x + ∫ t in (0 : ℝ)..1, Real.sqrt (lam (x + t • (y - x))) * ‖y - x‖)
    {p : ℂ} (hp : p ∈ Ω) (hdp : d p = 0) {r : ℝ} (hr : 0 < r)
    (hK : IsCompact {z | z ∈ Ω ∧ d z ≤ r}) :
    ∃ (c : ℝ → ℂ) (L : ℝ) (U₀ : Set ℂ),
      IsOpen U₀ ∧ {z | z ∈ Ω ∧ d z ≤ r} ⊆ U₀ ∧ U₀ ⊆ Ω ∧
      ContDiff ℝ ∞ c ∧ c 0 = p ∧ d (c L) = r ∧ r ≤ L ∧
      (∀ s ∈ Icc 0 L, c s ∈ Ω ∧ d (c s) ≤ r) ∧ (∀ s ∈ Ico 0 L, d (c s) < r) ∧
      (∀ s ∈ Icc 0 L, lam (c s) * ‖deriv c s‖ ^ 2 = 1) ∧
      (∀ η : ℝ → ℂ, ContDiff ℝ 1 η → (∀ s ∈ Icc 0 L, η s ∈ U₀) → η 0 = c 0 → η L = c L →
        ∫ s in (0 : ℝ)..L, u (c s) * Real.sqrt (lam (c s)) * ‖deriv c s‖ ≤
          ∫ s in (0 : ℝ)..L, u (η s) * Real.sqrt (lam (η s)) * ‖deriv η s‖) := by
  obtain ⟨c, L, ρt, V, hV, hKV, hVΩ, -, -, hρtV, -, hc, -, hc0, hcL, hrL, hcK, hfirst, harc,
    hmin⟩ := exists_minimizing_path_to_sphere_GM hΩ hlam hu hlam0 hu0 hd hseg hp hdp hr hK
  refine ⟨c, L, V, hV, hKV, hVΩ, hc, hc0, hcL, hrL, hcK, hfirst, harc, fun η hη hηV h0 h1 =>
    weightedLength_le_local_GM hρtV (hr.le.trans hrL) (fun s hs => hKV (hcK s hs)) hmin η hη hηV
      h0 h1⟩

end DifferentialGeometry.Geometry
