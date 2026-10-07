import DifferentialGeometry.Geometry.MinimalSurface.Plateau.CourantLebesgueCrosscutR7A
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.CourantLebesgueCircleR7A
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.SecondTrimR8
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.BoundaryArcADP
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.VaryingMetricAreaR7A

/-!
# S-MY-R7A G2：Courant–Lebesgue 边界参数化等度连续（固定 Jordan 边界 + 三点归一 + 能量一致界）

外审 D-R-MY3-6：不加 chord-arc；固定 Jordan boundary + 逆映射连续模 + 三点归一足以排除边界退化。

* `exists_pos_edist_of_dist_ge_R7A`：`Γ` embedding ⇒ 逆映射一致连续（`dist a b ≥ ε` ⇒
  `edist_g (Γ a) (Γ b) ≥ r`）。
* `courant_lebesgue_equicontinuity_R7A`：`g`-能量 `≤ Λ`、光滑到边界、三点归一、weak Jordan trace `Γ ∘ σ`
  的盘族，`σ` 等度连续。证明：`courant_lebesgue_crosscut_R7A` 给 crosscut 端点像近 ⇒ `Γ` 逆连续给
  `σ` 的端点近 ⇒ `wmo_oscillation_R7A`（三点归一排除"长弧"）给整个 crosscut 区间上 `σ` 的振幅小。
* `courant_lebesgue_equicontinuity_varying_R7A`：度量在变（`hrel` 于 `B`、`range ⊆ B`）的版本，供 R7 本体。
-/

set_option autoImplicit false
noncomputable section

open Set Filter Bundle Manifold DifferentialGeometry MeasureTheory
open DifferentialGeometry.Topology
open scoped Topology ContDiff Manifold NNReal ENNReal

namespace DifferentialGeometry.Geometry

section Aux

/-- 三个互异圆周点有正的两两分离。 -/
theorem exists_pos_gap_R7A {θ : Fin 3 → loopCircle} (hθ : Function.Injective θ) :
    ∃ g₁ : ℝ, 0 < g₁ ∧ ∀ i j, i ≠ j → g₁ ≤ ‖θ i - θ j‖ := by
  obtain ⟨p, hp, hmin⟩ := Finset.exists_min_image
    (Finset.univ.filter (fun p : Fin 3 × Fin 3 => p.1 ≠ p.2)) (fun p => ‖θ p.1 - θ p.2‖)
    ⟨(0, 1), by simp⟩
  have hp' : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
  refine ⟨‖θ p.1 - θ p.2‖, norm_pos_iff.mpr (sub_ne_zero.mpr (hθ.ne hp')), fun i j hij => ?_⟩
  exact hmin (i, j) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩)

end Aux

section Main

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

/-- `Γ` embedding ⇒ 逆映射一致连续：`ε ≤ dist a b` ⇒ `ofReal r ≤ edist_g (Γ a) (Γ b)`。 -/
theorem exists_pos_edist_of_dist_ge_R7A (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {Γ : freeLoop M}
    (hΓ : Topology.IsEmbedding Γ) {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ ∀ a b : loopCircle, ε ≤ dist a b →
      ENNReal.ofReal r ≤ riemannianEDistOf g (Γ a) (Γ b) := by
  set K : Set (loopCircle × loopCircle) := {p | ε ≤ dist p.1 p.2} with hK
  have hKc : IsCompact K := (isClosed_le continuous_const
    (continuous_fst.dist continuous_snd)).isCompact
  have hcont : Continuous (fun p : loopCircle × loopCircle =>
      riemannianEDistOf g (Γ p.1) (Γ p.2)) :=
    (continuous_riemannianEDistOf_prod_R8 g).comp
      ((Γ.continuous.comp continuous_fst).prodMk (Γ.continuous.comp continuous_snd))
  have hη : ∃ η : ℝ≥0∞, 0 < η ∧ ∀ p ∈ K, η ≤ riemannianEDistOf g (Γ p.1) (Γ p.2) := by
    rcases K.eq_empty_or_nonempty with hKe | hKne
    · exact ⟨1, one_pos, by simp [hKe]⟩
    · obtain ⟨p₀, hp₀, hmin⟩ := hKc.exists_isMinOn hKne hcont.continuousOn
      refine ⟨_, ?_, fun p hp => isMinOn_iff.mp hmin p hp⟩
      rw [pos_iff_ne_zero]
      intro h0
      have heq : p₀.1 = p₀.2 := hΓ.injective (eq_of_riemannianEDistOf_eq_zero_R8 g h0)
      have : ε ≤ dist p₀.1 p₀.2 := hp₀
      rw [heq, dist_self] at this
      linarith
  obtain ⟨η, hη0, hηK⟩ := hη
  refine ⟨(min η 1).toReal, ENNReal.toReal_pos (lt_min hη0 one_pos).ne'
    (ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)), fun a b hab => ?_⟩
  rw [ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _))]
  exact (min_le_left _ _).trans (hηK (a, b) hab)

/-- **G2**（Courant–Lebesgue，边界参数化等度连续）：固定 Jordan 边界 `Γ`（embedding）、三个互异标记点
`θ`、能量界 `Λ`。对任意 `ε > 0` 存在 `η > 0`，使得所有"光滑到边界、`g`-能量 `≤ Λ`、三点归一
（`u (∂θⱼ) = Γ θⱼ`）、trace 是 `Γ ∘ σ`（`σ` weakly monotone once）"的盘有 `dist s t < η ⇒
dist (σ s) (σ t) < ε`。不加 chord-arc。 -/
theorem courant_lebesgue_equicontinuity_R7A (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {Γ : freeLoop M} (hΓ : Topology.IsEmbedding Γ) (θ : Fin 3 → loopCircle)
    (hθ : Function.Injective θ) {Λ : ℝ} (hΛ0 : 0 ≤ Λ) {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ (u : C(closedDisk, M)) (Q : ℂ → M), SmoothDiskExtension (E := E) u Q →
      (∫ z in Metric.closedBall (0 : ℂ) 1, diskMapEnergyDensity g (diskExtension u) z) ≤ Λ →
      (∀ j, diskTrace u (θ j) = Γ (θ j)) →
      ∀ σ : C(loopCircle, loopCircle), IsWeaklyMonotoneOnce σ → diskTrace u = Γ.comp σ →
      ∀ s t : loopCircle, dist s t < η → dist (σ s) (σ t) < ε := by
  have hpi := Real.pi_pos
  obtain ⟨g₁, hg₁, hgap⟩ := exists_pos_gap_R7A hθ
  set g₀ : ℝ := min g₁ (1 / 4) with hg₀def
  have hg₀pos : 0 < g₀ := lt_min hg₁ (by norm_num)
  have hg₀4 : g₀ ≤ 1 / 4 := min_le_right _ _
  set ε' : ℝ := min (ε / 3) (g₀ / 2) with hε'def
  have hε'pos : 0 < ε' := lt_min (by positivity) (by positivity)
  have hε'g : ε' < g₀ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hε'ε : 2 * ε' < ε := by
    have := min_le_left (ε / 3) (g₀ / 2)
    linarith
  obtain ⟨r₀, hr₀, hΓinv⟩ := exists_pos_edist_of_dist_ge_R7A g hΓ hε'pos
  -- 选 `δ`
  set N : ℝ := 4 * Real.pi * (Λ + 1) / r₀ ^ 2 + 1 with hN
  have hNpos : 0 < N := by
    have : 0 ≤ 4 * Real.pi * (Λ + 1) / r₀ ^ 2 := by positivity
    linarith
  set δ : ℝ := min (Real.exp (-N)) (g₀ ^ 2) with hδdef
  have hδpos : 0 < δ := lt_min (Real.exp_pos _) (by positivity)
  have hδ1 : δ < 1 := lt_of_le_of_lt (min_le_left _ _) (by
    simpa using Real.exp_lt_exp.mpr (show -N < 0 by linarith))
  have hδg : Real.sqrt δ ≤ g₀ := by
    calc Real.sqrt δ ≤ Real.sqrt (g₀ ^ 2) := Real.sqrt_le_sqrt (min_le_right _ _)
      _ = g₀ := Real.sqrt_sq hg₀pos.le
  have hlogδ : N ≤ Real.log (1 / δ) := by
    have h1 : Real.exp N ≤ 1 / δ := by
      have : δ ≤ Real.exp (-N) := min_le_left _ _
      rw [one_div]
      calc Real.exp N = (Real.exp (-N))⁻¹ := by rw [Real.exp_neg, inv_inv]
        _ ≤ δ⁻¹ := inv_anti₀ hδpos this
    calc N = Real.log (Real.exp N) := (Real.log_exp N).symm
      _ ≤ Real.log (1 / δ) := Real.log_le_log (Real.exp_pos _) h1
  have hSr : 4 * Real.pi * (Λ + 1) / Real.log (1 / δ) < r₀ ^ 2 := by
    have hS0 : 0 < 4 * Real.pi * (Λ + 1) := by positivity
    calc 4 * Real.pi * (Λ + 1) / Real.log (1 / δ) ≤ 4 * Real.pi * (Λ + 1) / N :=
          div_le_div_of_nonneg_left hS0.le hNpos hlogδ
      _ < r₀ ^ 2 := by
          rw [div_lt_iff₀ hNpos, hN]
          have : 4 * Real.pi * (Λ + 1) / r₀ ^ 2 * r₀ ^ 2 = 4 * Real.pi * (Λ + 1) := by
            field_simp
          nlinarith [sq_nonneg r₀, pow_pos hr₀ 2]
  refine ⟨δ / (2 * Real.pi), by positivity, ?_⟩
  intro u Q hQ hE hmark σ hσ htr s t hst
  -- 标记点固定：`σ θⱼ = θⱼ`
  have hσθ : ∀ j, σ (θ j) = θ j := fun j => by
    have h : diskTrace u (θ j) = Γ (σ (θ j)) := congrArg (fun f : freeLoop M => f (θ j)) htr
    exact hΓ.injective (h.symm.trans (hmark j))
  have hu : ∀ y : loopCircle, u (diskBoundary y) = Γ (σ y) := fun y =>
    congrArg (fun f : freeLoop M => f y) htr
  choose x hx using fun j => QuotientAddGroup.mk_surjective (θ j)
  have hxsep : ∀ i j, i ≠ j → ∀ m : ℤ, g₀ ≤ |x i - x j - m| := fun i j hij m => by
    refine (min_le_left _ _).trans ((hgap i j hij).trans ?_)
    have h1 : ((x i : ℝ) : loopCircle) = θ i := hx i
    have h2 : ((x j : ℝ) : loopCircle) = θ j := hx j
    rw [← h1, ← h2, ← AddCircle.coe_sub]
    exact norm_coe_le_abs_sub_int_R7A _ m
  have hfix : ∀ j, σ ((x j : ℝ) : loopCircle) = ((x j : ℝ) : loopCircle) := fun j => by
    have h2 : ((x j : ℝ) : loopCircle) = θ j := hx j
    rw [h2]
    exact hσθ j
  -- `s`、`t` 的实数代表
  obtain ⟨s', rfl⟩ := QuotientAddGroup.mk_surjective s
  obtain ⟨h, hh, hhn⟩ := loopCircle_exists_minimal_lift (t - ((s' : ℝ) : loopCircle))
  have ht : t = ((s' + h : ℝ) : loopCircle) := by
    rw [AddCircle.coe_add, hh]
    abel
  have hhlt : |h| < δ / (2 * Real.pi) := by
    rw [hhn, ← norm_sub_rev, ← dist_eq_norm]
    exact hst
  -- crosscut
  obtain ⟨κ, hκlo, hκhi, hed⟩ := courant_lebesgue_crosscut_R7A g hQ hΛ0 hE s' hδpos hδ1
  have hκ0 : 0 < κ := lt_of_lt_of_le (by positivity) hκlo
  rw [hu, hu] at hed
  have hlt : ENNReal.ofReal (Real.sqrt (4 * Real.pi * (Λ + 1) / Real.log (1 / δ))) <
      ENNReal.ofReal r₀ :=
    (ENNReal.ofReal_lt_ofReal_iff hr₀).mpr ((Real.sqrt_lt' hr₀).mpr hSr)
  have hclose : dist (σ ((s' - κ : ℝ) : loopCircle)) (σ ((s' + κ : ℝ) : loopCircle)) < ε' := by
    by_contra hge
    exact absurd (hΓinv _ _ (not_lt.mp hge)) (not_le.mpr (lt_of_le_of_lt hed hlt))
  have hba : (s' + κ) - (s' - κ) < g₀ := by
    have : κ ≤ Real.sqrt δ / 4 := hκhi
    linarith
  have hosc := wmo_oscillation_R7A hσ hg₀4 hxsep hfix (by linarith) hba hε'g hclose
  have hhκ : |h| ≤ κ := by
    refine hhlt.le.trans hκlo
  have hmem1 : s' ∈ Icc (s' - κ) (s' + κ) := ⟨by linarith, by linarith⟩
  have hmem2 : s' + h ∈ Icc (s' - κ) (s' + κ) :=
    ⟨by linarith [(abs_le.mp hhκ).1], by linarith [(abs_le.mp hhκ).2]⟩
  rw [ht]
  exact lt_of_le_of_lt (hosc s' hmem1 (s' + h) hmem2) hε'ε

/-- **G2（度量在变）**：`uₙ` 是 `Gₙ`-Morrey 盘、`Gₙ → G` 于 `B`（`hrel`）、`range uₙ ⊆ B`、
`A_{Gₙ}(uₙ) ≤ Λ`、三点归一 ⇒ 存在 `η > 0` 与终将的 `n`，使所有 `uₙ` 的边界参数化 `σ`（weakly monotone
once）`η`-等度连续。能量用固定度量 `G` 衡量：`E_G(uₙ) ≤ 2 E_{Gₙ}(uₙ) = 2 A_{Gₙ}(uₙ) ≤ 2Λ`
（`hrel` 取 `ε = 1/2`）。`Γ` smooth embedded（F1a 给每个 `uₙ` 的闭盘光滑延拓）。 -/
theorem courant_lebesgue_equicontinuity_varying_R7A
    {G : SmoothRiemannianMetric 𝓘(ℝ, E) M} {Gn : ℕ → SmoothRiemannianMetric 𝓘(ℝ, E) M}
    {B : Set M}
    (hrel : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ x ∈ B, ∀ v : TangentSpace 𝓘(ℝ, E) x,
      |(Gn n).inner x v v - G.inner x v v| ≤ ε * G.inner x v v)
    {Γ : freeLoop M} (hΓ : IsSmoothEmbeddedLoop (E := E) Γ) (θ : Fin 3 → loopCircle)
    (hθ : Function.Injective θ)
    {u : ℕ → C(closedDisk, M)} (hu : ∀ n, IsMorreyDisk (Gn n) Γ (u n))
    (huB : ∀ n, range (u n) ⊆ B) (huθ : ∀ n j, diskTrace (u n) (θ j) = Γ (θ j))
    {Λ : ℝ} (hΛ0 : 0 ≤ Λ) (hΛ : ∀ n, riemannianDiskArea (Gn n) (u n) ≤ Λ) {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ᶠ n in atTop, ∀ σ : C(loopCircle, loopCircle),
      IsWeaklyMonotoneOnce σ → diskTrace (u n) = Γ.comp σ →
      ∀ s t : loopCircle, dist s t < η → dist (σ s) (σ t) < ε := by
  obtain ⟨η, hη, hmain⟩ := courant_lebesgue_equicontinuity_R7A G hΓ.embedding θ hθ
    (Λ := 2 * Λ) (by linarith) hε
  refine ⟨η, hη, ?_⟩
  filter_upwards [hrel (1 / 2) (by norm_num)] with n hn
  obtain ⟨Q, hQ, -⟩ := morrey_disk_closed_extension_lipschitz_ADP (Gn n) hΓ (hu n)
  -- `E_G(uₙ) ≤ 2 E_{Gₙ}(uₙ) = 2 A_{Gₙ}(uₙ) ≤ 2 Λ`
  have hpt : ∀ z, diskMapEnergyDensity G (diskExtension (u n)) z ≤
      2 * diskMapEnergyDensity (Gn n) (diskExtension (u n)) z := by
    intro z
    have hx := hn (diskExtension (u n) z) (huB n ⟨diskRetraction z, rfl⟩)
    have h1 : G.inner (diskExtension (u n) z) (diskMapPartial (diskExtension (u n)) z 1)
        (diskMapPartial (diskExtension (u n)) z 1) ≤ 2 * (Gn n).inner (diskExtension (u n) z)
        (diskMapPartial (diskExtension (u n)) z 1) (diskMapPartial (diskExtension (u n)) z 1) := by
      have := (abs_le.mp (hx (diskMapPartial (diskExtension (u n)) z 1))).1
      linarith
    have h2 : G.inner (diskExtension (u n) z) (diskMapPartial (diskExtension (u n)) z Complex.I)
        (diskMapPartial (diskExtension (u n)) z Complex.I) ≤ 2 * (Gn n).inner
        (diskExtension (u n) z) (diskMapPartial (diskExtension (u n)) z Complex.I)
        (diskMapPartial (diskExtension (u n)) z Complex.I) := by
      have := (abs_le.mp (hx (diskMapPartial (diskExtension (u n)) z Complex.I))).1
      linarith
    unfold diskMapEnergyDensity
    linarith
  have hnn : ∀ z, 0 ≤ diskMapEnergyDensity G (diskExtension (u n)) z := fun z =>
    div_nonneg (add_nonneg (metric_inner_self_nonneg G _ _) (metric_inner_self_nonneg G _ _))
      (by norm_num)
  have hEn : (∫ z in Metric.closedBall (0 : ℂ) 1,
      diskMapEnergyDensity (Gn n) (diskExtension (u n)) z) = riemannianDiskArea (Gn n) (u n) := by
    unfold riemannianDiskArea riemannianArea
    apply integral_congr_ae
    filter_upwards [ae_disk_interior] with z hz
    exact diskMapEnergyDensity_eq_areaDensity_of_conformal_R7A (Gn n) ((hu n).conformal z hz)
  have hE : (∫ z in Metric.closedBall (0 : ℂ) 1,
      diskMapEnergyDensity G (diskExtension (u n)) z) ≤ 2 * Λ := by
    calc (∫ z in Metric.closedBall (0 : ℂ) 1, diskMapEnergyDensity G (diskExtension (u n)) z)
        ≤ ∫ z in Metric.closedBall (0 : ℂ) 1,
            2 * diskMapEnergyDensity (Gn n) (diskExtension (u n)) z :=
          integral_mono_of_nonneg (Eventually.of_forall hnn)
            ((hu n).finiteEnergy.const_mul 2) (Eventually.of_forall hpt)
      _ = 2 * riemannianDiskArea (Gn n) (u n) := by rw [integral_const_mul, hEn]
      _ ≤ 2 * Λ := by linarith [hΛ n]
  intro σ hσ htr
  exact hmain (u n) Q hQ hE (huθ n) σ hσ htr

/-- `Γ` 连续 ⇒ `edist_g (Γ a) (Γ b)` 对圆周参数一致小。 -/
theorem exists_dist_lt_edist_lt_R7A (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {Γ : freeLoop M}
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a b : loopCircle, dist a b < δ →
      riemannianEDistOf g (Γ a) (Γ b) < ENNReal.ofReal ε := by
  set K : Set (loopCircle × loopCircle) :=
    {p | ENNReal.ofReal ε ≤ riemannianEDistOf g (Γ p.1) (Γ p.2)} with hK
  have hcont : Continuous (fun p : loopCircle × loopCircle =>
      riemannianEDistOf g (Γ p.1) (Γ p.2)) :=
    (continuous_riemannianEDistOf_prod_R8 g).comp
      ((Γ.continuous.comp continuous_fst).prodMk (Γ.continuous.comp continuous_snd))
  have hKc : IsCompact K := (isClosed_le continuous_const hcont).isCompact
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · refine ⟨1, one_pos, fun a b _ => ?_⟩
    by_contra hge
    have : (a, b) ∈ K := not_lt.mp hge
    simp [hKe] at this
  · obtain ⟨p₀, hp₀, hmin⟩ := hKc.exists_isMinOn hKne
      (continuous_fst.dist continuous_snd).continuousOn
    refine ⟨dist p₀.1 p₀.2, ?_, fun a b hab => ?_⟩
    · rw [dist_pos]
      intro heq
      have h0 : riemannianEDistOf g (Γ p₀.1) (Γ p₀.2) = 0 := by
        rw [heq]
        exact riemannianEDistOf_self g _
      have : ENNReal.ofReal ε ≤ 0 := h0 ▸ hp₀
      rw [nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at this
      linarith
    · by_contra hge
      have : (a, b) ∈ K := not_lt.mp hge
      have := isMinOn_iff.mp hmin (a, b) this
      linarith

/-- 圆周 `‖z‖ = 1` 上的两点 `z, w`：存在参数 `a, b` 使 `∂a = z`、`∂b = w`、`dist a b ≤ dist z w`。 -/
theorem exists_boundary_params_R7A {z w : closedDisk} (hz : ‖(z : ℂ)‖ = 1) (hw : ‖(w : ℂ)‖ = 1) :
    ∃ a b : loopCircle, diskBoundary a = z ∧ diskBoundary b = w ∧ dist a b ≤ dist z w := by
  let h := AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero
  let cz : Circle := ⟨(z : ℂ), mem_sphere_zero_iff_norm.mpr hz⟩
  let cw : Circle := ⟨(w : ℂ), mem_sphere_zero_iff_norm.mpr hw⟩
  obtain ⟨a, ha⟩ := h.surjective cz
  obtain ⟨b, hb⟩ := h.surjective cw
  have hbd : ∀ (y : loopCircle) (c : Circle), h y = c → diskBoundary y = ⟨(c : ℂ), by
      simp [Metric.mem_closedBall, dist_zero_right]⟩ := by
    intro y c hyc
    apply Subtype.ext
    have := congrArg (fun x : Circle => (x : ℂ)) hyc
    simp only [h, AddCircle.homeomorphCircle_apply] at this
    exact this
  refine ⟨a, b, ?_, ?_, ?_⟩
  · rw [hbd a cz ha]
  · rw [hbd b cw hb]
  · have hl := circle_parameter_lipschitz.dist_le_mul cz cw
    have e1 : h.symm cz = a := by rw [← ha]; exact h.symm_apply_apply a
    have e2 : h.symm cw = b := by rw [← hb]; exact h.symm_apply_apply b
    rw [e1, e2] at hl
    have hd : dist cz cw = dist z w := by
      rw [Subtype.dist_eq z w]
      rfl
    rw [← hd]
    simpa using hl

/-- **G2 consumer（边界等度连续）**：边界点上 `u` 的 `edist_g` 模连续性一致（`σ` 等度连续 + `Γ` 连续）。 -/
theorem courant_lebesgue_boundary_modulus_R7A (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {Γ : freeLoop M} (hΓ : Topology.IsEmbedding Γ) (θ : Fin 3 → loopCircle)
    (hθ : Function.Injective θ) {Λ : ℝ} (hΛ0 : 0 ≤ Λ) {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ (u : C(closedDisk, M)) (Q : ℂ → M), SmoothDiskExtension (E := E) u Q →
      (∫ z in Metric.closedBall (0 : ℂ) 1, diskMapEnergyDensity g (diskExtension u) z) ≤ Λ →
      (∀ j, diskTrace u (θ j) = Γ (θ j)) → DiskWeakJordanTrace Γ u →
      ∀ z w : closedDisk, ‖(z : ℂ)‖ = 1 → ‖(w : ℂ)‖ = 1 → dist z w < η →
        riemannianEDistOf g (u z) (u w) < ENNReal.ofReal ε := by
  obtain ⟨δ₂, hδ₂, hΓc⟩ := exists_dist_lt_edist_lt_R7A g (Γ := Γ) hε
  obtain ⟨η, hη, hmain⟩ := courant_lebesgue_equicontinuity_R7A g hΓ θ hθ hΛ0 hδ₂
  refine ⟨η, hη, ?_⟩
  intro u Q hQ hE hmark ⟨σ, hσ, htr⟩ z w hz hw hzw
  obtain ⟨a, b, rfl, rfl, hab⟩ := exists_boundary_params_R7A hz hw
  have hu : ∀ y : loopCircle, u (diskBoundary y) = Γ (σ y) := fun y =>
    congrArg (fun f : freeLoop M => f y) htr
  rw [hu, hu]
  exact hΓc _ _ (hmain u Q hQ hE hmark σ hσ htr a b (lt_of_le_of_lt hab hzw))

/-- **G2 consumer（度量在变，R7 本体用）**：边界点上 `uₙ` 的 `edist_G` 模连续性对 `n` 一致（终将）。
即 `∀ ε > 0, ∃ η > 0, ∀ᶠ n, ∀ z w ∈ ∂D, dist z w < η → edist_G (uₙ z) (uₙ w) < ε`。 -/
theorem courant_lebesgue_boundary_modulus_varying_R7A
    {G : SmoothRiemannianMetric 𝓘(ℝ, E) M} {Gn : ℕ → SmoothRiemannianMetric 𝓘(ℝ, E) M}
    {B : Set M}
    (hrel : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ x ∈ B, ∀ v : TangentSpace 𝓘(ℝ, E) x,
      |(Gn n).inner x v v - G.inner x v v| ≤ ε * G.inner x v v)
    {Γ : freeLoop M} (hΓ : IsSmoothEmbeddedLoop (E := E) Γ) (θ : Fin 3 → loopCircle)
    (hθ : Function.Injective θ)
    {u : ℕ → C(closedDisk, M)} (hu : ∀ n, IsMorreyDisk (Gn n) Γ (u n))
    (huB : ∀ n, range (u n) ⊆ B) (huθ : ∀ n j, diskTrace (u n) (θ j) = Γ (θ j))
    {Λ : ℝ} (hΛ0 : 0 ≤ Λ) (hΛ : ∀ n, riemannianDiskArea (Gn n) (u n) ≤ Λ) {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ᶠ n in atTop, ∀ z w : closedDisk, ‖(z : ℂ)‖ = 1 → ‖(w : ℂ)‖ = 1 →
      dist z w < η → riemannianEDistOf G (u n z) (u n w) < ENNReal.ofReal ε := by
  obtain ⟨δ₂, hδ₂, hΓc⟩ := exists_dist_lt_edist_lt_R7A G (Γ := Γ) hε
  obtain ⟨η, hη, hev⟩ := courant_lebesgue_equicontinuity_varying_R7A hrel hΓ θ hθ hu huB huθ hΛ0
    hΛ hδ₂
  refine ⟨η, hη, hev.mono fun n hn z w hz hw hzw => ?_⟩
  obtain ⟨σ, hσ, htr⟩ := (hu n).trace
  obtain ⟨a, b, rfl, rfl, hab⟩ := exists_boundary_params_R7A hz hw
  have hu' : ∀ y : loopCircle, u n (diskBoundary y) = Γ (σ y) := fun y =>
    congrArg (fun f : freeLoop M => f y) htr
  rw [hu', hu']
  exact hΓc _ _ (hn σ hσ htr a b (lt_of_le_of_lt hab hzw))

end Main
end DifferentialGeometry.Geometry

end
