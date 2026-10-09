import DifferentialGeometry.Geometry.Hyperbolic.HG06AdapterBasicHGA

/-!
# HG-A1：HG06 adapter 的协变导数比较常数链（S-HG-A1，后缀 `_HGA1`）

D-R-HG1-5(3) 的担心：pullback 误差张量 `c • f^*g' - h` 的 a 阶协变导数范数，donor
`metricDerivNorm`（`metricCkErrorOn` 里加权和 `Σ_{a ≤ N} (a!)⁻¹ sup |∇^a err|` 的第 a 项）
与 ch12 `ckErr`（`tensor0SFiberNorm H.metric p (2 + a) (iteratedMetricCovariantDerivative …)`）
之间的比较常数 `C_a`、restriction、derivative naturality 是否全部已证。

**核对结论：全部已证，且 `C_a = 1`（逐点等式，不是不等式）**，对**所有** `a`（不止 `a ≤ N`）。
S-HG-ADAPT 的 `metricDerivNorm_pullbackMetricOn_eq_ckErr_HGA` 是 `private`；本文件把它公开，并写出
完整的 chain（每一步都落到树里已有的无条件引理，见各定理 docstring 的步骤表）：

1. 导数可加：`iterCov_sub` / `covDerivOfField_sub`（`∇^a (g_k - g_∞) = ∇^a g_k - ∇^a g_∞`）。
2. frame 无关：`metricDerivNorm_eq_iterCov`（正交基下 `normSq0S` 与 `domDomCongr` 可换）。
3. restriction / naturality：`raw_iterated_covariant_derivative_restrict`（开集 `U` 上
   `h.restrictOpen U` 的 `iterCov` = 全空间 `iteratedMetricCovariantDerivative` 的限制）
   + `normSq0S_restrictOpen_apply`（范数不变）。
4. `metricDerivNorm_eq_raw_on_open`：把 1–3 合起来（任意 raw 张量场 `A`，任意阶 `k`）。
5. pullback 恒等：`pullbackMetricOn_inner` + `restrictOpen_inner` + `Φ = f`（与 `a` 无关）。

于是（本文件）：

* `covariantDerivative_comparison_pointwise_HGA1`：`metricDerivNorm a … x = ckErr_HGA … a x`
  （`C_a = 1`）。
* `covariantDerivative_comparison_chain_HGA1`：逐阶容差 `ε a`（`ckErr_HGA ≤ ε a` on `K`，`a ≤ N`）
  ⇒ `metricCkErrorOn Φ K N ≤ Σ_{a ≤ N} ofReal ((a!)⁻¹ * ε a)`；均匀容差 `ε a = c` 时权重和即
  `S_N * c`，`S_N = Σ 1/a! < 3`（`sum_inv_factorial_lt_three_HGA`）。
* `isMetricApproximationOn_of_ckErr_chain_HGA1` / `isMetricApproximationOnBall_of_ckErr_chain_HGA1`：
  chain ⇒ donor 的 `isMetricApproximationOn(Ball)`（后者含 open-embedding → `PartialDiffeomorph`）。
* `ckErr_le_of_isMetricApproximationOn_HGA1`：反向，`isMetricApproximationOn Φ K N ξ` ⇒
  `ckErr_HGA … a p ≤ a! * ξ`（`C_a = a!`，权重 `(a!)⁻¹` 的逆）。
-/

set_option autoImplicit false

noncomputable section

open Set TopologicalSpace
open DifferentialGeometry
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Connection
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Hyperbolic

universe u v

/-- **chain 逐点等式（`C_a = 1`，所有 `a`）。** pullback 误差张量
`f^*h' - h`（在 `Φ.source` 上，`Φ = f`）的 donor `metricDerivNorm a`（参考度量
`H.metric.restrictOpen Φ.source`）等于 ch12 `ckErr_HGA H H'.metric 1 f a`。步骤：
`metricDerivNorm_eq_raw_on_open`（可加性 + frame 无关 + 开集 restriction，任意阶）
+ pullback 度量的逐点内积恒等。 -/
theorem covariantDerivative_comparison_pointwise_HGA1
    (H : FiniteVolumeHyperbolicModel.{u}) (H' : FiniteVolumeHyperbolicModel.{v})
    (Φ : PartialDiffeomorph (𝓡 3) (𝓡 3) H.Carrier H'.Carrier ∞)
    (f : H.Carrier → H'.Carrier) (hΦf : (Φ : H.Carrier → H'.Carrier) = f) (a : ℕ)
    (x : (⟨Φ.source, Φ.open_source⟩ : Opens H.Carrier)) :
    CheegerGromovCompactness.metricDerivNorm a
      (DifferentialGeometry.PartialDiffeomorph.pullbackMetricOn Φ
        ⟨Φ.source, Φ.open_source⟩ Set.Subset.rfl H'.metric)
      (H.metric.restrictOpen ⟨Φ.source, Φ.open_source⟩)
      (H.metric.restrictOpen ⟨Φ.source, Φ.open_source⟩) x =
    ckErr_HGA H H'.metric 1 f a (x : H.Carrier) := by
  let A : (p : H.Carrier) → Tensor0SSpace 2 (𝓡 3) p := fun p =>
    ((continuousMultilinearCurryFin1 ℝ (TangentSpace (𝓡 3) p) ℝ).symm.toContinuousLinearMap.comp
      ((1 : ℝ) • localPullInner H'.metric f p - H.metric.inner p)).uncurryLeft
  have hA : ∀ (y : (⟨Φ.source, Φ.open_source⟩ : Opens H.Carrier))
      (v : Fin 2 → TangentSpace (𝓡 3) y),
      (metricTensorField (DifferentialGeometry.PartialDiffeomorph.pullbackMetricOn Φ
          ⟨Φ.source, Φ.open_source⟩ Set.Subset.rfl H'.metric) -
        metricTensorField (H.metric.restrictOpen ⟨Φ.source, Φ.open_source⟩)) y v =
        A (y : H.Carrier) v := by
    intro y v
    simp only [ContMDiffSection.coe_sub, Pi.sub_apply, Tensor0SSpace.sub_apply,
      metricTensorField_apply, DifferentialGeometry.PartialDiffeomorph.pullbackMetricOn_inner,
      SmoothRiemannianMetric.restrictOpen_inner]
    change _ = (((1 : ℝ) • localPullInner H'.metric f (y : H.Carrier) -
      H.metric.inner (y : H.Carrier) : TangentSpace (𝓡 3) (y : H.Carrier) →L[ℝ]
        TangentSpace (𝓡 3) (y : H.Carrier) →L[ℝ] ℝ) (v 0)) (v 1)
    rw [← hΦf]
    simp only [one_smul]
    rfl
  exact CheegerGromovCompactness.metricDerivNorm_eq_raw_on_open H.metric
    ⟨Φ.source, Φ.open_source⟩ _ A hA a x

/-- **chain：逐阶容差 ⇒ 加权和上界。** 对每个 `a ≤ N` 给 `K` 上的逐点估计
`ckErr_HGA H H'.metric 1 f a p ≤ ε a`（`ε` 随 `a` 变，即 `C_a`-形容差），则 donor 的
`metricCkErrorOn Φ K N`（加权和 `Σ (a!)⁻¹ sup |∇^a err|`）`≤ Σ_{a ≤ N} ofReal ((a!)⁻¹ * ε a)`。 -/
theorem covariantDerivative_comparison_chain_HGA1
    (H : FiniteVolumeHyperbolicModel.{u}) (H' : FiniteVolumeHyperbolicModel.{v})
    (Φ : PartialDiffeomorph (𝓡 3) (𝓡 3) H.Carrier H'.Carrier ∞)
    (f : H.Carrier → H'.Carrier) (hΦf : (Φ : H.Carrier → H'.Carrier) = f)
    (K : Set H.Carrier) (N : ℕ) (ε : ℕ → ℝ)
    (herr : ∀ a : ℕ, a ≤ N → ∀ p ∈ K, ckErr_HGA H H'.metric 1 f a p ≤ ε a) :
    DifferentialGeometry.PartialDiffeomorph.metricCkErrorOn Φ K N H.metric H'.metric ≤
      ∑ a ∈ Finset.range (N + 1), ENNReal.ofReal (((a.factorial : ℝ))⁻¹ * ε a) := by
  unfold DifferentialGeometry.PartialDiffeomorph.metricCkErrorOn
    CheegerGromovCompactness.metricCkENormOn
  apply Finset.sum_le_sum
  intro a ha
  have h1 : ((a.factorial : ℝ≥0∞))⁻¹ * ENNReal.ofReal (ε a) =
      ENNReal.ofReal (((a.factorial : ℝ))⁻¹ * ε a) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_inv_of_pos (by positivity),
      ENNReal.ofReal_natCast]
  rw [← h1]
  gcongr
  refine iSup₂_le fun x hx => ?_
  rw [covariantDerivative_comparison_pointwise_HGA1 H H' Φ f hΦf a x]
  exact ENNReal.ofReal_le_ofReal
    (herr a (Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)) (x : H.Carrier) hx)

/-- chain ⇒ donor 的 `isMetricApproximationOn`：逐阶容差 `ε a ≥ 0`，`Σ (a!)⁻¹ * ε a < ξ`，
`K ⊆ Φ.source`。 -/
theorem isMetricApproximationOn_of_ckErr_chain_HGA1
    (H : FiniteVolumeHyperbolicModel.{u}) (H' : FiniteVolumeHyperbolicModel.{v})
    (Φ : PartialDiffeomorph (𝓡 3) (𝓡 3) H.Carrier H'.Carrier ∞)
    (f : H.Carrier → H'.Carrier) (hΦf : (Φ : H.Carrier → H'.Carrier) = f)
    (K : Set H.Carrier) (hK : K ⊆ Φ.source) (N : ℕ) (ε : ℕ → ℝ) {ξ : ℝ}
    (hε0 : ∀ a : ℕ, a ≤ N → 0 ≤ ε a)
    (hsum : ∑ a ∈ Finset.range (N + 1), ((a.factorial : ℝ))⁻¹ * ε a < ξ)
    (herr : ∀ a : ℕ, a ≤ N → ∀ p ∈ K, ckErr_HGA H H'.metric 1 f a p ≤ ε a) :
    DifferentialGeometry.PartialDiffeomorph.isMetricApproximationOn Φ K N ξ
      H.metric H'.metric := by
  refine ⟨hK, (covariantDerivative_comparison_chain_HGA1 H H' Φ f hΦf K N ε herr).trans_lt ?_⟩
  have hnn : ∀ a ∈ Finset.range (N + 1), 0 ≤ ((a.factorial : ℝ))⁻¹ * ε a := fun a ha =>
    mul_nonneg (by positivity) (hε0 a (Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)))
  rw [← ENNReal.ofReal_sum_of_nonneg hnn]
  by_cases hξ : 0 < ξ
  · exact (ENNReal.ofReal_lt_ofReal_iff hξ).2 hsum
  · exact absurd (lt_of_le_of_lt (Finset.sum_nonneg hnn) hsum) hξ

/-- chain ⇒ donor 的 `isMetricApproximationOnBall`（含 open smooth embedding →
`PartialDiffeomorph`，`partialDiffeomorph_of_open_smooth_embedding_HGA`）。S-HG-ADAPT 的
`isMetricApproximationOnBall_of_ckErr_HGA` 是 `ε a = c` 的特例。 -/
theorem isMetricApproximationOnBall_of_ckErr_chain_HGA1
    (H : FiniteVolumeHyperbolicModel.{u}) (H' : FiniteVolumeHyperbolicModel.{v}) (o : H.Carrier)
    {r ξ : ℝ} (hr : 0 < r) (N : ℕ) (ε : ℕ → ℝ)
    (hε0 : ∀ a : ℕ, a ≤ N → 0 ≤ ε a)
    (hsum : ∑ a ∈ Finset.range (N + 1), ((a.factorial : ℝ))⁻¹ * ε a < ξ)
    (U : Opens H.Carrier) (f : H.Carrier → H'.Carrier)
    (hball : riemannianClosedBallOf H.metric o r ⊆ U)
    (hcm : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U)
    (hemb : _root_.Manifold.IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => f x))
    (herr : ∀ a : ℕ, a ≤ N → ∀ p ∈ riemannianClosedBallOf H.metric o r,
      ckErr_HGA H H'.metric 1 f a p ≤ ε a) :
    isMetricApproximationOnBall (fun y : (U : Set H.Carrier) => f y) H.metric H'.metric o r N
      ξ := by
  have : Nonempty H.Carrier := ⟨o⟩
  obtain ⟨Φ, hsrc, -, hΦf⟩ :=
    DifferentialGeometry.Topology.Manifold.partialDiffeomorph_of_open_smooth_embedding_HGA
      U f hcm hemb
  have hKsrc : riemannianClosedBallOf H.metric o r ⊆ Φ.source := hsrc ▸ hball
  exact ⟨hr, hball, Φ, isMetricApproximationOn_of_ckErr_chain_HGA1 H H' Φ f hΦf _ hKsrc N ε hε0
    hsum herr, fun y _ => congrFun hΦf y⟩

/-- **反向（`C_a = a!`）。** donor 的 `isMetricApproximationOn Φ K N ξ` ⇒ 每个 `a ≤ N`、
`p ∈ K` 有 `ckErr_HGA H H'.metric 1 f a p ≤ a! * ξ`（加权和 `< ξ` 里第 `a` 项带权 `(a!)⁻¹`）。 -/
theorem ckErr_le_of_isMetricApproximationOn_HGA1
    (H : FiniteVolumeHyperbolicModel.{u}) (H' : FiniteVolumeHyperbolicModel.{v})
    (Φ : PartialDiffeomorph (𝓡 3) (𝓡 3) H.Carrier H'.Carrier ∞)
    (f : H.Carrier → H'.Carrier) (hΦf : (Φ : H.Carrier → H'.Carrier) = f)
    (K : Set H.Carrier) (N : ℕ) {ξ : ℝ}
    (h : DifferentialGeometry.PartialDiffeomorph.isMetricApproximationOn Φ K N ξ
      H.metric H'.metric)
    (a : ℕ) (ha : a ≤ N) (p : H.Carrier) (hp : p ∈ K) :
    ckErr_HGA H H'.metric 1 f a p ≤ (a.factorial : ℝ) * ξ := by
  obtain ⟨hKΦ, hlt⟩ := h
  have hξ : 0 < ξ := ENNReal.ofReal_pos.mp (lt_of_le_of_lt zero_le hlt)
  have hx : (⟨p, hKΦ hp⟩ : (⟨Φ.source, Φ.open_source⟩ : Opens H.Carrier)) ∈
      Subtype.val ⁻¹' K := hp
  have h1 : ((a.factorial : ℝ≥0∞))⁻¹ * ENNReal.ofReal (ckErr_HGA H H'.metric 1 f a p) <
      ENNReal.ofReal ξ := by
    refine lt_of_le_of_lt ?_ hlt
    unfold DifferentialGeometry.PartialDiffeomorph.metricCkErrorOn
      CheegerGromovCompactness.metricCkENormOn
    refine le_trans ?_ (Finset.single_le_sum (f := fun a : ℕ => ((a.factorial : ℝ≥0∞))⁻¹ *
      ⨆ x ∈ Subtype.val ⁻¹' K, ENNReal.ofReal (CheegerGromovCompactness.metricDerivNorm a
        (DifferentialGeometry.PartialDiffeomorph.pullbackMetricOn Φ
          ⟨Φ.source, Φ.open_source⟩ Set.Subset.rfl H'.metric)
        (H.metric.restrictOpen ⟨Φ.source, Φ.open_source⟩)
        (H.metric.restrictOpen ⟨Φ.source, Φ.open_source⟩) x))
      (fun _ _ => zero_le) (Finset.mem_range.2 (Nat.lt_succ_of_le ha)))
    gcongr
    refine le_iSup₂_of_le ⟨p, hKΦ hp⟩ hx ?_
    rw [covariantDerivative_comparison_pointwise_HGA1 H H' Φ f hΦf a ⟨p, hKΦ hp⟩]
  have hfac0 : (a.factorial : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Nat.factorial_pos a).ne'
  have hfacT : (a.factorial : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have h2 : ENNReal.ofReal (ckErr_HGA H H'.metric 1 f a p) ≤
      (a.factorial : ℝ≥0∞) * ENNReal.ofReal ξ := by
    calc ENNReal.ofReal (ckErr_HGA H H'.metric 1 f a p)
        = (a.factorial : ℝ≥0∞) * (((a.factorial : ℝ≥0∞))⁻¹ *
            ENNReal.ofReal (ckErr_HGA H H'.metric 1 f a p)) := by
          rw [← mul_assoc, ENNReal.mul_inv_cancel hfac0 hfacT, one_mul]
      _ ≤ (a.factorial : ℝ≥0∞) * ENNReal.ofReal ξ := mul_le_mul_right h1.le _
  have h3 : (a.factorial : ℝ≥0∞) * ENNReal.ofReal ξ = ENNReal.ofReal ((a.factorial : ℝ) * ξ) := by
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  rw [h3] at h2
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h2

end DifferentialGeometry.Geometry.Hyperbolic
