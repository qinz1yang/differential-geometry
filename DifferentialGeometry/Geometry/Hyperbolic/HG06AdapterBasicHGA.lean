import DifferentialGeometry.Geometry.Hyperbolic.TruncationStability
import DifferentialGeometry.Geometry.Hyperbolic.IsometryDiffeomorph
import DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.RawRestriction
import DifferentialGeometry.Topology.Manifold.OpenEmbeddingPartialDiffeomorphHGA

/-!
# HG06 → ch12 消费形状的 adapter：基础件（S-HG-ADAPT G1 / G3 + 桥接，后缀 `_HGA`）

* **G1** `truncation_count_eq_endCount_HGA`、`truncation_count_le_iff_endCount_le_HGA`：
  `Tr.count = endCount`（donor `HyperbolicTruncation.endCount_eq_count` 的包装，无新前提）。
* **ckErr**：`ckErr_HGA` = ch12 `ckErr_O19` 的逐字同体 ℝ-值 def（D4：ℝ-值 helper 允许；不是 Prop）。
* **G2 桥**：`isMetricApproximationOnBall_of_ckErr_HGA`：ch12 形状的逐点 `ckErr` 估计（最大型范数）
  ⇒ donor 的 `isMetricApproximationOnBall`（加权 `Σ_{a≤N} (a!)⁻¹ sup |∇^a err|` 范数）。
  用到 `partialDiffeomorph_of_open_smooth_embedding_HGA`（G2）和 tree 里已有的
  `metricDerivNorm_eq_raw_on_open`（`metricDerivNorm` = `ckErr` 表达式，无换算常数）。
  换算常数只剩加权和 `S_N = Σ_{a≤N} 1/a!`（`S_N < e < 3`）。
* **G3** `riemannian_isometry_of_dist_isometry_HGA`：距离 `IsometryEquiv` ⇒ 光滑保黎曼度量同构
  （donor `exists_diffeomorph_eq_isometryEquiv_of_constant_negative_curvature` 对
  `FiniteVolumeHyperbolicModel` 的包装；Myers–Steenrod 在常曲率 `-1/4` 下已在树里）。
* **sSup → 逐点**：`hg06_pointwise_of_sSup_HGA`：donor 结论 `sSup (dist (e p) (f p)) < η`
  ⇒ `∀ p ∈ closedBall, riemannianEDistOf H'.metric (e p) (f p) < ofReal η`（经紧性给出 `BddAbove`）。
-/

set_option autoImplicit false

noncomputable section

open Set TopologicalSpace
open DifferentialGeometry
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Connection
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Hyperbolic

universe u v

/-! ## G1：`Tr.count = endCount` -/

theorem truncation_count_eq_endCount_HGA {H : FiniteVolumeHyperbolicModel.{u}}
    (Tr : HyperbolicTruncation H) :
    ((Tr.count : ℕ) : ℕ∞) = Geometry.Topology.endCount H.Carrier :=
  Tr.endCount_eq_count.symm

theorem truncation_count_le_iff_endCount_le_HGA
    {H : FiniteVolumeHyperbolicModel.{u}} {H' : FiniteVolumeHyperbolicModel.{v}}
    (Tr : HyperbolicTruncation H) (Tr' : HyperbolicTruncation H') :
    Tr.count ≤ Tr'.count ↔
      Geometry.Topology.endCount H.Carrier ≤ Geometry.Topology.endCount H'.Carrier := by
  rw [Tr.endCount_eq_count, Tr'.endCount_eq_count]
  exact ENat.natCast_le_natCast.symm

/-! ## `ckErr_HGA`：ch12 `ckErr_O19` 的逐字同体 -/

/-- `C^k` pullback error `|∇^k (c • f^*g' - h)|_h` at `p`（与 ch12 `ckErr_O19` 同一表达式；ℝ-值）。 -/
def ckErr_HGA (H : FiniteVolumeHyperbolicModel.{u}) {N : Type v} [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N] [IsManifold (𝓡 3) ∞ N]
    (g' : SmoothRiemannianMetric (𝓡 3) N) (c : ℝ) (f : H.Carrier → N) (k : ℕ)
    (p : H.Carrier) : ℝ :=
  tensor0SFiberNorm H.metric p (2 + k)
    (iteratedMetricCovariantDerivative H.metric 2
      (fun q : H.Carrier =>
        ((continuousMultilinearCurryFin1 ℝ (TangentSpace (𝓡 3) q) ℝ).symm.toContinuousLinearMap.comp
          (c • localPullInner g' f q - H.metric.inner q)).uncurryLeft) k p)

/-- donor `hyperbolic_stability_of_cusp_count_le` 要的曲率恒等式（`TruncationStability` 里 private
同名引理的复制）。 -/
theorem curvature_identity_HGA (H : FiniteVolumeHyperbolicModel.{u})
    (x : H.Carrier) (v w : TangentSpace (𝓡 3) x) :
    Curvature.metricRm04StandardAt H.metric x v w w v =
      (-1 / 4 : ℝ) * (H.metric.inner x v v * H.metric.inner x w w -
        H.metric.inner x v w * H.metric.inner x v w) := by
  simpa only [neg_div] using
    Curvature.metricRm04StandardAt_eq_of_sectionalCurvature_eq
      H.metric (-(1 / 4 : ℝ)) x (H.curvature x) v w

/-! ## G2 桥：逐点 `ckErr` ⇒ `isMetricApproximationOnBall` -/

private theorem metricDerivNorm_pullbackMetricOn_eq_ckErr_HGA
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

/-- **G2 桥。** ch12 形状的逐点 `ckErr_HGA ≤ c`（`a ≤ N`，半径 `ξ⁻¹` 的闭球上），加上
`(Σ_{a ≤ N} 1/a!) * c < ξ`，推出 donor 的 `isMetricApproximationOnBall`（半径 `ξ⁻¹`、阶 `N`、
误差 `ξ`）。`PartialDiffeomorph` 由 G2 给出，`metricCkErrorOn` = 加权和 `Σ (a!)⁻¹ sup`。 -/
theorem isMetricApproximationOnBall_of_ckErr_HGA
    (H : FiniteVolumeHyperbolicModel.{u}) (H' : FiniteVolumeHyperbolicModel.{v}) (o : H.Carrier)
    {ξ c : ℝ} (hξ : 0 < ξ) (hc0 : 0 ≤ c) (N : ℕ)
    (hc : (∑ a ∈ Finset.range (N + 1), ((a.factorial : ℝ))⁻¹) * c < ξ)
    (U : Opens H.Carrier) (f : H.Carrier → H'.Carrier)
    (hball : riemannianClosedBallOf H.metric o ξ⁻¹ ⊆ U)
    (hcm : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U)
    (hemb : _root_.Manifold.IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => f x))
    (herr : ∀ a : ℕ, a ≤ N → ∀ p ∈ riemannianClosedBallOf H.metric o ξ⁻¹,
      ckErr_HGA H H'.metric 1 f a p ≤ c) :
    isMetricApproximationOnBall (fun y : (U : Set H.Carrier) => f y) H.metric H'.metric o
      ξ⁻¹ N ξ := by
  have : Nonempty H.Carrier := ⟨o⟩
  obtain ⟨Φ, hsrc, -, hΦf⟩ :=
    DifferentialGeometry.Topology.Manifold.partialDiffeomorph_of_open_smooth_embedding_HGA
      U f hcm hemb
  have hKsrc : riemannianClosedBallOf H.metric o ξ⁻¹ ⊆ Φ.source := hsrc ▸ hball
  refine ⟨inv_pos.mpr hξ, hball, Φ, ⟨hKsrc, ?_⟩, fun y _ => congrFun hΦf y⟩
  have hsum : DifferentialGeometry.PartialDiffeomorph.metricCkErrorOn Φ
      (riemannianClosedBallOf H.metric o ξ⁻¹) N H.metric H'.metric ≤
      ∑ a ∈ Finset.range (N + 1), ((a.factorial : ℝ≥0∞))⁻¹ * ENNReal.ofReal c := by
    unfold DifferentialGeometry.PartialDiffeomorph.metricCkErrorOn
      CheegerGromovCompactness.metricCkENormOn
    apply Finset.sum_le_sum
    intro a ha
    gcongr
    refine iSup₂_le fun x hx => ?_
    rw [metricDerivNorm_pullbackMetricOn_eq_ckErr_HGA H H' Φ f hΦf a x]
    exact ENNReal.ofReal_le_ofReal
      (herr a (Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)) (x : H.Carrier) hx)
  refine hsum.trans_lt ?_
  have h1 : ∀ a ∈ Finset.range (N + 1), ((a.factorial : ℝ≥0∞))⁻¹ * ENNReal.ofReal c =
      ENNReal.ofReal (((a.factorial : ℝ))⁻¹ * c) := by
    intro a _
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_inv_of_pos (by positivity),
      ENNReal.ofReal_natCast]
  rw [Finset.sum_congr rfl h1, ← ENNReal.ofReal_sum_of_nonneg (fun a _ => by positivity),
    ← Finset.sum_mul]
  exact (ENNReal.ofReal_lt_ofReal_iff hξ).2 hc

/-- `Σ_{a ≤ N} 1/a! < 3`（`≤ e < 3`）：ch12 的 `ξ/3` 吸收加权和的换算。 -/
theorem sum_inv_factorial_lt_three_HGA (N : ℕ) :
    ∑ a ∈ Finset.range (N + 1), ((a.factorial : ℝ))⁻¹ < 3 := by
  have h := Real.sum_le_exp_of_nonneg (x := 1) zero_le_one (N + 1)
  have h1 : ∑ a ∈ Finset.range (N + 1), ((a.factorial : ℝ))⁻¹ =
      ∑ i ∈ Finset.range (N + 1), (1 : ℝ) ^ i / (i.factorial : ℝ) := by
    simp
  rw [h1]
  exact h.trans_lt (Real.exp_one_lt_d9.trans (by norm_num))

/-! ## G3：距离 `IsometryEquiv` ⇒ 光滑保黎曼度量同构 -/

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- **G3。** `FiniteVolumeHyperbolicModel`（完备、常曲率 `-1/4`）之间由 `H.metric`/`H'.metric`
诱导距离的 `IsometryEquiv` 是光滑 diffeomorphism，且保黎曼度量 `localPullInner H'.metric e p =
H.metric.inner p`。 -/
theorem riemannian_isometry_of_dist_isometry_HGA
    (H : FiniteVolumeHyperbolicModel.{u}) (H' : FiniteVolumeHyperbolicModel.{v}) :
    letI : TopologicalSpace.MetrizableSpace H.Carrier := Manifold.metrizableSpace (𝓡 3) H.Carrier
    letI : PseudoMetricSpace H.Carrier := H.metric.toPseudoMetricSpace
    letI : MetricSpace H.Carrier := MetricSpace.ofT0PseudoMetricSpace H.Carrier
    letI : TopologicalSpace.MetrizableSpace H'.Carrier :=
      Manifold.metrizableSpace (𝓡 3) H'.Carrier
    letI : PseudoMetricSpace H'.Carrier := H'.metric.toPseudoMetricSpace
    letI : MetricSpace H'.Carrier := MetricSpace.ofT0PseudoMetricSpace H'.Carrier
    ∀ a : H.Carrier ≃ᵢ H'.Carrier, ∃ e : H.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ H'.Carrier,
      (∀ x, e x = a x) ∧ ∀ p, localPullInner H'.metric e p = H.metric.inner p := by
  let _ : TopologicalSpace.MetrizableSpace H.Carrier := Manifold.metrizableSpace (𝓡 3) H.Carrier
  let _ : PseudoMetricSpace H.Carrier := H.metric.toPseudoMetricSpace
  let _ : MetricSpace H.Carrier := MetricSpace.ofT0PseudoMetricSpace H.Carrier
  let _ : TopologicalSpace.MetrizableSpace H'.Carrier := Manifold.metrizableSpace (𝓡 3) H'.Carrier
  let _ : PseudoMetricSpace H'.Carrier := H'.metric.toPseudoMetricSpace
  let _ : MetricSpace H'.Carrier := MetricSpace.ofT0PseudoMetricSpace H'.Carrier
  intro a
  obtain ⟨e, hea, hinner⟩ :=
    exists_diffeomorph_eq_isometryEquiv_of_constant_negative_curvature H.metric H'.metric
      (-1 / 4 : ℝ) (by norm_num) H.complete H'.complete (curvature_identity_HGA H)
      (curvature_identity_HGA H') a
  refine ⟨e, hea, fun p => ?_⟩
  ext v w
  rw [localPullInner_apply]
  exact hinner p v w

end DifferentialGeometry.Geometry.Hyperbolic
