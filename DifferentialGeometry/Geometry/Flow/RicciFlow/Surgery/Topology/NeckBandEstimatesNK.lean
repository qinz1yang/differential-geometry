import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.NeckCylindricalChartBridge
import DifferentialGeometry.Geometry.Neck.SectionCurvature
import DifferentialGeometry.Geometry.Curvature.ScalarRoundCylinder
import DifferentialGeometry.Geometry.Metric.LengthPerturbation
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.LocalPullbackScaling
import DifferentialGeometry.Topology.Manifold.OpenFunctionExtension

/-!
# Route W, IMS06′ 的 neck band 估计（S-W-NECK G2，后缀 `_NK`）

从 `NormalizedNeck h δ k`（`δ`-neck：scalar-one 归一化、`C^k`-`δ`-接近标准圆柱 `S² × ℝ`）推出
band `{|z| < 20}` 上的两个估计：

* `1/2 ≤ metricScalarAt`：`C²` 闭近（`k ≥ 2`）⇒ 圆柱 scalar `1` 的扰动 `|R − 1| ≤ 4323 δ`
  （`abs_scalar_curvature_restricted_roundCylinder_sub_one_le`），`δ ≤ 1/8646` 时 `R ≥ 1/2`；
  不需要曲率收敛定理。
* `(dz w)^2 ≤ 4 g(w, w)`：度量分量的 `C⁰` 闭近 `g ≥ (1 − δ) g₀`，`dz² ≤ g₀`。

度量取 scalar-one 归一化 `scaleMetric N.scale h`（`R = 1` 在 neck 中心）。IAU02 的 δ-neck 的
`δ < δ*` 对应 `η₀ = 1/8646`（只需 `k ≥ 2`），band 取 neck 自己的坐标 `|z| < 20 ≤ δ⁻¹`。
`height_NK` 是 `range chart` 上的高度坐标（其余处取 `0`），band 的闭包仍在 `range chart` 内
（`{|z| ≤ 20}` 的像紧），供 G3 的 first-exit 论证使用。
-/

set_option autoImplicit false
noncomputable section
open Set Manifold
open DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

private local instance : Fact (Module.finrank ℝ ThreeSpace = 2 + 1) := ⟨by simp [ThreeSpace]⟩

private lemma infty_ne_zero_NK : (∞ : WithTop ℕ∞) ≠ 0 := by decide

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M] [T2Space M] [SigmaCompactSpace M]
  {h : SmoothRiemannianMetric ThreeModel M} {δ : ℝ} {k : ℕ}

omit [T2Space M] [SigmaCompactSpace M] in
theorem NormalizedNeck.metricDerivNorm_le_NK (N : NormalizedNeck h δ k) (hk : 2 ≤ k)
    {x : neckBuffer δ} (hx : x ∈ neckClosedTest δ) {m : ℕ} (hm : m ≤ 2) :
    metricDerivNorm m N.normalizedMetric
      ((Geometry.Metric.roundCylinderMetric (E := ThreeSpace) (n := 2)).restrictOpen
        (neckBuffer δ))
      ((Geometry.Metric.roundCylinderMetric (E := ThreeSpace) (n := 2)).restrictOpen
        (neckBuffer δ)) x ≤ δ := by
  rw [← roundCylinderMetric_eq_geometry]
  exact (derivNorm_le_sup (isCompact_neckClosedTest δ) (hm.trans hk) _ _ _ hx).trans
    N.closeness.le

omit [T2Space M] [SigmaCompactSpace M] in
theorem NormalizedNeck.scalar_lower_NK (N : NormalizedNeck h δ k) (hk : 2 ≤ k)
    (hδ : δ ≤ 1 / 8646) {x : neckBuffer δ} (hx : x ∈ neckClosedTest δ) :
    1 / 2 ≤ metricScalarAt N.normalizedMetric x := by
  have h1 := abs_scalar_curvature_restricted_roundCylinder_sub_one_le (E := ThreeSpace)
    (neckBuffer δ) N.normalizedMetric x δ (by linarith)
    (fun m hm => N.metricDerivNorm_le_NK hk hx hm)
  have h2 := (abs_le.mp h1).1
  linarith

theorem mfderiv_height_apply_NK (x : neckBuffer δ) (w : TangentSpace NeckCylinderModel x) :
    mfderiv NeckCylinderModel 𝓘(ℝ, ℝ) (fun y : neckBuffer δ => y.1.2) x w = w.2 := by
  have hval : MDifferentiableAt NeckCylinderModel NeckCylinderModel
      (Subtype.val : neckBuffer δ → NeckCylinder) x :=
    (hasMFDerivAt_subtype_val (I := NeckCylinderModel) (neckBuffer δ) x).mdifferentiableAt
  have hsnd : MDifferentiableAt NeckCylinderModel 𝓘(ℝ, ℝ) (Prod.snd : NeckCylinder → ℝ) x.1 :=
    mdifferentiableAt_snd
  have hc := mfderiv_comp x hsnd hval
  change mfderiv NeckCylinderModel 𝓘(ℝ, ℝ)
    (Prod.snd ∘ (Subtype.val : neckBuffer δ → NeckCylinder)) x w = _
  rw [hc, ContinuousLinearMap.comp_apply, mfderiv_subtype_val_apply, mfderiv_snd]
  rfl

omit [T2Space M] [SigmaCompactSpace M] in
theorem NormalizedNeck.dz_sq_le_NK (N : NormalizedNeck h δ k) (hk : 2 ≤ k) (hδ : δ ≤ 1 / 2)
    {x : neckBuffer δ} (hx : x ∈ neckClosedTest δ) (w : TangentSpace NeckCylinderModel x) :
    (show ℝ from mfderiv NeckCylinderModel 𝓘(ℝ, ℝ) (fun y : neckBuffer δ => y.1.2) x w) ^ 2 ≤
      4 * N.normalizedMetric.inner x w w := by
  rw [mfderiv_height_apply_NK]
  have h0 := N.metricDerivNorm_le_NK hk hx (m := 0) (by norm_num)
  have hδ0 : 0 ≤ δ := (Real.sqrt_nonneg _).trans h0
  have hcmp := (Geometry.Metric.sqrt_inner_comparison_of_metric_difference N.normalizedMetric
    ((Geometry.Metric.roundCylinderMetric (E := ThreeSpace) (n := 2)).restrictOpen
        (neckBuffer δ)) x δ (by linarith) h0 w).1
  have hA : 0 ≤ ((Geometry.Metric.roundCylinderMetric (E := ThreeSpace) (n := 2)).restrictOpen
        (neckBuffer δ)).inner x w w := metric_inner_self_nonneg _ _ _
  have hB : 0 ≤ N.normalizedMetric.inner x w w := metric_inner_self_nonneg _ _ _
  have hsq := pow_le_pow_left₀ (by positivity) hcmp 2
  rw [mul_pow, Real.sq_sqrt (by linarith), Real.sq_sqrt hA, Real.sq_sqrt hB] at hsq
  have hRC : ((Geometry.Metric.roundCylinderMetric (E := ThreeSpace) (n := 2)).restrictOpen
        (neckBuffer δ)).inner x w w =
      2 * inner ℝ (dIncl (E := ThreeSpace) (n := 2) x.1.1 w.1)
        (dIncl (E := ThreeSpace) (n := 2) x.1.1 w.1) + w.2 * w.2 :=
    Geometry.Metric.roundCylinderMetric_inner (E := ThreeSpace) (n := 2) x.1 w w
  have hin := real_inner_self_nonneg (x := dIncl (E := ThreeSpace) (n := 2) x.1.1 w.1)
  nlinarith [mul_nonneg (sub_nonneg.mpr hδ) hA]

omit [T2Space M] [SigmaCompactSpace M] in
theorem NormalizedNeck.isLocalDiffeomorph_chart_NK (N : NormalizedNeck h δ k) :
    IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ (N.chart : neckBuffer δ → M) := fun y =>
  Perelman.KappaSolutions.immersionAt_isLocalDiffeomorphAt_of_finrank_eq
    (by simp [ThreeSpace, Module.finrank_prod]) (N.chart_smooth.isImmersion.isImmersionAt y)

omit [T2Space M] [SigmaCompactSpace M] in
theorem NormalizedNeck.normalizedMetric_eq_localPull_NK (N : NormalizedNeck h δ k) :
    N.normalizedMetric = localPullMetric (scaleMetric N.scale N.scale_pos h)
      (N.chart : neckBuffer δ → M) N.isLocalDiffeomorph_chart_NK := by
  apply SmoothRiemannianMetric.ext_inner
  intro y V W
  rw [localPullMetric_inner, scaleMetric_inner, N.normalized_inner]

omit [SigmaCompactSpace M] in
theorem NormalizedNeck.metricScalarAt_chart_NK (N : NormalizedNeck h δ k) (x : neckBuffer δ) :
    metricScalarAt (scaleMetric N.scale N.scale_pos h) (N.chart x) =
      metricScalarAt N.normalizedMetric x := by
  rw [N.normalizedMetric_eq_localPull_NK, metricScalarAt_localPullMetric_scaleMetric,
    metricScalarAt_scaleMetric]

/-- neck 的高度坐标 `z : M → ℝ`（`chart` 像上取圆柱 `S² × ℝ` 的 ℝ 分量，其余处取 `0`）。 -/
def NormalizedNeck.height_NK (N : NormalizedNeck h δ k) : M → ℝ :=
  Subtype.val.extend (fun y : N.cylindricalChart.target =>
    (N.cylindricalChart.chart.symm y :
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ).2) (fun _ => 0)

omit [T2Space M] [SigmaCompactSpace M] in
theorem NormalizedNeck.height_chart_NK (N : NormalizedNeck h δ k) (x : neckBuffer δ) :
    N.height_NK (N.chart x) = x.1.2 := by
  rw [← N.cylindricalChart_chart_apply x]
  unfold NormalizedNeck.height_NK
  rw [Subtype.val_injective.extend_apply]
  exact congrArg (fun y : N.cylindricalChart.domain =>
    (y : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ).2)
    (N.cylindricalChart.chart.symm_apply_apply x)

omit [T2Space M] [SigmaCompactSpace M] in
theorem NormalizedNeck.isOpen_range_chart_NK (N : NormalizedNeck h δ k) :
    IsOpen (Set.range (N.chart : neckBuffer δ → M)) := by
  rw [← N.cylindricalChart_target]
  exact N.cylindricalChart.target.isOpen

omit [T2Space M] [SigmaCompactSpace M] in
theorem NormalizedNeck.contMDiffOn_height_NK (N : NormalizedNeck h δ k) :
    ContMDiffOn ThreeModel 𝓘(ℝ, ℝ) ∞ N.height_NK (Set.range (N.chart : neckBuffer δ → M)) := by
  have hq : ContMDiff ((𝓡 2).prod 𝓘(ℝ)) 𝓘(ℝ) ∞
      (fun y : N.cylindricalChart.domain =>
        (y : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ).2) :=
    contMDiff_snd.comp contMDiff_subtype_val
  have hf : ContMDiff ThreeModel 𝓘(ℝ) ∞ (fun y : N.cylindricalChart.target =>
      (N.cylindricalChart.chart.symm y :
        Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ).2) :=
    hq.comp N.cylindricalChart.chart.symm.contMDiff
  have h := contMDiffOn_extend_from_open N.cylindricalChart.target
    (fun y : N.cylindricalChart.target =>
      (N.cylindricalChart.chart.symm y :
        Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ).2) (fun _ => 0)
    (A := Set.univ) isOpen_univ hf.contMDiffOn
  rw [Set.image_univ, Subtype.range_coe, N.cylindricalChart_target] at h
  exact h

theorem isCompact_neckHeightLe_NK (δ c : ℝ) (hc : c ≤ δ⁻¹) :
    IsCompact {y : neckBuffer δ | |y.1.2| ≤ c} := by
  rw [Topology.IsEmbedding.isCompact_iff
    (Topology.IsEmbedding.subtypeVal (p := fun q => q ∈ neckBuffer δ))]
  have himg : (Subtype.val '' {y : neckBuffer δ | |y.1.2| ≤ c} : Set NeckCylinder) =
      (Set.univ : Set (Sphere 2)) ×ˢ Icc (-c) c := by
    ext q
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨Set.mem_univ _, abs_le.mp hy⟩
    · rintro ⟨-, hq⟩
      refine ⟨⟨q, ?_⟩, abs_le.mpr hq, rfl⟩
      change -δ⁻¹ - 1 < q.2 ∧ q.2 < δ⁻¹ + 1
      constructor <;> linarith [hq.1, hq.2]
  rw [himg]
  exact isCompact_univ.prod isCompact_Icc

omit [SigmaCompactSpace M] in
theorem NormalizedNeck.closure_band_subset_range_NK (N : NormalizedNeck h δ k)
    (h20 : 20 ≤ δ⁻¹) :
    closure {p : M | p ∈ Set.range (N.chart : neckBuffer δ → M) ∧ |N.height_NK p| < 20} ⊆
      Set.range (N.chart : neckBuffer δ → M) := by
  have hK : IsCompact (N.chart '' {y : neckBuffer δ | |y.1.2| ≤ 20}) :=
    (isCompact_neckHeightLe_NK δ 20 h20).image N.chart.continuous
  have hsub : {p : M | p ∈ Set.range (N.chart : neckBuffer δ → M) ∧ |N.height_NK p| < 20} ⊆
      N.chart '' {y : neckBuffer δ | |y.1.2| ≤ 20} := by
    rintro _ ⟨⟨y, rfl⟩, hy⟩
    rw [N.height_chart_NK] at hy
    exact ⟨y, hy.le, rfl⟩
  exact (closure_minimal hsub hK.isClosed).trans (Set.image_subset_range _ _)

omit [T2Space M] [SigmaCompactSpace M] in
theorem NormalizedNeck.height_dz_sq_le_NK (N : NormalizedNeck h δ k) (hk : 2 ≤ k)
    (hδ : δ ≤ 1 / 2) (h20 : 20 ≤ δ⁻¹) {p : M} (hp : p ∈ Set.range (N.chart : neckBuffer δ → M))
    (hz : |N.height_NK p| < 20) (w : TangentSpace ThreeModel p) :
    (show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ) N.height_NK p w) ^ 2 ≤
      4 * (scaleMetric N.scale N.scale_pos h).inner p w w := by
  obtain ⟨x, rfl⟩ := hp
  rw [N.height_chart_NK] at hz
  have hx : x ∈ neckClosedTest δ := by
    have := abs_le.mp (hz.le.trans h20)
    exact this
  obtain ⟨v, hv⟩ := (N.isLocalDiffeomorph_chart_NK.mfderivToContinuousLinearEquiv
    infty_ne_zero_NK x).surjective w
  have hv' : mfderiv NeckCylinderModel ThreeModel (N.chart : neckBuffer δ → M) x v = w := by
    rw [← hv]
    exact (N.isLocalDiffeomorph_chart_NK.mfderivToContinuousLinearEquiv_coe infty_ne_zero_NK x
      ▸ rfl)
  have hZ : MDifferentiableAt ThreeModel 𝓘(ℝ, ℝ) N.height_NK (N.chart x) :=
    ((N.contMDiffOn_height_NK _ ⟨x, rfl⟩).contMDiffAt
      (N.isOpen_range_chart_NK.mem_nhds ⟨x, rfl⟩)).mdifferentiableAt (by simp)
  have hC : MDifferentiableAt NeckCylinderModel ThreeModel (N.chart : neckBuffer δ → M) x :=
    (N.chart_smooth.contMDiff.mdifferentiableAt (by simp))
  have hcomp : N.height_NK ∘ (N.chart : neckBuffer δ → M) = fun y : neckBuffer δ => y.1.2 :=
    funext N.height_chart_NK
  have hchain := mfderiv_comp x hZ hC
  rw [hcomp] at hchain
  have hdz : (show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ) N.height_NK (N.chart x) w) =
      (show ℝ from mfderiv NeckCylinderModel 𝓘(ℝ, ℝ) (fun y : neckBuffer δ => y.1.2) x v) := by
    rw [hchain]
    change _ = (mfderiv ThreeModel 𝓘(ℝ, ℝ) N.height_NK (N.chart x))
      (mfderiv NeckCylinderModel ThreeModel (N.chart : neckBuffer δ → M) x v)
    rw [hv']
  rw [hdz, scaleMetric_inner, ← hv', ← N.normalized_inner]
  exact N.dz_sq_le_NK hk hδ hx v

omit [SigmaCompactSpace M] in
/-- **IMS06′ 的 band 估计（G2）**：`k ≥ 2`、`δ ≤ 1/8646`（于是 `20 ≤ δ⁻¹`）的 `NormalizedNeck`
给出开集 `range chart`、其上的光滑高度 `height_NK`，band `{|z| < 20}` 的闭包仍在 `range chart` 内，
且在 band 上（对 scalar-one 归一化度量 `scaleMetric N.scale h`）`R ≥ 1/2`、`|dz|² ≤ 4 g`。 -/
theorem NormalizedNeck.band_estimates_NK (N : NormalizedNeck h δ k) (hk : 2 ≤ k)
    (hδ : δ ≤ 1 / 8646) :
    IsOpen (Set.range (N.chart : neckBuffer δ → M)) ∧
    ContMDiffOn ThreeModel 𝓘(ℝ, ℝ) ∞ N.height_NK (Set.range (N.chart : neckBuffer δ → M)) ∧
    closure {p : M | p ∈ Set.range (N.chart : neckBuffer δ → M) ∧ |N.height_NK p| < 20} ⊆
      Set.range (N.chart : neckBuffer δ → M) ∧
    (∀ p ∈ Set.range (N.chart : neckBuffer δ → M), |N.height_NK p| < 20 →
      1 / 2 ≤ metricScalarAt (scaleMetric N.scale N.scale_pos h) p) ∧
    (∀ p ∈ Set.range (N.chart : neckBuffer δ → M), |N.height_NK p| < 20 →
      ∀ w : TangentSpace ThreeModel p,
        (show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ) N.height_NK p w) ^ 2 ≤
          4 * (scaleMetric N.scale N.scale_pos h).inner p w w) := by
  have h20 : 20 ≤ δ⁻¹ := by
    have hpos := N.delta_pos
    rw [le_inv_comm₀ (by norm_num) hpos]
    linarith
  refine ⟨N.isOpen_range_chart_NK, N.contMDiffOn_height_NK,
    N.closure_band_subset_range_NK h20, ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩ hz
    rw [N.height_chart_NK] at hz
    have hx : x ∈ neckClosedTest δ := abs_le.mp (hz.le.trans h20)
    rw [N.metricScalarAt_chart_NK]
    exact N.scalar_lower_NK hk hδ hx
  · intro p hp hz w
    exact N.height_dz_sq_le_NK hk (by linarith) h20 hp hz w

omit [SigmaCompactSpace M] in
/-- 同一个 η₀ 的存在形式（IAU02 的 `δ < δ*` 对应）：`η₀ = 1/8646`，`k ≥ 2`。 -/
theorem exists_eta_band_estimates_NK :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ {h : SmoothRiemannianMetric ThreeModel M} {δ : ℝ} {k : ℕ}
      (N : NormalizedNeck h δ k), 2 ≤ k → δ < η₀ →
      IsOpen (Set.range (N.chart : neckBuffer δ → M)) ∧
      ContMDiffOn ThreeModel 𝓘(ℝ, ℝ) ∞ N.height_NK (Set.range (N.chart : neckBuffer δ → M)) ∧
      closure {p : M | p ∈ Set.range (N.chart : neckBuffer δ → M) ∧ |N.height_NK p| < 20} ⊆
        Set.range (N.chart : neckBuffer δ → M) ∧
      (∀ p ∈ Set.range (N.chart : neckBuffer δ → M), |N.height_NK p| < 20 →
        1 / 2 ≤ metricScalarAt (scaleMetric N.scale N.scale_pos h) p) ∧
      (∀ p ∈ Set.range (N.chart : neckBuffer δ → M), |N.height_NK p| < 20 →
        ∀ w : TangentSpace ThreeModel p,
          (show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ) N.height_NK p w) ^ 2 ≤
            4 * (scaleMetric N.scale N.scale_pos h).inner p w w) :=
  ⟨1 / 8646, by norm_num, fun N hk hδ => N.band_estimates_NK hk hδ.le⟩

omit [T2Space M] [SigmaCompactSpace M] in
/-- consumer：band 估计的平方形式给出 `|dz w| ≤ 2 √(g w w)`（路径长度引理用的 Lipschitz 形式）。 -/
theorem abs_mfderiv_height_le_NK {g : SmoothRiemannianMetric ThreeModel M} (Z : M → ℝ) {p : M}
    (hdz : ∀ w : TangentSpace ThreeModel p,
      (show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ) Z p w) ^ 2 ≤ 4 * g.inner p w w)
    (w : TangentSpace ThreeModel p) :
    |show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ) Z p w| ≤ 2 * Real.sqrt (g.inner p w w) := by
  have h := hdz w
  have h0 : 0 ≤ g.inner p w w := metric_inner_self_nonneg g p w
  rw [← sq_le_sq₀ (abs_nonneg _) (by positivity), sq_abs, mul_pow, Real.sq_sqrt h0]
  linarith

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
