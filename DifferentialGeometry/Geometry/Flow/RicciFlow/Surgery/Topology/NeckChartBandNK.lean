import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.NeckBandEstimatesNK
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.NeckCylindricalChartBridge

/-!
# Route W, c4：一般嵌入 `c : neckBuffer δ → M` 的 band 估计转运（S-W-NECK G5，后缀 `_NK`，第 1 部分）

G2 的 M 侧部分只用到 `NormalizedNeck` 的 chart 是光滑嵌入，这里写成一般形式：
`chartHeight_NK c`（`range c` 上取圆柱的 ℝ 分量，其余处 `0`），以及
`chart_band_estimates_NK`：若 `ĝ = c^* gm`（逐点 `ĝ.inner x V W = gm.inner (c x) (dc V) (dc W)`）
在 `|z| < 20` 上满足 `a ≤ R`、`(dz)² ≤ C ĝ`，则 `gm` 在 `range c` 的 band 上满足同样估计，
并且 `range c` 开、`chartHeight_NK c` 光滑、band 闭包仍在 `range c` 内（`20 ≤ δ⁻¹`）。
用于 surgery 前时刻 `s ↑ τ₀` 的 slice：`c = stageChart`，`gm = scaleMetric (r²)⁻¹ (g s)`。
-/

set_option autoImplicit false
noncomputable section
open Set Manifold Filter
open DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

private local instance : Fact (Module.finrank ℝ ThreeSpace = 2 + 1) := ⟨by simp [ThreeSpace]⟩

private lemma infty_ne_zero_NK2 : (∞ : WithTop ℕ∞) ≠ 0 := by decide

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M] [T2Space M]

/-- 任意光滑嵌入 `c : neckBuffer δ → M` 的高度坐标（`range c` 上取圆柱的 ℝ 分量，其余处取 `0`）。 -/
def chartHeight_NK {δ : ℝ} (c : neckBuffer δ → M) : M → ℝ :=
  Function.extend c (fun y : neckBuffer δ => y.1.2) (fun _ => 0)

omit [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M] [T2Space M] in
theorem chartHeight_chart_NK {δ : ℝ} {c : neckBuffer δ → M} (hc : Function.Injective c)
    (x : neckBuffer δ) : chartHeight_NK c (c x) = x.1.2 :=
  hc.extend_apply _ _ x

omit [IsManifold ThreeModel ∞ M] [T2Space M] in
theorem isLocalDiffeomorph_of_embedding_NK {δ : ℝ} {c : neckBuffer δ → M}
    (hc : IsSmoothEmbedding NeckCylinderModel ThreeModel ∞ c) :
    IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ c := fun y =>
  Perelman.KappaSolutions.immersionAt_isLocalDiffeomorphAt_of_finrank_eq
    (by simp [ThreeSpace, Module.finrank_prod]) (hc.isImmersion.isImmersionAt y)

omit [T2Space M] in
theorem exists_chart_diffeo_NK {δ : ℝ} {c : neckBuffer δ → M}
    (hc : IsSmoothEmbedding NeckCylinderModel ThreeModel ∞ c) :
    ∃ (V : TopologicalSpace.Opens M) (Φ : neckBuffer δ ≃ₘ⟮NeckCylinderModel, ThreeModel⟯ V),
      (V : Set M) = Set.range c ∧ (∀ x, (Φ x : M) = c x) ∧ (∀ y : V, c (Φ.symm y) = (y : M)) := by
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ) =
      Module.finrank ℝ ThreeSpace := by
    simp [ThreeSpace]
  have hinj : ∀ y : neckBuffer δ,
      Function.Injective (mfderiv NeckCylinderModel ThreeModel c y) :=
    fun y => injective_mfderiv_of_isImmersionAt NeckCylinderModel ThreeModel c y
      (hc.isImmersion.isImmersionAt y)
  exact exists_diffeomorph_onto_range_of_injective_immersion (I := NeckCylinderModel)
    (J := ThreeModel) c hc.contMDiff hc.isEmbedding.injective hinj hdim

omit [T2Space M] in
theorem isOpen_range_chart_of_embedding_NK {δ : ℝ} {c : neckBuffer δ → M}
    (hc : IsSmoothEmbedding NeckCylinderModel ThreeModel ∞ c) : IsOpen (Set.range c) := by
  obtain ⟨V, Φ, hV, -, -⟩ := exists_chart_diffeo_NK hc
  rw [← hV]
  exact V.isOpen

omit [T2Space M] in
theorem contMDiffOn_chartHeight_NK {δ : ℝ} {c : neckBuffer δ → M}
    (hc : IsSmoothEmbedding NeckCylinderModel ThreeModel ∞ c) :
    ContMDiffOn ThreeModel 𝓘(ℝ, ℝ) ∞ (chartHeight_NK c) (Set.range c) := by
  obtain ⟨V, Φ, hV, hΦ, hΦ'⟩ := exists_chart_diffeo_NK hc
  have hq : ContMDiff NeckCylinderModel 𝓘(ℝ) ∞ (fun y : neckBuffer δ => y.1.2) :=
    contMDiff_snd.comp contMDiff_subtype_val
  have hf : ContMDiff ThreeModel 𝓘(ℝ) ∞ (fun y : V => ((Φ.symm y : neckBuffer δ)).1.2) :=
    hq.comp Φ.symm.contMDiff
  have h := contMDiffOn_extend_from_open V (fun y : V => ((Φ.symm y : neckBuffer δ)).1.2)
    (fun _ => 0) (A := Set.univ) isOpen_univ hf.contMDiffOn
  rw [Set.image_univ, Subtype.range_coe, hV] at h
  refine h.congr ?_
  rintro _ ⟨x, rfl⟩
  rw [chartHeight_chart_NK hc.isEmbedding.injective, ← hΦ x,
    Subtype.val_injective.extend_apply]
  exact congrArg (fun y : neckBuffer δ => y.1.2) (Φ.symm_apply_apply x).symm

omit [IsManifold ThreeModel ∞ M] in
theorem closure_band_chart_NK {δ : ℝ} {c : neckBuffer δ → M}
    (hc : IsSmoothEmbedding NeckCylinderModel ThreeModel ∞ c) (h20 : 20 ≤ δ⁻¹) :
    closure {p : M | p ∈ Set.range c ∧ |chartHeight_NK c p| < 20} ⊆ Set.range c := by
  have hK : IsCompact (c '' {y : neckBuffer δ | |y.1.2| ≤ 20}) :=
    (isCompact_neckHeightLe_NK δ 20 h20).image hc.contMDiff.continuous
  have hsub : {p : M | p ∈ Set.range c ∧ |chartHeight_NK c p| < 20} ⊆
      c '' {y : neckBuffer δ | |y.1.2| ≤ 20} := by
    rintro _ ⟨⟨y, rfl⟩, hy⟩
    rw [chartHeight_chart_NK hc.isEmbedding.injective] at hy
    exact ⟨y, hy.le, rfl⟩
  exact (closure_minimal hsub hK.isClosed).trans (Set.image_subset_range _ _)

/-- **一般嵌入的 band 估计转运**：`ĝ = c^* gm` 在 `|z| < 20` 上满足 `a ≤ R`、`(dz)² ≤ C ĝ`，
则 `gm` 在 `range c` 的 band 上满足同样的估计（`z = chartHeight_NK c`）。 -/
theorem chart_band_estimates_NK {δ : ℝ} {c : neckBuffer δ → M}
    (hc : IsSmoothEmbedding NeckCylinderModel ThreeModel ∞ c) (h20 : 20 ≤ δ⁻¹)
    (gm : SmoothRiemannianMetric ThreeModel M)
    (ĝ : SmoothRiemannianMetric NeckCylinderModel (neckBuffer δ))
    (hĝ : ∀ x V W, ĝ.inner x V W = gm.inner (c x)
      (mfderiv NeckCylinderModel ThreeModel c x V) (mfderiv NeckCylinderModel ThreeModel c x W))
    {a C : ℝ}
    (hR : ∀ x : neckBuffer δ, |x.1.2| < 20 → a ≤ metricScalarAt ĝ x)
    (hdz : ∀ x : neckBuffer δ, |x.1.2| < 20 → ∀ w : TangentSpace NeckCylinderModel x,
      (show ℝ from mfderiv NeckCylinderModel 𝓘(ℝ, ℝ) (fun y : neckBuffer δ => y.1.2) x w) ^ 2 ≤
        C * ĝ.inner x w w) :
    IsOpen (Set.range c) ∧
    ContMDiffOn ThreeModel 𝓘(ℝ, ℝ) ∞ (chartHeight_NK c) (Set.range c) ∧
    closure {p : M | p ∈ Set.range c ∧ |chartHeight_NK c p| < 20} ⊆ Set.range c ∧
    (∀ p ∈ Set.range c, |chartHeight_NK c p| < 20 → a ≤ metricScalarAt gm p) ∧
    (∀ p ∈ Set.range c, |chartHeight_NK c p| < 20 → ∀ w : TangentSpace ThreeModel p,
      (show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ) (chartHeight_NK c) p w) ^ 2 ≤
        C * gm.inner p w w) := by
  have hlocal := isLocalDiffeomorph_of_embedding_NK hc
  have hEq : ĝ = localPullMetric gm c hlocal := by
    apply SmoothRiemannianMetric.ext_inner
    intro y V W
    rw [localPullMetric_inner, hĝ]
  refine ⟨isOpen_range_chart_of_embedding_NK hc, contMDiffOn_chartHeight_NK hc,
    closure_band_chart_NK hc h20, ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩ hz
    rw [chartHeight_chart_NK hc.isEmbedding.injective] at hz
    have := hR x hz
    rwa [hEq, metricScalarAt_localPull] at this
  · rintro _ ⟨x, rfl⟩ hz w
    rw [chartHeight_chart_NK hc.isEmbedding.injective] at hz
    obtain ⟨v, hv⟩ := (hlocal.mfderivToContinuousLinearEquiv infty_ne_zero_NK2 x).surjective w
    have hv' : mfderiv NeckCylinderModel ThreeModel c x v = w := by
      rw [← hv]
      exact (hlocal.mfderivToContinuousLinearEquiv_coe infty_ne_zero_NK2 x ▸ rfl)
    have hZ : MDifferentiableAt ThreeModel 𝓘(ℝ, ℝ) (chartHeight_NK c) (c x) :=
      (((contMDiffOn_chartHeight_NK hc) _ ⟨x, rfl⟩).contMDiffAt
        ((isOpen_range_chart_of_embedding_NK hc).mem_nhds ⟨x, rfl⟩)).mdifferentiableAt
        (by simp)
    have hC : MDifferentiableAt NeckCylinderModel ThreeModel c x :=
      hc.contMDiff.mdifferentiableAt (by simp)
    have hcomp : chartHeight_NK c ∘ c = fun y : neckBuffer δ => y.1.2 :=
      funext (chartHeight_chart_NK hc.isEmbedding.injective)
    have hchain := mfderiv_comp x hZ hC
    rw [hcomp] at hchain
    have hdz' : (show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ) (chartHeight_NK c) (c x) w) =
        (show ℝ from mfderiv NeckCylinderModel 𝓘(ℝ, ℝ) (fun y : neckBuffer δ => y.1.2) x v) := by
      rw [hchain]
      change _ = (mfderiv ThreeModel 𝓘(ℝ, ℝ) (chartHeight_NK c) (c x))
        (mfderiv NeckCylinderModel ThreeModel c x v)
      rw [hv']
    rw [hdz', ← hv', ← hĝ]
    exact hdz x hz v

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
