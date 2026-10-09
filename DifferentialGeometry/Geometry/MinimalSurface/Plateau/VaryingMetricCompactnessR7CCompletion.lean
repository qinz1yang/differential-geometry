import DifferentialGeometry.Geometry.Metric.Conformal.PositiveDomain
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.HomogeneousRegularity
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# R7C：`C` 的 completion buffer `(W, Ĝ)`（"W-trick"，route M 的 L3）

R7 varying-metric compactness 中，所有 local comparison 只发生在 `C`（像所在的紧集）附近。本文件在
`int B` 里造一个开集 `W ⊇ C`（闭包紧且 ⊆ `int B`）和 `W` 上的 homogeneously regular 度量
`Ĝ = δ⁻² G`（树内 `canonicalPositiveDomainMetric`，`δ` 为光滑 bump，`δ = 1` 于 `C` 的开邻域 `O`，
`{δ > 0} = W`），满足：
- `Ĝ ≥ G` 于 `W`（`δ ≤ 1`），于是 `Gₙ ≤ (1+ε)G ≤ (1+ε)Ĝ` 于 `W`；
- `Ĝ = G` 于 `O` 的每点邻域（germ 相等），于是像在 `C` 里的盘的 `Ĝ`-能量 = `G`-能量。
这样树内 HR 版 competitor 构造（常数只依赖 `(W, Ĝ)`）可以对所有 `Gₙ`-Morrey 盘一致使用。
不需要 `Ĝ` complete（只用 HR）。
-/

set_option autoImplicit false

open Set Filter Bundle Manifold TopologicalSpace DifferentialGeometry.Geometry.Metric
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- **completion buffer**（R7C L3）：`C` 紧 ⊆ `int B` ⇒ 存在开 `W`（`C ⊆ O ⊆ W`，`closure W` 紧且
⊆ `int B`）与 `W` 上 homogeneously regular 度量 `Ĝ`，`Ĝ ≥ G|_W` 逐点，且在 `O` 的点附近
`Ĝ = G|_W`（inner germ 相等）。`Ĝ = δ⁻² G`，`δ` 是 `C` 邻域上恒为 1 的光滑 bump。 -/
theorem exists_completion_buffer_R7C [T3Space M] [SecondCountableTopology M]
    (hdim : Module.finrank ℝ E = 3) (G : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {B C : Set M} (hC : IsCompact C) (hCB : C ⊆ interior B) :
    ∃ (W : Opens M) (Ghat : SmoothRiemannianMetric 𝓘(ℝ, E) W) (O : Set M),
      IsOpen O ∧ C ⊆ O ∧ O ⊆ (W : Set M) ∧ closure (W : Set M) ⊆ interior B ∧
      IsCompact (closure (W : Set M)) ∧ HomogeneouslyRegularMetric Ghat ∧
      (∀ (x : W) (v : TangentSpace 𝓘(ℝ, E) x),
        (G.restrictOpen W).inner x v v ≤ Ghat.inner x v v) ∧
      ∀ x : W, (x : M) ∈ O → ∀ᶠ y in 𝓝 x, Ghat.inner y = (G.restrictOpen W).inner y := by
  have : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional 𝓘(ℝ, E)
  obtain ⟨V, hVo, hCV, hVB, hVc⟩ :=
    exists_open_between_and_isCompact_closure hC isOpen_interior hCB
  obtain ⟨O, hOo, hCO, hOV, _⟩ := exists_open_between_and_isCompact_closure hC hVo hCV
  have hdisj : Disjoint Vᶜ (closure O) :=
    disjoint_compl_left_iff_subset.mpr hOV
  obtain ⟨f, hf0, hf1, hf01⟩ := exists_contMDiffMap_zero_one_of_isClosed (n := (⊤ : ℕ∞))
    𝓘(ℝ, E) hVo.isClosed_compl isClosed_closure hdisj
  set δ : M → ℝ := fun x => f x with hδdef
  have hδ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ δ := f.contMDiff
  let W : Opens M := ⟨{x | 0 < δ x}, isOpen_lt continuous_const hδ.continuous⟩
  have hW : ∀ x : M, x ∈ W ↔ 0 < δ x := fun x => Iff.rfl
  have hWV : (W : Set M) ⊆ V := by
    intro x hx
    by_contra hxV
    have h0 : δ x = 0 := hf0 hxV
    have hpos : 0 < δ x := hx
    linarith
  have hO1 : ∀ x ∈ O, δ x = 1 := fun x hx => hf1 (subset_closure hx)
  have hOW : O ⊆ (W : Set M) := by
    intro x hx
    change 0 < δ x
    rw [hO1 x hx]
    exact one_pos
  have hWcl : closure (W : Set M) ⊆ closure V := closure_mono hWV
  refine ⟨W, canonicalPositiveDomainMetric G hδ W hW, O, hOo, hCO, hOW, hWcl.trans hVB,
    hVc.of_isClosed_subset isClosed_closure hWcl, ?_, ?_, ?_⟩
  · exact PositiveDomainCharts.homogeneouslyRegularMetric_positive_domain
      G hδ W hW (hVc.of_isClosed_subset isClosed_closure hWcl) _
      (canonicalPositiveDomainMetric_inner G hδ W hW) hdim
  · intro x v
    rw [canonicalPositiveDomainMetric_inner]
    have hpos : 0 < δ (x : M) := x.property
    have hle : δ (x : M) ≤ 1 := (hf01 x).2
    have hinv : 1 ≤ (δ (x : M))⁻¹ := one_le_inv₀ hpos |>.mpr hle
    have hsq : 1 ≤ (δ (x : M))⁻¹ ^ 2 := one_le_pow₀ hinv
    have hnn : 0 ≤ (G.restrictOpen W).inner x v v := metric_inner_self_nonneg _ _ _
    nlinarith
  · intro x hx
    exact canonicalPositiveDomainMetric_inner_eventuallyEq G hδ W hW ⟨O, hOo⟩ hO1 x hx

end DifferentialGeometry.Geometry
