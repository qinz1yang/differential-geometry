import DifferentialGeometry.Geometry.MinimalSurface.Plateau.TrimCollarMR1
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Embeddedness.RegularDisk
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.PairedReplacementFoldLocalRank
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.ChartFoldShortening
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.ImmersionLift
import DifferentialGeometry.Geometry.MinimalSurface.Variation.NonzeroFoldFlow
import DifferentialGeometry.Geometry.Measure.Area.ForwardPhaseDisk
import DifferentialGeometry.Topology.Embedding.TransverseIntersectionLimit

/-!
# S-MY-SHAPES G2：外审 R1 / R2 / R4 / R13 / R15 的 shape adapters（后缀 _MYS）

只放 `example`：把 W8 树里已有定理的精确陈述对到外审 R-合同的形状（EXACT：型相同；
ADAPTER：几行推导）。**不引入任何新定义 / 新 Prop / 新 theorem 名；不加任何前提**。
对应审计表 `docs/geometrization/chapter8/MY-SHAPES-AUDIT-20261006.md`。

* `R1`：`lemma_R1_MR1`（TrimCollarMR1:297）⇒ 外审 R1 的显式形（collar、trimmed 边界嵌入、
  内外像不交、ε 分离、重数界）。
* `R2`：R1 给出的 trimmed disk 是同一 metric 下的 Morrey disk ⇒ `A_G(q_r) ≤ A_G(v)`，
  对一切 weak-phase Lipschitz competitor（含取值于 `K` 的子类）。
* `R2-obligation`：`exists_forwardPhase_pastedDisk` 的前提表里只有 `ContDiff ∞ φ` +
  `StrictMono φ` + 周期性，**没有**逆相位 Lipschitz / 正导数（D-R-MY1-5 的核对证书）。
* `R4`：`exists_supported_flow_of_nonzero_fold` + `exists_disk_area_lt_of_fold_divergence_neg`
  ⇒ conormal 和 ≠ 0 的 fold 给出严格更小的 Lipschitz competitor（同 trace、同 target 内部）。
* `R11-lift`：`IsMorreyDisk.minimizesLipschitz_of_immersion_lift`（smooth 面积侧的 lift 极小性）。
* `R13-smooth`：`not_transverse_of_paired_source_disks` 改写成 `f ∘ b = f` 的边界识别形
  （只覆盖 smooth 闭盘 chart；cornered / bi-Lipschitz 版缺失，见审计表）。
* `R15`：MY-13 的 `Topology.Manifold` 版 = R15 的 C¹ 极限无 transverse collision；source 缩放
  不变性；R15 结论 ⇒ K13 的 `hNoTransverse` ⇒ `IsEmbedding q`。
-/

set_option autoImplicit false
noncomputable section

open Set Filter Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.ImmersedDiskDivergence.Within
open DifferentialGeometry.Geometry.ImmersedDiskDivergence.HalfDisk
open scoped Topology Manifold ContDiff NNReal ENNReal ComplexConjugate

namespace GC.LongTime.CuspP1

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

/-! ## R1（EXACT）：trim + singleton collar + compact collision relation -/

/-- 外审 R1 的显式形：`lemma_R1_MR1` 逐项给出。`r₁ < r₂` 两个 trim 半径都在 `(ρ₀, 1)`；
`q_r(D°) ∩ q_r(S¹) = ∅` 写成逐点不等式。 -/
example
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {γ : freeLoop M}
    {q : C(closedDisk, M)} (hq : IsMorreyDisk g γ q) (hγ : IsSmoothEmbeddedLoop (E := E) γ)
    {Q : ℂ → M} (hQ : SmoothDiskExtension (E := E) q Q)
    (hrank : ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) Q z))
    (hseparate : ∀ z : closedDisk, ‖(z : ℂ)‖ < 1 → ∀ θ : loopCircle, q z ≠ γ θ) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ρ₀ < 1 ∧
      (∀ z w : closedDisk, ρ₀ < ‖(z : ℂ)‖ → q z = q w → z = w) ∧
      (∀ r₁ r₂ : ℝ, ρ₀ < r₁ → r₁ < r₂ → r₂ < 1 →
        (IsSmoothEmbeddedLoop (E := E) (diskTrace (affineSubdisk q 0 r₁)) ∧
          ∀ z w : closedDisk, ‖(z : ℂ)‖ < 1 → ‖(w : ℂ)‖ = 1 →
            affineSubdisk q 0 r₁ z ≠ affineSubdisk q 0 r₁ w) ∧
        (IsSmoothEmbeddedLoop (E := E) (diskTrace (affineSubdisk q 0 r₂)) ∧
          ∀ z w : closedDisk, ‖(z : ℂ)‖ < 1 → ‖(w : ℂ)‖ = 1 →
            affineSubdisk q 0 r₂ z ≠ affineSubdisk q 0 r₂ w)) ∧
      (∃ ε : ℝ, 0 < ε ∧
        ∀ x y : closedDisk, x ≠ y → q x = q y → ε ≤ dist (x : ℂ) (y : ℂ)) ∧
      ∃ m : ℕ, ∀ p : M, (q ⁻¹' {p}).Finite ∧ (q ⁻¹' {p}).ncard ≤ m := by
  obtain ⟨ρ₀, hρ₀, hρ₀1, hcol, htrim, hε, hm⟩ :=
    lemma_R1_MR1 hq hγ hQ hrank hseparate
  have hsep (r : ℝ) (hr : ρ₀ < r) (hr1 : r < 1) :
      IsSmoothEmbeddedLoop (E := E) (diskTrace (affineSubdisk q 0 r)) ∧
        ∀ z w : closedDisk, ‖(z : ℂ)‖ < 1 → ‖(w : ℂ)‖ = 1 →
          affineSubdisk q 0 r z ≠ affineSubdisk q 0 r w := by
    obtain ⟨hloop, -, hdisj⟩ := htrim r hr hr1
    refine ⟨hloop, fun z w hz hw hzw => ?_⟩
    exact Set.disjoint_left.mp hdisj ⟨z, hz, rfl⟩ ⟨w, hw, hzw.symm⟩
  exact ⟨ρ₀, hρ₀, hρ₀1, hcol,
    fun r₁ r₂ h₁ h₁₂ h₂ => ⟨hsep r₁ h₁ (h₁₂.trans h₂), hsep r₂ (h₁.trans h₁₂) h₂⟩, hε, hm⟩

/-! ## R2（EXACT，经 R1）：proper subdisk 在同一 target 中面积极小 -/

/-- 外审 R2：`ρ₀ < r < 1` 时 `q_r = affineSubdisk q 0 r` 对一切 trace 为 `Γ_r` 的 weakly monotone
once 参数化、metric-Lipschitz 的 `v : C(closedDisk, M)` 有 `A_G(q_r) ≤ A_G(v)`；取值于子集
`K` 的 competitor 类是其子类。这里没有逆 weak phase 的 Lipschitz 假设。 -/
example
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {γ : freeLoop M}
    {q : C(closedDisk, M)} (hq : IsMorreyDisk g γ q) (hγ : IsSmoothEmbeddedLoop (E := E) γ)
    {Q : ℂ → M} (hQ : SmoothDiskExtension (E := E) q Q)
    (hrank : ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) Q z))
    (hseparate : ∀ z : closedDisk, ‖(z : ℂ)‖ < 1 → ∀ θ : loopCircle, q z ≠ γ θ) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ρ₀ < 1 ∧ ∀ r : ℝ, ρ₀ < r → r < 1 →
      ∀ K : Set M, ∀ v : C(closedDisk, M), Set.range v ⊆ K →
        DiskWeakJordanTrace (diskTrace (affineSubdisk q 0 r)) v →
        (∃ L : ℝ≥0, ∀ z w : closedDisk,
          riemannianEDistOf g (v z) (v w) ≤ (L : ℝ≥0∞) * edist z w) →
        riemannianDiskArea g (affineSubdisk q 0 r) ≤ riemannianDiskArea g v := by
  obtain ⟨ρ₀, hρ₀, hρ₀1, -, htrim, -, -⟩ := lemma_R1_MR1 hq hγ hQ hrank hseparate
  refine ⟨ρ₀, hρ₀, hρ₀1, fun r hr hr1 K v _ hv hLip => ?_⟩
  exact (htrim r hr hr1).2.1.minimizesLipschitz v hv hLip

/-- D-R-MY1-5 的核对证书：MY-2 的 forward-phase paste 只要 `φ : ℝ ≃ₜ ℝ`、`ContDiff ∞`、
`StrictMono`、周期 `φ (t+1) = φ t + 1`；前提表里没有 `LipschitzWith φ.symm`、`0 < deriv φ`
之类的逆相位控制。下面 `example` 的前提就是该定理的前提（逐项照抄）。 -/
example
    (G : SmoothRiemannianMetric 𝓘(ℝ, E) M) (q a : C(closedDisk, M)) {Lq La : ℝ≥0}
    (hqLip : ∀ z w : closedDisk, riemannianEDistOf G (q z) (q w) ≤ (Lq : ℝ≥0∞) * edist z w)
    (haLip : ∀ z w : closedDisk, riemannianEDistOf G (a z) (a w) ≤ (La : ℝ≥0∞) * edist z w)
    (hqSmooth : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (diskExtension q) (Metric.ball (0 : ℂ) 1))
    {r b : ℝ} (hr : 0 < r) (hrb : r < b) (hb : b < 1)
    (φ : ℝ ≃ₜ ℝ) (hφ : ContDiff ℝ ∞ (fun t : ℝ => φ t))
    (hm : StrictMono φ) (hp : ∀ t : ℝ, φ (t + 1) = φ t + 1)
    (htrace : ∀ t : ℝ, diskTrace a (t : loopCircle) =
      diskExtension q (r • (AddCircle.toCircle (φ t : loopCircle) : ℂ))) :
    ∃ F : C(closedDisk, M), diskTrace F = diskTrace q ∧
      riemannianDiskArea G F = riemannianDiskArea G q -
        riemannianArea G (diskExtension q) (Metric.closedBall (0 : ℂ) r) +
        riemannianDiskArea G a := by
  obtain ⟨F, -, -, -, -, -, -, htr, -, -, harea⟩ :=
    exists_forwardPhase_pastedDisk G q a hqLip haLip hqSmooth hr hrb hb φ hφ hm hp htrace
  exact ⟨F, htr, harea⟩

/-! ## R4（ADAPTER）：fold ⇒ 严格更优的 Lipschitz competitor -/

/-- 外审 R4（conformal-parameter、seam 在源坐标里是实轴线段的形）：在两个闭半盘 sheet
`u|_{上半盘}`、`u∘conj|_{上半盘}`（`C¹` 到 seam、内部 smooth、conformal harmonic、
differential 单射）的 seam 点 `p` 处 outward conormal 和 `≠ 0`，且 `u(p)` 在 `W` 的内部，则存在
metric-Lipschitz `v`，trace 与 `u` 相同、取值于 `W`、面积严格更小。competitor 是 map，不要求
embedded；变分支在 seam 附近的开 ball 内。 -/
example
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (u : C(closedDisk, M)) {L : ℝ≥0}
    (huLip : ∀ z w, riemannianEDistOf g (u z) (u w) ≤ (L : ℝ≥0∞) * edist z w)
    {W : Set M} (huW : Set.range u ⊆ W) {p R : ℝ} (hR : 0 < R) (hpR : ‖(p : ℂ)‖ + R < 1)
    (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 (diskExtension u) (closedHalfDisk p R))
    (hUr : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 (diskExtension u ∘ conj) (closedHalfDisk p R))
    (hi : ∀ z ∈ closedHalfDisk p R, Function.Injective
      (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) (closedHalfDisk p R) z))
    (hir : ∀ z ∈ closedHalfDisk p R, Function.Injective
      (mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u ∘ conj) (closedHalfDisk p R) z))
    (hUi : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (diskExtension u) (openHalfDisk p R))
    (hUri : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (diskExtension u ∘ conj) (openHalfDisk p R))
    (hconf : ∀ z ∈ (openHalfDisk p R : Set ℂ), DiskMapConformalAt g (diskExtension u) z)
    (hconfr : ∀ z ∈ (openHalfDisk p R : Set ℂ), DiskMapConformalAt g (diskExtension u ∘ conj) z)
    (htension : ∀ z ∈ (openHalfDisk p R : Set ℂ), diskMapTension g (diskExtension u) z = 0)
    (htensionr : ∀ z ∈ (openHalfDisk p R : Set ℂ),
      diskMapTension g (diskExtension u ∘ conj) z = 0)
    (hpW : diskExtension u (p : ℂ) ∈ interior W)
    (hfold : inwardConormalWithin g (diskExtension u) (closedHalfDisk p R) (p : ℂ) +
      tangentSpaceCast 𝓘(ℝ, E) ((diskExtension u ∘ conj) (p : ℂ)) (diskExtension u (p : ℂ))
        (inwardConormalWithin g (diskExtension u ∘ conj) (closedHalfDisk p R) (p : ℂ)) ≠ 0) :
    ∃ (v : C(closedDisk, M)) (K : ℝ≥0),
      (∀ z w, riemannianEDistOf g (v z) (v w) ≤ (K : ℝ≥0∞) * edist z w) ∧
      diskTrace v = diskTrace u ∧ Set.range v ⊆ W ∧
      riemannianDiskArea g v < riemannianDiskArea g u := by
  obtain ⟨r, Y, Φ, -, hrR, hY, -, -, hΦ, hΦzero, hvelocity, hfix, hΦW, hneg⟩ :=
    exists_supported_flow_of_nonzero_fold g u hR hU hUr hi hir hUi hUri hconf hconfr htension
      htensionr hpW hfold
  have hopen : Metric.ball (p : ℂ) r ∩ {z : ℂ | 0 < z.im} ⊆ (openHalfDisk p R : Set ℂ) :=
    fun z hz => ⟨hz.2, (Metric.mem_ball.mp hz.1).trans_le hrR⟩
  have hopenClosed : (openHalfDisk p R : Set ℂ) ⊆ closedHalfDisk p R :=
    fun z hz => ⟨(show 0 < z.im from hz.1).le, Metric.ball_subset_closedBall hz.2⟩
  have hnhds (z : ℂ) (hz : z ∈ Metric.ball (p : ℂ) r ∩ {z : ℂ | 0 < z.im}) :
      closedHalfDisk p R ∈ 𝓝 z :=
    Filter.mem_of_superset ((openHalfDisk p R).isOpen.mem_nhds (hopen hz)) hopenClosed
  have hi' : ∀ z ∈ Metric.ball (p : ℂ) r ∩ {z : ℂ | 0 < z.im},
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) z) := by
    intro z hz
    rw [← mfderivWithin_of_mem_nhds (hnhds z hz)]
    exact hi z (mem_of_mem_nhds (hnhds z hz))
  have hir' : ∀ z ∈ Metric.ball (p : ℂ) r ∩ {z : ℂ | 0 < z.im},
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u ∘ conj) z) := by
    intro z hz
    rw [← mfderivWithin_of_mem_nhds (hnhds z hz)]
    exact hir z (mem_of_mem_nhds (hnhds z hz))
  have hpr : ‖(p : ℂ)‖ + r < 1 := by
    have : ‖(p : ℂ)‖ + r ≤ ‖(p : ℂ)‖ + R := by linarith
    linarith
  obtain ⟨v, K, hvLip, hvtrace, hvW, hvarea⟩ :=
    exists_disk_area_lt_of_fold_divergence_neg g u huLip Φ hΦ hΦzero Y hY hvelocity p r hpr
      hfix huW hΦW (hUi.mono hopen) (hUri.mono hopen) hi' hir' hneg
  exact ⟨v, K, hvLip, hvtrace, hvW, hvarea⟩

/-! ## R11 的 smooth lift 步（ADAPTER）：lift 的极小性靠投影回原 target -/

/-- 外审 R11 的「lift 极小性」：`p : M → N` smooth immersion（对 `g.pullback p` 局部等距），
`uLift`、`γLift` 是 `u`、`γ` 的 lift（`p ∘ uLift = u`，`p ∘ γLift = γ`）；原盘 `u` 在 `N` 中面积极小
⇒ `uLift` 对 `g.pullback p` 在 weak-Jordan-trace-`γLift` 的 Lipschitz competitor 类里面积极小。
只是 smooth 面积侧的一步；PL tower 的有限归纳 / 终止在审计表 R11（PARTIAL）。 -/
example
    {F N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ, F) ∞ N]
    {g : SmoothRiemannianMetric 𝓘(ℝ, F) N} {γ : freeLoop N} {u : C(closedDisk, N)}
    (hu : IsMorreyDisk g γ u) (p : M → N) (hp : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ p)
    (himm : ∀ x, Function.Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) p x))
    (uLift : C(closedDisk, M)) (γLift : freeLoop M)
    (hmap : ∀ z, p (uLift z) = u z) (hloop : ∀ θ, p (γLift θ) = γ θ) {C : ℝ≥0}
    (hLift : ∀ z w, riemannianEDistOf (g.pullback p hp himm) (uLift z) (uLift w) ≤
      (C : ℝ≥0∞) * edist z w) :
    ∀ v : C(closedDisk, M), DiskWeakJordanTrace γLift v →
      (∃ L : ℝ≥0, ∀ z w : closedDisk,
        riemannianEDistOf (g.pullback p hp himm) (v z) (v w) ≤ (L : ℝ≥0∞) * edist z w) →
      riemannianDiskArea (g.pullback p hp himm) uLift ≤
        riemannianDiskArea (g.pullback p hp himm) v :=
  fun v hv hvLip =>
    hu.minimizesLipschitz_of_immersion_lift p hp himm uLift γLift hmap hloop hLift v hv hvLip

/-! ## R13（smooth 子情形的 ADAPTER）：配对源盘 + 整边界识别 ⇒ 匹配点不横截 -/

/-- 外审 R13 在 `Ω_i = e_i(closedBall 0 1)`（smooth 闭盘 chart）下的形：`b : ∂Ω₂ → ∂Ω₁` 写成
`f ∘ b = f`，`b (e₂ z) = e₁ z`。结论是 `∂Ω₂` 的匹配点 `w = e₂ p` 处 `df_{b w}` 与 `df_w`
的 `coprod` 不满射（不横截）。**不要求** `Ω₁`、`Ω₂` 内部不交；`e₁ = e₂` 不被排除。
piecewise smooth corners / 只有 bi-Lipschitz 的 `b` 不在此范围（审计表：MISSING）。 -/
example
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {γ : freeLoop M} {u : C(closedDisk, M)}
    (hu : IsMorreyDisk g γ u) {Uext : ℂ → M} (hUext : SmoothDiskExtension (E := E) u Uext)
    (e₁ e₂ : PartialDiffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ ∞)
    (hsrc₁ : Metric.closedBall (0 : ℂ) 1 ⊆ e₁.source)
    (hsrc₂ : Metric.closedBall (0 : ℂ) 1 ⊆ e₂.source)
    (hinside₁ : e₁ '' Metric.closedBall (0 : ℂ) 1 ⊆ Metric.ball (0 : ℂ) 1)
    (hinside₂ : e₂ '' Metric.closedBall (0 : ℂ) 1 ⊆ Metric.ball (0 : ℂ) 1)
    (b : ℂ → ℂ) (hb : ∀ z ∈ Metric.sphere (0 : ℂ) 1, b (e₂ z) = e₁ z)
    (hfb : ∀ w ∈ e₂ '' Metric.sphere (0 : ℂ) 1, diskExtension u (b w) = diskExtension u w)
    (hiU : ∀ z ∈ Metric.ball (0 : ℂ) 1,
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) z))
    (hdim : Module.finrank ℝ E = 3)
    {W : Set M} (huW : Set.range u ⊆ W) (p : ℂ) (hp : ‖p‖ = 1)
    (hpW : diskExtension u (e₁ p) ∈ interior W) :
    ¬ Function.Surjective
      ((show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) (b (e₂ p))).coprod
        (-(show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) (e₂ p)))) := by
  have hpS : p ∈ Metric.sphere (0 : ℂ) 1 := by simpa only [mem_sphere_iff_norm, sub_zero] using hp
  have hboundary : ∀ z ∈ Metric.sphere (0 : ℂ) 1,
      diskExtension u (e₁ z) = diskExtension u (e₂ z) := fun z hz => by
    rw [← hb z hz]
    exact hfb (e₂ z) ⟨z, hz, rfl⟩
  rw [hb p hpS]
  exact hu.not_transverse_of_paired_source_disks hUext e₁ e₂ hsrc₁ hsrc₂ hinside₁ hinside₂
    hboundary hiU hdim huW p hp hpW

/-! ## R15（ADAPTER）：C¹ 极限无 transverse collision，source 缩放不变，接 K13 -/

omit [T3Space M] in
/-- 外审 R15 的核心：`v n` 在 `ball 0 1` 上单射（embedded），在固定 target chart 里 `C¹` 局部一致
收敛到 `v₀`（chart containment、逐点收敛、导数在紧子集上一致收敛都是显式输入）⇒ `v₀`
的任意两个不同的同像内部点处 `(dv₀_x, -dv₀_y)` 不满射。只传递 no-transverse；不声称极限 embedded。 -/
example
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
    {v : ℕ → ℂ → M} {v₀ : ℂ → M}
    (hv : ∀ᶠ n in atTop, MDifferentiableOn 𝓘(ℝ, ℂ) 𝓘(ℝ, F) (v n) (Metric.ball (0 : ℂ) 1))
    (hv₀ : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, F) 1 v₀ (Metric.ball (0 : ℂ) 1))
    (hinj : ∀ᶠ n in atTop, InjOn (v n) (Metric.ball (0 : ℂ) 1))
    (hval : ∀ p : M, ∀ x ∈ Metric.ball (0 : ℂ) 1,
      v₀ x ∈ (extChartAt 𝓘(ℝ, F) p).source →
      Tendsto (fun n => extChartAt 𝓘(ℝ, F) p (v n x)) atTop
        (𝓝 (extChartAt 𝓘(ℝ, F) p (v₀ x))))
    (hchart : ∀ p : M, ∀ K : Set ℂ, IsCompact K →
      K ⊆ Metric.ball (0 : ℂ) 1 ∩ v₀ ⁻¹' (extChartAt 𝓘(ℝ, F) p).source →
      ∀ᶠ n in atTop, MapsTo (v n) K (extChartAt 𝓘(ℝ, F) p).source)
    (hder : ∀ p : M, ∀ K : Set ℂ, IsCompact K →
      K ⊆ Metric.ball (0 : ℂ) 1 ∩ v₀ ⁻¹' (extChartAt 𝓘(ℝ, F) p).source →
      TendstoUniformlyOn
        (fun n x => fderiv ℝ (fun z => extChartAt 𝓘(ℝ, F) p (v n z)) x)
        (fun x => fderiv ℝ (fun z => extChartAt 𝓘(ℝ, F) p (v₀ z)) x) atTop K) :
    ∀ x ∈ Metric.ball (0 : ℂ) 1, ∀ y ∈ Metric.ball (0 : ℂ) 1, x ≠ y → v₀ x = v₀ y →
      ¬ Function.Surjective
        ((show ℂ →L[ℝ] F from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, F) v₀ x).coprod
          (-(show ℂ →L[ℝ] F from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, F) v₀ y))) :=
  fun _ hx _ hy hxy heq =>
    DifferentialGeometry.Topology.Manifold.not_surjective_coprod_mfderiv_of_injective_c1_limit
      Metric.isOpen_ball hv hv₀ hinj hval hchart hder hx hy hxy heq

omit [T3Space M] in
/-- R15 的 source 缩放步骤：`v₀ z = Q (r • z)`（`r ≠ 0`，`Q` 在 `a`、`b` 可微）在 `a/r`、`b/r`
的 `coprod` 不满射 ⇒ `Q` 在 `a`、`b` 的 `coprod` 不满射。tangent-plane transversality 对 source
正缩放不变，这就是把 `q_{r₁}` 的结论传回整个原盘 `q` 的那一步。 -/
example
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [ChartedSpace F M]
    (Q : ℂ → M) (r : ℝ) (hr : r ≠ 0) (a b : ℂ)
    (hQa : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, F) Q a)
    (hQb : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, F) Q b)
    (hnot : ¬ Function.Surjective
      ((show ℂ →L[ℝ] F from
          mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, F) (fun z => Q (r • z)) (r⁻¹ • a)).coprod
        (-(show ℂ →L[ℝ] F from
          mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, F) (fun z => Q (r • z)) (r⁻¹ • b))))) :
    ¬ Function.Surjective
      ((show ℂ →L[ℝ] F from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, F) Q a).coprod
        (-(show ℂ →L[ℝ] F from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, F) Q b))) := by
  intro hsurj
  apply hnot
  let T : ℂ →L[ℝ] ℂ := r • ContinuousLinearMap.id ℝ ℂ
  have hT : ∀ z : ℂ, T z = r • z := fun z => rfl
  have hchain (c : ℂ) (hQc : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, F) Q c) :
      (show ℂ →L[ℝ] F from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, F) (fun z => Q (r • z)) (r⁻¹ • c)) =
        (show ℂ →L[ℝ] F from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, F) Q c).comp T := by
    have hc : r • (r⁻¹ • c) = c := smul_inv_smul₀ hr c
    have hQ' : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, F) Q (T (r⁻¹ • c)) := by
      rw [hT, hc]
      exact hQc
    have hTd : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun z : ℂ => T z) (r⁻¹ • c) :=
      T.differentiableAt.mdifferentiableAt
    have hcomp := mfderiv_comp (r⁻¹ • c) hQ' hTd
    have hTfd : mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun z : ℂ => T z) (r⁻¹ • c) = T := by
      rw [mfderiv_eq_fderiv]
      exact T.fderiv
    have hfun : (fun z : ℂ => Q (r • z)) = Q ∘ (fun z : ℂ => T z) := rfl
    have hTc : T (r⁻¹ • c) = c := by rw [hT, hc]
    rw [hfun, hcomp, hTfd, hTc]
    rfl
  have key : ∀ A B : ℂ →L[ℝ] F, Function.Surjective (A.coprod (-B)) →
      Function.Surjective ((A.comp T).coprod (-(B.comp T))) := by
    intro A B h y
    obtain ⟨⟨z₁, z₂⟩, hz⟩ := h y
    refine ⟨⟨r⁻¹ • z₁, r⁻¹ • z₂⟩, ?_⟩
    simp only [ContinuousLinearMap.coprod_apply, ContinuousLinearMap.comp_apply, neg_apply, hT,
      smul_inv_smul₀ hr] at hz ⊢
    exact hz
  rw [hchain a hQa, hchain b hQb]
  exact key _ _ hsurj

/-- R15 的结论（不带 immersion 前提）⇒ K13 `hNoTransverse` 谓词；与闭盘 rank 和 `hseparate` 一起，
K13 给出 `IsEmbedding q`。这就是 R15 之后 `hMY` 余下的装配。 -/
example
    {G : SmoothRiemannianMetric 𝓘(ℝ, E) M}
    {γ : freeLoop M} {q : C(closedDisk, M)}
    (hq : IsMorreyDisk G γ q) (hγ : IsSmoothEmbeddedLoop (E := E) γ)
    (hd3 : Module.finrank ℝ E = 3)
    {Q : ℂ → M} (hQ : SmoothDiskExtension (E := E) q Q)
    (hrank : ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) Q z))
    (hseparate : ∀ z : closedDisk, ‖(z : ℂ)‖ < 1 → ∀ θ : loopCircle, q z ≠ γ θ)
    (hR15 : ∀ x ∈ Metric.ball (0 : ℂ) 1, ∀ y ∈ Metric.ball (0 : ℂ) 1, x ≠ y →
      diskExtension q x = diskExtension q y →
      ¬ Function.Surjective
        ((show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension q) x).coprod
          (-(show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension q) y)))) :
    Topology.IsEmbedding q :=
  hq.isEmbedding_of_no_transverse hγ hd3 hQ hrank hseparate
    (fun x hx y hy hxy heq _ _ => hR15 x hx y hy hxy heq)

end GC.LongTime.CuspP1
