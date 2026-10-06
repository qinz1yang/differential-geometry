import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.ClosedRankHC_KP
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Embeddedness.RegularDisk

/-!
# S-MY-NT G2：`hMY` 的结论 ⇐ 单个 no-transverse 前提 `hNT`

冻结文本见 `docs/geometrization/chapter8/sheet-MY-hNT-20261006.md`。`hMY`
（`design-A08-reduction-20261006.md` §3）的结论 `Function.Injective q ∧ ∃ Q, SmoothDiskExtension q Q ∧
闭盘 rank` 在 `_HC2` clause 上被拆成三块：

* **rank 半边**：`closed_rank_of_HC_clauses_KP`（K16a，`ClosedRankHC_KP.lean`）；
* **`hseparate`**（开盘内部点不碰边界曲线）：`hseparate_of_HC2_MYN`，内部 `ρ < 0` +
  `boundary_zero_of_weak_trace_KP`（边界 `ρ = 0`），约 10 行；
* **`hNoTransverse`**（= IMS03 的 MY-G，**未证**）：作为唯一显式前提 `hNT` 传入，
  喂给 K13 `IsMorreyDisk.isEmbedding_of_no_transverse`（`Plateau/Embeddedness/RegularDisk.lean:648`）。

本文件不证 `hNT`；`hNT` 的文本是 `hMY` 的前提逐字、只把结论换成 K13 的 no-transverse 谓词
（写在 `diskExtension q` 上，模型 `𝓡 3`）。`hMY_concl_of_hNT_MYN` 的前提只取 `hMY` 前提中
真正被用到的 clause（`hcvx`、`IsSmoothEmbeddedLoop γU`、`IsMorreyDisk G γU q`、内部 `ρ < 0`、
边界 `ρ = 0`）；wrapper（`A08OfHNT_MYN`、`A11OfHNT_MYN`）在 `hMY` 的完整 binder 下调用它。

REGISTRATION：只 import admission-free 模块（不经 skeleton）（`ClosedRankHC_KP` 链 + K13 的 `RegularDisk` 链），可登记。
-/

set_option autoImplicit false
noncomputable section

open Bundle Filter Manifold Set TopologicalSpace
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Geometry.MinimalSurface
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.Endpoint GC.LongTime
open DifferentialGeometry.Geometry.Hyperbolic
open scoped Manifold ContDiff Topology

namespace GC.LongTime.CuspP1

universe u

/-- **`hseparate` on the `_HC2` clauses.**  `q` 带 weak Jordan trace `γ`、边界值落在 `{ρ = 0}`、
内部值落在 `{ρ < 0}` ⇒ 开盘内部点都不落在曲线 `γ` 上。（`boundary_zero_of_weak_trace_KP` 把
`ρ = 0` 从 `q ∘ diskBoundary` 搬到 `γ`；于是 `ρ (q z) < 0 = ρ (γ θ)` 排除 `q z = γ θ`。）
这正是 `IsMorreyDisk.isEmbedding_of_no_transverse` 的 `hseparate` 前提。 -/
theorem hseparate_of_HC2_MYN {M : Type*} [TopologicalSpace M] (ρ : M → ℝ)
    {γ : freeLoop M} {q : C(closedDisk, M)} (htr : DiskWeakJordanTrace γ q)
    (hbd : ∀ θ : loopCircle, ρ (q (diskBoundary θ)) = 0)
    (hneg : ∀ z : closedDisk, ‖(z : ℂ)‖ < 1 → ρ (q z) < 0) :
    ∀ z : closedDisk, ‖(z : ℂ)‖ < 1 → ∀ θ : loopCircle, q z ≠ γ θ := by
  intro z hz θ h
  have h1 : ρ (q z) < 0 := hneg z hz
  rw [h, boundary_zero_of_weak_trace_KP ρ htr hbd θ] at h1
  exact lt_irrefl 0 h1

/-- **`hMY` conclusion ⇐ `hNT`.**  On the clauses of `exists_eventual_confined_morrey_disk_HC2`
(`hcvx`, smooth embedded `γU`, Morrey disk `q`, interior `ρ < 0`, boundary `ρ = 0`), the single
no-transverse premise (K13's `hNoTransverse` for `diskExtension q`, model `𝓡 3`) gives the frozen
`hMY` conclusion: `q` is injective and has a smooth extension `Q` of rank two on the closed disk.
Rank is K16a (`closed_rank_of_HC_clauses_KP`), separation is `hseparate_of_HC2_MYN`, and the
embedding is K13's `IsMorreyDisk.isEmbedding_of_no_transverse`. -/
theorem hMY_concl_of_hNT_MYN
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} (t : ℝ)
    (a : ℝ) (ha : 0 < a)
    (ρ : (postStage F.observation t).Carrier → ℝ) (hρ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ ρ)
    (hcvx : ∀ x, 0 ≤ ρ x → ρ x < a →
      mfderiv (𝓡 3) 𝓘(ℝ) ρ x ≠ 0 ∧
        ∀ v : TangentSpace (𝓡 3) x, v ≠ 0 →
          0 < hessFun (postMetric F.observation t) ρ x v v) :
    let U : Opens (postStage F.observation t).Carrier :=
      ⟨{x | ρ x < a}, isOpen_lt hρ.continuous continuous_const⟩
    let δ : (postStage F.observation t).Carrier → ℝ := fun x => cutoff_P2A a (ρ x)
    let hδ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ δ :=
      (cutoff_smooth_P2A a).contMDiff.comp hρ
    let hU : ∀ x : (postStage F.observation t).Carrier, x ∈ U ↔ 0 < δ x :=
      fun x => (cutoff_pos_iff_P2A ha (ρ x)).symm
    let G := canonicalPositiveDomainMetric_P2A (postMetric F.observation t) hδ U hU
    let ι : C(U, (postStage F.observation t).Carrier) :=
      ⟨Subtype.val, continuous_subtype_val⟩
    ∀ (γU : freeLoop U) (q : C(closedDisk, U)),
      IsSmoothEmbeddedLoop (E := EuclideanSpace ℝ (Fin 3)) γU →
      IsMorreyDisk G γU q →
      (∀ z : closedDisk, ‖(z : ℂ)‖ < 1 → ρ ((ι.comp q) z) < 0) →
      (∀ θ : loopCircle, ρ ((ι.comp q) (diskBoundary θ)) = 0) →
      (∀ x ∈ Metric.ball (0 : ℂ) 1, ∀ y ∈ Metric.ball (0 : ℂ) 1,
        x ≠ y → diskExtension q x = diskExtension q y →
        Function.Injective (mfderiv 𝓘(ℝ, ℂ) (𝓡 3) (diskExtension q) x) →
        Function.Injective (mfderiv 𝓘(ℝ, ℂ) (𝓡 3) (diskExtension q) y) →
        ¬ Function.Surjective
          ((show ℂ →L[ℝ] EuclideanSpace ℝ (Fin 3) from
              mfderiv 𝓘(ℝ, ℂ) (𝓡 3) (diskExtension q) x).coprod
            (-(show ℂ →L[ℝ] EuclideanSpace ℝ (Fin 3) from
              mfderiv 𝓘(ℝ, ℂ) (𝓡 3) (diskExtension q) y)))) →
      Function.Injective q ∧
        ∃ Q : ℂ → U, SmoothDiskExtension (E := EuclideanSpace ℝ (Fin 3)) q Q ∧
          ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
            Function.Injective (mfderiv 𝓘(ℝ, ℂ) (𝓡 3) Q z) := by
  intro U δ hδ hU G ι γU q hsm hMor hneg hbd hNT
  obtain ⟨⟨Q, hQ⟩, hall⟩ := closed_rank_of_HC_clauses_KP t a ha ρ hρ hcvx γU q hsm hMor hbd
  have hrank : ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) (𝓡 3) Q z) := fun z hz => ((hall Q hQ).2 z hz).1
  have hsep := hseparate_of_HC2_MYN (fun x : U => ρ (x : (postStage F.observation t).Carrier))
    hMor.trace hbd hneg
  have hd3 : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := finrank_euclideanSpace_fin
  exact ⟨(hMor.isEmbedding_of_no_transverse hsm hd3 hQ hrank hsep hNT).injective, Q, hQ, hrank⟩

/-- **`hMY ⇒ hNT` 的结论层对应物.**  `q` 单射 ⇒ no-transverse 谓词（开盘内两个不同点 `x ≠ y` 在
`diskExtension q` 下不会有同一个像，所以谓词是空真）。与 `hMY_concl_of_hNT_MYN` 合起来：在
`_HC2` 前提下，`hNT` 与 `hMY` **等价**，`hNT` 没有比 `hMY` 多要求任何东西，只是把 rank 与 separation
从显式义务里拿掉。 -/
theorem noTransverse_of_injective_MYN {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] {q : C(closedDisk, M)} (hq : Function.Injective q) :
    ∀ x ∈ Metric.ball (0 : ℂ) 1, ∀ y ∈ Metric.ball (0 : ℂ) 1,
      x ≠ y → diskExtension q x = diskExtension q y →
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) (𝓡 3) (diskExtension q) x) →
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) (𝓡 3) (diskExtension q) y) →
      ¬ Function.Surjective
        ((show ℂ →L[ℝ] EuclideanSpace ℝ (Fin 3) from
            mfderiv 𝓘(ℝ, ℂ) (𝓡 3) (diskExtension q) x).coprod
          (-(show ℂ →L[ℝ] EuclideanSpace ℝ (Fin 3) from
            mfderiv 𝓘(ℝ, ℂ) (𝓡 3) (diskExtension q) y))) := by
  intro x hx y hy hxy hext
  exfalso
  refine hxy ?_
  have hx' := diskExtension_coe q ⟨x, Metric.ball_subset_closedBall hx⟩
  have hy' := diskExtension_coe q ⟨y, Metric.ball_subset_closedBall hy⟩
  exact congrArg Subtype.val (hq ((hx'.symm.trans hext).trans hy'))

/-- Consumer：`hseparate_of_HC2_MYN` 直接吃 `hMY` 前提里的 clause（`ι.comp q` 形状、`DiskWeakJordanTrace`
来自 `IsMorreyDisk.trace`），无转换。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} (t : ℝ)
    (ρ : (postStage F.observation t).Carrier → ℝ)
    (U : Opens (postStage F.observation t).Carrier) (G : SmoothRiemannianMetric (𝓡 3) U)
    (γU : freeLoop U) (q : C(closedDisk, U)) (hMor : IsMorreyDisk G γU q)
    (hneg : ∀ z : closedDisk, ‖(z : ℂ)‖ < 1 →
      ρ ((({ toFun := Subtype.val, continuous_toFun := continuous_subtype_val } :
        C(U, (postStage F.observation t).Carrier)).comp q) z) < 0)
    (hbd : ∀ θ : loopCircle,
      ρ ((({ toFun := Subtype.val, continuous_toFun := continuous_subtype_val } :
        C(U, (postStage F.observation t).Carrier)).comp q) (diskBoundary θ)) = 0) :
    ∀ z : closedDisk, ‖(z : ℂ)‖ < 1 → ∀ θ : loopCircle, q z ≠ γU θ :=
  hseparate_of_HC2_MYN (fun x : U => ρ (x : (postStage F.observation t).Carrier)) hMor.trace hbd
    hneg

end GC.LongTime.CuspP1
