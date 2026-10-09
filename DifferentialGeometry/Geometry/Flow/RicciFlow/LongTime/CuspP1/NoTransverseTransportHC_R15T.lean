import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.HMYOfHNT_MYN
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.TrimCollarHC_MR1
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.NoTransverseTransportR15T

/-!
# S-MY-R15T consumer：transport adapter（D-R-MY2a-4）在 `_HC2` confined Morrey disk 上

`_HC2` 的 Morrey disk `q : C(closedDisk, U)`（`exists_eventual_confined_morrey_disk_HC2` 的 clause）：

* R1（`trim_collar_of_HC_clauses_MR1`）给 singleton collar `ρ₀ ∈ (0,1)`；
* G1（`noTransverse_of_trimmed_R15T`）：对 `r ∈ (ρ₀, 1)`，trimmed 盘 `affineSubdisk q 0 r` 的 K13
  no-transverse 谓词 ⇒ 原盘 `diskExtension q` 的 K13 谓词（= `hNT` 的结论，sheet-MY-hNT §1）；
* `hNT_concl_of_trimmed_HC2_R15T`：以上两步合成的 `_HC2` 形；
* `hMY_concl_of_trimmed_HC2_R15T`：再接 `hMY_concl_of_hNT_MYN`，得 `hMY` 的结论
  （`Function.Injective q ∧ ∃ Q, SmoothDiskExtension q Q ∧ 闭盘 rank`）；
* `hMY_concl_of_c1_limit_trimmed_HC2_R15T`：把 MY-13（`Topology.Manifold` 版，经 G1c）喂进
  trimmed 前提：`q_r` 的 `diskExtension` 在 `ball 0 1` 上是单射映射列的 chartwise `C¹` 极限 ⇒ `hMY`
  的结论。这是 R8 + R15 到 `hNT`（进而 `hMY`）的终端接口；**不**证 approximants 存在（R8）。

`ρ₀` 在 `∃` 里，`r` 在其后 `∀`：外层只需「`ρ₀ < r < 1` 里任意一个 `r` 的 trimmed 谓词」，与 R15 的
approximants 对每个 `r ∈ (ρ₀, 1)` 独立产生一致。MY-13 同名定理全名引用，不 open `Analysis`。
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

/-- **`hNT` 结论 ⇐ trimmed no-transverse，`_HC2` 形。** R1 的 collar `ρ₀` 之后，对任意
`r ∈ (ρ₀, 1)`：trimmed 盘 `affineSubdisk q 0 r` 上的 K13 谓词 ⇒ 原盘 `diskExtension q` 上逐字的
K13 `hNoTransverse`（`hNT` 的结论，模型 `𝓡 3`）。 -/
theorem hNT_concl_of_trimmed_HC2_R15T
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
      ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ρ₀ < 1 ∧ ∀ r : ℝ, ρ₀ < r → r < 1 →
        (∀ u ∈ Metric.ball (0 : ℂ) 1, ∀ v ∈ Metric.ball (0 : ℂ) 1,
          u ≠ v → diskExtension (affineSubdisk q 0 r) u = diskExtension (affineSubdisk q 0 r) v →
          Function.Injective
            (mfderiv 𝓘(ℝ, ℂ) (𝓡 3) (diskExtension (affineSubdisk q 0 r)) u) →
          Function.Injective
            (mfderiv 𝓘(ℝ, ℂ) (𝓡 3) (diskExtension (affineSubdisk q 0 r)) v) →
          ¬ Function.Surjective
            ((show ℂ →L[ℝ] EuclideanSpace ℝ (Fin 3) from
                mfderiv 𝓘(ℝ, ℂ) (𝓡 3) (diskExtension (affineSubdisk q 0 r)) u).coprod
              (-(show ℂ →L[ℝ] EuclideanSpace ℝ (Fin 3) from
                mfderiv 𝓘(ℝ, ℂ) (𝓡 3) (diskExtension (affineSubdisk q 0 r)) v)))) →
        ∀ x ∈ Metric.ball (0 : ℂ) 1, ∀ y ∈ Metric.ball (0 : ℂ) 1,
          x ≠ y → diskExtension q x = diskExtension q y →
          Function.Injective (mfderiv 𝓘(ℝ, ℂ) (𝓡 3) (diskExtension q) x) →
          Function.Injective (mfderiv 𝓘(ℝ, ℂ) (𝓡 3) (diskExtension q) y) →
          ¬ Function.Surjective
            ((show ℂ →L[ℝ] EuclideanSpace ℝ (Fin 3) from
                mfderiv 𝓘(ℝ, ℂ) (𝓡 3) (diskExtension q) x).coprod
              (-(show ℂ →L[ℝ] EuclideanSpace ℝ (Fin 3) from
                mfderiv 𝓘(ℝ, ℂ) (𝓡 3) (diskExtension q) y))) := by
  intro U δ hδ hU G ι γU q hsm hMor hneg hbd
  obtain ⟨⟨ρ₀, hρ₀, hρ₀1, hcol, -⟩, -⟩ :=
    trim_collar_of_HC_clauses_MR1 t a ha ρ hρ hcvx γU q hsm hMor hbd hneg
  exact ⟨ρ₀, hρ₀, hρ₀1, fun r hr _ htrim =>
    noTransverse_of_trimmed_R15T hcol (hρ₀.trans hr) hr htrim⟩

/-- **`hMY` 结论 ⇐ trimmed no-transverse，`_HC2` 形。** `hNT_concl_of_trimmed_HC2_R15T` 的结论正是
`hMY_concl_of_hNT_MYN` 的 `hNT` 槽，所以 collar `ρ₀` 之后、任意 `r ∈ (ρ₀, 1)`：trimmed 盘的 K13
谓词 ⇒ `Function.Injective q ∧ ∃ Q, SmoothDiskExtension q Q ∧ 闭盘 rank`（`hMY` 的结论）。 -/
theorem hMY_concl_of_trimmed_HC2_R15T
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
      ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ρ₀ < 1 ∧ ∀ r : ℝ, ρ₀ < r → r < 1 →
        (∀ u ∈ Metric.ball (0 : ℂ) 1, ∀ v ∈ Metric.ball (0 : ℂ) 1,
          u ≠ v → diskExtension (affineSubdisk q 0 r) u = diskExtension (affineSubdisk q 0 r) v →
          Function.Injective
            (mfderiv 𝓘(ℝ, ℂ) (𝓡 3) (diskExtension (affineSubdisk q 0 r)) u) →
          Function.Injective
            (mfderiv 𝓘(ℝ, ℂ) (𝓡 3) (diskExtension (affineSubdisk q 0 r)) v) →
          ¬ Function.Surjective
            ((show ℂ →L[ℝ] EuclideanSpace ℝ (Fin 3) from
                mfderiv 𝓘(ℝ, ℂ) (𝓡 3) (diskExtension (affineSubdisk q 0 r)) u).coprod
              (-(show ℂ →L[ℝ] EuclideanSpace ℝ (Fin 3) from
                mfderiv 𝓘(ℝ, ℂ) (𝓡 3) (diskExtension (affineSubdisk q 0 r)) v)))) →
        Function.Injective q ∧
          ∃ Q : ℂ → U, SmoothDiskExtension (E := EuclideanSpace ℝ (Fin 3)) q Q ∧
            ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
              Function.Injective (mfderiv 𝓘(ℝ, ℂ) (𝓡 3) Q z) := by
  intro U δ hδ hU G ι γU q hsm hMor hneg hbd
  obtain ⟨ρ₀, hρ₀, hρ₀1, hr⟩ :=
    hNT_concl_of_trimmed_HC2_R15T t a ha ρ hρ hcvx γU q hsm hMor hneg hbd
  exact ⟨ρ₀, hρ₀, hρ₀1, fun r hr0 hr1 htrim =>
    hMY_concl_of_hNT_MYN t a ha ρ hρ hcvx γU q hsm hMor hneg hbd (hr r hr0 hr1 htrim)⟩

/-- **R8 + R15 → `hMY` 结论的终端接口（`_HC2` 形）。** collar `ρ₀` 之后、任意 `r ∈ (ρ₀, 1)`：若
trimmed 盘 `q_r = affineSubdisk q 0 r` 的 `diskExtension` 在 `ball 0 1` 上是某列 `ball 0 1` 上单射映射
`v n : ℂ → U` 的 chartwise `C¹` 极限（MY-13 `Topology.Manifold` 版的 `hval / hchart / hder`，对每个
target chart `p`），则 `Function.Injective q ∧ ∃ Q, SmoothDiskExtension q Q ∧ 闭盘 rank`。
`SmoothDiskExtension q Q`（给 `dE q_r` 在 `ball 0 1` 上 `C¹`）来自 K16a `closed_rank_of_HC_clauses_KP`。
**不**证 `v n` 的存在（R8）。 -/
theorem hMY_concl_of_c1_limit_trimmed_HC2_R15T
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
      ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ρ₀ < 1 ∧ ∀ r : ℝ, ρ₀ < r → r < 1 →
        ∀ v : ℕ → ℂ → U,
          (∀ᶠ n in atTop,
            MDifferentiableOn 𝓘(ℝ, ℂ) (𝓡 3) (v n) (Metric.ball (0 : ℂ) 1)) →
          (∀ᶠ n in atTop, InjOn (v n) (Metric.ball (0 : ℂ) 1)) →
          (∀ p : U, ∀ x ∈ Metric.ball (0 : ℂ) 1,
            diskExtension (affineSubdisk q 0 r) x ∈ (extChartAt (𝓡 3) p).source →
            Tendsto (fun n => extChartAt (𝓡 3) p (v n x)) atTop
              (𝓝 (extChartAt (𝓡 3) p (diskExtension (affineSubdisk q 0 r) x)))) →
          (∀ p : U, ∀ K : Set ℂ, IsCompact K →
            K ⊆ Metric.ball (0 : ℂ) 1 ∩
              diskExtension (affineSubdisk q 0 r) ⁻¹' (extChartAt (𝓡 3) p).source →
            ∀ᶠ n in atTop, MapsTo (v n) K (extChartAt (𝓡 3) p).source) →
          (∀ p : U, ∀ K : Set ℂ, IsCompact K →
            K ⊆ Metric.ball (0 : ℂ) 1 ∩
              diskExtension (affineSubdisk q 0 r) ⁻¹' (extChartAt (𝓡 3) p).source →
            TendstoUniformlyOn
              (fun n x => fderiv ℝ (fun z => extChartAt (𝓡 3) p (v n z)) x)
              (fun x => fderiv ℝ
                (fun z => extChartAt (𝓡 3) p (diskExtension (affineSubdisk q 0 r) z)) x)
              atTop K) →
          Function.Injective q ∧
            ∃ Q : ℂ → U, SmoothDiskExtension (E := EuclideanSpace ℝ (Fin 3)) q Q ∧
              ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
                Function.Injective (mfderiv 𝓘(ℝ, ℂ) (𝓡 3) Q z) := by
  intro U δ hδ hU G ι γU q hsm hMor hneg hbd
  obtain ⟨⟨ρ₀, hρ₀, hρ₀1, hcol, -⟩, -⟩ :=
    trim_collar_of_HC_clauses_MR1 t a ha ρ hρ hcvx γU q hsm hMor hbd hneg
  obtain ⟨⟨Q, hQ⟩, -⟩ := closed_rank_of_HC_clauses_KP t a ha ρ hρ hcvx γU q hsm hMor hbd
  exact ⟨ρ₀, hρ₀, hρ₀1, fun r hr hr1 v hv hinj hval hchart hder =>
    hMY_concl_of_hNT_MYN t a ha ρ hρ hcvx γU q hsm hMor hneg hbd
      (noTransverse_of_c1_limit_trimmed_R15T hQ hcol (hρ₀.trans hr) hr hr1.le
        hv hinj hval hchart hder)⟩

/-- Consumer（sanity：G1 的空真情形）：trimmed 盘 `q_r` 单射（例如已经嵌入）时，trimmed 谓词由
`noTransverse_of_injective_MYN` 空真成立，于是 G1 给出原盘 `diskExtension q` 上的 `hNT` 结论
（`𝓡 3` 就是 `𝓘(ℝ, EuclideanSpace ℝ (Fin 3))`，与 `hMY_concl_of_hNT_MYN` 的 `hNT` 槽逐字对齐）。 -/
example {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {q : C(closedDisk, M)} {ρ₀ r : ℝ}
    (hcol : ∀ z w : closedDisk, ρ₀ < ‖(z : ℂ)‖ → q z = q w → z = w)
    (hr : 0 < r) (hρr : ρ₀ < r) (hq : Function.Injective (affineSubdisk q 0 r)) :
    ∀ x ∈ Metric.ball (0 : ℂ) 1, ∀ y ∈ Metric.ball (0 : ℂ) 1,
      x ≠ y → diskExtension q x = diskExtension q y →
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) (𝓡 3) (diskExtension q) x) →
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) (𝓡 3) (diskExtension q) y) →
      ¬ Function.Surjective
        ((show ℂ →L[ℝ] EuclideanSpace ℝ (Fin 3) from
            mfderiv 𝓘(ℝ, ℂ) (𝓡 3) (diskExtension q) x).coprod
          (-(show ℂ →L[ℝ] EuclideanSpace ℝ (Fin 3) from
            mfderiv 𝓘(ℝ, ℂ) (𝓡 3) (diskExtension q) y))) :=
  noTransverse_of_trimmed_R15T hcol hr hρr (noTransverse_of_injective_MYN hq)

/-- Consumer（一般版整条链，`E` 一般 `finrank = 3`）：R1 的 collar（`lemma_R1_MR1`）→ G1 transport →
K13 `isEmbedding_of_no_transverse`。给定 Morrey disk 及其 smooth extension、闭盘 rank、`hseparate`：
`∃ ρ₀ ∈ (0,1)`，对 `ρ₀ < r < 1`，trimmed 盘 `q_r` 的 K13 no-transverse 谓词 ⇒ `IsEmbedding q`。 -/
example {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]
    {G : SmoothRiemannianMetric 𝓘(ℝ, E) M} {γ : freeLoop M} {q : C(closedDisk, M)}
    (hq : IsMorreyDisk G γ q) (hγ : IsSmoothEmbeddedLoop (E := E) γ)
    (hd3 : Module.finrank ℝ E = 3) {Q : ℂ → M} (hQ : SmoothDiskExtension (E := E) q Q)
    (hrank : ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) Q z))
    (hseparate : ∀ z : closedDisk, ‖(z : ℂ)‖ < 1 → ∀ θ : loopCircle, q z ≠ γ θ) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ρ₀ < 1 ∧ ∀ r : ℝ, ρ₀ < r → r < 1 →
      (∀ u ∈ Metric.ball (0 : ℂ) 1, ∀ v ∈ Metric.ball (0 : ℂ) 1,
        u ≠ v → diskExtension (affineSubdisk q 0 r) u = diskExtension (affineSubdisk q 0 r) v →
        Function.Injective
          (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension (affineSubdisk q 0 r)) u) →
        Function.Injective
          (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension (affineSubdisk q 0 r)) v) →
        ¬ Function.Surjective
          ((show ℂ →L[ℝ] E from
              mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension (affineSubdisk q 0 r)) u).coprod
            (-(show ℂ →L[ℝ] E from
              mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension (affineSubdisk q 0 r)) v)))) →
      Topology.IsEmbedding q := by
  obtain ⟨ρ₀, hρ₀, hρ₀1, hcol, -⟩ := lemma_R1_MR1 hq hγ hQ hrank hseparate
  exact ⟨ρ₀, hρ₀, hρ₀1, fun r hr hr1 htrim =>
    hq.isEmbedding_of_no_transverse hγ hd3 hQ hrank hseparate
      (noTransverse_of_trimmed_R15T hcol (hρ₀.trans hr) hr htrim)⟩

end GC.LongTime.CuspP1
