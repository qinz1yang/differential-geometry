import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.A08ReductionHC2MY
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.HMYOfHNT_MYN

/-!
# S-MY-NT G3：A08 ⇐ `hNT`

A08（`LongTime/CuspExteriorProducers.lean:34`，`exists_attained_leastExteriorDiskArea`）的**逐字**结论，
唯一的几何前提是冻结的 `hNT`（`docs/geometrization/chapter8/sheet-MY-hNT-20261006.md` §1）：
前提 = 冻结 `hMY` 的前提逐字，结论换成 K13 的 no-transverse 谓词（`diskExtension q`，模型 `𝓡 3`）。

证明：`hMY_concl_of_hNT_MYN`（G2；rank = K16a、separation = `hseparate_of_HC2_MYN`、
embedding = K13 `IsMorreyDisk.isEmbedding_of_no_transverse`）把 `hNT` 变成 `hMY`，再喂
`exists_attained_leastExteriorDiskArea_of_hMY_MY`（`A08ReductionHC2MY`）。A08 原签名里的
`hK δ hadm hdec` 本归约不需要，照 `A08ReductionHC2MY` 省略（"无未用假设" 规则）；`HNTConsumerMYN`
里的 `example` 用 `type_of%` 把本定理的结论与 A08 的陈述对齐。

这是 conditional theorem，**不经 skeleton admission**。REGISTRATION：只 import admission-free 模块（不经 skeleton），可登记。
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

/-- **A08 ⇐ `hNT`.**  结论与 A08 逐字相同；唯一几何前提 `hNT`（= `hMY` 前提逐字 + K13 的
no-transverse 结论）。证明不用 `hNT` 以外的任何几何义务。 -/
theorem exists_attained_leastExteriorDiskArea_of_hNT_MYN
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {K : ℕ}
    {cores : PersistentHyperbolicCores F (K + 4)} (M : PrescribedCuspMeridian cores)
    (hNT : ∀ (t : ℝ) (ht : M.exterior.start ≤ t) (a : ℝ) (ha : 0 < a)
      (ρ : (postStage F.observation t).Carrier → ℝ) (hρ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ ρ),
      M.exterior.region t = {x | ρ x ≤ 0} →
      IsCompact (closure {x | ρ x < a}) →
      (∀ x, 0 ≤ ρ x → ρ x < a →
        mfderiv (𝓡 3) 𝓘(ℝ) ρ x ≠ 0 ∧
        ∀ v : TangentSpace (𝓡 3) x, v ≠ 0 →
          0 < hessFun (postMetric F.observation t) ρ x v v) →
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
        ι.comp γU = M.transported t ht →
        IsSmoothEmbeddedLoop (E := EuclideanSpace ℝ (Fin 3)) γU →
        IsMorreyDisk G γU q →
        range (ι.comp q) ⊆ M.exterior.region t →
        (∀ z : closedDisk, ‖(z : ℂ)‖ < 1 →
          (ι.comp q) z ∈ interior (M.exterior.region t)) →
        (∀ z : closedDisk, ‖(z : ℂ)‖ < 1 → ρ ((ι.comp q) z) < 0) →
        (∀ θ : loopCircle, ρ ((ι.comp q) (diskBoundary θ)) = 0) →
        DiskWeakJordanTrace (M.transported t ht) (ι.comp q) →
        (∀ z : closedDisk, ∀ᶠ y : U in 𝓝 (q z),
          G.inner y = ((postMetric F.observation t).restrictOpen U).inner y ∧
            barrier_P2A a (ρ (y : (postStage F.observation t).Carrier)) =
              ρ (y : (postStage F.observation t).Carrier)) →
        ∀ x ∈ Metric.ball (0 : ℂ) 1, ∀ y ∈ Metric.ball (0 : ℂ) 1,
          x ≠ y → diskExtension q x = diskExtension q y →
          Function.Injective (mfderiv 𝓘(ℝ, ℂ) (𝓡 3) (diskExtension q) x) →
          Function.Injective (mfderiv 𝓘(ℝ, ℂ) (𝓡 3) (diskExtension q) y) →
          ¬ Function.Surjective
            ((show ℂ →L[ℝ] EuclideanSpace ℝ (Fin 3) from
                mfderiv 𝓘(ℝ, ℂ) (𝓡 3) (diskExtension q) x).coprod
              (-(show ℂ →L[ℝ] EuclideanSpace ℝ (Fin 3) from
                mfderiv 𝓘(ℝ, ℂ) (𝓡 3) (diskExtension q) y)))) :
    ∃ T₀ : ℝ, ∃ h₀ : M.exterior.start ≤ T₀, ∀ T : ℝ, ∀ h : T₀ ≤ T,
      hasExteriorDiskMinimizersAfter F.observation M.exterior.region T
        (M.loopAfter T (h₀.trans h)) ∧
      ∀ t ∈ Ici T, 0 < exteriorDiskArea F.observation M.exterior.region T
        (M.loopAfter T (h₀.trans h)) t := by
  refine exists_attained_leastExteriorDiskArea_of_hMY_MY M ?_
  intro t ht a ha ρ hρ hreg hcpt hcvx U δ hδ hU G ι γU q hγ hsm hMor hrange hint hneg hbd hweak hloc
  exact hMY_concl_of_hNT_MYN t a ha ρ hρ hcvx γU q hsm hMor hneg hbd
    (hNT t ht a ha ρ hρ hreg hcpt hcvx γU q hγ hsm hMor hrange hint hneg hbd hweak hloc)

end GC.LongTime.CuspP1
