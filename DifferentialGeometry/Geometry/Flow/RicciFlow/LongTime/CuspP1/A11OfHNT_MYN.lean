import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.P2AdapterA11RBHC2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.HMYOfHNT_MYN

/-!
# S-MY-NT G3：A11 ⇐ `hNT`

A11（`LongTime/CuspExteriorProducers.lean:16`，`exists_primitive_meridian_of_compressible_seam`）的
**逐字**结论 `Nonempty (PrescribedCuspMeridian L.cores)`，前提 = A11 前提 + 冻结的 `hNT`
（`docs/geometrization/chapter8/sheet-MY-hNT-20261006.md` §1）。A11 不给定 `M`，而是由
`exists_primitive_meridian_top_CPA3` 产出，所以 `hNT` 对每个 Top 对象
`M : PrescribedCuspMeridianTop_CPQ L.cores` 量化（与
`exists_primitive_meridian_of_compressible_seam_of_hMY_HC2_RB` 里的 `hMY` 同形）。

证明：逐个 `M` 用 `hMY_concl_of_hNT_MYN`（G2）把 `hNT` 变成 `hMY`，再喂
`exists_primitive_meridian_of_compressible_seam_of_hMY_HC2_RB`（`P2AdapterA11RBHC2`）。
`HNTConsumerMYN` 里的 `example` 用 `type_of%` 把本定理的结论与 A11 的陈述对齐。

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

/-- **A11 ⇐ `hNT`.**  结论与 A11 逐字相同；前提 = A11 前提 + `hNT`。 -/
theorem exists_primitive_meridian_of_compressible_seam_of_hNT_MYN
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    (K : ℕ) (hK : lateDerivativeOrder ≤ K) (δ : ℝ → ℝ) (hadm : hasAnalyticAdmissibility F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    {slices : ℕ → RegularSlice F.observation} (L : LateCutFamily F K slices)
    (j : ℕ) (hj : L.first ≤ j) (C : ConnectedComponents (slices j).stage.Carrier)
    (s : Fin (L.decomposition j C).boundary.count) (x : Torus)
    (hcomp : ¬ Function.Injective (FundamentalGroup.map
      ((L.decomposition j C).reconstructionAtlas.torusInPrime
        (L.decomposition j C).reconstruction s) x))
    (hNT : ∀ M : PrescribedCuspMeridianTop_CPQ L.cores,
      ∀ (t : ℝ) (ht : M.exterior.start ≤ t) (a : ℝ) (ha : 0 < a)
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
    Nonempty (PrescribedCuspMeridian L.cores) := by
  refine exists_primitive_meridian_of_compressible_seam_of_hMY_HC2_RB K hK δ hadm hdec L j hj C s x
    hcomp ?_
  intro M t ht a ha ρ hρ hreg hcpt hcvx U δ' hδ hU G ι γU q hγ hsm hMor hrange hint hneg hbd hweak
    hloc
  exact hMY_concl_of_hNT_MYN t a ha ρ hρ hcvx γU q hsm hMor hneg hbd
    (hNT M t ht a ha ρ hρ hreg hcpt hcvx γU q hγ hsm hMor hrange hint hneg hbd hweak hloc)

end GC.LongTime.CuspP1
