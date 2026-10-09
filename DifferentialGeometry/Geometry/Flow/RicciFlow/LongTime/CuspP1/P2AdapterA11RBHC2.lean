import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.P2AdapterHP2AfterRBHC2

/-!
# S-A11-ROUTEB G2：A11 ⇐ `hMY`（"第 8 章只剩一个几何义务" 的 conditional witness）

`GC.LongTime.exists_primitive_meridian_of_compressible_seam`（`CuspExteriorProducers.lean:16`，A11）
的**逐字**结论 `Nonempty (PrescribedCuspMeridian L.cores)`，前提 = A11 前提 + 冻结的 `hMY`
（`docs/geometrization/chapter8/design-A08-reduction-20261006.md` §3，与 A08 同一文本；这里对每个
Top 对象 `M : PrescribedCuspMeridianTop_CPQ L.cores` 量化，因为 A11 不给定 `M`，而是由
`exists_primitive_meridian_top_CPA3` 产出）。证明 = `via_restart_CPRS` ∘ G1。

Route W（PLAN §5）下 A11 不再被端点消费；本定理作为 MY 路线的 paper trail：IMS03 交付
`hMY` 的 discharger 后，用它关闭 A11。本文件是 `P2AdapterA11RB` 的 `_HC2` 版（经
`P2AdapterHP2AfterRBHC2`），axioms 标准，**可注册**。
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

/-- **G2.**  A11 的逐字结论，前提 = A11 前提 + `hMY`。 -/
theorem exists_primitive_meridian_of_compressible_seam_of_hMY_HC2_RB
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    (K : ℕ) (hK : lateDerivativeOrder ≤ K) (δ : ℝ → ℝ) (hadm : hasAnalyticAdmissibility F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    {slices : ℕ → RegularSlice F.observation} (L : LateCutFamily F K slices)
    (j : ℕ) (hj : L.first ≤ j) (C : ConnectedComponents (slices j).stage.Carrier)
    (s : Fin (L.decomposition j C).boundary.count) (x : Torus)
    (hcomp : ¬ Function.Injective (FundamentalGroup.map
      ((L.decomposition j C).reconstructionAtlas.torusInPrime
        (L.decomposition j C).reconstruction s) x))
    (hMY : ∀ M : PrescribedCuspMeridianTop_CPQ L.cores,
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
        Function.Injective q ∧
          ∃ Q : ℂ → U, SmoothDiskExtension (E := EuclideanSpace ℝ (Fin 3)) q Q ∧
            ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
              Function.Injective (mfderiv 𝓘(ℝ, ℂ) (𝓡 3) Q z)) :
    Nonempty (PrescribedCuspMeridian L.cores) :=
  exists_primitive_meridian_of_compressible_seam_via_restart_CPRS K hK δ hadm hdec L j hj C s x
    hcomp (hP2After_of_hMY_HC2_RB hMY)

/-- Consumer：G2 的 `M : PrescribedCuspMeridian L.cores` 带 `spans`，即对 `t ≥ M.exterior.start` 的
exterior spanning disk；这正是 A08/A10/A14 以 `M.loopAfter` 消费的输入。 -/
example
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    (K : ℕ) (hK : lateDerivativeOrder ≤ K) (δ : ℝ → ℝ) (hadm : hasAnalyticAdmissibility F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    {slices : ℕ → RegularSlice F.observation} (L : LateCutFamily F K slices)
    (j : ℕ) (hj : L.first ≤ j) (C : ConnectedComponents (slices j).stage.Carrier)
    (s : Fin (L.decomposition j C).boundary.count) (x : Torus)
    (hcomp : ¬ Function.Injective (FundamentalGroup.map
      ((L.decomposition j C).reconstructionAtlas.torusInPrime
        (L.decomposition j C).reconstruction s) x))
    (hMY : ∀ M : PrescribedCuspMeridianTop_CPQ L.cores,
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
        Function.Injective q ∧
          ∃ Q : ℂ → U, SmoothDiskExtension (E := EuclideanSpace ℝ (Fin 3)) q Q ∧
            ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
              Function.Injective (mfderiv 𝓘(ℝ, ℂ) (𝓡 3) Q z)) :
    ∃ M : PrescribedCuspMeridian L.cores, ∀ (t : ℝ) (ht : M.exterior.start ≤ t),
      ∃ u : C(closedDisk, (postStage F.observation t).Carrier),
        isExteriorSpanningDisk (M.exterior.region t)
          (M.loopAfter M.exterior.start le_rfl t ht) u := by
  obtain ⟨M⟩ := exists_primitive_meridian_of_compressible_seam_of_hMY_HC2_RB K hK δ hadm hdec L j hj
    C s x hcomp hMY
  exact ⟨M, fun t ht => M.spans t ht⟩

end GC.LongTime.CuspP1
