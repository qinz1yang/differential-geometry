import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.P2AdapterImportedMorreyHC
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.P2AdapterCloseRB
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.RestartBridge

/-!
# S-A11-ROUTEB G1：`hP2After` ⇐ `hMY`

`RestartBridge.lean:65` 的 `hP2After`（A11 的剩余义务）由 `exists_eventual_confined_morrey_disk_HC`
的 Morrey 盘与冻结的 `hMY`（`docs/geometrization/chapter8/design-A08-reduction-20261006.md` §3，
逐字；与 A08 共用同一文本）推出。`hMY` 作为显式 ∀-前提（对每个 Top 对象 `M`；A08 里 `M` 是
固定的 binder），不是新具名 Prop。

时间结构：`_HC` 是 "∃ a T₀ h₀, ∀ T ≥ T₀, ∀ t ≥ T"，`hP2After` 是 "∃ T₀ h₀, ∀ t ≥ T₀"：
取 `T := t`（`le_refl`），`M.transported` 的 `exterior.start ≤ t` 证明项各处不同，
proof irrelevance 吸收；不需要 max。

本模块 import `P2AdapterImportedMorreyHC`（经 3 个 sorry mirror）⇒ **NOT registered**；
S-MIRRORS 的 `_HC2` 到后换 import 重交（`_HC2` 陈述逐字相同）。
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

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {K : ℕ}
  {cores : PersistentHyperbolicCores F K}

/-- **G1.**  `hP2After`（`RestartBridge.lean:65`）⇐ `hMY`。 -/
theorem hP2After_of_hMY_RB
    (hMY : ∀ M : PrescribedCuspMeridianTop_CPQ cores,
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
    ∀ M : PrescribedCuspMeridianTop_CPQ cores, ∃ T₀ : ℝ, ∃ h₀ : M.exterior.start ≤ T₀,
      ∀ t : ℝ, ∀ ht : T₀ ≤ t, ∃ u : C(closedDisk, (postStage F.observation t).Carrier),
        isExteriorSpanningDisk (M.exterior.region t) (M.transported t (h₀.trans ht)) u := by
  intro M
  obtain ⟨a, ha, T₀, h₀, -, -, hHC⟩ := M.exists_eventual_confined_morrey_disk_HC 0
  refine ⟨T₀, h₀, fun t ht => ?_⟩
  have hst : M.exterior.start ≤ t := h₀.trans ht
  obtain ⟨ρ, hρ, hreg, hcpt, hcvx, γU, q, hγ, hsm, hMor, hrange, hint, hneg, hbd, hweak, hloc⟩ :=
    hHC t ht t le_rfl
  have hout := hMY M t hst a ha ρ hρ hreg hcpt hcvx γU q hγ hsm hMor hrange hint hneg hbd hweak hloc
  rw [hreg]
  exact exists_exteriorSpanningDisk_of_confined_RB hρ.continuous ha
    (fun x h0 h1 => (hcvx x h0 h1).1)
    (M.transported_isSmoothEmbeddedLoop_P2A t hst) _ hweak (hreg ▸ hrange)
    (hreg ▸ hint) hbd hout

/-- Consumer：`hP2After_of_hMY_RB` 的结论与
`exists_primitive_meridian_of_compressible_seam_via_restart_CPRS`（`RestartBridge.lean:65`）
的 `hP2After` 前提逐字同形，无转换即可喂入。 -/
example {slices : ℕ → RegularSlice F.observation} (hK : lateDerivativeOrder ≤ K) (δ : ℝ → ℝ)
    (hadm : hasAnalyticAdmissibility F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    (L : LateCutFamily F K slices) (j : ℕ) (hj : L.first ≤ j)
    (C : ConnectedComponents (slices j).stage.Carrier)
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
    hcomp (hP2After_of_hMY_RB hMY)

end GC.LongTime.CuspP1
