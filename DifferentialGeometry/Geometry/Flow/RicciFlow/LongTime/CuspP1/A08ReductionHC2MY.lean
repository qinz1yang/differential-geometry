import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.P2AdapterImportedMorreyHC2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.A08ReductionCoreMY
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.CanonicalMetricAgreeMY
import DifferentialGeometry.Geometry.MinimalSurface.FixedBoundary.SpanningDiskRegularity

/-!
# O-A08 G3′：A08 `exists_attained_leastExteriorDiskArea` 的 reduction theorem（前提 = `hMY`）

结论与 A08（`CuspExteriorProducers.lean:34`）**逐字相同**；唯一的几何前提是冻结的 `hMY`
（`docs/geometrization/chapter8/design-A08-reduction-20261006.md` §3，S-A11-ROUTEB 用同一文本）。
A08 原签名里的 `hK`、`δ`、`hadm`、`hdec` 在本归约中不需要（`_HC2` 不用 flow admissibility），按
COMMON 的 "无未用假设" 规则省略；文末 `example` 证明 A08 的完整签名形状由本定理直接得到。

证明：`exists_eventual_confined_morrey_disk_HC2`（S-MIRRORS G4，sorry-free；Top 版，经
`prescribedCuspMeridian_toTop_CPQ`）给出每个
`t ≥ T ≥ T₀` 的 confined Morrey disk；`hMY` 给单射 + 闭盘 rank；G0′ 给 `G = g.restrictOpen U` on region；
`M.spans` 给 `range γ ⊆ frontier W` 与（经 IMS03 K3）`IsSmoothEmbeddedLoop γ`；G3′ core
`exists_attaining_exteriorDisk_of_open_target_MY` 给 attainer 与正性；`exteriorDiskArea_eq` 收尾。

REGISTRATION：只 import sorry-free 模块（`_HC2` 链、G0′、G3′ core、IMS03 K1/K2/K3 拷贝）⇒ 可登记。
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

/-- **G3′.**  A08 的结论（逐字），唯一几何前提为冻结的 `hMY`。 -/
theorem exists_attained_leastExteriorDiskArea_of_hMY_MY
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {K : ℕ}
    {cores : PersistentHyperbolicCores F (K + 4)} (M : PrescribedCuspMeridian cores)
    (hMY : ∀ (t : ℝ) (ht : M.exterior.start ≤ t) (a : ℝ) (ha : 0 < a)
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
    ∃ T₀ : ℝ, ∃ h₀ : M.exterior.start ≤ T₀, ∀ T : ℝ, ∀ h : T₀ ≤ T,
      hasExteriorDiskMinimizersAfter F.observation M.exterior.region T
        (M.loopAfter T (h₀.trans h)) ∧
      ∀ t ∈ Ici T, 0 < exteriorDiskArea F.observation M.exterior.region T
        (M.loopAfter T (h₀.trans h)) t := by
  obtain ⟨a, ha, T₀, h₀, -, -, hHC⟩ :=
    (prescribedCuspMeridian_toTop_CPQ M).exists_eventual_confined_morrey_disk_HC2 0
  refine ⟨T₀, h₀, fun T h => ?_⟩
  have key : ∀ (t : ℝ) (ht : T ≤ t), ∃ e : C(closedDisk, (postStage F.observation t).Carrier),
      isExteriorSpanningDisk (M.exterior.region t) (M.loopAfter T (h₀.trans h) t ht) e ∧
      riemannianDiskArea (postMetric F.observation t) e =
        leastExteriorDiskArea (postMetric F.observation t) (M.exterior.region t)
          (M.loopAfter T (h₀.trans h) t ht) ∧
      0 < leastExteriorDiskArea (postMetric F.observation t) (M.exterior.region t)
          (M.loopAfter T (h₀.trans h) t ht) := by
    intro t ht
    obtain ⟨ρ, hρ, hreg, hcpt, hcvx, γU, q, hγ, hsm, hMor, hrange, hint, hneg, hbd, hweak,
      hloc⟩ := hHC T h t ht
    obtain ⟨hinj, Q, hQ, hrank⟩ := hMY t ((h₀.trans h).trans ht) a ha ρ hρ hreg hcpt hcvx γU q
      hγ hsm hMor hrange hint hneg hbd hweak hloc
    obtain ⟨u₀, hu₀⟩ := M.spans t ((h₀.trans h).trans ht)
    have hreg' : M.exterior.region t = {x | ρ x ≤ 0} := hreg
    have hWU : M.exterior.region t ⊆ {x | ρ x < a} := by
      intro x hx
      rw [hreg'] at hx
      change ρ x < a
      change ρ x ≤ 0 at hx
      linarith
    have hmetric := canonicalPositiveDomainMetric_inner_eq_of_nonpos_MY
      (postMetric F.observation t) ha hρ
    exact exists_attaining_exteriorDisk_of_open_target_MY (postMetric F.observation t) _ _ hWU
      (fun x hx => hmetric x (by rw [hreg'] at hx; exact hx)) hγ hsm
      hu₀.isSmoothEmbeddedLoop hu₀.2.1 hMor hrange hint hweak hinj hQ hrank
  refine ⟨fun t ht => ?_, fun t ht => ?_⟩
  · obtain ⟨e, he, harea, -⟩ := key t ht
    exact ⟨e, he, harea.trans (exteriorDiskArea_eq F.observation M.exterior.region T
      (M.loopAfter T (h₀.trans h)) t ht).symm⟩
  · obtain ⟨e, -, -, hpos⟩ := key t ht
    rw [exteriorDiskArea_eq F.observation M.exterior.region T (M.loopAfter T (h₀.trans h)) t ht]
    exact hpos

/-- **Consumer**（A08 签名对齐）：A08 的完整 binder（含本归约不需要的 `hK δ hadm hdec`）加冻结 `hMY`
⇒ A08 的结论，逐字由 `exists_attained_leastExteriorDiskArea_of_hMY_MY` 给出。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    (K : ℕ) (_hK : lateDerivativeOrder ≤ K) (δ : ℝ → ℝ) (_hadm : hasAnalyticAdmissibility F δ)
    (_hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    {cores : PersistentHyperbolicCores F (K + 4)} (M : PrescribedCuspMeridian cores)
    (hMY : ∀ (t : ℝ) (ht : M.exterior.start ≤ t) (a : ℝ) (ha : 0 < a)
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
    ∃ T₀ : ℝ, ∃ h₀ : M.exterior.start ≤ T₀, ∀ T : ℝ, ∀ h : T₀ ≤ T,
      hasExteriorDiskMinimizersAfter F.observation M.exterior.region T
        (M.loopAfter T (h₀.trans h)) ∧
      ∀ t ∈ Ici T, 0 < exteriorDiskArea F.observation M.exterior.region T
        (M.loopAfter T (h₀.trans h)) t :=
  exists_attained_leastExteriorDiskArea_of_hMY_MY M hMY

end GC.LongTime.CuspP1
