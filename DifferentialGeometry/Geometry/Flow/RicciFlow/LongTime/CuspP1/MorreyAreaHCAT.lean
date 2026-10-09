import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.P2AdapterImportedDefs
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.MorreyAreaFlowAT

/-!
# S-A08-ATTAIN G1″（`_HC` 形状）：`morreyAreaS` = `_HC` 的 Morrey 盘 `ι ∘ q` 的面积

`exists_eventual_confined_morrey_disk_HC`（及 `_HC2`）解构出的条款逐字作参数（`let U δ hδ hU G ι`
与 `_HC` 结论体相同），结论
`morreyAreaS O W T γ t = riemannianDiskArea (postMetric O t) (ι ∘ q)`。

`G = canonicalPositiveDomainMetric_P2A … = exp (2 · (−log (cutoff_P2A a (ρ x)))) · g|_U`，
而 `cutoff_P2A a r = 1`（`r ≤ 0`），所以在 `W t = {ρ ≤ 0}` 上 `G = (postMetric O t).restrictOpen U`
（`canonicalPositiveDomainMetric_inner_eq_of_nonpos_AT`，与 O-A08 scratch 的 `_MY` 同证明）。
本文件只 import `P2AdapterImportedDefs`（逐字拷贝，已证）与 `MorreyAreaFlowAT`，不 import 任何
`P2AdapterImported{Lemmas,Top,MorreyHC}`（即不经过 3 个镜像）。
-/

set_option autoImplicit false
noncomputable section

open Bundle Manifold Set TopologicalSpace
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.LongTime
open scoped Manifold ContDiff Topology

namespace GC.LongTime.CuspP1

universe u

theorem cutoff_eq_one_of_nonpos_AT {a r : ℝ} (ha : 0 < a) (hr : r ≤ 0) :
    cutoff_P2A a r = 1 := by
  have h : 2 * r / a - 1 ≤ 0 := by
    have : 2 * r / a ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) ha.le
    linarith
  simp only [cutoff_P2A, Real.smoothTransition.zero_of_nonpos h, sub_zero]

section Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

theorem canonicalPositiveDomainMetric_inner_eq_of_nonpos_AT
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {a : ℝ} (ha : 0 < a)
    {ρ : M → ℝ} (hρ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ ρ) :
    let U : Opens M := ⟨{x | ρ x < a}, isOpen_lt hρ.continuous continuous_const⟩
    let δ : M → ℝ := fun x => cutoff_P2A a (ρ x)
    let hδ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ δ := (cutoff_smooth_P2A a).contMDiff.comp hρ
    let hU : ∀ x : M, x ∈ U ↔ 0 < δ x := fun x => (cutoff_pos_iff_P2A ha (ρ x)).symm
    ∀ x : U, ρ (x : M) ≤ 0 →
      (canonicalPositiveDomainMetric_P2A g hδ U hU).inner x = (g.restrictOpen U).inner x := by
  intro U δ hδ hU x hx
  have h1 : δ (x : M) = 1 := cutoff_eq_one_of_nonpos_AT ha hx
  ext v w
  change Real.exp (2 * -Real.log (δ (x : M))) * (g.restrictOpen U).inner x v w = _
  rw [h1, Real.log_one, neg_zero, mul_zero, Real.exp_zero, one_mul]

end Metric

variable {P : OrientedThreeStage.{u}} {g : P.Metric}

/-- **G1″（`_HC` 形状）.**  `_HC` 的 confined Morrey 盘 `q`（`U = {ρ < a}` 上关于
`G = canonicalPositiveDomainMetric_P2A` 的 Morrey 盘，`ι ∘ γU = γ t ht`，`range (ι ∘ q) ⊆ W t`，
`W t = {ρ ≤ 0}`）：`morreyAreaS O W T γ t = riemannianDiskArea (postMetric O t) (ι ∘ q)`。 -/
theorem morreyAreaS_eq_area_HC_AT (O : ObservationTower P g)
    (W : (t : ℝ) → Set (postStage O t).Carrier) (T : ℝ)
    (γ : (t : ℝ) → T ≤ t → freeLoop (postStage O t).Carrier) (t : ℝ) (ht : T ≤ t)
    (a : ℝ) (ha : 0 < a) (ρ : (postStage O t).Carrier → ℝ)
    (hρ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ ρ) (hW : W t = {x | ρ x ≤ 0}) :
    let U : Opens (postStage O t).Carrier :=
      ⟨{x | ρ x < a}, isOpen_lt hρ.continuous continuous_const⟩
    let δ : (postStage O t).Carrier → ℝ := fun x => cutoff_P2A a (ρ x)
    let hδ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ δ :=
      (cutoff_smooth_P2A a).contMDiff.comp hρ
    let hU : ∀ x : (postStage O t).Carrier, x ∈ U ↔ 0 < δ x :=
      fun x => (cutoff_pos_iff_P2A ha (ρ x)).symm
    let G := canonicalPositiveDomainMetric_P2A (postMetric O t) hδ U hU
    let ι : C(U, (postStage O t).Carrier) :=
      ⟨Subtype.val, continuous_subtype_val⟩
    ∀ (γU : freeLoop U) (q : C(closedDisk, U)),
      ι.comp γU = γ t ht →
      IsSmoothEmbeddedLoop (E := EuclideanSpace ℝ (Fin 3)) γU →
      IsMorreyDisk G γU q →
      range (ι.comp q) ⊆ W t →
      morreyAreaS O W T γ t = riemannianDiskArea (postMetric O t) (ι.comp q) := by
  intro U δ hδ hU G ι γU q hγγ hγ hq hqW
  have hWU : W t ⊆ U := by
    intro x hx
    rw [hW] at hx
    exact lt_of_le_of_lt hx ha
  refine morreyAreaS_eq_area_open_AT O W T γ t ht U G hWU ?_
    (fun θ => congrArg (fun f : freeLoop (postStage O t).Carrier => f θ) hγγ) hγ hq hqW
  intro x hx
  rw [hW] at hx
  exact canonicalPositiveDomainMetric_inner_eq_of_nonpos_AT (postMetric O t) ha hρ x hx

/-- Consumer of G1″（`_HC` 形状）：`_HC` 的 Morrey 盘 `ι ∘ q` 在 region 内的光滑竞争者里面积最小
（`morreyAreaS_le` 与上面的等号合并；这是 IMS09′ 里 `Ā ≥ A′` 的单时刻内容）。 -/
theorem area_le_competitor_of_HC_AT (O : ObservationTower P g)
    (W : (t : ℝ) → Set (postStage O t).Carrier) (T : ℝ)
    (γ : (t : ℝ) → T ≤ t → freeLoop (postStage O t).Carrier) (t : ℝ) (ht : T ≤ t)
    (a : ℝ) (ha : 0 < a) (ρ : (postStage O t).Carrier → ℝ)
    (hρ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ ρ) (hW : W t = {x | ρ x ≤ 0}) :
    let U : Opens (postStage O t).Carrier :=
      ⟨{x | ρ x < a}, isOpen_lt hρ.continuous continuous_const⟩
    let δ : (postStage O t).Carrier → ℝ := fun x => cutoff_P2A a (ρ x)
    let hδ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ δ :=
      (cutoff_smooth_P2A a).contMDiff.comp hρ
    let hU : ∀ x : (postStage O t).Carrier, x ∈ U ↔ 0 < δ x :=
      fun x => (cutoff_pos_iff_P2A ha (ρ x)).symm
    let G := canonicalPositiveDomainMetric_P2A (postMetric O t) hδ U hU
    let ι : C(U, (postStage O t).Carrier) :=
      ⟨Subtype.val, continuous_subtype_val⟩
    ∀ (γU : freeLoop U) (q : C(closedDisk, U)),
      ι.comp γU = γ t ht →
      IsSmoothEmbeddedLoop (E := EuclideanSpace ℝ (Fin 3)) γU →
      IsMorreyDisk G γU q →
      range (ι.comp q) ⊆ W t →
      ∀ v : C(closedDisk, (postStage O t).Carrier),
        DiskSmoothUpToBoundary (E := EuclideanSpace ℝ (Fin 3)) v →
        DiskWeakJordanTrace (γ t ht) v → range v ⊆ W t →
        riemannianDiskArea (postMetric O t) (ι.comp q) ≤ riemannianDiskArea (postMetric O t) v := by
  intro U δ hδ hU G ι γU q hγγ hγ hq hqW v hv hw hWv
  rw [← morreyAreaS_eq_area_HC_AT O W T γ t ht a ha ρ hρ hW γU q hγγ hγ hq hqW]
  exact morreyAreaS_le O W T γ t ht hv hw hWv

end GC.LongTime.CuspP1
