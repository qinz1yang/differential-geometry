import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.ExteriorDiskFlow
import DifferentialGeometry.Geometry.MinimalSurface.MorreyLeastAreaSmoothAT

/-!
# S-A08-ATTAIN G2′（Route W）：`morreyAreaS` 的流版本

照 `ExteriorDiskFlow.lean` 的 `exteriorDiskAreaOn` / `exteriorDiskArea` 模式：

* `morreyAreaSOn M g W T γ t`：`t ≥ T` 时是 `morreyLeastAreaS (g t) (W t) (γ t ht)`，否则 `0`；
* `morreyAreaS O W T γ`：在 `postStage O t` / `postMetric O t` 上的版本；
* `_nonneg`、`_eq`（`T ≤ t` 时展开成 `morreyLeastAreaS`）、`_le`（任一类内竞争者 `v`：`A′ ≤ Area v`，
  即下游的 `hA_le`）、以及 open-target consumer `morreyAreaS_eq_area_open_AT`
  （`_HC` 的 Morrey 盘 `ι ∘ q` 的面积就是 `morreyAreaS … t`）。

`W` 取 `M.exterior.region`，`γ` 取 `M.loopAfter T _`（与 `exteriorDiskArea` 同一组参数）。
-/

set_option autoImplicit false
noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff

namespace GC.LongTime

universe u

/-- `t ≥ T` 时是时刻 `t` 的 Morrey 光滑类最小面积，否则 `0`（与 `exteriorDiskAreaOn` 同模式）。 -/
def morreyAreaSOn
    (M : ℝ → Type*) [∀ t, TopologicalSpace (M t)]
    [∀ t, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (M t)]
    [∀ t, IsManifold (𝓡 3) ∞ (M t)]
    (g : ∀ t, SmoothRiemannianMetric (𝓡 3) (M t))
    (W : ∀ t, Set (M t)) (T : ℝ)
    (γ : (t : ℝ) → T ≤ t → freeLoop (M t)) (t : ℝ) : ℝ :=
  if ht : T ≤ t then morreyLeastAreaS (g t) (W t) (γ t ht) else 0

theorem morreyAreaSOn_nonneg
    (M : ℝ → Type*) [∀ t, TopologicalSpace (M t)]
    [∀ t, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (M t)]
    [∀ t, IsManifold (𝓡 3) ∞ (M t)]
    (g : ∀ t, SmoothRiemannianMetric (𝓡 3) (M t))
    (W : ∀ t, Set (M t)) (T : ℝ)
    (γ : (t : ℝ) → T ≤ t → freeLoop (M t)) (t : ℝ) :
    0 ≤ morreyAreaSOn M g W T γ t := by
  unfold morreyAreaSOn
  split
  · exact morreyLeastAreaS_nonneg _ _ _
  · exact le_rfl

theorem morreyAreaSOn_eq
    (M : ℝ → Type*) [∀ t, TopologicalSpace (M t)]
    [∀ t, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (M t)]
    [∀ t, IsManifold (𝓡 3) ∞ (M t)]
    (g : ∀ t, SmoothRiemannianMetric (𝓡 3) (M t))
    (W : ∀ t, Set (M t)) (T : ℝ)
    (γ : (t : ℝ) → T ≤ t → freeLoop (M t)) (t : ℝ) (ht : T ≤ t) :
    morreyAreaSOn M g W T γ t = morreyLeastAreaS (g t) (W t) (γ t ht) := by
  simp [morreyAreaSOn, ht]

/-- 任一类内竞争者 `v`：`morreyAreaSOn … t ≤ Area v`（下游 `hA_le`）。 -/
theorem morreyAreaSOn_le
    (M : ℝ → Type*) [∀ t, TopologicalSpace (M t)]
    [∀ t, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (M t)]
    [∀ t, IsManifold (𝓡 3) ∞ (M t)]
    (g : ∀ t, SmoothRiemannianMetric (𝓡 3) (M t))
    (W : ∀ t, Set (M t)) (T : ℝ)
    (γ : (t : ℝ) → T ≤ t → freeLoop (M t)) (t : ℝ) (ht : T ≤ t)
    {v : C(closedDisk, M t)} (hv : DiskSmoothUpToBoundary (E := EuclideanSpace ℝ (Fin 3)) v)
    (hw : DiskWeakJordanTrace (γ t ht) v) (hW : Set.range v ⊆ W t) :
    morreyAreaSOn M g W T γ t ≤ riemannianDiskArea (g t) v := by
  rw [morreyAreaSOn_eq M g W T γ t ht]
  exact morreyLeastAreaS_le (g t) hv hw hW

variable {P : OrientedThreeStage.{u}} {g : P.Metric}

/-- `postStage` / `postMetric` 上的 Morrey 光滑类最小面积（`exteriorDiskArea` 的 Route W 对应物）。 -/
def morreyAreaS (O : ObservationTower P g)
    (W : (t : ℝ) → Set (postStage O t).Carrier) (T : ℝ)
    (γ : (t : ℝ) → T ≤ t → freeLoop (postStage O t).Carrier) : ℝ → ℝ :=
  morreyAreaSOn (fun t => (postStage O t).Carrier) (postMetric O) W T γ

theorem morreyAreaS_nonneg (O : ObservationTower P g)
    (W : (t : ℝ) → Set (postStage O t).Carrier) (T : ℝ)
    (γ : (t : ℝ) → T ≤ t → freeLoop (postStage O t).Carrier) (t : ℝ) :
    0 ≤ morreyAreaS O W T γ t :=
  morreyAreaSOn_nonneg (fun t => (postStage O t).Carrier) (postMetric O) W T γ t

theorem morreyAreaS_eq (O : ObservationTower P g)
    (W : (t : ℝ) → Set (postStage O t).Carrier) (T : ℝ)
    (γ : (t : ℝ) → T ≤ t → freeLoop (postStage O t).Carrier)
    (t : ℝ) (ht : T ≤ t) :
    morreyAreaS O W T γ t = morreyLeastAreaS (postMetric O t) (W t) (γ t ht) :=
  morreyAreaSOn_eq (fun t => (postStage O t).Carrier) (postMetric O) W T γ t ht

theorem morreyAreaS_le (O : ObservationTower P g)
    (W : (t : ℝ) → Set (postStage O t).Carrier) (T : ℝ)
    (γ : (t : ℝ) → T ≤ t → freeLoop (postStage O t).Carrier) (t : ℝ) (ht : T ≤ t)
    {v : C(closedDisk, (postStage O t).Carrier)}
    (hv : DiskSmoothUpToBoundary (E := EuclideanSpace ℝ (Fin 3)) v)
    (hw : DiskWeakJordanTrace (γ t ht) v) (hW : Set.range v ⊆ W t) :
    morreyAreaS O W T γ t ≤ riemannianDiskArea (postMetric O t) v :=
  morreyAreaSOn_le (fun t => (postStage O t).Carrier) (postMetric O) W T γ t ht hv hw hW

/-- **Consumer（open target）.**  时刻 `t ≥ T`：`U` 上关于 `G` 的 Morrey 盘 `q`
（`G = (postMetric O t).restrictOpen U` 在 `W t` 上，`ι ∘ γU = γ t`，`range (ι ∘ q) ⊆ W t`）
给出 `morreyAreaS O W T γ t = riemannianDiskArea (postMetric O t) (ι ∘ q)`。 -/
theorem morreyAreaS_eq_area_open_AT (O : ObservationTower P g)
    (W : (t : ℝ) → Set (postStage O t).Carrier) (T : ℝ)
    (γ : (t : ℝ) → T ≤ t → freeLoop (postStage O t).Carrier) (t : ℝ) (ht : T ≤ t)
    (U : TopologicalSpace.Opens (postStage O t).Carrier)
    (G : SmoothRiemannianMetric (𝓡 3) U) (hWU : W t ⊆ U)
    (hG : ∀ x : U, (x : (postStage O t).Carrier) ∈ W t →
      G.inner x = ((postMetric O t).restrictOpen U).inner x)
    {γU : freeLoop U} (hγγ : ∀ θ, (γU θ : (postStage O t).Carrier) = γ t ht θ)
    (hγ : IsSmoothEmbeddedLoop (E := EuclideanSpace ℝ (Fin 3)) γU)
    {q : C(closedDisk, U)} (hq : IsMorreyDisk G γU q)
    (hqW : Set.range ((⟨Subtype.val, continuous_subtype_val⟩ :
      C(U, (postStage O t).Carrier)).comp q) ⊆ W t) :
    morreyAreaS O W T γ t = riemannianDiskArea (postMetric O t)
      ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, (postStage O t).Carrier)).comp q) := by
  rw [morreyAreaS_eq O W T γ t ht]
  exact (morreyLeastAreaS_eq_area_open_AT (postMetric O t) U G hWU hG (by simp) hγγ hγ hq
    hqW).symm

end GC.LongTime
