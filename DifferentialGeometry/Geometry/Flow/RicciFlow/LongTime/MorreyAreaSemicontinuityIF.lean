import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.ExteriorDiskFlow
import DifferentialGeometry.Geometry.MinimalSurface.WeakDiskTransportK8
import DifferentialGeometry.Geometry.MinimalSurface.MorreyLeastAreaSmoothAT

/-!
# IMS08′（Route W）：constrained Morrey 面积的单侧半连续性 ⇐ 显式 transport 数据（O-IFACE G1）

设计见 `docs/geometrization/chapter8/design-IFACE-K-transport-20261006.md` §A（rev2：光滑类 + region）。
竞争类（与 `morreyLeastAreaS` 逐字一致）：`DiskSmoothUpToBoundary v ∧ DiskWeakJordanTrace (γ t) v ∧
range v ⊆ W t`。对一般函数 `A : ℝ → ℝ` 只用下确界性质 `hA_le`（`A t ≤` 每个竞争者的面积）。

* `le_mul_of_smoothTransport_IF`（单对 kernel）：时刻 `s` 的竞争者 `v`（`area v ≤ A s`）落在开集 `K`
  里，`φ : M s → M t` 满足 TPW（`K` 上 `C^∞`、`MapsTo φ (K ∩ W s) (W t)`、`φ ∘ γ_s = γ_t`、
  `φ^* g_t ≤ c · g_s` on `K`）⇒ `A t ≤ c * A s`。证明：S-A14-KERNEL 的
  `smoothCompetitor_transport_K8`。
* `left_comparison_of_transport_IF`：HT-L ⇒ 乘法形式的 left lower semicontinuity
  （`s ↑ t₀` 时 `A t₀ ≤ e^ε A s`）；`right_comparison_of_transport_IF`：HT-R ⇒ 乘法形式的
  right upper semicontinuity（`s ↓ t₀` 时 `A s ≤ e^ε A t₀`）。
* Consumer：`morreyAreaS_left_comparison_IF`，`A` 取 `morreyLeastAreaS` 的流版本。

`K` 只出现在 transport 数据里：surgery 时刻的左侧取 survivor domain 的开集，其余取 `univ`。
不引入新结构 / 新 Prop。
-/

set_option autoImplicit false
noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology Set
open scoped Manifold ContDiff

namespace GC.LongTime

universe u

section Transport

variable {P : OrientedThreeStage.{u}} {g : P.Metric} (O : ObservationTower P g)
  (W : (t : ℝ) → Set (postStage O t).Carrier) (T : ℝ)
  (γ : (t : ℝ) → T ≤ t → freeLoop (postStage O t).Carrier) (A : ℝ → ℝ)

/-- 单对 kernel：时刻 `s` 的一个竞争者（面积 `≤ A s`、range 在开集 `K` 里）沿 `K` 上的
transport `φ` 送到时刻 `t`，得到 `A t ≤ c * A s`。 -/
theorem le_mul_of_smoothTransport_IF {s t : ℝ} (hs : T ≤ s) (ht : T ≤ t)
    (hA_le : ∀ v : C(closedDisk, (postStage O t).Carrier),
      DiskSmoothUpToBoundary (E := EuclideanSpace ℝ (Fin 3)) v →
      DiskWeakJordanTrace (γ t ht) v → range v ⊆ W t →
      A t ≤ riemannianDiskArea (postMetric O t) v)
    {c : ℝ} (hc : 0 < c) (v : C(closedDisk, (postStage O s).Carrier))
    (hvs : DiskSmoothUpToBoundary (E := EuclideanSpace ℝ (Fin 3)) v)
    (hv : DiskWeakJordanTrace (γ s hs) v) (hvW : range v ⊆ W s)
    (hvA : riemannianDiskArea (postMetric O s) v ≤ A s)
    {K : Set (postStage O s).Carrier} (φ : (postStage O s).Carrier → (postStage O t).Carrier)
    (hK : IsOpen K) (hvK : range v ⊆ K) (hφ : ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ K)
    (hW : MapsTo φ (K ∩ W s) (W t)) (hγ : ∀ θ, φ (γ s hs θ) = γ t ht θ)
    (hmetric : ∀ p ∈ K, ∀ w : TangentSpace (𝓡 3) p,
      (postMetric O t).inner (φ p) (mfderiv (𝓡 3) (𝓡 3) φ p w) (mfderiv (𝓡 3) (𝓡 3) φ p w) ≤
        c * (postMetric O s).inner p w w) :
    A t ≤ c * A s := by
  obtain ⟨w, _, ⟨hws, hwt, hwW⟩, harea⟩ := smoothCompetitor_transport_K8
    (postMetric O s) (postMetric O t) hc hK hφ hW hγ hmetric hvs hv hvW hvK
  calc A t ≤ riemannianDiskArea (postMetric O t) w := hA_le w hws hwt hwW
    _ ≤ c * riemannianDiskArea (postMetric O s) v := harea
    _ ≤ c * A s := mul_le_mul_of_nonneg_left hvA hc.le

/-- HT-L ⇒ left lower semicontinuity（乘法形式）：`s ↑ t₀` 时 `A t₀ ≤ e^ε A s`。
这是唯一需要 `K ≠ univ` 的 transport（surgery 时刻的 pre-surgery 一侧）。 -/
theorem left_comparison_of_transport_IF
    (hA_le : ∀ (t : ℝ) (ht : T ≤ t) (v : C(closedDisk, (postStage O t).Carrier)),
      DiskSmoothUpToBoundary (E := EuclideanSpace ℝ (Fin 3)) v →
      DiskWeakJordanTrace (γ t ht) v → range v ⊆ W t →
      A t ≤ riemannianDiskArea (postMetric O t) v)
    (hL : ∀ (t₀ : ℝ) (ht₀ : T ≤ t₀), ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ),
      ∀ (s : ℝ) (hs : T ≤ s), t₀ - δ < s → s < t₀ →
        ∃ (v : C(closedDisk, (postStage O s).Carrier)) (K : Set (postStage O s).Carrier)
          (φ : (postStage O s).Carrier → (postStage O t₀).Carrier),
          DiskSmoothUpToBoundary (E := EuclideanSpace ℝ (Fin 3)) v ∧
          DiskWeakJordanTrace (γ s hs) v ∧ range v ⊆ W s ∧
          riemannianDiskArea (postMetric O s) v ≤ A s ∧ range v ⊆ K ∧
          IsOpen K ∧ ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ K ∧ MapsTo φ (K ∩ W s) (W t₀) ∧
          (∀ θ, φ (γ s hs θ) = γ t₀ ht₀ θ) ∧
          ∀ p ∈ K, ∀ w : TangentSpace (𝓡 3) p,
            (postMetric O t₀).inner (φ p) (mfderiv (𝓡 3) (𝓡 3) φ p w)
                (mfderiv (𝓡 3) (𝓡 3) φ p w) ≤
              Real.exp ε * (postMetric O s).inner p w w) :
    ∀ t₀ ∈ Ici T, ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ),
      ∀ s ∈ Ici T, t₀ - δ < s → s < t₀ → A t₀ ≤ Real.exp ε * A s := by
  intro t₀ ht₀ ε hε
  obtain ⟨δ, hδ, hd⟩ := hL t₀ ht₀ ε hε
  refine ⟨δ, hδ, fun s hs hlo hhi => ?_⟩
  obtain ⟨v, K, φ, hvs, hv, hvW, hvA, hvK, hK, hφ, hW, hγ, hmetric⟩ := hd s hs hlo hhi
  exact le_mul_of_smoothTransport_IF O W T γ A hs ht₀ (hA_le t₀ ht₀) (Real.exp_pos ε)
    v hvs hv hvW hvA φ hK hvK hφ hW hγ hmetric

/-- HT-R ⇒ right upper semicontinuity（乘法形式）：`s ↓ t₀` 时 `A s ≤ e^ε A t₀`。
在 HG14 off-countable 变体里只在 event 时刻用；post-surgery stage 上 `K = univ` 可取。 -/
theorem right_comparison_of_transport_IF
    (hA_le : ∀ (t : ℝ) (ht : T ≤ t) (v : C(closedDisk, (postStage O t).Carrier)),
      DiskSmoothUpToBoundary (E := EuclideanSpace ℝ (Fin 3)) v →
      DiskWeakJordanTrace (γ t ht) v → range v ⊆ W t →
      A t ≤ riemannianDiskArea (postMetric O t) v)
    (hR : ∀ (t₀ : ℝ) (ht₀ : T ≤ t₀), ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ),
      ∀ (s : ℝ) (hs : T ≤ s), t₀ < s → s < t₀ + δ →
        ∃ (v : C(closedDisk, (postStage O t₀).Carrier)) (K : Set (postStage O t₀).Carrier)
          (φ : (postStage O t₀).Carrier → (postStage O s).Carrier),
          DiskSmoothUpToBoundary (E := EuclideanSpace ℝ (Fin 3)) v ∧
          DiskWeakJordanTrace (γ t₀ ht₀) v ∧ range v ⊆ W t₀ ∧
          riemannianDiskArea (postMetric O t₀) v ≤ A t₀ ∧ range v ⊆ K ∧
          IsOpen K ∧ ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ K ∧ MapsTo φ (K ∩ W t₀) (W s) ∧
          (∀ θ, φ (γ t₀ ht₀ θ) = γ s hs θ) ∧
          ∀ p ∈ K, ∀ w : TangentSpace (𝓡 3) p,
            (postMetric O s).inner (φ p) (mfderiv (𝓡 3) (𝓡 3) φ p w)
                (mfderiv (𝓡 3) (𝓡 3) φ p w) ≤
              Real.exp ε * (postMetric O t₀).inner p w w) :
    ∀ t₀ ∈ Ici T, ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ),
      ∀ s, t₀ < s → s < t₀ + δ → A s ≤ Real.exp ε * A t₀ := by
  intro t₀ ht₀ ε hε
  obtain ⟨δ, hδ, hd⟩ := hR t₀ ht₀ ε hε
  refine ⟨δ, hδ, fun s hlo hhi => ?_⟩
  have hs : T ≤ s := le_trans ht₀ hlo.le
  obtain ⟨v, K, φ, hvs, hv, hvW, hvA, hvK, hK, hφ, hW, hγ, hmetric⟩ := hd s hs hlo hhi
  exact le_mul_of_smoothTransport_IF O W T γ A ht₀ hs (hA_le s hs) (Real.exp_pos ε)
    v hvs hv hvW hvA φ hK hvK hφ hW hγ hmetric

end Transport

section Consumer

variable {P : OrientedThreeStage.{u}} {g : P.Metric} (O : ObservationTower P g)
  (W : (t : ℝ) → Set (postStage O t).Carrier) (T : ℝ)
  (γ : (t : ℝ) → T ≤ t → freeLoop (postStage O t).Carrier)

/-- Consumer：`A` 取 `morreyLeastAreaS` 的流版本（`t < T` 时取 `0`），下确界性质由
`morreyLeastAreaS_le` 给出；HT-L（竞争者面积 `≤ morreyLeastAreaS`）⇒ left lower
semicontinuity of `morreyLeastAreaS`。 -/
theorem morreyAreaS_left_comparison_IF
    (hL : ∀ (t₀ : ℝ) (ht₀ : T ≤ t₀), ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ),
      ∀ (s : ℝ) (hs : T ≤ s), t₀ - δ < s → s < t₀ →
        ∃ (v : C(closedDisk, (postStage O s).Carrier)) (K : Set (postStage O s).Carrier)
          (φ : (postStage O s).Carrier → (postStage O t₀).Carrier),
          DiskSmoothUpToBoundary (E := EuclideanSpace ℝ (Fin 3)) v ∧
          DiskWeakJordanTrace (γ s hs) v ∧ range v ⊆ W s ∧
          riemannianDiskArea (postMetric O s) v ≤
            morreyLeastAreaS (postMetric O s) (W s) (γ s hs) ∧ range v ⊆ K ∧
          IsOpen K ∧ ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ K ∧ MapsTo φ (K ∩ W s) (W t₀) ∧
          (∀ θ, φ (γ s hs θ) = γ t₀ ht₀ θ) ∧
          ∀ p ∈ K, ∀ w : TangentSpace (𝓡 3) p,
            (postMetric O t₀).inner (φ p) (mfderiv (𝓡 3) (𝓡 3) φ p w)
                (mfderiv (𝓡 3) (𝓡 3) φ p w) ≤
              Real.exp ε * (postMetric O s).inner p w w) :
    ∀ t₀ (ht₀ : T ≤ t₀), ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ),
      ∀ (s : ℝ) (hs : T ≤ s), t₀ - δ < s → s < t₀ →
        morreyLeastAreaS (postMetric O t₀) (W t₀) (γ t₀ ht₀) ≤
          Real.exp ε * morreyLeastAreaS (postMetric O s) (W s) (γ s hs) := by
  let A : ℝ → ℝ := fun t =>
    if ht : T ≤ t then morreyLeastAreaS (postMetric O t) (W t) (γ t ht) else 0
  have hA (t : ℝ) (ht : T ≤ t) : A t = morreyLeastAreaS (postMetric O t) (W t) (γ t ht) :=
    dite_eq_left ht
  have hA_le : ∀ (t : ℝ) (ht : T ≤ t) (v : C(closedDisk, (postStage O t).Carrier)),
      DiskSmoothUpToBoundary (E := EuclideanSpace ℝ (Fin 3)) v →
      DiskWeakJordanTrace (γ t ht) v → range v ⊆ W t →
      A t ≤ riemannianDiskArea (postMetric O t) v := fun t ht v hvs hv hW => by
    rw [hA t ht]
    exact morreyLeastAreaS_le (postMetric O t) hvs hv hW
  intro t₀ ht₀ ε hε
  obtain ⟨δ, hδ, hd⟩ := left_comparison_of_transport_IF O W T γ A hA_le
    (fun t₁ ht₁ ε₁ hε₁ => by
      obtain ⟨δ₁, hδ₁, hd₁⟩ := hL t₁ ht₁ ε₁ hε₁
      refine ⟨δ₁, hδ₁, fun s hs hlo hhi => ?_⟩
      obtain ⟨v, K, φ, hvs, hv, hvW, hvA, hrest⟩ := hd₁ s hs hlo hhi
      exact ⟨v, K, φ, hvs, hv, hvW, (hA s hs).symm ▸ hvA, hrest⟩)
    t₀ ht₀ ε hε
  refine ⟨δ, hδ, fun s hs hlo hhi => ?_⟩
  have h := hd s hs hlo hhi
  rwa [hA t₀ ht₀, hA s hs] at h

end Consumer

end GC.LongTime
