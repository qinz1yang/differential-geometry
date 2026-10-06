import DifferentialGeometry.Geometry.MinimalSurface.ExteriorDiskAttainment
import DifferentialGeometry.Geometry.MinimalSurface.ExteriorDiskPhase

/-!
# O-A08 G3′（MY 路线 paper trail）

open target 里 embedded + closed-rank 的 Morrey disk ⇒ exterior 下确界被达到。

冻结 `hMY`（`docs/geometrization/chapter8/design-A08-reduction-20261006.md` §3）的结论是
`Function.Injective q ∧ ∃ Q, SmoothDiskExtension q Q ∧`
`∀ z ∈ closedBall 0 1, Injective (mfderiv Q z)`，
对象是 open target `U` 里的 Morrey disk `q`（度量 `G`）。本文件把它与 `_HC` 的其余条款组装成
ambient `isExteriorSpanningDisk` 的 attainer，且面积 = `leastExteriorDiskArea` > 0：
* `isExteriorSpanningDisk_comp_of_open_target_MY`：`ι ∘ q` 是 trace `γ ∘ σ` 的 exterior spanning disk
  （embedding 由 compact → T2 的单射；smooth extension 沿 `ι`；`mfderiv_subtypeVal_comp` 搬 rank）；
* `exists_attaining_exteriorDisk_of_open_target_MY`：再用 IMS03 K2
  `isExteriorSpanningDisk.exists_exact_trace_of_weakly_monotone_phase`（exact trace、面积不变）与 K1
  `isExteriorSpanningDisk.attains_positive_leastExteriorDiskArea_of_morrey_open`
  （open-target 比较 + 正性）。
只 import sorry-free 模块（S-IMS03-INTAKE G1/G2 的逐字拷贝）。无新结构 / 新 Prop。
-/

set_option autoImplicit false
noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry Set
open DifferentialGeometry.Geometry.MinimalSurface
open scoped Manifold ContDiff

namespace GC.LongTime.CuspP1

variable {X : Type*} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
  [IsManifold (𝓡 3) ∞ X] [T3Space X]

omit [IsManifold (𝓡 3) ∞ X] in
/-- `ι ∘ q`（`ι : U → X` 为包含）在 ambient 里是 weak trace `γ ∘ σ` 的 exterior spanning disk，
只要 `q` 单射且其 smooth extension 在闭盘上导数单射（即冻结 `hMY` 的结论）。 -/
theorem isExteriorSpanningDisk_comp_of_open_target_MY
    {W : Set X} {γ : freeLoop X} (U : TopologicalSpace.Opens X) {q : C(closedDisk, U)}
    {σ : C(loopCircle, loopCircle)}
    (htrace : diskTrace ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)).comp q) = γ.comp σ)
    (hfront : range γ ⊆ frontier W)
    (hrange : range ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)).comp q) ⊆ W)
    (hint : ∀ z : closedDisk, ‖(z : ℂ)‖ < 1 →
      ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)).comp q) z ∈ interior W)
    (hinj : Function.Injective q) {Q : ℂ → U}
    (hQ : SmoothDiskExtension (E := EuclideanSpace ℝ (Fin 3)) q Q)
    (hrank : ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) (𝓡 3) Q z)) :
    isExteriorSpanningDisk W (γ.comp σ)
      ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)).comp q) := by
  refine ⟨htrace, ?_, ?_, hrange, hint, Subtype.val ∘ Q, ?_, ?_⟩
  · rintro _ ⟨θ, rfl⟩
    exact hfront (mem_range_self (σ θ))
  · have hi : Function.Injective ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)).comp q) :=
      Subtype.val_injective.comp hinj
    exact (((⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)).comp q).continuous.isClosedEmbedding
      hi).isEmbedding
  · exact hQ.comp ⟨Subtype.val, continuous_subtype_val⟩ contMDiff_subtype_val
  · intro z hz
    rw [DifferentialGeometry.Topology.mfderiv_subtypeVal_comp (I := 𝓘(ℝ, ℂ)) (J := 𝓡 3) U Q z]
    exact hrank z hz

/-- **G3′ core.**  open target `(U, G)` 的 Morrey disk `q`（`G = g` on `W ⊆ U`），weak trace 在 ambient
`γ = ι ∘ γU` 上，加上冻结 `hMY` 的结论（单射 + 闭盘 rank）⇒ 存在 `W` 的 exterior spanning disk `e`，
`area g e = leastExteriorDiskArea g W γ > 0`。 -/
theorem exists_attaining_exteriorDisk_of_open_target_MY
    (g : SmoothRiemannianMetric (𝓡 3) X) (U : TopologicalSpace.Opens X)
    (G : SmoothRiemannianMetric (𝓡 3) U) {W : Set X} (hWU : W ⊆ (U : Set X))
    (hmetric : ∀ x : U, (x : X) ∈ W → G.inner x = (g.restrictOpen U).inner x)
    {γ : freeLoop X} {γU : freeLoop U} {q : C(closedDisk, U)}
    (hγU : (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)).comp γU = γ)
    (hsm : IsSmoothEmbeddedLoop (E := EuclideanSpace ℝ (Fin 3)) γU)
    (hγ : IsSmoothEmbeddedLoop (E := EuclideanSpace ℝ (Fin 3)) γ)
    (hfront : range γ ⊆ frontier W) (hMor : IsMorreyDisk G γU q)
    (hrange : range ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)).comp q) ⊆ W)
    (hint : ∀ z : closedDisk, ‖(z : ℂ)‖ < 1 →
      ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)).comp q) z ∈ interior W)
    (hweak : DiskWeakJordanTrace γ ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)).comp q))
    (hinj : Function.Injective q) {Q : ℂ → U}
    (hQ : SmoothDiskExtension (E := EuclideanSpace ℝ (Fin 3)) q Q)
    (hrank : ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) (𝓡 3) Q z)) :
    ∃ e : C(closedDisk, X), isExteriorSpanningDisk W γ e ∧
      riemannianDiskArea g e = leastExteriorDiskArea g W γ ∧
      0 < leastExteriorDiskArea g W γ := by
  obtain ⟨σ, hσ, htr⟩ := hweak
  have hu := isExteriorSpanningDisk_comp_of_open_target_MY U htr hfront hrange hint hinj hQ hrank
  obtain ⟨_, _, φ, _, _, _, _, hexact, _, harea⟩ :=
    hu.exists_exact_trace_of_weakly_monotone_phase hγ hσ
  have huW : ∀ z : closedDisk, (q z : X) ∈ W := fun z => hrange (mem_range_self z)
  subst hγU
  exact ⟨_, hexact, isExteriorSpanningDisk.attains_positive_leastExteriorDiskArea_of_morrey_open
    g U G hWU hmetric hMor hsm huW hexact (harea g)⟩

end GC.LongTime.CuspP1
