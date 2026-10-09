import DifferentialGeometry.Geometry.MinimalSurface.ExteriorDiskAttainAT

/-!
# S-A11-ROUTEB G1，零件 RB-1：弱 Jordan trace + 嵌入 + 光滑延拓 ⇒ `isExteriorSpanningDisk`

S-A08-ATTAIN 的 `isExteriorSpanningDisk_of_morrey_AT` 要求 `IsMorreyDisk g γ u`（ambient 的 `g`）。
`exists_eventual_confined_morrey_disk_HC` 给的盘 `q` 住在开子集 `U` 里、metric 是 `G`，
所以 ambient 盘 `ι ∘ q` 不是 `IsMorreyDisk g`，但 exact trace 只用到 `DiskWeakJordanTrace γ u`
（`IsMorreyDisk.trace`）。这里把 `_AT` 的证明（`exists_exactTrace_reparametrization_AT` 之后的组装）
重写成只要 `DiskWeakJordanTrace` 的版本，不涉及面积。
-/

set_option autoImplicit false
noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology Set
open scoped Manifold ContDiff NNReal

namespace DifferentialGeometry.Geometry.MinimalSurface

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]

/-- 弱 Jordan trace 的嵌入盘（光滑延拓、闭盘上导数单射）经 disk diffeomorphism 重参数化后，
是以 `γ` 为精确迹的 exterior spanning disk。不要求 `IsMorreyDisk`。 -/
theorem exists_isExteriorSpanningDisk_of_weakJordan_RB {W : Set M} {γ : freeLoop M}
    (hγ : IsSmoothEmbeddedLoop (E := EuclideanSpace ℝ (Fin 3)) γ) {u : C(closedDisk, M)}
    (hwj : DiskWeakJordanTrace γ u) (hrange : Set.range u ⊆ W)
    (hint : ∀ z : closedDisk, ‖(z : ℂ)‖ < 1 → u z ∈ interior W)
    (hfront : Set.range γ ⊆ frontier W)
    (hemb : ∃ U : ℂ → M, SmoothDiskExtension (E := EuclideanSpace ℝ (Fin 3)) u U ∧
      Topology.IsEmbedding u ∧ ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
        Function.Injective (mfderiv 𝓘(ℝ, ℂ) (𝓡 3) U z)) :
    ∃ u' : C(closedDisk, M), isExteriorSpanningDisk W γ u' := by
  obtain ⟨U, hU, hemb', hinj⟩ := hemb
  obtain ⟨σ, ψc, φ, Φ, htrace, hσψ, hΦφ, hbd, -, -⟩ :=
    exists_exactTrace_reparametrization_AT hγ hwj hU hemb' hinj
  have hE : isExteriorSpanningDisk W (γ.comp σ) u :=
    ⟨htrace, fun _ ⟨θ, hθ⟩ => hfront ⟨σ θ, hθ⟩, hemb', hrange, hint, U, hU, hinj⟩
  have hE' := hE.comp_smooth_disk_reparametrization φ ψc Φ hΦφ hbd
  have hγeq : (γ.comp σ).comp ⟨ψc, ψc.continuous⟩ = γ := by
    ext θ
    exact congrArg γ (hσψ θ)
  rw [hγeq] at hE'
  exact ⟨u.comp ⟨φ, φ.continuous⟩, hE'⟩

end DifferentialGeometry.Geometry.MinimalSurface
