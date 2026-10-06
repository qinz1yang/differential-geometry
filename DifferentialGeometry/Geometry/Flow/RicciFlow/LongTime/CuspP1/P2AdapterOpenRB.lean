import DifferentialGeometry.Geometry.MinimalSurface.ExteriorDiskArea
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.ExistenceReduction
import DifferentialGeometry.Topology.Manifold.BoundaryExtrema
import DifferentialGeometry.Topology.Manifold.OpenSubtype

/-!
# S-A11-ROUTEB G1，零件 RB-2 / RB-F：开子集搬运与 frontier

`exists_eventual_confined_morrey_disk_HC` 的 Morrey 盘 `q : C(closedDisk, U)` 住在开子集
`U : Opens X` 里（metric `G` 是 `U` 上的 canonical positive-domain metric），而
`isExteriorSpanningDisk` 是在 ambient `X` 里陈述的。这里是两个与 `hMY` 措辞无关的小引理组：

* RB-2：`Subtype.val` 是开嵌入，故 `U` 里的 `SmoothDiskExtension` / `mfderiv` 单射 / `IsEmbedding`
  逐字搬到 ambient（`ι.comp q`，`ι ∘ Uext`）。
* RB-F：`range γ ⊆ frontier W` 由盘的边界落在 `frontier W` 加上 weak Jordan 迹的 σ 满射推出；
  `frontier {ρ ≤ 0}` 的边界点判据 `frontier_of_profile_RB`（`dρ ≠ 0` 的零点不是局部极大）。

不 import `P2AdapterImported*` 家族（无 sorry 链），可登记。
-/

set_option autoImplicit false
noncomputable section

open Filter Set TopologicalSpace
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry
open scoped Manifold ContDiff Topology

namespace GC.LongTime.CuspP1

variable {X : Type*} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]

/-- `dρ ≠ 0` 的零点在 `{ρ ≤ 0}` 的 frontier 上（无边界流形上局部极大点处 `dρ = 0`）。
与 `P2AdapterImportedTop.frontier_of_profile_P2A` 同一证明，但不依赖 sorry 家族。 -/
theorem frontier_of_profile_RB {ρ : X → ℝ} {x : X} (hx0 : ρ x = 0)
    (hd : mfderiv (𝓡 3) 𝓘(ℝ) ρ x ≠ 0) (hcont : Continuous ρ) :
    x ∈ frontier {y | ρ y ≤ 0} := by
  have hclosed : IsClosed {y | ρ y ≤ 0} := isClosed_le hcont continuous_const
  rw [frontier, hclosed.closure_eq]
  refine ⟨hx0.le, fun hint => ?_⟩
  have hmax : IsLocalMax ρ x := by
    filter_upwards [mem_interior_iff_mem_nhds.mp hint] with y hy
    exact hx0 ▸ hy
  have hb := DifferentialGeometry.Topology.Manifold.isBoundaryPoint_of_isLocalMax_of_mfderiv_ne_zero
    (I := 𝓡 3) hmax hd
  exact ((𝓡 3).isBoundaryPoint_iff_not_isInteriorPoint x).mp hb
    (BoundarylessManifold.isInteriorPoint (I := 𝓡 3) (x := x))

/-- weak Jordan 迹的 σ 满射：盘的边界全在 `frontier W` ⇒ 曲线 `γ` 的像在 `frontier W`。 -/
theorem range_subset_of_weakJordan_boundary_RB {M : Type*} [TopologicalSpace M] {S : Set M}
    {γ : freeLoop M} {u : C(closedDisk, M)} (hu : DiskWeakJordanTrace γ u)
    (hb : ∀ θ : loopCircle, u (diskBoundary θ) ∈ S) : Set.range γ ⊆ S := by
  obtain ⟨σ, hσ, htr⟩ := hu
  rintro _ ⟨θ, rfl⟩
  obtain ⟨θ₀, rfl⟩ := hσ.surjective θ
  have h := congrArg (fun f : freeLoop M => f θ₀) htr
  change u (diskBoundary θ₀) = γ (σ θ₀) at h
  rw [← h]
  exact hb θ₀

section OpenSubset

/-- 开子集里的 `SmoothDiskExtension` 沿包含映射搬到 ambient。 -/
theorem smoothDiskExtension_val_comp_RB (U : Opens X) {q : C(closedDisk, U)} {Uext : ℂ → U}
    (h : SmoothDiskExtension (E := EuclideanSpace ℝ (Fin 3)) q Uext) :
    SmoothDiskExtension (E := EuclideanSpace ℝ (Fin 3))
      ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)).comp q) (fun z => (Uext z : X)) :=
  h.comp ⟨Subtype.val, continuous_subtype_val⟩ contMDiff_subtype_val

/-- 开嵌入保持 `mfderiv` 的单射性。 -/
theorem injective_mfderiv_val_comp_RB (U : Opens X) {Uext : ℂ → U} {z : ℂ}
    (h : Function.Injective (mfderiv 𝓘(ℝ, ℂ) (𝓡 3) Uext z)) :
    Function.Injective (mfderiv 𝓘(ℝ, ℂ) (𝓡 3) (fun y => (Uext y : X)) z) := by
  rw [DifferentialGeometry.mfderiv_subtypeVal_comp (I := 𝓘(ℝ, ℂ)) (J := 𝓡 3) Uext z]
  exact h

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] in
/-- 开嵌入保持嵌入性。 -/
theorem isEmbedding_val_comp_RB (U : Opens X) {q : C(closedDisk, U)}
    (hq : Topology.IsEmbedding q) :
    Topology.IsEmbedding ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)).comp q) :=
  Topology.IsEmbedding.subtypeVal.comp hq

end OpenSubset

end GC.LongTime.CuspP1
