import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Embeddedness.CoincidentGermClosureR3B
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Embeddedness.SheetCoincidenceDiskR3B

/-!
# O-MY-R3B G2：R3b 合同本体 `no_open_sheet_coincidence_R3B`（无 minimality）

rev2 §A-4 / D-R-MY2-4 的 R3b：闭盘 smooth（`SmoothDiskExtension`）+ 闭盘 rank 的 conformal harmonic
盘，边界单射、内部像不碰边界像 ⇒ 不存在两块不交非空开集 `V₁ V₂ ⊆ D°`（`diskExtension f` 在两边
单射）使 `f(V₁) = f(V₂)`。陈述与 scratch `MYD2/R01to05.lean:110` 的 `no_open_sheet_coincidence_MYD2`
逐字一致（文件末 `example` 做型对齐）。

证明链（全部在树里或本车道新文件，**无** `IsMorreyDisk` / `minimizes*`）：
1. `hbdry` + `hsep` ⇒ 每个边界点 fiber 单点（`boundary_fiber_eq_of_bdry_sep_R3B`）；
2. 去 minimizer 的闭性 `confHarm_coincident_germ_pairs_isClosed_R3B`（port 链 4 个文件）；
3. G1 continuation（clopen ⇒ 全或无）+ singleton fiber ⇒ `coincidentGermPairs f = ∅`；
4. G1 的 Baire + invariance-of-domain 种子：`f(V₁) ⊆ f(V₂)` 会给出一对 coincident germ，矛盾。

与 MY-T §2 Lemma 3 的差别：不把 transition `τ` 延拓成全局 conformal/anti-conformal 自映射，也不用
degree；"全体点都有 coincident partner" 直接与边界 singleton fiber 矛盾。缩到 embedded patch 的地方
只用紧集 `K ⊆ V₂`（`K.domRestrict f` 是 closed embedding），不把 `V₂` 上的单射当全局 embedding。
-/

set_option autoImplicit false
noncomputable section

open Set Filter Manifold DifferentialGeometry
open DifferentialGeometry.Geometry DifferentialGeometry.Topology
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

/-- MYD2 形状的 `hbdry` + `hsep` ⇒ 树里 `boundary_fiber_eq` 形状的边界 singleton fiber。 -/
theorem boundary_fiber_eq_of_bdry_sep_R3B {Y : Type*} (f : closedDisk → Y)
    (hbdry : ∀ θ θ' : loopCircle, f (diskBoundary θ) = f (diskBoundary θ') → θ = θ')
    (hsep : ∀ z : closedDisk, ‖(z : ℂ)‖ < 1 → ∀ θ : loopCircle, f z ≠ f (diskBoundary θ)) :
    ∀ (θ : loopCircle) (z : closedDisk), f z = f (diskBoundary θ) → z = diskBoundary θ := by
  intro θ z hz
  by_cases hlt : ‖(z : ℂ)‖ < 1
  · exact absurd hz (hsep z hlt θ)
  · obtain ⟨θ', rfl⟩ := exists_diskBoundary_eq_of_not_mem_ball_R3B z hlt
    rw [hbdry θ' θ hz]

/-- **无 minimality 的 coincident germ pairs 为空**：闭盘 smooth + 闭盘 rank + 开盘 conformal
harmonic + 边界单射 + 内部像不碰边界像 ⇒ `coincidentGermPairs f = ∅`。 -/
theorem coincidentGermPairs_eq_empty_confHarm_R3B [T2Space M]
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} (hdim : Module.finrank ℝ E = 3)
    {f : C(closedDisk, M)} {F : ℂ → M} (hF : SmoothDiskExtension (E := E) f F)
    (hrank : ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F z))
    (hconf : ∀ z ∈ Metric.ball (0 : ℂ) 1, DiskMapConformalAt g (diskExtension f) z)
    (hharm : ∀ z ∈ Metric.ball (0 : ℂ) 1, diskMapTension g (diskExtension f) z = 0)
    (hbdry : ∀ θ θ' : loopCircle, f (diskBoundary θ) = f (diskBoundary θ') → θ = θ')
    (hsep : ∀ z : closedDisk, ‖(z : ℂ)‖ < 1 → ∀ θ : loopCircle, f z ≠ f (diskBoundary θ)) :
    coincidentGermPairs (f : closedDisk → M) = ∅ := by
  have hboundary := boundary_fiber_eq_of_bdry_sep_R3B (f : closedDisk → M) hbdry hsep
  exact coincidentGermPairs_eq_empty_of_isClosed_R3B hF hrank ⟨diskBoundary 0, hboundary 0⟩
    (CuspIncompressibility.ConsumerAudit.confHarm_coincident_germ_pairs_isClosed_R3B
      hdim hF hrank hconf hharm hboundary)

/-- **G2 R3b 合同本体（无 minimality）。** 逐字同 `no_open_sheet_coincidence_MYD2`
（`MYD2/R01to05.lean:110`）。 -/
theorem no_open_sheet_coincidence_R3B [T2Space M]
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} (hdim : Module.finrank ℝ E = 3)
    {f : C(closedDisk, M)} {F : ℂ → M} (hF : SmoothDiskExtension (E := E) f F)
    (hrank : ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F z))
    (hconf : ∀ z ∈ Metric.ball (0 : ℂ) 1, DiskMapConformalAt g (diskExtension f) z)
    (hharm : ∀ z ∈ Metric.ball (0 : ℂ) 1, diskMapTension g (diskExtension f) z = 0)
    (hbdry : ∀ θ θ' : loopCircle, f (diskBoundary θ) = f (diskBoundary θ') → θ = θ')
    (hsep : ∀ z : closedDisk, ‖(z : ℂ)‖ < 1 → ∀ θ : loopCircle, f z ≠ f (diskBoundary θ)) :
    ¬ ∃ V₁ V₂ : Set ℂ, IsOpen V₁ ∧ IsOpen V₂ ∧ V₁.Nonempty ∧ V₂.Nonempty ∧ Disjoint V₁ V₂ ∧
      V₁ ⊆ Metric.ball 0 1 ∧ V₂ ⊆ Metric.ball 0 1 ∧
      InjOn (diskExtension f) V₁ ∧ InjOn (diskExtension f) V₂ ∧
      diskExtension f '' V₁ = diskExtension f '' V₂ :=
  no_open_sheet_coincidence_of_coincidentGermPairs_eq_empty_R3B
    (coincidentGermPairs_eq_empty_confHarm_R3B hdim hF hrank hconf hharm hbdry hsep)

/-- 单向包含版（更强）：`f '' V₁ ⊆ f '' V₂` 也不可能（只要 `V₁` 非空）。 -/
theorem no_open_sheet_inclusion_R3B [T2Space M]
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} (hdim : Module.finrank ℝ E = 3)
    {f : C(closedDisk, M)} {F : ℂ → M} (hF : SmoothDiskExtension (E := E) f F)
    (hrank : ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F z))
    (hconf : ∀ z ∈ Metric.ball (0 : ℂ) 1, DiskMapConformalAt g (diskExtension f) z)
    (hharm : ∀ z ∈ Metric.ball (0 : ℂ) 1, diskMapTension g (diskExtension f) z = 0)
    (hbdry : ∀ θ θ' : loopCircle, f (diskBoundary θ) = f (diskBoundary θ') → θ = θ')
    (hsep : ∀ z : closedDisk, ‖(z : ℂ)‖ < 1 → ∀ θ : loopCircle, f z ≠ f (diskBoundary θ)) :
    ¬ ∃ V₁ V₂ : Set ℂ, IsOpen V₁ ∧ IsOpen V₂ ∧ V₁.Nonempty ∧ Disjoint V₁ V₂ ∧
      V₁ ⊆ Metric.ball 0 1 ∧ V₂ ⊆ Metric.ball 0 1 ∧
      InjOn (diskExtension f) V₁ ∧ InjOn (diskExtension f) V₂ ∧
      diskExtension f '' V₁ ⊆ diskExtension f '' V₂ :=
  no_open_sheet_inclusion_of_coincidentGermPairs_eq_empty_R3B
    (coincidentGermPairs_eq_empty_confHarm_R3B hdim hF hrank hconf hharm hbdry hsep)

/-- 型对齐（consumer）：`no_open_sheet_coincidence_MYD2` 的陈述逐字（`MYD2/R01to05.lean:110`），
由 G2 直接给出。 -/
example [T2Space M]
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} (hdim : Module.finrank ℝ E = 3)
    {f : C(closedDisk, M)} {F : ℂ → M} (hF : SmoothDiskExtension (E := E) f F)
    (hrank : ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) F z))
    (hconf : ∀ z ∈ Metric.ball (0 : ℂ) 1, DiskMapConformalAt g (diskExtension f) z)
    (hharm : ∀ z ∈ Metric.ball (0 : ℂ) 1, diskMapTension g (diskExtension f) z = 0)
    (hbdry : ∀ θ θ' : loopCircle, f (diskBoundary θ) = f (diskBoundary θ') → θ = θ')
    (hsep : ∀ z : closedDisk, ‖(z : ℂ)‖ < 1 → ∀ θ : loopCircle, f z ≠ f (diskBoundary θ)) :
    ¬ ∃ V₁ V₂ : Set ℂ, IsOpen V₁ ∧ IsOpen V₂ ∧ V₁.Nonempty ∧ V₂.Nonempty ∧ Disjoint V₁ V₂ ∧
      V₁ ⊆ Metric.ball 0 1 ∧ V₂ ⊆ Metric.ball 0 1 ∧
      InjOn (diskExtension f) V₁ ∧ InjOn (diskExtension f) V₂ ∧
      diskExtension f '' V₁ = diskExtension f '' V₂ :=
  no_open_sheet_coincidence_R3B hdim hF hrank hconf hharm hbdry hsep

end DifferentialGeometry.Geometry
