import DifferentialGeometry.Geometry.MinimalSurface.Plateau.CollisionEdgeSidesR10
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.R11StepAlignR11PL

/-!
# O-MY-R10PL G3：R10 输出 → R11-step 接口（`_R10`）

联合 producer `relative_regular_nbhd_sector_collar_R10`（prepared + R9 字段 `local_product`、
`ambient_collar`）的输出逐字喂给 S-MY-R11PL 的 `exists_double_cover_of_isRelRegularNbhd_R10_R11PL`：
`IsRelRegularNbhd_R10` 的 ∧-链解包不变；R11PL 原来的显式前提 `hO … hGmaps`（ambient `O ⊇ Nb` 与
strong deformation retraction `G : O → Nb`）现在由 `HasAmbientCollar_R10 Nb` **提供**（同形同序）。
剩下的前提只有 `H₁(N;F₂) ≠ 0` 的 witness `hε`（D-23，R11-step 总装的义务）。同一 witness
`Nb = h(|A|)` 还带 `IsSectorControlledCollapse_R10`（R10.2 / R10.3 用），这里不消费。
-/

set_option autoImplicit false
noncomputable section

open Set Filter Bundle Manifold
open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.Topology.PiecewiseLinear
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.Geometry

universe u

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]

/-- **G3 consumer**：prepared + `local_product` + `ambient_collar` + `H₁(N;F₂) ≠ 0` ⇒ 在含 `h(|A|)` 的开集
`O` 上存在 genuine connected double cover（deck `τ`、纤维 `{x, τ x}`、`p⁻¹(L)` 连通、`f` 的 lift `f'`）。
`IsRelRegularNbhd_R10` 与 `HO` 都来自同一个 R10 witness `Nb = h(|A|)`。 -/
theorem exists_double_cover_of_prepared_R10 [T2Space M] {f : C(closedDisk, M)} {F : ℂ → M}
    {T : _root_.Geometry.SimplicialComplex ℝ ℂ} {α : ℂ → ℂ} {N : ℕ}
    {A : _root_.Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N))}
    {φ : ℂ → EuclideanSpace ℝ (Fin N)} {h : EuclideanSpace ℝ (Fin N) → M}
    (hprep : IsPreparedSheetComplex_FIX (E := E) f F T α N A φ h)
    (hlp : HasLocalProductCollapse_R10 (E := E) f F T α (h '' A.space))
    (hcol : HasAmbientCollar_R10 (h '' A.space))
    (hε : ∀ (N' : ℕ) (Ab : _root_.Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N')))
      (hb : EuclideanSpace ℝ (Fin N') → M), Ab.faces.Finite → ContinuousOn hb Ab.space →
      InjOn hb Ab.space → hb '' Ab.space = h '' A.space →
      ∃ ε : SimplicialBoolCocycle Ab, ¬ ε.IsCoboundary) :
    ∃ O : Set M, IsOpen O ∧ h '' A.space ⊆ O ∧
      ∃ (X' : Type u) (_ : TopologicalSpace X') (p : X' → M) (τ : X' → X')
        (f' : C(closedDisk, X')),
        T2Space X' ∧ Continuous p ∧ range p = O ∧ IsCoveringMapOn p O ∧ ConnectedSpace X' ∧
        IsConnected O ∧ Continuous τ ∧ (∀ x, p (τ x) = p x) ∧ (∀ x, τ (τ x) = x) ∧
        (∀ x, τ x ≠ x) ∧ (∀ x y, p x = p y → y = x ∨ y = τ x) ∧
        IsConnected (p ⁻¹' range f) ∧ (∀ z, p (f' z) = f z) := by
  obtain ⟨Nb, R, hN, -, ⟨O, G, hO, hNO, hGc, hG0, hG1, hGfix, hGm⟩, rfl⟩ :=
    relative_regular_nbhd_sector_collar_R10 hprep hlp hcol
  exact ⟨O, hO, hNO,
    exists_double_cover_of_isRelRegularNbhd_R10_R11PL hN hε hO hNO hGc hG0 hG1 hGfix hGm⟩

end DifferentialGeometry.Geometry
