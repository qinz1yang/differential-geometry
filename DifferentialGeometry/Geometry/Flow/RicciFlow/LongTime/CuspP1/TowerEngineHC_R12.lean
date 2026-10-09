import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.ClosedRankHC_KP
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.PreparedSheetComplexFlatFIX
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.TowerEngineR12
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.FoldCompetitorR4rR12

/-!
# S-MY-R12 G3：tower 总装 conditional engine 的 consumers（`_HC2` 的 (U, G) 实例 + 平坦盘 n = 0 实例）

G2 `prepared_least_area_embedded_R12`（`Plateau/TowerEngineR12`）的五条 ∀-前提里，R4r 已由 G4
`reparametrized_fold_competitor_R12`（`Plateau/FoldCompetitorR4rR12`）discharge；其余四条（R10.1 / R10.2
producer `hR10` + 投影 `hspine`、10.3/10.4 弱版 producer `hcaps`、R11-step `hR11`、R14 descent `hR14`）
尚无 producer，所以 consumer 里它们仍是**显式 hypothesis**（`variable` + `include`，原样重述一次；
不新建具名 Prop）。这里验证：

* `prepared_least_area_embedded_HC2_R12`：G2 在 `_HC2` 的 (U, G)（`U = {ρ < a}`，`G` = canonical positive
  domain metric；binder 前缀与 `FoldCompetitorSeamHC_R4C` 逐字相同）上的实例：`E = ℝ³ = E3_FIX`，
  `M = ↥U`，所有 `[ChartedSpace]`、`[IsManifold]`、`[T2Space]` 实例在 `↥U` 上解析；
* `flatDisk_injective_of_tower_R12`：对 S-MY-FIX 的 `flatDisk_prepared_FIX`（`E = M = ℝ³`）取
  `n = 0`（归纳起点由 `flatDisk_complexity_zero_FIX`：`|P_T(f, α)| = 0` 给出），得平坦盘单射——空真起点，
  展示 `IsPreparedSheetComplex_FIX` 的输出类型确实被 G2 吃进去（`T = triComplex_FIX`、`α = radialGrid_FIX`、
  `A = bipyramid_FIX`）。`IsMorreyDisk g Γ flatDisk_FIX` 作为 hypothesis（树里没有“平坦盘是 Morrey 盘”）。

`RelNbhd` 是谓词参数 `RelNbhd f F T α Nb R`；O-MY-R10PL 的输出形状
`IsRelRegularNbhd_R10 f Nb R ∧ IsSectorControlledCollapse_R10 F T α Nb R` 实例化它。
-/

set_option autoImplicit false
noncomputable section

open Bundle Filter Manifold Set TopologicalSpace
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry
open DifferentialGeometry.Topology.PiecewiseLinear
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Geometry.MinimalSurface
open DifferentialGeometry.Geometry.ImmersedDiskDivergence.Within
open DifferentialGeometry.Geometry.ImmersedDiskDivergence.HalfDisk
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.Endpoint GC.LongTime
open DifferentialGeometry.Geometry.Hyperbolic
open scoped Manifold ContDiff Topology NNReal ENNReal ComplexConjugate

namespace GC.LongTime.CuspP1

universe u

section FlatDisk

variable (RelNbhd : ∀ {M : Type}
    [TopologicalSpace M] [ChartedSpace E3_FIX M] [IsManifold 𝓘(ℝ, E3_FIX) ∞ M]
    [T2Space M], C(closedDisk, M) → (ℂ → M) → _root_.Geometry.SimplicialComplex ℝ ℂ →
    (ℂ → ℂ) → Set M → (M → M) → Prop)
variable (hspine : ∀ {M : Type}
    [TopologicalSpace M] [ChartedSpace E3_FIX M] [IsManifold 𝓘(ℝ, E3_FIX) ∞ M]
    [T2Space M] {f : C(closedDisk, M)} {F : ℂ → M} {T : _root_.Geometry.SimplicialComplex ℝ ℂ}
    {α : ℂ → ℂ} {Nb : Set M} {R : M → M}, RelNbhd f F T α Nb R → Set.range f ⊆ Nb)
variable (hR10 : ∀ {M : Type}
    [TopologicalSpace M] [ChartedSpace E3_FIX M] [IsManifold 𝓘(ℝ, E3_FIX) ∞ M]
    [T2Space M], Module.finrank ℝ E3_FIX = 3 →
    ∀ {g : SmoothRiemannianMetric 𝓘(ℝ, E3_FIX) M} {Γ : freeLoop M} {f : C(closedDisk, M)},
    IsMorreyDisk g Γ f → ∀ {F : ℂ → M} {T : _root_.Geometry.SimplicialComplex ℝ ℂ} {α : ℂ → ℂ}
    {N : ℕ} {A : _root_.Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N))}
    {φ : ℂ → EuclideanSpace ℝ (Fin N)} {h : EuclideanSpace ℝ (Fin N) → M},
    IsPreparedSheetComplex_FIX (E := E3_FIX) f F T α N A φ h →
    ∃ (Nb : Set M) (R : M → M), RelNbhd f F T α Nb R)
variable (hcaps : ∀ {M : Type}
    [TopologicalSpace M] [ChartedSpace E3_FIX M] [IsManifold 𝓘(ℝ, E3_FIX) ∞ M]
    [T2Space M], Module.finrank ℝ E3_FIX = 3 →
    ∀ {g : SmoothRiemannianMetric 𝓘(ℝ, E3_FIX) M} {Γ : freeLoop M} {f : C(closedDisk, M)},
    IsMorreyDisk g Γ f → ∀ {F : ℂ → M} {T : _root_.Geometry.SimplicialComplex ℝ ℂ} {α : ℂ → ℂ}
    {N : ℕ} {A : _root_.Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N))}
    {φ : ℂ → EuclideanSpace ℝ (Fin N)} {h : EuclideanSpace ℝ (Fin N) → M},
    IsPreparedSheetComplex_FIX (E := E3_FIX) f F T α N A φ h →
    ∀ {Nb : Set M} {R : M → M}, RelNbhd f F T α Nb R →
    Nonempty (connectedComponentIn (frontier Nb) (f (diskBoundary 0)) ≃ₜ sphere2_R12) →
    ∃ ap am : C(closedDisk, M),
      (∃ L : ℝ≥0, ∀ z w : closedDisk,
        riemannianEDistOf g (ap z) (ap w) ≤ (L : ℝ≥0∞) * edist z w) ∧
      (∃ L : ℝ≥0, ∀ z w : closedDisk,
        riemannianEDistOf g (am z) (am w) ≤ (L : ℝ≥0∞) * edist z w) ∧
      DiskWeakJordanTrace Γ ap ∧ DiskWeakJordanTrace Γ am ∧
      riemannianDiskArea g ap + riemannianDiskArea g am ≤ 2 * riemannianDiskArea g f ∧
      ((∃ x y : closedDisk, x ≠ y ∧ f x = f y) →
        riemannianDiskArea g ap + riemannianDiskArea g am < 2 * riemannianDiskArea g f ∨
          HasReparametrizedFold_R12 g ap (diskExtension f) ∨
            HasReparametrizedFold_R12 g am (diskExtension f)))
variable (hR11 : ∀ {M : Type}
    [TopologicalSpace M] [ChartedSpace E3_FIX M] [IsManifold 𝓘(ℝ, E3_FIX) ∞ M]
    [T2Space M], Module.finrank ℝ E3_FIX = 3 →
    ∀ {g : SmoothRiemannianMetric 𝓘(ℝ, E3_FIX) M} {Γ : freeLoop M} {f : C(closedDisk, M)},
    IsMorreyDisk g Γ f → ∀ {F : ℂ → M} {T : _root_.Geometry.SimplicialComplex ℝ ℂ}
    [Finite T.faces] {α : ℂ → ℂ} {N : ℕ}
    {A : _root_.Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N))}
    {φ : ℂ → EuclideanSpace ℝ (Fin N)} {h : EuclideanSpace ℝ (Fin N) → M},
    IsPreparedSheetComplex_FIX (E := E3_FIX) f F T α N A φ h →
    ∀ {Nb : Set M} {R : M → M}, RelNbhd f F T α Nb R →
    IsEmpty (connectedComponentIn (frontier Nb) (f (diskBoundary 0)) ≃ₜ sphere2_R12) →
    ∃ (O : TopologicalSpace.Opens M) (M' : Type) (_ : TopologicalSpace M')
      (_ : ChartedSpace E3_FIX M') (_ : IsManifold 𝓘(ℝ, E3_FIX) ∞ M') (_ : T2Space M') (pr : M' → M)
      (hπ : ContMDiff 𝓘(ℝ, E3_FIX) 𝓘(ℝ, E3_FIX) ∞ pr)
      (himm : ∀ x, Function.Injective (mfderiv 𝓘(ℝ, E3_FIX) 𝓘(ℝ, E3_FIX) pr x))
      (τ : M' → M') (f' : C(closedDisk, M')) (Γ' : freeLoop M'),
      Nb ⊆ O ∧ IsConnected (O : Set M) ∧
      (∃ HO : unitInterval × M → M, ContinuousOn HO (univ ×ˢ (O : Set M)) ∧
        (∀ x ∈ (O : Set M), HO (0, x) = x) ∧ (∀ x ∈ (O : Set M), HO (1, x) ∈ Nb) ∧
        (∀ t, ∀ x ∈ Nb, HO (t, x) = x) ∧ ∀ t, MapsTo (fun x => HO (t, x)) O O) ∧
      Set.range pr = O ∧ IsCoveringMapOn pr (O : Set M) ∧ ConnectedSpace M' ∧
      ContMDiff 𝓘(ℝ, E3_FIX) 𝓘(ℝ, E3_FIX) ∞ τ ∧
      (∀ x, pr (τ x) = pr x) ∧ (∀ x, τ (τ x) = x) ∧ (∀ x, τ x ≠ x) ∧
      (∀ x y, pr x = pr y → y = x ∨ y = τ x) ∧ IsConnected (pr ⁻¹' Set.range f) ∧
      (∀ z, pr (f' z) = f z) ∧ (∀ θ, pr (Γ' θ) = Γ θ) ∧
      IsMorreyDisk (g.pullback pr hπ himm) Γ' f' ∧
      (∃ (F' : ℂ → M') (N' : ℕ)
        (A' : _root_.Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N')))
        (φ' : ℂ → EuclideanSpace ℝ (Fin N')) (h' : EuclideanSpace ℝ (Fin N') → M'),
        IsPreparedSheetComplex_FIX (E := E3_FIX) f' F' T α N' A' φ' h') ∧
      vertexCollisionPairs T (diskExtension f' ∘ α) ⊂
        vertexCollisionPairs T (diskExtension f ∘ α))
variable (hR14 : ∀ {M M' : Type}
    [TopologicalSpace M] [ChartedSpace E3_FIX M] [IsManifold 𝓘(ℝ, E3_FIX) ∞ M]
    [T2Space M] [TopologicalSpace M'] [ChartedSpace E3_FIX M'] [IsManifold 𝓘(ℝ, E3_FIX) ∞ M']
    [T2Space M'], Module.finrank ℝ E3_FIX = 3 →
    ∀ {g : SmoothRiemannianMetric 𝓘(ℝ, E3_FIX) M} {Γ : freeLoop M} {f : C(closedDisk, M)},
    IsMorreyDisk g Γ f → ∀ {F : ℂ → M} {T : _root_.Geometry.SimplicialComplex ℝ ℂ} {α : ℂ → ℂ}
    {N : ℕ} {A : _root_.Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N))}
    {φ : ℂ → EuclideanSpace ℝ (Fin N)} {h : EuclideanSpace ℝ (Fin N) → M},
    IsPreparedSheetComplex_FIX (E := E3_FIX) f F T α N A φ h →
    ∀ (O : TopologicalSpace.Opens M) (pr : M' → M) (_ : ContMDiff 𝓘(ℝ, E3_FIX) 𝓘(ℝ, E3_FIX) ∞ pr),
    (∀ x, Function.Injective (mfderiv 𝓘(ℝ, E3_FIX) 𝓘(ℝ, E3_FIX) pr x)) →
    IsCoveringMapOn pr (O : Set M) → Set.range pr = O → Set.range f ⊆ O →
    ∀ (τ : M' → M'), (∀ x, pr (τ x) = pr x) → (∀ x, τ (τ x) = x) → (∀ x, τ x ≠ x) →
    (∀ x y, pr x = pr y → y = x ∨ y = τ x) →
    ∀ (f' : C(closedDisk, M')), (∀ z, pr (f' z) = f z) → Function.Injective f' →
    Function.Injective f)

include hspine hR10 hcaps hR11 hR14

/-- **G3 consumer（平坦盘，`n = 0`）。** `flatDisk_prepared_FIX` 的 prepared 数据（`E = M = ℝ³`）喂给 G2：
`|P_T(f, α)| = 0`（`flatDisk_complexity_zero_FIX`）⇒ 归纳起点 `n = 0`；R4r 由 G4 discharge，
其余四条前提仍是 hypothesis。 -/
theorem flatDisk_injective_of_tower_R12 (g : SmoothRiemannianMetric 𝓘(ℝ, E3_FIX) E3_FIX)
    (Γ : freeLoop E3_FIX) (hf : IsMorreyDisk g Γ flatDisk_FIX) :
    Function.Injective flatDisk_FIX :=
  prepared_least_area_embedded_R12 finrank_euclideanSpace_fin RelNbhd hspine hR10 hcaps
    reparametrized_fold_competitor_R12 hR11 hR14
    0 hf flatDisk_prepared_FIX flatDisk_complexity_zero_FIX.le

end FlatDisk

section HC2

variable (RelNbhd : ∀ {M : Type u}
    [TopologicalSpace M] [ChartedSpace E3_FIX M] [IsManifold 𝓘(ℝ, E3_FIX) ∞ M]
    [T2Space M], C(closedDisk, M) → (ℂ → M) → _root_.Geometry.SimplicialComplex ℝ ℂ →
    (ℂ → ℂ) → Set M → (M → M) → Prop)
variable (hspine : ∀ {M : Type u}
    [TopologicalSpace M] [ChartedSpace E3_FIX M] [IsManifold 𝓘(ℝ, E3_FIX) ∞ M]
    [T2Space M] {f : C(closedDisk, M)} {F : ℂ → M} {T : _root_.Geometry.SimplicialComplex ℝ ℂ}
    {α : ℂ → ℂ} {Nb : Set M} {R : M → M}, RelNbhd f F T α Nb R → Set.range f ⊆ Nb)
variable (hR10 : ∀ {M : Type u}
    [TopologicalSpace M] [ChartedSpace E3_FIX M] [IsManifold 𝓘(ℝ, E3_FIX) ∞ M]
    [T2Space M], Module.finrank ℝ E3_FIX = 3 →
    ∀ {g : SmoothRiemannianMetric 𝓘(ℝ, E3_FIX) M} {Γ : freeLoop M} {f : C(closedDisk, M)},
    IsMorreyDisk g Γ f → ∀ {F : ℂ → M} {T : _root_.Geometry.SimplicialComplex ℝ ℂ} {α : ℂ → ℂ}
    {N : ℕ} {A : _root_.Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N))}
    {φ : ℂ → EuclideanSpace ℝ (Fin N)} {h : EuclideanSpace ℝ (Fin N) → M},
    IsPreparedSheetComplex_FIX (E := E3_FIX) f F T α N A φ h →
    ∃ (Nb : Set M) (R : M → M), RelNbhd f F T α Nb R)
variable (hcaps : ∀ {M : Type u}
    [TopologicalSpace M] [ChartedSpace E3_FIX M] [IsManifold 𝓘(ℝ, E3_FIX) ∞ M]
    [T2Space M], Module.finrank ℝ E3_FIX = 3 →
    ∀ {g : SmoothRiemannianMetric 𝓘(ℝ, E3_FIX) M} {Γ : freeLoop M} {f : C(closedDisk, M)},
    IsMorreyDisk g Γ f → ∀ {F : ℂ → M} {T : _root_.Geometry.SimplicialComplex ℝ ℂ} {α : ℂ → ℂ}
    {N : ℕ} {A : _root_.Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N))}
    {φ : ℂ → EuclideanSpace ℝ (Fin N)} {h : EuclideanSpace ℝ (Fin N) → M},
    IsPreparedSheetComplex_FIX (E := E3_FIX) f F T α N A φ h →
    ∀ {Nb : Set M} {R : M → M}, RelNbhd f F T α Nb R →
    Nonempty (connectedComponentIn (frontier Nb) (f (diskBoundary 0)) ≃ₜ sphere2_R12) →
    ∃ ap am : C(closedDisk, M),
      (∃ L : ℝ≥0, ∀ z w : closedDisk,
        riemannianEDistOf g (ap z) (ap w) ≤ (L : ℝ≥0∞) * edist z w) ∧
      (∃ L : ℝ≥0, ∀ z w : closedDisk,
        riemannianEDistOf g (am z) (am w) ≤ (L : ℝ≥0∞) * edist z w) ∧
      DiskWeakJordanTrace Γ ap ∧ DiskWeakJordanTrace Γ am ∧
      riemannianDiskArea g ap + riemannianDiskArea g am ≤ 2 * riemannianDiskArea g f ∧
      ((∃ x y : closedDisk, x ≠ y ∧ f x = f y) →
        riemannianDiskArea g ap + riemannianDiskArea g am < 2 * riemannianDiskArea g f ∨
          HasReparametrizedFold_R12 g ap (diskExtension f) ∨
            HasReparametrizedFold_R12 g am (diskExtension f)))
variable (hR11 : ∀ {M : Type u}
    [TopologicalSpace M] [ChartedSpace E3_FIX M] [IsManifold 𝓘(ℝ, E3_FIX) ∞ M]
    [T2Space M], Module.finrank ℝ E3_FIX = 3 →
    ∀ {g : SmoothRiemannianMetric 𝓘(ℝ, E3_FIX) M} {Γ : freeLoop M} {f : C(closedDisk, M)},
    IsMorreyDisk g Γ f → ∀ {F : ℂ → M} {T : _root_.Geometry.SimplicialComplex ℝ ℂ}
    [Finite T.faces] {α : ℂ → ℂ} {N : ℕ}
    {A : _root_.Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N))}
    {φ : ℂ → EuclideanSpace ℝ (Fin N)} {h : EuclideanSpace ℝ (Fin N) → M},
    IsPreparedSheetComplex_FIX (E := E3_FIX) f F T α N A φ h →
    ∀ {Nb : Set M} {R : M → M}, RelNbhd f F T α Nb R →
    IsEmpty (connectedComponentIn (frontier Nb) (f (diskBoundary 0)) ≃ₜ sphere2_R12) →
    ∃ (O : TopologicalSpace.Opens M) (M' : Type u) (_ : TopologicalSpace M')
      (_ : ChartedSpace E3_FIX M') (_ : IsManifold 𝓘(ℝ, E3_FIX) ∞ M') (_ : T2Space M') (pr : M' → M)
      (hπ : ContMDiff 𝓘(ℝ, E3_FIX) 𝓘(ℝ, E3_FIX) ∞ pr)
      (himm : ∀ x, Function.Injective (mfderiv 𝓘(ℝ, E3_FIX) 𝓘(ℝ, E3_FIX) pr x))
      (τ : M' → M') (f' : C(closedDisk, M')) (Γ' : freeLoop M'),
      Nb ⊆ O ∧ IsConnected (O : Set M) ∧
      (∃ HO : unitInterval × M → M, ContinuousOn HO (univ ×ˢ (O : Set M)) ∧
        (∀ x ∈ (O : Set M), HO (0, x) = x) ∧ (∀ x ∈ (O : Set M), HO (1, x) ∈ Nb) ∧
        (∀ t, ∀ x ∈ Nb, HO (t, x) = x) ∧ ∀ t, MapsTo (fun x => HO (t, x)) O O) ∧
      Set.range pr = O ∧ IsCoveringMapOn pr (O : Set M) ∧ ConnectedSpace M' ∧
      ContMDiff 𝓘(ℝ, E3_FIX) 𝓘(ℝ, E3_FIX) ∞ τ ∧
      (∀ x, pr (τ x) = pr x) ∧ (∀ x, τ (τ x) = x) ∧ (∀ x, τ x ≠ x) ∧
      (∀ x y, pr x = pr y → y = x ∨ y = τ x) ∧ IsConnected (pr ⁻¹' Set.range f) ∧
      (∀ z, pr (f' z) = f z) ∧ (∀ θ, pr (Γ' θ) = Γ θ) ∧
      IsMorreyDisk (g.pullback pr hπ himm) Γ' f' ∧
      (∃ (F' : ℂ → M') (N' : ℕ)
        (A' : _root_.Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N')))
        (φ' : ℂ → EuclideanSpace ℝ (Fin N')) (h' : EuclideanSpace ℝ (Fin N') → M'),
        IsPreparedSheetComplex_FIX (E := E3_FIX) f' F' T α N' A' φ' h') ∧
      vertexCollisionPairs T (diskExtension f' ∘ α) ⊂
        vertexCollisionPairs T (diskExtension f ∘ α))
variable (hR14 : ∀ {M M' : Type u}
    [TopologicalSpace M] [ChartedSpace E3_FIX M] [IsManifold 𝓘(ℝ, E3_FIX) ∞ M]
    [T2Space M] [TopologicalSpace M'] [ChartedSpace E3_FIX M'] [IsManifold 𝓘(ℝ, E3_FIX) ∞ M']
    [T2Space M'], Module.finrank ℝ E3_FIX = 3 →
    ∀ {g : SmoothRiemannianMetric 𝓘(ℝ, E3_FIX) M} {Γ : freeLoop M} {f : C(closedDisk, M)},
    IsMorreyDisk g Γ f → ∀ {F : ℂ → M} {T : _root_.Geometry.SimplicialComplex ℝ ℂ} {α : ℂ → ℂ}
    {N : ℕ} {A : _root_.Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N))}
    {φ : ℂ → EuclideanSpace ℝ (Fin N)} {h : EuclideanSpace ℝ (Fin N) → M},
    IsPreparedSheetComplex_FIX (E := E3_FIX) f F T α N A φ h →
    ∀ (O : TopologicalSpace.Opens M) (pr : M' → M) (_ : ContMDiff 𝓘(ℝ, E3_FIX) 𝓘(ℝ, E3_FIX) ∞ pr),
    (∀ x, Function.Injective (mfderiv 𝓘(ℝ, E3_FIX) 𝓘(ℝ, E3_FIX) pr x)) →
    IsCoveringMapOn pr (O : Set M) → Set.range pr = O → Set.range f ⊆ O →
    ∀ (τ : M' → M'), (∀ x, pr (τ x) = pr x) → (∀ x, τ (τ x) = x) → (∀ x, τ x ≠ x) →
    (∀ x y, pr x = pr y → y = x ∨ y = τ x) →
    ∀ (f' : C(closedDisk, M')), (∀ z, pr (f' z) = f z) → Function.Injective f' →
    Function.Injective f)

include hspine hR10 hcaps hR11 hR14

/-- **G3 consumer（`_HC2` 的 (U, G)）。** G2 在 `U = {ρ < a}`、`G = canonicalPositiveDomainMetric_P2A`
上的实例：`γU` 的 `IsMorreyDisk G γU f` + `IsPreparedSheetComplex_FIX`（`E = ℝ³`）+ complexity 上界 `n`
⇒ `f` 单射。 -/
theorem prepared_least_area_embedded_HC2_R12
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} (t : ℝ)
    (a : ℝ) (ha : 0 < a)
    (ρ : (postStage F.observation t).Carrier → ℝ) (hρ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ ρ) :
    let U : Opens (postStage F.observation t).Carrier :=
      ⟨{x | ρ x < a}, isOpen_lt hρ.continuous continuous_const⟩
    let δ : (postStage F.observation t).Carrier → ℝ := fun x => cutoff_P2A a (ρ x)
    let hδ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ δ :=
      (cutoff_smooth_P2A a).contMDiff.comp hρ
    let hU : ∀ x : (postStage F.observation t).Carrier, x ∈ U ↔ 0 < δ x :=
      fun x => (cutoff_pos_iff_P2A ha (ρ x)).symm
    let G := canonicalPositiveDomainMetric_P2A (postMetric F.observation t) hδ U hU
    ∀ (n : ℕ) (γU : freeLoop U) (f : C(closedDisk, U)) {F' : ℂ → U}
      {T : _root_.Geometry.SimplicialComplex ℝ ℂ} [Finite T.faces] {α : ℂ → ℂ} {N : ℕ}
      {A : _root_.Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N))}
      {φ : ℂ → EuclideanSpace ℝ (Fin N)} {h : EuclideanSpace ℝ (Fin N) → U},
      IsMorreyDisk G γU f → IsPreparedSheetComplex_FIX (E := E3_FIX) f F' T α N A φ h →
      (vertexCollisionPairs T (diskExtension f ∘ α)).card ≤ n → Function.Injective f := by
  intro U δ hδ hU G n γU f F' T _ α N A φ h hf hprep hcard
  exact prepared_least_area_embedded_R12 finrank_euclideanSpace_fin RelNbhd hspine hR10 hcaps
    reparametrized_fold_competitor_R12 hR11 hR14
    n hf hprep hcard

end HC2

end GC.LongTime.CuspP1
