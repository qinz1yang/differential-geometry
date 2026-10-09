import DifferentialGeometry.Geometry.MinimalSurface.Plateau.TowerEngineR12
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.FoldCompetitorR4rR12
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.CollisionEdgeSidesR10
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.R11StepAlignR11PL

/-!
# S-MY-R12 G3'：G2 与 O-MY-R10PL / S-MY-R11PL 实际交付的陈述对齐

`prepared_least_area_embedded_R12` 的 `RelNbhd f F T α Nb R` 取成 O-MY-R10PL 的输出形状
`IsRelRegularNbhd_R10 f Nb R ∧ IsSectorControlledCollapse_R10 F T α Nb R`（同一 `Nb R`，R-MY3），
各前提对着两条车道的真实定理核对：

* `range_subset_of_relRegularNbhd_R10_R12`：`hspine` 是 `IsRelRegularNbhd_R10` 的 `⟨hLN, _⟩` 投影；
* `hR10_of_localProduct_R12`：`hR10`（R10.1 + R10.2 联合 producer）= `relative_regular_nbhd_sector_R10`，
  额外只需 R9 rev3 的第 23 字段 `local_product : HasLocalProductCollapse_R10 …`（作 ∀-前提）；
  O-MY-R10PL 的一般 producer `relative_regular_nbhd_spine_R10` 只给 `IsRelRegularNbhd_R10` 一半，
  所以联合形必须带 `local_product`（他们的 state 里同样记为 R9 字段请求）；
* `hlt_of_cover_R12`：`hR11` 输出里的 `hlt`（`P_T(f', α) ⊊ P_T(f, α)`）可由同一输出的 deck / 纤维 /
  `p⁻¹(L)` 连通 / lift 与两份 prepared 数据经 S-MY-R11PL `vertexCollisionPairs_ssubset_of_cover_R11PL`
  推出（所以 `hR11` 的 `hlt` 子句是冗余的，保留它是为了逐字对齐 scratch 合同）；
* `hasAmbientCollar_of_hR11_R12`：`hR11` 输出的 `Nb ⊆ O ∧ HO`（开 `O` 强形变收缩到 `Nb`）就是
  `HasAmbientCollar_R10 Nb`——R10PL 把它记为 R9 字段 `ambient_collar`；
* `hR11_collar_of_hasAmbientCollar_R12`：反向（R10PL 的 `HasAmbientCollar_R10` 供给 `hR11` 的 `HO`）；
* `prepared_least_area_embedded_aligned_R12`：G2 在上述实例化下的整条链，R4r 由 G4 discharge，
  剩余显式前提 = `local_product`（R9 字段）+ `hcaps`（10.3/10.4）+ `hR11`（R11-step 总装）+ `hR14`。
-/

set_option autoImplicit false
noncomputable section

open Set DifferentialGeometry.Topology DifferentialGeometry.Topology.PiecewiseLinear
open scoped Manifold ContDiff NNReal ENNReal

namespace DifferentialGeometry.Geometry

universe u

section Align

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- `hspine`：`IsRelRegularNbhd_R10` 的 `range f ⊆ Nb` 投影。 -/
theorem range_subset_of_relRegularNbhd_R12 {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
    {f : C(closedDisk, M)} {F : ℂ → M} {T : _root_.Geometry.SimplicialComplex ℝ ℂ} {α : ℂ → ℂ}
    {Nb : Set M} {R : M → M}
    (hN : IsRelRegularNbhd_R10 f Nb R ∧ IsSectorControlledCollapse_R10 (E := E) F T α Nb R) :
    Set.range f ⊆ Nb := by
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, ⟨hLN, -⟩⟩, -⟩ := hN
  exact hLN

/-- `hR10`：R10.1 + R10.2 联合 producer（`relative_regular_nbhd_sector_R10`）+ R9 字段 `local_product`。 -/
theorem hR10_of_localProduct_R12
    (hlp : ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
      [T2Space M] {f : C(closedDisk, M)} {F : ℂ → M}
      {T : _root_.Geometry.SimplicialComplex ℝ ℂ} {α : ℂ → ℂ} {N : ℕ}
      {A : _root_.Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N))}
      {φ : ℂ → EuclideanSpace ℝ (Fin N)} {h : EuclideanSpace ℝ (Fin N) → M},
      IsPreparedSheetComplex_FIX (E := E) f F T α N A φ h →
      HasLocalProductCollapse_R10 (E := E) f F T α (h '' A.space))
    {M : Type u} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    (_ : Module.finrank ℝ E = 3) {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {Γ : freeLoop M}
    {f : C(closedDisk, M)} (_ : IsMorreyDisk g Γ f) {F : ℂ → M}
    {T : _root_.Geometry.SimplicialComplex ℝ ℂ} {α : ℂ → ℂ} {N : ℕ}
    {A : _root_.Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N))}
    {φ : ℂ → EuclideanSpace ℝ (Fin N)} {h : EuclideanSpace ℝ (Fin N) → M}
    (hprep : IsPreparedSheetComplex_FIX (E := E) f F T α N A φ h) :
    ∃ (Nb : Set M) (R : M → M), (IsRelRegularNbhd_R10 f Nb R ∧
      IsSectorControlledCollapse_R10 (E := E) F T α Nb R) := by
  obtain ⟨Nb, R, hN, hsc, -⟩ := relative_regular_nbhd_sector_R10 hprep (hlp hprep)
  exact ⟨Nb, R, hN, hsc⟩

omit [FiniteDimensional ℝ E] in
/-- `hR11` 输出里的 `hlt`：由同一输出的 cover 数据 + 两份 prepared 数据经 S-MY-R11PL G1 推出。 -/
theorem hlt_of_cover_R12 {M M' : Type u} [TopologicalSpace M] [ChartedSpace E M]
    [TopologicalSpace M'] [ChartedSpace E M'] [T2Space M'] {f : C(closedDisk, M)} {F : ℂ → M}
    {f' : C(closedDisk, M')} {F' : ℂ → M'} {T : _root_.Geometry.SimplicialComplex ℝ ℂ}
    [Finite T.faces] {α : ℂ → ℂ} {N N' : ℕ}
    {A : _root_.Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N))}
    {A' : _root_.Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N'))}
    {φ : ℂ → EuclideanSpace ℝ (Fin N)} {φ' : ℂ → EuclideanSpace ℝ (Fin N')}
    {h : EuclideanSpace ℝ (Fin N) → M} {h' : EuclideanSpace ℝ (Fin N') → M'}
    (hprep : IsPreparedSheetComplex_FIX (E := E) f F T α N A φ h)
    (hprep' : IsPreparedSheetComplex_FIX (E := E) f' F' T α N' A' φ' h')
    (pr : M' → M) (hlift : ∀ z, pr (f' z) = f z) (τ : M' → M')
    (hτ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ τ) (hτ₁ : ∀ x, pr (τ x) = pr x) (hτ₃ : ∀ x, τ x ≠ x)
    (hfib : ∀ x y, pr x = pr y → y = x ∨ y = τ x) (hconn : IsConnected (pr ⁻¹' Set.range f)) :
    vertexCollisionPairs T (diskExtension f' ∘ α) ⊂
      vertexCollisionPairs T (diskExtension f ∘ α) :=
  vertexCollisionPairs_ssubset_of_cover_R11PL hprep hprep' pr hlift τ hτ.continuous hτ₁ hτ₃ hfib
    hconn

omit [FiniteDimensional ℝ E] in
/-- `hR11` 输出的 `Nb ⊆ O ∧ HO` 就是 `HasAmbientCollar_R10 Nb`。 -/
theorem hasAmbientCollar_of_hR11_R12 {M : Type u} [TopologicalSpace M] {Nb : Set M}
    (O : TopologicalSpace.Opens M) (hNO : Nb ⊆ O)
    (hHO : ∃ HO : unitInterval × M → M, ContinuousOn HO (univ ×ˢ (O : Set M)) ∧
      (∀ x ∈ (O : Set M), HO (0, x) = x) ∧ (∀ x ∈ (O : Set M), HO (1, x) ∈ Nb) ∧
      (∀ t, ∀ x ∈ Nb, HO (t, x) = x) ∧ ∀ t, MapsTo (fun x => HO (t, x)) O O) :
    HasAmbientCollar_R10 Nb := by
  obtain ⟨HO, h1, h2, h3, h4, h5⟩ := hHO
  exact ⟨O, HO, O.isOpen, hNO, h1, h2, h3, h4, h5⟩

omit [FiniteDimensional ℝ E] in
/-- 反向：R10PL 的 `HasAmbientCollar_R10 Nb`（R9 字段 `ambient_collar`）供给 `hR11` 输出的
`Nb ⊆ O ∧ HO`（取 `O := ⟨O, hO⟩`）。 -/
theorem hR11_collar_of_hasAmbientCollar_R12 {M : Type u} [TopologicalSpace M] {Nb : Set M}
    (hcol : HasAmbientCollar_R10 Nb) :
    ∃ O : TopologicalSpace.Opens M, Nb ⊆ O ∧
      ∃ HO : unitInterval × M → M, ContinuousOn HO (univ ×ˢ (O : Set M)) ∧
        (∀ x ∈ (O : Set M), HO (0, x) = x) ∧ (∀ x ∈ (O : Set M), HO (1, x) ∈ Nb) ∧
        (∀ t, ∀ x ∈ Nb, HO (t, x) = x) ∧ ∀ t, MapsTo (fun x => HO (t, x)) O O := by
  obtain ⟨O, G, hO, hNO, h1, h2, h3, h4, h5⟩ := hcol
  exact ⟨⟨O, hO⟩, hNO, G, h1, h2, h3, h4, h5⟩

variable (hcaps : ∀ {M : Type u}
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [T2Space M], Module.finrank ℝ E = 3 →
    ∀ {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {Γ : freeLoop M} {f : C(closedDisk, M)},
    IsMorreyDisk g Γ f → ∀ {F : ℂ → M} {T : _root_.Geometry.SimplicialComplex ℝ ℂ} {α : ℂ → ℂ}
    {N : ℕ} {A : _root_.Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N))}
    {φ : ℂ → EuclideanSpace ℝ (Fin N)} {h : EuclideanSpace ℝ (Fin N) → M},
    IsPreparedSheetComplex_FIX (E := E) f F T α N A φ h →
    ∀ {Nb : Set M} {R : M → M}, (IsRelRegularNbhd_R10 f Nb R ∧
    IsSectorControlledCollapse_R10 (E := E) F T α Nb R) →
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
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [T2Space M], Module.finrank ℝ E = 3 →
    ∀ {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {Γ : freeLoop M} {f : C(closedDisk, M)},
    IsMorreyDisk g Γ f → ∀ {F : ℂ → M} {T : _root_.Geometry.SimplicialComplex ℝ ℂ}
    [Finite T.faces] {α : ℂ → ℂ} {N : ℕ}
    {A : _root_.Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N))}
    {φ : ℂ → EuclideanSpace ℝ (Fin N)} {h : EuclideanSpace ℝ (Fin N) → M},
    IsPreparedSheetComplex_FIX (E := E) f F T α N A φ h →
    ∀ {Nb : Set M} {R : M → M}, (IsRelRegularNbhd_R10 f Nb R ∧
    IsSectorControlledCollapse_R10 (E := E) F T α Nb R) →
    IsEmpty (connectedComponentIn (frontier Nb) (f (diskBoundary 0)) ≃ₜ sphere2_R12) →
    ∃ (O : TopologicalSpace.Opens M) (M' : Type u) (_ : TopologicalSpace M')
      (_ : ChartedSpace E M') (_ : IsManifold 𝓘(ℝ, E) ∞ M') (_ : T2Space M') (pr : M' → M)
      (hπ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ pr)
      (himm : ∀ x, Function.Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) pr x))
      (τ : M' → M') (f' : C(closedDisk, M')) (Γ' : freeLoop M'),
      Nb ⊆ O ∧ IsConnected (O : Set M) ∧
      (∃ HO : unitInterval × M → M, ContinuousOn HO (univ ×ˢ (O : Set M)) ∧
        (∀ x ∈ (O : Set M), HO (0, x) = x) ∧ (∀ x ∈ (O : Set M), HO (1, x) ∈ Nb) ∧
        (∀ t, ∀ x ∈ Nb, HO (t, x) = x) ∧ ∀ t, MapsTo (fun x => HO (t, x)) O O) ∧
      Set.range pr = O ∧ IsCoveringMapOn pr (O : Set M) ∧ ConnectedSpace M' ∧
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ τ ∧
      (∀ x, pr (τ x) = pr x) ∧ (∀ x, τ (τ x) = x) ∧ (∀ x, τ x ≠ x) ∧
      (∀ x y, pr x = pr y → y = x ∨ y = τ x) ∧ IsConnected (pr ⁻¹' Set.range f) ∧
      (∀ z, pr (f' z) = f z) ∧ (∀ θ, pr (Γ' θ) = Γ θ) ∧
      IsMorreyDisk (g.pullback pr hπ himm) Γ' f' ∧
      (∃ (F' : ℂ → M') (N' : ℕ)
        (A' : _root_.Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N')))
        (φ' : ℂ → EuclideanSpace ℝ (Fin N')) (h' : EuclideanSpace ℝ (Fin N') → M'),
        IsPreparedSheetComplex_FIX (E := E) f' F' T α N' A' φ' h') ∧
      vertexCollisionPairs T (diskExtension f' ∘ α) ⊂
        vertexCollisionPairs T (diskExtension f ∘ α))
variable (hR14 : ∀ {M M' : Type u}
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [T2Space M] [TopologicalSpace M'] [ChartedSpace E M'] [IsManifold 𝓘(ℝ, E) ∞ M']
    [T2Space M'], Module.finrank ℝ E = 3 →
    ∀ {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {Γ : freeLoop M} {f : C(closedDisk, M)},
    IsMorreyDisk g Γ f → ∀ {F : ℂ → M} {T : _root_.Geometry.SimplicialComplex ℝ ℂ} {α : ℂ → ℂ}
    {N : ℕ} {A : _root_.Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N))}
    {φ : ℂ → EuclideanSpace ℝ (Fin N)} {h : EuclideanSpace ℝ (Fin N) → M},
    IsPreparedSheetComplex_FIX (E := E) f F T α N A φ h →
    ∀ (O : TopologicalSpace.Opens M) (pr : M' → M) (_ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ pr),
    (∀ x, Function.Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) pr x)) →
    IsCoveringMapOn pr (O : Set M) → Set.range pr = O → Set.range f ⊆ O →
    ∀ (τ : M' → M'), (∀ x, pr (τ x) = pr x) → (∀ x, τ (τ x) = x) → (∀ x, τ x ≠ x) →
    (∀ x y, pr x = pr y → y = x ∨ y = τ x) →
    ∀ (f' : C(closedDisk, M')), (∀ z, pr (f' z) = f z) → Function.Injective f' →
    Function.Injective f)

include hcaps hR11 hR14

/-- **G2 在 R10PL / R11PL 实际 notion 下的整条链**：`RelNbhd := IsRelRegularNbhd_R10 ∧
IsSectorControlledCollapse_R10`，`hspine` / `hR10` 由 R10PL 的投影与联合 producer（带 `local_product`）
discharge，`hR4r` 由 G4 discharge；剩余显式前提 `hcaps`（10.3/10.4 弱版）、`hR11`（R11-step）、`hR14`。 -/
theorem prepared_least_area_embedded_aligned_R12 (hdim : Module.finrank ℝ E = 3)
    (hlp : ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
      [T2Space M] {f : C(closedDisk, M)} {F : ℂ → M}
      {T : _root_.Geometry.SimplicialComplex ℝ ℂ} {α : ℂ → ℂ} {N : ℕ}
      {A : _root_.Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N))}
      {φ : ℂ → EuclideanSpace ℝ (Fin N)} {h : EuclideanSpace ℝ (Fin N) → M},
      IsPreparedSheetComplex_FIX (E := E) f F T α N A φ h →
      HasLocalProductCollapse_R10 (E := E) f F T α (h '' A.space))
    (n : ℕ) {M : Type u} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [T2Space M] {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {Γ : freeLoop M} {f : C(closedDisk, M)}
    {F : ℂ → M} {T : _root_.Geometry.SimplicialComplex ℝ ℂ} [Finite T.faces] {α : ℂ → ℂ} {N : ℕ}
    {A : _root_.Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N))}
    {φ : ℂ → EuclideanSpace ℝ (Fin N)} {h : EuclideanSpace ℝ (Fin N) → M}
    (hf : IsMorreyDisk g Γ f) (hprep : IsPreparedSheetComplex_FIX (E := E) f F T α N A φ h)
    (hcard : (vertexCollisionPairs T (diskExtension f ∘ α)).card ≤ n) : Function.Injective f :=
  prepared_least_area_embedded_R12 hdim
    (fun f F T α Nb R => IsRelRegularNbhd_R10 f Nb R ∧
      IsSectorControlledCollapse_R10 (E := E) F T α Nb R)
    range_subset_of_relRegularNbhd_R12 (hR10_of_localProduct_R12 hlp) hcaps
    reparametrized_fold_competitor_R12 hR11 hR14 n hf hprep hcard

end Align

end DifferentialGeometry.Geometry
